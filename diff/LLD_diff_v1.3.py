#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
로그 비교 GUI (WinMerge 유사) - diff-match-patch 기반 (개선판 + 3대 개선)

【추가 개선 3개】
1) lines_to_chars 유니코드 초과 시 fallback
   - diff-match-patch 매핑 실패(ValueError) → difflib opcode 기반 hunk 생성으로 자동 전환

2) TF-IDF 예외 로그(디버그 옵션)
   - GUI에서 "디버그 로그" 체크 시, TF-IDF 벡터화 실패 원인을 로그로 출력(과다 로그 방지)

3) 가중치 자동 정규화(UX)
   - GUI에서 "자동 정규화" 체크 시, 실행 시점에 가중치 합이 1.0이 되도록 자동 보정
   - 슬라이더 값은 건드리지 않고, 실행 파라미터만 정규화 + 로그에 적용값 출력
"""

from __future__ import annotations

import os
import re
import fnmatch
import threading
import queue
import time
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple, Set

from difflib import SequenceMatcher

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from tkinter.scrolledtext import ScrolledText

import difflib
from diff_match_patch import diff_match_patch

from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity


# ==========
# 설정
# ==========

PREFERRED_ENCODINGS = ["utf-8", "utf-8-sig", "cp932", "euc-kr"]
MAX_FILE_SIZE_BYTES = 100 * 1024 * 1024
MAX_SAMPLE_SIZE = 50000  # TF-IDF용 샘플 크기

PREVIEW_N = 10
TOP_N = 20

END_MARKER = "----------------------------------------------------------------------------------------------------[END]"
BLOCK_HEADER_RE = re.compile(r"^\s*#\s+(.*)$")

# 기본 파라미터
DEFAULT_PARAMS = {
    "threshold": 0.45,
    "weights": {
        "key": 0.25,
        "yaml_sig": 0.25,
        "yaml_keys": 0.20,
        "tfidf": 0.30,
    },
}

# TF-IDF 에러 로그 과다 방지(1회 실행당 최대 N개)
TFIDF_ERROR_LOG_LIMIT = 50


# ==========
# 무시 규칙
# ==========

IGNORE_LINE_RULES: List[Tuple[re.Pattern, str]] = [
    (re.compile(r"^\s*[\-]?\s*uid\s*:\s*.*$", re.IGNORECASE), "__IGNORED_UID__"),
    (re.compile(r"^\s*[\-]?\s*Local time\s*:\s*.*$", re.IGNORECASE), "__IGNORED_LOCAL_TIME__"),
    (re.compile(r"^\s*[\-]?\s*generation\s*:\s*.*$", re.IGNORECASE), "generation: __IGNORED__"),
    (re.compile(r"^\s*[\-]?\s*creationTimestamp\s*:\s*.*$", re.IGNORECASE), "creationTimestamp: __IGNORED__"),
    (re.compile(r"^\s*[\-]?\s*lastTransitionTime\s*:\s*.*$", re.IGNORECASE), "lastTransitionTime: __IGNORED__"),
    (re.compile(r"^\s*[\-]?\s*lastResync\s*:\s*.*$", re.IGNORECASE), "lastResync: __IGNORED__"),
    (re.compile(r"^\s*[\-]?\s*observedGeneration\s*:\s*.*$", re.IGNORECASE), "observedGeneration: __IGNORED__"),
    (re.compile(r"^\s*[\-]?\s*managedFields\s*:\s*.*$", re.IGNORECASE), "managedFields: __IGNORED_SECTION__"),
    (re.compile(r"^\s*[\-]?\s*Universal time\s*:\s*.*$", re.IGNORECASE), "Universal time: __IGNORED_SECTION__"),
    (re.compile(r"^\s*[\-]?\s*resourceVersion\s*:\s*.*$", re.IGNORECASE), "resourceVersion: __IGNORED_SECTION__"),
    (re.compile(r"^\s*[\-]?\s*RTC time\s*:\s*.*$", re.IGNORECASE), "RTC time: __IGNORED_SECTION__"),
]

YAML_IGNORE_SECTION_STARTS: List[re.Pattern] = [
    re.compile(r"^\s*managedFields\s*:\s*$", re.IGNORECASE),
    re.compile(r"^\s*kubectl\.kubernetes\.io/last-applied-configuration\s*:\s*\|\s*$", re.IGNORECASE),
]


# ==========
# 데이터 모델
# ==========

@dataclass
class LogBlock:
    key: str
    body_lines: List[str]
    header_line_no: Optional[int]
    body_start_line_no: int
    body_end_line_no: int
    yaml_signature: Optional[Dict[str, str]] = None
    body_text: str = ""
    yaml_keys: Optional[Set[str]] = None


@dataclass
class DiffHunk:
    index: int
    source_start: int
    source_end: int
    target_start: int
    target_end: int
    hunk_type: str
    source_lines: List[str]
    target_lines: List[str]


@dataclass
class FileDiffSummary:
    hunks: int
    inserted: int
    deleted: int
    replaced: int
    similarity_pct: int


@dataclass
class ComparisonParams:
    """비교 파라미터 캡슐화"""
    threshold: float
    weights: Dict[str, float]
    debug_tfidf: bool = False  # TF-IDF 예외 로그 출력 여부


# ==========
# 유틸: 경로/스캔
# ==========

def _is_subpath(parent: str, child: str) -> bool:
    """자식 경로가 부모 경로 아래에 있는지 확인"""
    try:
        parent = os.path.abspath(parent)
        child = os.path.abspath(child)
        return os.path.commonpath([parent, child]) == parent
    except ValueError:
        return False


def build_file_map(root: str, pattern: str, exclude_dir_abs: Optional[str] = None) -> Dict[str, str]:
    """파일 맵 구성"""
    root_abs = os.path.abspath(root)
    exclude_abs = os.path.abspath(exclude_dir_abs) if exclude_dir_abs else None

    file_map: Dict[str, str] = {}

    for dirpath, dirnames, filenames in os.walk(root_abs):
        dirpath_abs = os.path.abspath(dirpath)

        if exclude_abs:
            kept = []
            for d in dirnames:
                cand = os.path.abspath(os.path.join(dirpath_abs, d))
                if cand == exclude_abs or _is_subpath(exclude_abs, cand):
                    continue
                kept.append(d)
            dirnames[:] = kept

        filenames.sort()
        for name in filenames:
            if pattern and pattern != "*" and not fnmatch.fnmatch(name, pattern):
                continue
            abs_path = os.path.join(dirpath_abs, name)
            rel_path = os.path.relpath(abs_path, root_abs)
            file_map[rel_path] = abs_path

    return file_map


# ==========
# 파일 읽기 (상세 예외 처리)
# ==========

def read_text_lines_with_fallback(path: str) -> Tuple[Optional[List[str]], str]:
    """파일 읽기 (여러 인코딩 시도)"""
    try:
        size = os.path.getsize(path)
        if size > MAX_FILE_SIZE_BYTES:
            return None, f"FILE_SIZE_EXCEEDED: {size/1024/1024:.1f}MB"

        for enc in PREFERRED_ENCODINGS:
            try:
                with open(path, "r", encoding=enc, errors="replace") as f:
                    raw_lines = f.readlines()
                lines = [ln.rstrip("\r\n") for ln in raw_lines]
                return lines, enc
            except (UnicodeDecodeError, LookupError):
                continue

        return None, "ENCODING_UNSUPPORTED"

    except PermissionError:
        return None, f"PERMISSION_DENIED: {path}"
    except OSError as e:
        return None, f"OS_ERROR: {type(e).__name__}: {e}"
    except Exception as e:
        return None, f"READ_ERROR: {type(e).__name__}: {e}"


# ==========
# YAML 분석
# ==========

def extract_yaml_signature(lines: List[str]) -> Optional[Dict[str, str]]:
    """YAML 서명 추출 (apiVersion, kind, name 등)"""
    if not lines:
        return None

    sig: Dict[str, str] = {}

    for line in lines[:50]:
        line_stripped = line.strip()

        if line_stripped.startswith("apiVersion:"):
            val = line_stripped.split(":", 1)[1].strip()
            if val:
                sig["apiVersion"] = val
        elif line_stripped.startswith("kind:"):
            val = line_stripped.split(":", 1)[1].strip()
            if val:
                sig["kind"] = val
        elif re.match(r"^\s{2,4}name:\s+", line):
            val = line.split(":", 1)[1].strip()
            if val:
                sig["name"] = val
        elif re.match(r"^\s{2,4}namespace:\s+", line):
            val = line.split(":", 1)[1].strip()
            if val:
                sig["namespace"] = val
        elif re.match(r"^\s{2,4}uid:\s+", line):
            val = line.split(":", 1)[1].strip()
            if val:
                sig["uid"] = val

    if "apiVersion" in sig and "kind" in sig:
        return sig
    return None


def extract_yaml_keys(text: str) -> Optional[Set[str]]:
    """YAML 키 구조 추출"""
    if not text or len(text) < 10:
        return None

    keys: Set[str] = set()
    for line in text.split("\n"):
        match = re.match(r"^\s*([a-zA-Z_][a-zA-Z0-9_-]*)\s*:", line)
        if match:
            keys.add(match.group(1).lower())

    return keys if keys else None


# ==========
# 전처리
# ==========

def _indent_level(s: str) -> int:
    """들여쓰기 레벨 계산"""
    return len(s) - len(s.lstrip(" "))


def normalize_line(
    line: str,
    *,
    trim: bool,
    ignore_space: bool,
    ignore_case: bool,
) -> str:
    """라인 정규화"""
    for pat, token in IGNORE_LINE_RULES:
        if pat.match(line):
            return token

    s = line

    if trim:
        s = s.strip()

    if ignore_space:
        s = re.sub(r"\s+", " ", s)

    if ignore_case:
        s = s.lower()

    return s


def preprocess_lines(
    lines: List[str],
    *,
    trim: bool,
    ignore_space: bool,
    ignore_case: bool,
) -> List[str]:
    """라인 전처리 (YAML 섹션 무시 포함)"""
    out: List[str] = []
    skip_mode = False
    skip_base_indent = 0

    for ln in lines:
        if skip_mode:
            if ln.strip() == "":
                continue
            if _indent_level(ln) <= skip_base_indent:
                skip_mode = False
            else:
                continue

        if not skip_mode:
            for sp in YAML_IGNORE_SECTION_STARTS:
                if sp.match(ln):
                    skip_mode = True
                    skip_base_indent = _indent_level(ln)
                    out.append("__IGNORED_YAML_SECTION__")
                    break
            else:
                out.append(normalize_line(ln, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case))

    return out


# ==========
# 블록 분해
# ==========

def split_log_into_blocks(lines: List[str]) -> List[LogBlock]:
    """로그를 블록으로 분해"""
    blocks: List[LogBlock] = []

    current_key: Optional[str] = None
    current_header_ln: Optional[int] = None
    current_body: List[Tuple[int, str]] = []
    unheadered_body: List[Tuple[int, str]] = []

    def commit_current() -> None:
        nonlocal current_key, current_header_ln, current_body
        if current_key is None:
            return
        filtered = [(no, s) for (no, s) in current_body if s.strip() != END_MARKER]
        if filtered:
            body_lines = [s for _, s in filtered]
            body_start = filtered[0][0]
            body_end = filtered[-1][0]
        else:
            body_lines = []
            body_start = (current_header_ln or 0) + 1
            body_end = body_start - 1

        yaml_sig = extract_yaml_signature(body_lines)
        body_text = "\n".join(body_lines)
        yaml_keys = extract_yaml_keys(body_text)

        blocks.append(
            LogBlock(
                key=current_key.strip(),
                body_lines=body_lines,
                header_line_no=current_header_ln,
                body_start_line_no=body_start,
                body_end_line_no=body_end,
                yaml_signature=yaml_sig,
                body_text=body_text,
                yaml_keys=yaml_keys,
            )
        )
        current_key = None
        current_header_ln = None
        current_body = []

    for i, ln in enumerate(lines, 1):
        m = BLOCK_HEADER_RE.match(ln)
        if m:
            commit_current()
            current_key = m.group(1).strip()
            current_header_ln = i
            current_body = []
            continue

        if current_key is not None:
            current_body.append((i, ln))
        else:
            unheadered_body.append((i, ln))

    commit_current()

    if unheadered_body:
        filtered = [(no, s) for (no, s) in unheadered_body if s.strip() != END_MARKER]
        if filtered:
            body_lines = [s for _, s in filtered]
            body_start = filtered[0][0]
            body_end = filtered[-1][0]
            yaml_sig = extract_yaml_signature(body_lines)
            body_text = "\n".join(body_lines)
            yaml_keys = extract_yaml_keys(body_text)
            blocks.insert(
                0,
                LogBlock(
                    key="##UNHEADERED##",
                    body_lines=body_lines,
                    header_line_no=None,
                    body_start_line_no=body_start,
                    body_end_line_no=body_end,
                    yaml_signature=yaml_sig,
                    body_text=body_text,
                    yaml_keys=yaml_keys,
                ),
            )

    return blocks


def _canonicalize_block_key(key: str) -> str:
    """블록 키 정규화"""
    s = key.strip().lower()
    s = re.sub(r"([_\-])v\d+(\.\d+)*", r"\1v#", s)
    s = re.sub(r"\s*\(#\d+\)\s*$", "", s)
    return s


def _key_similarity(k1: str, k2: str) -> float:
    """블록 키 유사도"""
    return SequenceMatcher(None, _canonicalize_block_key(k1), _canonicalize_block_key(k2)).ratio()


def _yaml_signature_similarity(sig1: Optional[Dict[str, str]], sig2: Optional[Dict[str, str]]) -> float:
    """YAML 서명 유사도"""
    if sig1 is None and sig2 is None:
        return 1.0
    if sig1 is None or sig2 is None:
        return 0.0

    score = 0.0
    if sig1.get("apiVersion") == sig2.get("apiVersion"):
        score += 0.5
    if sig1.get("kind") == sig2.get("kind"):
        score += 0.3
    if sig1.get("name") and sig2.get("name"):
        if sig1.get("name") == sig2.get("name"):
            score += 0.2
    if sig1.get("namespace") and sig2.get("namespace"):
        if sig1.get("namespace") == sig2.get("namespace"):
            score += 0.1

    return min(score, 1.0)


def _yaml_keys_similarity(keys1: Optional[Set[str]], keys2: Optional[Set[str]]) -> float:
    """YAML 키 구조 유사도"""
    if keys1 is None and keys2 is None:
        return 1.0
    if keys1 is None or keys2 is None:
        return 0.0
    if not keys1 or not keys2:
        return 0.0

    intersection = len(keys1 & keys2)
    union = len(keys1 | keys2)
    if union == 0:
        return 0.0
    return intersection / union


def _body_structure_similarity_tfidf(
    body1: str,
    body2: str,
    *,
    debug: bool,
    log_cb: Optional[Callable[[str], None]],
    context: str,
) -> float:
    """본문 구조 유사도 (TF-IDF) - 샘플링 + 디버그 로그 옵션"""
    if not body1 and not body2:
        return 1.0
    if not body1 or not body2:
        return 0.0

    if len(body1) > MAX_SAMPLE_SIZE:
        body1 = body1[:MAX_SAMPLE_SIZE]
    if len(body2) > MAX_SAMPLE_SIZE:
        body2 = body2[:MAX_SAMPLE_SIZE]

    if len(body1) < 50 and len(body2) < 50:
        set1 = set(body1.split())
        set2 = set(body2.split())
        if not set1 and not set2:
            return 1.0
        intersection = len(set1 & set2)
        union = len(set1 | set2)
        return intersection / union if union > 0 else 0.0

    try:
        vectorizer = TfidfVectorizer(
            analyzer="char",
            ngram_range=(2, 3),
            lowercase=True,
            norm="l2",
        )
        vectors = vectorizer.fit_transform([body1, body2])
        similarity = cosine_similarity(vectors)[0, 1]
        return float(similarity)
    except Exception as e:
        if debug and log_cb:
            log_cb(f"[TFIDF_ERROR] {context} | {type(e).__name__}: {e}")
        return 0.0


def _block_similarity(
    sb: LogBlock,
    tb: LogBlock,
    params: ComparisonParams,
    *,
    log_cb: Optional[Callable[[str], None]],
) -> Tuple[float, Dict[str, float]]:
    """블록 유사도 계산 (파라미터 전달 방식)"""
    # kind 불일치 방지
    if (sb.yaml_signature is not None and tb.yaml_signature is not None):
        sb_kind = sb.yaml_signature.get("kind", "")
        tb_kind = tb.yaml_signature.get("kind", "")
        if sb_kind and tb_kind and sb_kind != tb_kind:
            return 0.0, {
                "key": 0.0,
                "yaml_sig": 0.0,
                "yaml_keys": 0.0,
                "body": 0.0,
                "reason": f'kind_mismatch: "{sb_kind}" != "{tb_kind}"',
            }

    key_sim = _key_similarity(sb.key, tb.key)
    yaml_sig_sim = _yaml_signature_similarity(sb.yaml_signature, tb.yaml_signature)
    yaml_keys_sim = _yaml_keys_similarity(sb.yaml_keys, tb.yaml_keys)

    ctx = f'"{sb.key}" vs "{tb.key}"'
    body_sim = _body_structure_similarity_tfidf(
        sb.body_text,
        tb.body_text,
        debug=params.debug_tfidf,
        log_cb=log_cb,
        context=ctx,
    )

    combined_sim = (
        (key_sim * params.weights["key"]) +
        (yaml_sig_sim * params.weights["yaml_sig"]) +
        (yaml_keys_sim * params.weights["yaml_keys"]) +
        (body_sim * params.weights["tfidf"])
    )

    detail = {
        "key": key_sim,
        "yaml_sig": yaml_sig_sim,
        "yaml_keys": yaml_keys_sim,
        "body": body_sim,
    }

    return combined_sim, detail


def align_blocks(
    src_blocks: List[LogBlock],
    tgt_blocks: List[LogBlock],
    params: ComparisonParams,
    *,
    log_cb: Optional[Callable[[str], None]],
) -> List[Tuple[Optional[LogBlock], Optional[LogBlock], str]]:
    """블록 정렬 (파라미터 전달)"""
    src_keys = [_canonicalize_block_key(b.key) for b in src_blocks]
    tgt_keys = [_canonicalize_block_key(b.key) for b in tgt_blocks]

    sm = SequenceMatcher(None, src_keys, tgt_keys)
    opcodes = sm.get_opcodes()

    aligned: List[Tuple[Optional[LogBlock], Optional[LogBlock], str]] = []

    for tag, i1, i2, j1, j2 in opcodes:
        if tag == "equal":
            for si, tj in zip(range(i1, i2), range(j1, j2)):
                b1 = src_blocks[si]
                b2 = tgt_blocks[tj]
                aligned.append((b1, b2, b1.key))
        elif tag == "delete":
            for si in range(i1, i2):
                b1 = src_blocks[si]
                aligned.append((b1, None, b1.key))
        elif tag == "insert":
            for tj in range(j1, j2):
                b2 = tgt_blocks[tj]
                aligned.append((None, b2, b2.key))
        else:  # replace
            src_span = src_blocks[i1:i2]
            tgt_span = tgt_blocks[j1:j2]

            used_tgt = set()
            pairs: List[Tuple[int, int, float]] = []

            for si, sb in enumerate(src_span):
                best_j = -1
                best_sim = 0.0
                for tj, tb in enumerate(tgt_span):
                    if tj in used_tgt:
                        continue
                    sim, _ = _block_similarity(sb, tb, params, log_cb=log_cb)
                    if sim > best_sim:
                        best_sim = sim
                        best_j = tj
                if best_j >= 0 and best_sim >= params.threshold:
                    used_tgt.add(best_j)
                    pairs.append((si, best_j, best_sim))

            paired_src = set(si for si, _, _ in pairs)
            paired_tgt = set(tj for _, tj, _ in pairs)

            for si, tj, _ in sorted(pairs, key=lambda x: x[0]):
                sb = src_span[si]
                tb = tgt_span[tj]
                aligned.append((sb, tb, sb.key))

            for si in range(len(src_span)):
                if si not in paired_src:
                    aligned.append((src_span[si], None, src_span[si].key))

            for tj in range(len(tgt_span)):
                if tj not in paired_tgt:
                    aligned.append((None, tgt_span[tj], tgt_span[tj].key))

    return aligned


# ==========
# diff-match-patch + Fallback(유니코드 초과)
# ==========

def lines_to_chars(a: List[str], b: List[str]) -> Tuple[str, str, List[str]]:
    """라인을 문자로 변환 (diff-match-patch용)"""
    line_array: List[str] = [""]
    line_hash: Dict[str, int] = {}

    def encode(lines: List[str]) -> str:
        out_chars: List[str] = []
        for ln in lines:
            if ln in line_hash:
                idx = line_hash[ln]
            else:
                idx = len(line_array)
                line_hash[ln] = idx
                line_array.append(ln)
                if idx > 0x10FFFF:
                    raise ValueError("Too many unique lines to map into Unicode code points.")
            out_chars.append(chr(idx))
        return "".join(out_chars)

    return encode(a), encode(b), line_array


def chars_to_lines(diffs: List[Tuple[int, str]], line_array: List[str]) -> List[Tuple[int, List[str]]]:
    """문자를 라인으로 변환"""
    out: List[Tuple[int, List[str]]] = []
    for op, text in diffs:
        lines: List[str] = []
        for ch in text:
            lines.append(line_array[ord(ch)])
        out.append((op, lines))
    return out


def build_hunks_from_diffs(diffs_lines: List[Tuple[int, List[str]]]) -> List[DiffHunk]:
    """diff-match-patch 결과에서 hunks 구성"""
    hunks: List[DiffHunk] = []

    src_ln = 1
    tgt_ln = 1
    hidx = 0
    i = 0

    while i < len(diffs_lines):
        op, lines = diffs_lines[i]

        if op == 0:
            n = len(lines)
            src_ln += n
            tgt_ln += n
            i += 1
            continue

        hunk_src_start = src_ln
        hunk_tgt_start = tgt_ln
        del_lines: List[str] = []
        ins_lines: List[str] = []

        while i < len(diffs_lines) and diffs_lines[i][0] != 0:
            op2, l2 = diffs_lines[i]
            if op2 == -1:
                del_lines.extend(l2)
            elif op2 == 1:
                ins_lines.extend(l2)
            i += 1

        if del_lines and ins_lines:
            htype = "replace"
        elif del_lines:
            htype = "delete"
        else:
            htype = "insert"

        if del_lines:
            src_start = hunk_src_start
            src_end = hunk_src_start + len(del_lines) - 1
        else:
            src_start = 0
            src_end = 0

        if ins_lines:
            tgt_start = hunk_tgt_start
            tgt_end = hunk_tgt_start + len(ins_lines) - 1
        else:
            tgt_start = 0
            tgt_end = 0

        src_ln = hunk_src_start + len(del_lines)
        tgt_ln = hunk_tgt_start + len(ins_lines)

        hidx += 1
        hunks.append(
            DiffHunk(
                index=hidx,
                source_start=src_start,
                source_end=src_end,
                target_start=tgt_start,
                target_end=tgt_end,
                hunk_type=htype,
                source_lines=del_lines,
                target_lines=ins_lines,
            )
        )

    return hunks


def build_hunks_from_opcodes(source_lines: List[str], target_lines: List[str]) -> List[DiffHunk]:
    """
    Fallback: difflib opcode 기반 hunk 생성
    - lines_to_chars가 유니코드 범위를 초과할 때 사용
    """
    sm = difflib.SequenceMatcher(None, source_lines, target_lines)
    hunks: List[DiffHunk] = []
    hidx = 0

    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue

        hidx += 1
        del_lines = source_lines[i1:i2] if tag in ("delete", "replace") else []
        ins_lines = target_lines[j1:j2] if tag in ("insert", "replace") else []

        if del_lines and ins_lines:
            htype = "replace"
        elif del_lines:
            htype = "delete"
        else:
            htype = "insert"

        src_start = i1 + 1 if del_lines else 0
        src_end = i2 if del_lines else 0

        tgt_start = j1 + 1 if ins_lines else 0
        tgt_end = j2 if ins_lines else 0

        hunks.append(
            DiffHunk(
                index=hidx,
                source_start=src_start,
                source_end=src_end,
                target_start=tgt_start,
                target_end=tgt_end,
                hunk_type=htype,
                source_lines=del_lines,
                target_lines=ins_lines,
            )
        )

    return hunks


def count_changes(hunks: List[DiffHunk]) -> Tuple[int, int, int]:
    """변경사항 계산"""
    inserted = 0
    deleted = 0
    replaced = 0
    for h in hunks:
        if h.hunk_type == "insert":
            inserted += len(h.target_lines)
        elif h.hunk_type == "delete":
            deleted += len(h.source_lines)
        else:
            deleted += len(h.source_lines)
            inserted += len(h.target_lines)
            replaced += min(len(h.source_lines), len(h.target_lines))
    return inserted, deleted, replaced


def diff_lines_winmerge_like(
    source_lines: List[str],
    target_lines: List[str],
    *,
    log_cb: Optional[Callable[[str], None]] = None,
) -> Tuple[List[DiffHunk], int]:
    """
    라인 단위 diff
    - 기본: diff-match-patch
    - fallback: lines_to_chars 유니코드 초과 시 difflib opcode 기반 hunks 생성
    """
    ratio = difflib.SequenceMatcher(None, source_lines, target_lines).ratio()
    similarity_pct = int(round(ratio * 100))

    try:
        a_chars, b_chars, line_array = lines_to_chars(source_lines, target_lines)

        dmp = diff_match_patch()
        diffs = dmp.diff_main(a_chars, b_chars, checklines=False)
        dmp.diff_cleanupSemantic(diffs)

        diffs_lines = chars_to_lines(diffs, line_array)
        hunks = build_hunks_from_diffs(diffs_lines)
        return hunks, similarity_pct

    except ValueError as e:
        # 유니코드 codepoint 범위 초과 등
        if log_cb:
            log_cb(f"[FALLBACK] diff-match-patch 사용 불가 → difflib fallback 적용: {type(e).__name__}: {e}")
        hunks = build_hunks_from_opcodes(source_lines, target_lines)
        return hunks, similarity_pct

    except Exception as e:
        # 기타 예외도 fallback
        if log_cb:
            log_cb(f"[FALLBACK] diff-match-patch 예외 → difflib fallback 적용: {type(e).__name__}: {e}")
        hunks = build_hunks_from_opcodes(source_lines, target_lines)
        return hunks, similarity_pct


# ==========
# 결과 파일 작성
# ==========

def ensure_report_root(output_base: str) -> str:
    """리포트 루트 디렉토리 생성"""
    base = os.path.abspath(output_base)
    if os.path.basename(base).lower() == "lld_diff":
        os.makedirs(base, exist_ok=True)
        return base
    report_root = os.path.join(base, "LLD_diff")
    os.makedirs(report_root, exist_ok=True)
    return report_root


def write_changed_report(
    report_root: str,
    rel_path: str,
    hunks_with_block: List[Tuple[str, Optional[LogBlock], Optional[LogBlock], DiffHunk]],
    similarity_pct: int,
) -> None:
    """변경된 파일 리포트 작성"""
    rel_dir = os.path.dirname(rel_path)
    out_dir = os.path.join(report_root, rel_dir) if rel_dir else report_root
    os.makedirs(out_dir, exist_ok=True)

    base_name = os.path.basename(rel_path)
    out_path = os.path.join(out_dir, f"{base_name}.txt")

    hunks_only = [h for _, _, _, h in hunks_with_block]
    inserted, deleted, replaced = count_changes(hunks_only)

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"Path: {rel_path}\n")
        f.write("Status: changed\n")
        f.write("Summary:\n")
        f.write(f"  Hunks: {len(hunks_only)}\n")
        f.write(f"  InsertedLines: {inserted}\n")
        f.write(f"  DeletedLines: {deleted}\n")
        f.write(f"  ReplacedLines: {replaced}\n")
        f.write(f"  Similarity: {similarity_pct}%\n")
        f.write("\n")

        for idx, (bkey, sb, tb, h) in enumerate(hunks_with_block, 1):
            f.write(f"HUNK {idx}\n")
            f.write(f"  Block: {bkey}\n")

            def absolute_line_range(block: Optional[LogBlock], start: int, end: int) -> str:
                if block is None or start <= 0 or end <= 0:
                    return "0-0"
                if end < start:
                    return "0-0"
                abs_s = block.body_start_line_no + (start - 1)
                abs_e = block.body_start_line_no + (end - 1)
                return f"{abs_s}-{abs_e}"

            src_range = absolute_line_range(sb, h.source_start, h.source_end)
            tgt_range = absolute_line_range(tb, h.target_start, h.target_end)

            src_label = sb.key if sb else "(none)"
            tgt_label = tb.key if tb else "(none)"

            f.write(f"  SourceRange: {src_range} ({src_label})\n")
            f.write(f"  TargetRange: {tgt_range} ({tgt_label})\n")
            f.write(f"  Type: {h.hunk_type}\n")

            if sb and sb.yaml_signature:
                f.write(f"  SourceYAML: {sb.yaml_signature.get('kind', '?')}/{sb.yaml_signature.get('name', '?')}\n")
            if tb and tb.yaml_signature:
                f.write(f"  TargetYAML: {tb.yaml_signature.get('kind', '?')}/{tb.yaml_signature.get('name', '?')}\n")

            f.write("  SourcePreview:\n")
            if not h.source_lines:
                f.write("    (none)\n")
            else:
                for ln in h.source_lines[:PREVIEW_N]:
                    f.write(f"    {ln}\n")
                if len(h.source_lines) > PREVIEW_N:
                    f.write("    ...(truncated)\n")

            f.write("  TargetPreview:\n")
            if not h.target_lines:
                f.write("    (none)\n")
            else:
                for ln in h.target_lines[:PREVIEW_N]:
                    f.write(f"    {ln}\n")
                if len(h.target_lines) > PREVIEW_N:
                    f.write("    ...(truncated)\n")

            f.write("\n")


# ==========
# 비교 엔진
# ==========

class ComparisonEngine:
    """비교 엔진"""
    def __init__(
        self,
        progress_cb: Optional[Callable[[int, int, str], None]] = None,
        log_cb: Optional[Callable[[str], None]] = None,
    ):
        self.progress_cb = progress_cb
        self.log_cb = log_cb
        self._tfidf_error_count = 0

    def _log(self, msg: str) -> None:
        if self.log_cb:
            self.log_cb(msg)

    def _tfidf_log(self, msg: str) -> None:
        # 과다 로그 방지
        if self._tfidf_error_count >= TFIDF_ERROR_LOG_LIMIT:
            return
        self._tfidf_error_count += 1
        self._log(msg)

    def compare_folders(
        self,
        source_root: str,
        target_root: str,
        output_base: str,
        *,
        trim: bool,
        ignore_space: bool,
        ignore_case: bool,
        file_pattern: str,
        block_mode: bool = True,
        params: Optional[ComparisonParams] = None,
    ) -> Dict[str, object]:
        """폴더 비교 실행"""
        if params is None:
            params = ComparisonParams(
                threshold=DEFAULT_PARAMS["threshold"],
                weights=DEFAULT_PARAMS["weights"].copy(),
                debug_tfidf=False,
            )

        source_root = os.path.abspath(source_root)
        target_root = os.path.abspath(target_root)
        output_base = os.path.abspath(output_base)

        report_root = ensure_report_root(output_base)

        exclude_source = report_root if _is_subpath(source_root, report_root) else None
        exclude_target = report_root if _is_subpath(target_root, report_root) else None

        pattern = file_pattern.strip() or "all"
        if pattern.lower() == "all":
            pattern = "*"

        src_map = build_file_map(source_root, pattern, exclude_dir_abs=exclude_source)
        tgt_map = build_file_map(target_root, pattern, exclude_dir_abs=exclude_target)

        src_relpaths = set(src_map.keys())
        tgt_relpaths = set(tgt_map.keys())

        matched = sorted(src_relpaths & tgt_relpaths)
        target_missing = sorted(src_relpaths - tgt_relpaths)
        source_missing = sorted(tgt_relpaths - src_relpaths)

        summary = {
            "TotalMatched": len(matched),
            "Identical": 0,
            "Changed": 0,
            "SourceMissing": len(source_missing),
            "TargetMissing": len(target_missing),
            "EncodingError": 0,
        }

        changed_details: List[Tuple[str, FileDiffSummary]] = []

        total_steps = max(len(matched) + len(source_missing) + len(target_missing), 1)
        done = 0

        def advance(label: str) -> None:
            nonlocal done
            done += 1
            if self.progress_cb:
                self.progress_cb(done, total_steps, label)

        for rel in target_missing:
            advance(f"{rel} (target_missing)")

        for rel in source_missing:
            advance(f"{rel} (source_missing)")

        for rel in matched:
            sp = src_map[rel]
            tp = tgt_map[rel]

            s_lines, s_enc = read_text_lines_with_fallback(sp)
            t_lines, t_enc = read_text_lines_with_fallback(tp)

            if s_lines is None or t_lines is None:
                summary["EncodingError"] += 1
                self._log(f"[READ_FAIL] {rel} | src={s_enc} | tgt={t_enc}")
                advance(f"{rel} (encoding_error)")
                continue

            if block_mode:
                src_blocks = split_log_into_blocks(s_lines)
                tgt_blocks = split_log_into_blocks(t_lines)

                aligned = align_blocks(
                    src_blocks,
                    tgt_blocks,
                    params,
                    log_cb=self._tfidf_log if params.debug_tfidf else None,
                )

                all_hunks_with_block: List[Tuple[str, Optional[LogBlock], Optional[LogBlock], DiffHunk]] = []

                sim_src_concat: List[str] = []
                sim_tgt_concat: List[str] = []

                for sb, tb, label_key in aligned:
                    sim_src_concat.append(f"@@BLOCK@@ {label_key}")
                    sim_tgt_concat.append(f"@@BLOCK@@ {label_key}")

                    if sb is not None:
                        sim_src_concat.extend(sb.body_lines)
                    if tb is not None:
                        sim_tgt_concat.extend(tb.body_lines)

                    if sb is None and tb is not None:
                        h = DiffHunk(
                            index=0,
                            source_start=0,
                            source_end=0,
                            target_start=1,
                            target_end=max(1, len(tb.body_lines)),
                            hunk_type="insert",
                            source_lines=[],
                            target_lines=tb.body_lines,
                        )
                        all_hunks_with_block.append((label_key, None, tb, h))
                        continue

                    if sb is not None and tb is None:
                        h = DiffHunk(
                            index=0,
                            source_start=1,
                            source_end=max(1, len(sb.body_lines)),
                            target_start=0,
                            target_end=0,
                            hunk_type="delete",
                            source_lines=sb.body_lines,
                            target_lines=[],
                        )
                        all_hunks_with_block.append((label_key, sb, None, h))
                        continue

                    if sb is None or tb is None:
                        continue

                    s_proc = preprocess_lines(sb.body_lines, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)
                    t_proc = preprocess_lines(tb.body_lines, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)

                    hunks, _ = diff_lines_winmerge_like(
                        s_proc,
                        t_proc,
                        log_cb=self._log,
                    )
                    for h in hunks:
                        all_hunks_with_block.append((label_key, sb, tb, h))

                sim_src_proc = preprocess_lines(sim_src_concat, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)
                sim_tgt_proc = preprocess_lines(sim_tgt_concat, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)
                _, similarity_pct = diff_lines_winmerge_like(sim_src_proc, sim_tgt_proc, log_cb=self._log)

                if not all_hunks_with_block:
                    summary["Identical"] += 1
                else:
                    summary["Changed"] += 1

                    hunks_only = [h for _, _, _, h in all_hunks_with_block]
                    inserted, deleted, replaced = count_changes(hunks_only)
                    fd = FileDiffSummary(
                        hunks=len(hunks_only),
                        inserted=inserted,
                        deleted=deleted,
                        replaced=replaced,
                        similarity_pct=similarity_pct,
                    )
                    changed_details.append((rel, fd))
                    write_changed_report(report_root, rel, all_hunks_with_block, similarity_pct)

                advance(f"{rel} (compared)")
                continue

            # no block mode
            s_proc = preprocess_lines(s_lines, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)
            t_proc = preprocess_lines(t_lines, trim=trim, ignore_space=ignore_space, ignore_case=ignore_case)

            hunks, similarity_pct = diff_lines_winmerge_like(s_proc, t_proc, log_cb=self._log)

            if not hunks:
                summary["Identical"] += 1
            else:
                summary["Changed"] += 1
                inserted, deleted, replaced = count_changes(hunks)
                fd = FileDiffSummary(
                    hunks=len(hunks),
                    inserted=inserted,
                    deleted=deleted,
                    replaced=replaced,
                    similarity_pct=similarity_pct,
                )
                changed_details.append((rel, fd))

                hunks_with_block = [("##NO_BLOCK_MODE##", None, None, h) for h in hunks]
                write_changed_report(report_root, rel, hunks_with_block, similarity_pct)

            advance(f"{rel} (compared)")

        changed_details_sorted = sorted(
            changed_details,
            key=lambda x: (x[1].hunks, x[1].inserted + x[1].deleted, x[0]),
            reverse=True,
        )[:TOP_N]

        return {
            "summary": summary,
            "report_root": report_root,
            "top_changed": changed_details_sorted,
        }


# ==========
# GUI
# ==========

class App:
    """메인 GUI 애플리케이션"""
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("로그 비교 GUI (scikit-learn TF-IDF + YAML 키) - 개선판(+3대 개선)")
        self.root.geometry("980x820")

        self.source_var = tk.StringVar()
        self.target_var = tk.StringVar()
        self.output_var = tk.StringVar()

        self.trim_var = tk.BooleanVar(value=False)
        self.ignore_space_var = tk.BooleanVar(value=False)
        self.ignore_case_var = tk.BooleanVar(value=False)
        self.block_mode_var = tk.BooleanVar(value=True)

        self.filter_var = tk.StringVar(value="all")

        # 유사도 파라미터
        self.threshold_var = tk.DoubleVar(value=DEFAULT_PARAMS["threshold"])
        self.key_weight_var = tk.DoubleVar(value=DEFAULT_PARAMS["weights"]["key"])
        self.yaml_sig_weight_var = tk.DoubleVar(value=DEFAULT_PARAMS["weights"]["yaml_sig"])
        self.yaml_keys_weight_var = tk.DoubleVar(value=DEFAULT_PARAMS["weights"]["yaml_keys"])
        self.tfidf_weight_var = tk.DoubleVar(value=DEFAULT_PARAMS["weights"]["tfidf"])

        # 3대 개선: 자동 정규화 + TFIDF 디버그 옵션
        self.auto_norm_var = tk.BooleanVar(value=True)
        self.debug_tfidf_var = tk.BooleanVar(value=False)

        self.progress_var = tk.StringVar(value="0.0% - 대기 중")
        self.summary_var = tk.StringVar(value="요약: 원본과 비교대상 폴더를 선택 후 '비교 시작' 클릭하세요")
        self.param_var = tk.StringVar(value="")

        # 큐 maxsize
        self.q: queue.Queue[Tuple[str, object]] = queue.Queue(maxsize=1000)
        self.worker: Optional[threading.Thread] = None

        self._build_ui()

    def _build_ui(self) -> None:
        frm = ttk.Frame(self.root, padding=12)
        frm.pack(fill="both", expand=True)

        r0 = ttk.Frame(frm)
        r0.pack(fill="x", pady=4)
        ttk.Button(r0, text="원본 폴더 선택", command=self.pick_source).pack(side="left")
        ttk.Entry(r0, textvariable=self.source_var, state="readonly").pack(side="left", fill="x", expand=True, padx=8)

        r1 = ttk.Frame(frm)
        r1.pack(fill="x", pady=4)
        ttk.Button(r1, text="비교대상 폴더 선택", command=self.pick_target).pack(side="left")
        ttk.Entry(r1, textvariable=self.target_var, state="readonly").pack(side="left", fill="x", expand=True, padx=8)

        r2 = ttk.Frame(frm)
        r2.pack(fill="x", pady=4)
        ttk.Button(r2, text="출력 폴더 선택", command=self.pick_output).pack(side="left")
        ttk.Entry(r2, textvariable=self.output_var, state="readonly").pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(r2, text="기본(타겟/LLD_diff)", command=self.use_default_output).pack(side="left")

        # 옵션
        self.opt = ttk.LabelFrame(frm, text="옵션")
        self.opt.pack(fill="x", pady=8)

        ttk.Checkbutton(self.opt, text="라인 trim 후 비교", variable=self.trim_var).grid(row=0, column=0, sticky="w", padx=8, pady=4)
        ttk.Checkbutton(self.opt, text="공백만 다른 차이는 무시(연속 공백 정규화)", variable=self.ignore_space_var).grid(row=0, column=1, sticky="w", padx=8, pady=4)
        ttk.Checkbutton(self.opt, text="대소문자 무시", variable=self.ignore_case_var).grid(row=0, column=2, sticky="w", padx=8, pady=4)

        ttk.Checkbutton(
            self.opt,
            text="로그 블록(# ... 단위)로 비교 (블록 정렬 후 블록 내부 diff)",
            variable=self.block_mode_var,
        ).grid(row=1, column=0, columnspan=2, sticky="w", padx=8, pady=4)

        ttk.Label(self.opt, text="파일 필터:").grid(row=2, column=0, sticky="w", padx=8, pady=4)
        self.filter_combo = ttk.Combobox(self.opt, textvariable=self.filter_var, values=["all", "*.log", "*.txt"], width=20)
        self.filter_combo.grid(row=2, column=1, sticky="w", padx=8, pady=4)
        ttk.Label(self.opt, text="(직접 입력 가능: 예 foo*.log)").grid(row=2, column=2, sticky="w", padx=8, pady=4)

        ttk.Separator(self.opt, orient="horizontal").grid(row=3, column=0, columnspan=3, sticky="ew", padx=8, pady=8)

        # Threshold
        ttk.Label(self.opt, text="블록 매칭 임계값 (Threshold):").grid(row=4, column=0, sticky="w", padx=8, pady=4)
        ttk.Scale(self.opt, from_=0.30, to=0.70, variable=self.threshold_var, orient="horizontal").grid(row=4, column=1, sticky="ew", padx=8, pady=4)
        self.threshold_label = ttk.Label(self.opt, text=f"{self.threshold_var.get():.2f}")
        self.threshold_label.grid(row=4, column=2, sticky="w", padx=8)

        # Weights
        ttk.Label(self.opt, text="가중치 - 블록 키:").grid(row=5, column=0, sticky="w", padx=8, pady=4)
        ttk.Scale(self.opt, from_=0.0, to=0.5, variable=self.key_weight_var, orient="horizontal").grid(row=5, column=1, sticky="ew", padx=8, pady=4)
        self.key_weight_label = ttk.Label(self.opt, text=f"{self.key_weight_var.get():.2f}")
        self.key_weight_label.grid(row=5, column=2, sticky="w", padx=8)

        ttk.Label(self.opt, text="가중치 - YAML 서명:").grid(row=6, column=0, sticky="w", padx=8, pady=4)
        ttk.Scale(self.opt, from_=0.0, to=0.5, variable=self.yaml_sig_weight_var, orient="horizontal").grid(row=6, column=1, sticky="ew", padx=8, pady=4)
        self.yaml_sig_weight_label = ttk.Label(self.opt, text=f"{self.yaml_sig_weight_var.get():.2f}")
        self.yaml_sig_weight_label.grid(row=6, column=2, sticky="w", padx=8)

        ttk.Label(self.opt, text="가중치 - YAML 키:").grid(row=7, column=0, sticky="w", padx=8, pady=4)
        ttk.Scale(self.opt, from_=0.0, to=0.5, variable=self.yaml_keys_weight_var, orient="horizontal").grid(row=7, column=1, sticky="ew", padx=8, pady=4)
        self.yaml_keys_weight_label = ttk.Label(self.opt, text=f"{self.yaml_keys_weight_var.get():.2f}")
        self.yaml_keys_weight_label.grid(row=7, column=2, sticky="w", padx=8)

        ttk.Label(self.opt, text="가중치 - TF-IDF:").grid(row=8, column=0, sticky="w", padx=8, pady=4)
        ttk.Scale(self.opt, from_=0.0, to=0.5, variable=self.tfidf_weight_var, orient="horizontal").grid(row=8, column=1, sticky="ew", padx=8, pady=4)
        self.tfidf_weight_label = ttk.Label(self.opt, text=f"{self.tfidf_weight_var.get():.2f}")
        self.tfidf_weight_label.grid(row=8, column=2, sticky="w", padx=8)

        self.weight_sum_label = ttk.Label(self.opt, text="가중치 합: 1.00", foreground="green")
        self.weight_sum_label.grid(row=9, column=0, columnspan=3, sticky="w", padx=8, pady=4)

        # 3대 개선 옵션(자동정규화/디버그)
        opt2 = ttk.Frame(self.opt)
        opt2.grid(row=10, column=0, columnspan=3, sticky="w", padx=8, pady=6)
        ttk.Checkbutton(opt2, text="가중치 자동 정규화(실행 시 합=1.00으로 보정)", variable=self.auto_norm_var).pack(side="left", padx=(0, 16))
        ttk.Checkbutton(opt2, text="디버그 로그(TF-IDF 예외/폴백 메시지 출력)", variable=self.debug_tfidf_var).pack(side="left")

        self.opt.columnconfigure(0, weight=1)
        self.opt.columnconfigure(1, weight=1)
        self.opt.columnconfigure(2, weight=1)

        # 값 변경 시 UI 갱신
        self.threshold_var.trace_add("write", lambda *_: self._update_param_widgets())
        self.key_weight_var.trace_add("write", lambda *_: self._update_param_widgets())
        self.yaml_sig_weight_var.trace_add("write", lambda *_: self._update_param_widgets())
        self.yaml_keys_weight_var.trace_add("write", lambda *_: self._update_param_widgets())
        self.tfidf_weight_var.trace_add("write", lambda *_: self._update_param_widgets())
        self._update_param_widgets()

        # 무시되는 필드 안내
        info_frame = ttk.LabelFrame(frm, text="📋 무시되는 필드 (자동 제외)")
        info_frame.pack(fill="x", pady=8)
        ignored_fields_text = (
            "uid • creationTimestamp • generation • lastTransitionTime • lastResync • observedGeneration • managedFields • universal time • resourceVersion • RTC time\n"
            "⚠️ 위 필드들은 버전/실행환경마다 변경되므로 자동으로 비교에서 제외됩니다"
        )
        ttk.Label(info_frame, text=ignored_fields_text, wraplength=900, justify="left", foreground="gray40").pack(anchor="w", padx=8, pady=6)

        self.start_btn = ttk.Button(frm, text="비교 시작", command=self.start)
        self.start_btn.pack(fill="x", pady=8)

        self.pbar = ttk.Progressbar(frm, maximum=100, mode="determinate")
        self.pbar.pack(fill="x", pady=4)
        ttk.Label(frm, textvariable=self.progress_var).pack(anchor="w")
        ttk.Label(frm, textvariable=self.summary_var).pack(anchor="w", pady=2)
        ttk.Label(frm, textvariable=self.param_var).pack(anchor="w", pady=2)

        self.out = ScrolledText(frm, height=22)
        self.out.pack(fill="both", expand=True)

        self._log("준비 완료\n")
        self._log(self._param_info_text(header="【 현재 설정 파라미터 】") + "\n")

    def _update_param_widgets(self) -> None:
        self.threshold_label.config(text=f"{self.threshold_var.get():.2f}")
        self.key_weight_label.config(text=f"{self.key_weight_var.get():.2f}")
        self.yaml_sig_weight_label.config(text=f"{self.yaml_sig_weight_var.get():.2f}")
        self.yaml_keys_weight_label.config(text=f"{self.yaml_keys_weight_var.get():.2f}")
        self.tfidf_weight_label.config(text=f"{self.tfidf_weight_var.get():.2f}")

        total = (self.key_weight_var.get() + self.yaml_sig_weight_var.get() + self.yaml_keys_weight_var.get() + self.tfidf_weight_var.get())
        color = "green" if abs(total - 1.0) < 0.01 else "red"
        self.weight_sum_label.config(text=f"가중치 합: {total:.2f}", foreground=color)

        self.param_var.set(
            f"【 현재 파라미터 】"
            f" 임계값:{self.threshold_var.get():.2f} | "
            f"키:{self.key_weight_var.get():.2f} YAML서명:{self.yaml_sig_weight_var.get():.2f} "
            f"YAML키:{self.yaml_keys_weight_var.get():.2f} TF-IDF:{self.tfidf_weight_var.get():.2f} | "
            f"합계:{total:.2f} | "
            f"자동정규화:{'ON' if self.auto_norm_var.get() else 'OFF'} | "
            f"디버그:{'ON' if self.debug_tfidf_var.get() else 'OFF'}"
        )

    def _param_info_text(self, header: str, *, normalized_preview: Optional[Dict[str, float]] = None) -> str:
        total = (self.key_weight_var.get() + self.yaml_sig_weight_var.get() + self.yaml_keys_weight_var.get() + self.tfidf_weight_var.get())
        check = "✓" if abs(total - 1.0) < 0.01 else "✗"

        lines = []
        lines.append("=" * 80)
        lines.append(header)
        lines.append("=" * 80)
        lines.append(f"임계값:              {self.threshold_var.get():.2f} (블록이 이 이상 유사해야 매칭)")
        lines.append("")
        lines.append("가중치(슬라이더 값):")
        lines.append(f"  • 블록 키:        {self.key_weight_var.get():.2f}")
        lines.append(f"  • YAML 서명:      {self.yaml_sig_weight_var.get():.2f}")
        lines.append(f"  • YAML 키 구조:   {self.yaml_keys_weight_var.get():.2f}")
        lines.append(f"  • TF-IDF (본문):  {self.tfidf_weight_var.get():.2f}")
        lines.append("  ─────────────────────")
        lines.append(f"  합계:             {total:.2f} {check}")
        lines.append("")
        lines.append(f"자동 정규화:         {'ON' if self.auto_norm_var.get() else 'OFF'}")
        lines.append(f"디버그 로그:         {'ON' if self.debug_tfidf_var.get() else 'OFF'}")

        if normalized_preview is not None:
            lines.append("")
            lines.append("가중치(실행 적용값):")
            lines.append(f"  • 블록 키:        {normalized_preview['key']:.4f}")
            lines.append(f"  • YAML 서명:      {normalized_preview['yaml_sig']:.4f}")
            lines.append(f"  • YAML 키 구조:   {normalized_preview['yaml_keys']:.4f}")
            lines.append(f"  • TF-IDF (본문):  {normalized_preview['tfidf']:.4f}")
            lines.append(f"  ─────────────────────")
            lines.append(f"  합계:             {sum(normalized_preview.values()):.4f}")

        lines.append("=" * 80)
        return "\n".join(lines)

    def _log(self, msg: str) -> None:
        self.out.insert("end", msg + "\n")
        self.out.see("end")

    # ---- Folder pickers ----

    def pick_source(self) -> None:
        p = filedialog.askdirectory(title="원본 폴더 선택")
        if p:
            self.source_var.set(p)

    def pick_target(self) -> None:
        p = filedialog.askdirectory(title="비교대상 폴더 선택")
        if p:
            self.target_var.set(p)
            if not self.output_var.get().strip():
                self.use_default_output()

    def pick_output(self) -> None:
        p = filedialog.askdirectory(title="출력 폴더 선택 (그 아래 LLD_diff 생성)")
        if p:
            self.output_var.set(p)

    def use_default_output(self) -> None:
        t = self.target_var.get().strip()
        if not t:
            messagebox.showinfo("안내", "비교대상 폴더를 먼저 선택하세요.")
            return
        self.output_var.set(t)

    # ---- Params build ----

    def _build_run_params(self) -> Tuple[ComparisonParams, Dict[str, float]]:
        """
        실행 파라미터 스냅샷 생성
        - 자동 정규화 ON이면 weights를 합=1이 되도록 보정
        - 반환: (ComparisonParams, 실행 적용 weight dict)
        """
        weights_raw = {
            "key": float(self.key_weight_var.get()),
            "yaml_sig": float(self.yaml_sig_weight_var.get()),
            "yaml_keys": float(self.yaml_keys_weight_var.get()),
            "tfidf": float(self.tfidf_weight_var.get()),
        }

        if self.auto_norm_var.get():
            s = sum(weights_raw.values())
            if s <= 0.0:
                # 전부 0이면 기본값으로 복구
                weights_norm = DEFAULT_PARAMS["weights"].copy()
            else:
                weights_norm = {k: (v / s) for k, v in weights_raw.items()}
        else:
            weights_norm = weights_raw

        params = ComparisonParams(
            threshold=float(self.threshold_var.get()),
            weights=weights_norm,
            debug_tfidf=bool(self.debug_tfidf_var.get()),
        )
        return params, weights_norm

    # ---- Run ----

    def start(self) -> None:
        s = self.source_var.get().strip()
        t = self.target_var.get().strip()
        o = self.output_var.get().strip()

        if not s or not t:
            messagebox.showerror("오류", "원본/비교대상 폴더를 선택하세요.")
            return
        if not os.path.isdir(s) or not os.path.isdir(t):
            messagebox.showerror("오류", "존재하지 않는 폴더가 있습니다.")
            return
        if not o:
            self.use_default_output()
            o = self.output_var.get().strip()
            if not o:
                return

        # 실행 파라미터 스냅샷(메인스레드에서)
        run_params, weights_applied = self._build_run_params()

        self.start_btn.config(state=tk.DISABLED)
        self.pbar["value"] = 0
        self.progress_var.set("0.0% - 시작")
        self.summary_var.set("요약: -")
        self.out.delete("1.0", "end")

        self._log("비교 시작...\n")
        self._log(self._param_info_text(header="【 비교 시작 - 설정된 파라미터 】", normalized_preview=weights_applied) + "\n")

        def progress_cb(done: int, total: int, label: str) -> None:
            try:
                self.q.put_nowait(("progress", (done, total, label)))
            except queue.Full:
                # 진행률 이벤트는 버려도 됨
                pass

        def log_cb(msg: str) -> None:
            # 디버그 OFF면 fallback/에러 로그도 최소화
            if not run_params.debug_tfidf:
                # fallback 로그는 유용할 수 있어서, 최소한 FALLBACK만 출력
                if not msg.startswith("[FALLBACK]") and not msg.startswith("[READ_FAIL]"):
                    return
            try:
                self.q.put_nowait(("log", msg))
            except queue.Full:
                pass

        def worker() -> None:
            try:
                engine = ComparisonEngine(progress_cb=progress_cb, log_cb=log_cb)
                start_ts = time.time()
                result = engine.compare_folders(
                    s, t, o,
                    trim=self.trim_var.get(),
                    ignore_space=self.ignore_space_var.get(),
                    ignore_case=self.ignore_case_var.get(),
                    file_pattern=self.filter_var.get(),
                    block_mode=self.block_mode_var.get(),
                    params=run_params,
                )
                elapsed = time.time() - start_ts
                self.q.put(("done", (result, elapsed)))
            except Exception as e:
                self.q.put(("error", f"{type(e).__name__}: {e}"))

        self.worker = threading.Thread(target=worker, daemon=True)
        self.worker.start()
        self.root.after(80, self._poll_queue)

    def _poll_queue(self) -> None:
        try:
            while True:
                typ, payload = self.q.get_nowait()
                if typ == "progress":
                    done, total, label = payload
                    pct = (done / total) * 100 if total else 0
                    self.pbar["value"] = pct
                    self.progress_var.set(f"{pct:5.1f}% - {label}")
                elif typ == "log":
                    self._log(str(payload))
                elif typ == "done":
                    result, elapsed = payload
                    self._show_done(result, elapsed)
                    return
                elif typ == "error":
                    self.start_btn.config(state=tk.NORMAL)
                    self._log(f"[ERROR] {payload}")
                    messagebox.showerror("오류", str(payload))
                    return
        except queue.Empty:
            self.root.after(80, self._poll_queue)

    def _show_done(self, result: Dict[str, object], elapsed: float) -> None:
        self.start_btn.config(state=tk.NORMAL)
        self.pbar["value"] = 100
        self.progress_var.set("100.0% - 완료")

        summary = result["summary"]
        report_root = result["report_root"]
        top_changed = result["top_changed"]

        identical_pct = (summary["Identical"] / summary["TotalMatched"] * 100) if summary["TotalMatched"] > 0 else 0
        self.summary_var.set(
            f"✓ 매칭:{summary['TotalMatched']} | 동일:{summary['Identical']}({identical_pct:.0f}%) | "
            f"변경:{summary['Changed']} | 누락-원본:{summary['SourceMissing']} | "
            f"누락-비교:{summary['TargetMissing']} | 시간:{elapsed:.1f}초"
        )

        self._log("\n" + "=" * 80)
        self._log("【 실행 결과 요약 】")
        self._log("=" * 80)
        self._log(f"처리 시간: {elapsed:.2f}초")
        self._log(f"결과 폴더: {report_root}")
        self._log("")
        self._log("【 파일 비교 현황 】")
        self._log(f"  총 매칭 파일: {summary['TotalMatched']}")
        self._log(f"  ✓ 동일 파일:   {summary['Identical']} ({identical_pct:.1f}%)")
        self._log(f"  ◆ 변경 파일:   {summary['Changed']} (TXT 리포트 생성됨)")
        self._log(f"  ◇ 원본에만:    {summary['SourceMissing']}")
        self._log(f"  ◇ 비교에만:    {summary['TargetMissing']}")
        self._log(f"  ✗ 인코딩 오류: {summary['EncodingError']}")

        if summary["Changed"] > 0:
            self._log("")
            self._log(f"【 변경된 파일 상세 (상위 {min(TOP_N, len(top_changed))}개) 】")
            for idx, (rel, fd) in enumerate(top_changed, 1):
                change_type = f"+{fd.inserted}/-{fd.deleted}"
                self._log(f"{idx:2d}. {rel}")
                self._log(
                    f"    Hunks:{fd.hunks:3d} | {change_type:15s} | Repl:{fd.replaced:3d} | "
                    f"유사도:{fd.similarity_pct:3d}% | 결과:LLD_diff/{rel}.txt"
                )

        self._log("=" * 80)
        self._log("")

        messagebox.showinfo(
            "완료",
            f"비교 완료!\n\n"
            f"✓ 매칭 파일: {summary['TotalMatched']}\n"
            f"✓ 동일 파일: {summary['Identical']}\n"
            f"◆ 변경 파일: {summary['Changed']}\n\n"
            f"처리 시간: {elapsed:.1f}초\n\n"
            f"결과 폴더:\n{report_root}",
        )


def main() -> None:
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
