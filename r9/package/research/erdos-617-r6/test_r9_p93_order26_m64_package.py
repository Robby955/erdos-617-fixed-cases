#!/usr/bin/env python3
"""Corruption tests for the fixed-r=9, m=64 proof package."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from typing import Any

import networkx as nx  # type: ignore[import-untyped]
import pytest


HERE = Path(__file__).resolve().parent
DUAL_PATH = HERE / "verify_r9_p93_order26_m64_duals.py"
SCALAR_PATH = HERE / "r9_p93_order26_m64_scalar_side_verifier.py"
TAU3_PATH = HERE / "r9_p93_order26_m64_tau3_verifier.py"
ORBIT_PATH = HERE / "r9_p93_order26_m64_p1_orbit_verifier.py"
CADICAL_PATH = HERE / "r9_p93_order26_m64_cadical_audit.py"
MANIFEST_VERIFIER_PATH = HERE / "verify_r9_p93_order26_m64_manifest.py"
DATA_PATH = HERE / "r9_p93_order26_m64_duals.jsonl"
EXPECTED_DATA_SHA256 = (
    "4710a3e7761bcfe319a3af94c92fb228cb98eba0ea2d2ff9753568389ea6465c"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_module("erdos617_m64_test_dual", DUAL_PATH)
SCALAR = load_module("erdos617_m64_test_scalar", SCALAR_PATH)
TAU3 = load_module("erdos617_m64_test_tau3", TAU3_PATH)
ORBIT = load_module("erdos617_m64_test_orbit", ORBIT_PATH)
CADICAL_AUDIT = load_module("erdos617_m64_test_cadical", CADICAL_PATH)
MANIFEST = load_module("erdos617_m64_test_manifest", MANIFEST_VERIFIER_PATH)
CANONICAL_BYTES = DATA_PATH.read_bytes()
CANONICAL_LINES = tuple(DATA_PATH.read_text(encoding="ascii").splitlines())
CANONICAL_RECORDS = tuple(json.loads(line) for line in CANONICAL_LINES[1:])
CORE_CASES = tuple(
    SimpleNamespace(graph6=name.encode("ascii"))
    for name in sorted({record["core"] for record in CANONICAL_RECORDS})
)
SHELL_CASES = tuple(
    SimpleNamespace(graph6=name.encode("ascii"))
    for name in sorted({record["shell"] for record in CANONICAL_RECORDS})
)


def write_lines(path: Path, lines: tuple[str, ...] | list[str]) -> None:
    path.write_text("\n".join(lines) + "\n", encoding="ascii")


def patched_digest_check(path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        SCALAR.DUAL,
        "EXPECTED_DATA_SHA256",
        hashlib.sha256(path.read_bytes()).hexdigest(),
    )
    SCALAR.certified_pairs(path, CORE_CASES, SHELL_CASES)


def test_canonical_file_sha256_is_pinned() -> None:
    digest = hashlib.sha256(CANONICAL_BYTES).hexdigest()
    assert digest == EXPECTED_DATA_SHA256
    assert digest == DUAL.EXPECTED_DATA_SHA256
    assert digest == SCALAR.DUAL.EXPECTED_DATA_SHA256


def test_byte_flip_is_rejected_before_parsing(tmp_path: Path) -> None:
    corrupted = bytearray(CANONICAL_BYTES)
    position = corrupted.index(ord("6"))
    corrupted[position] = ord("7")
    path = tmp_path / "byte-flip.jsonl"
    path.write_bytes(corrupted)
    with pytest.raises(AssertionError, match="dual data digest mismatch"):
        SCALAR.certified_pairs(path, CORE_CASES, SHELL_CASES)


def test_truncation_is_rejected_before_parsing(tmp_path: Path) -> None:
    path = tmp_path / "truncated.jsonl"
    path.write_bytes(CANONICAL_BYTES[:-23])
    with pytest.raises(AssertionError, match="dual data digest mismatch"):
        SCALAR.certified_pairs(path, CORE_CASES, SHELL_CASES)


def test_removed_record_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "removed.jsonl"
    write_lines(path, list(CANONICAL_LINES[:-1]))
    with pytest.raises(AssertionError, match="wrong dual line count"):
        patched_digest_check(path, monkeypatch)


def test_duplicate_pair_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    lines[2] = lines[1]
    path = tmp_path / "duplicate.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="duplicate dual pair"):
        patched_digest_check(path, monkeypatch)


def test_bad_header_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    header = json.loads(lines[0])
    header["schema"] = "wrong-schema"
    lines[0] = json.dumps(header, sort_keys=True, separators=(",", ":"))
    path = tmp_path / "bad-header.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="certificate header mismatch"):
        patched_digest_check(path, monkeypatch)


def test_unknown_graph_name_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    record = json.loads(lines[1])
    record["shell"] = "not-a-catalog-graph"
    lines[1] = json.dumps(record, sort_keys=True, separators=(",", ":"))
    path = tmp_path / "unknown-shell.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="outside the catalogs"):
        patched_digest_check(path, monkeypatch)


def test_malformed_weight_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    record = json.loads(lines[1])
    record["weights"][0][1] = "1"
    lines[1] = json.dumps(record, sort_keys=True, separators=(",", ":"))
    path = tmp_path / "malformed-weight.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="numerator must be an integer"):
        patched_digest_check(path, monkeypatch)


def test_dual_coefficient_overload_is_rejected() -> None:
    record = dict(CANONICAL_RECORDS[0])
    record["weights"] = [[0, 2, 1]]
    core_name = record["core"]
    shell_name = record["shell"]
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    with pytest.raises(AssertionError, match="coefficient above one"):
        DUAL.BASE.verify_record(record, {core_name: core}, {shell_name: shell})


def test_tau3_profile_corruption_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(TAU3, "EXPECTED_RECEIPT_SHA256", "0" * 64)
    with pytest.raises(AssertionError, match="receipt digest mismatch"):
        TAU3.main()


def test_orbit_profile_corruption_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(ORBIT, "EXPECTED_PROFILE_SHA256", "0" * 64)
    with pytest.raises(AssertionError, match="profile digest mismatch"):
        ORBIT.run_self_test(False)


def test_orbit_rejects_wrong_core() -> None:
    with pytest.raises(AssertionError, match="unexpected m=64 core"):
        ORBIT.build_orbit_model("not-a-core")


def test_complete_bipartite_premise_rejects_missing_edge() -> None:
    graph = nx.complete_bipartite_graph(8, 8)
    graph.remove_edge(0, 8)
    with pytest.raises(AssertionError, match="wrong order or size"):
        CADICAL_AUDIT.bipartition(graph)


def test_cadical_audit_hashes_are_pinned() -> None:
    assert CADICAL_AUDIT.EXPECTED_CLASSIFICATION_SHA256 == (
        "e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331"
    )
    assert CADICAL_AUDIT.EXPECTED_RECEIPT_SHA256 == (
        "d08cee42dcfbab41f8caaa3fec7a7133059577d63ec7a02ebe81db496a04c218"
    )


def test_scalar_cover_lemma_rejects_missing_edge() -> None:
    graph = nx.complete_bipartite_graph(8, 8)
    graph.remove_edge(0, 8)
    with pytest.raises(AssertionError, match="containing neither side"):
        SCALAR.verify_complete_bipartite_cover_lemma(graph)


def test_manifest_digest_corruption_is_rejected(tmp_path: Path) -> None:
    manifest = tmp_path / "manifest.json"
    manifest.write_text("{}\n", encoding="ascii")
    manifest.with_name("manifest.sha256").write_text(
        f"{'0' * 64}  manifest.json\n",
        encoding="ascii",
    )
    with pytest.raises(AssertionError, match="does not match"):
        MANIFEST.verify_digest_file(manifest)


def test_manifest_path_escape_is_rejected() -> None:
    with pytest.raises(AssertionError, match="escapes the repository"):
        MANIFEST.resolve_repo_path("../outside", "test.path")
