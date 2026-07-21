#!/usr/bin/env python3
"""Corruption tests for the fixed-r=9, m=62 proof package."""

from __future__ import annotations

from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from typing import Any, cast

import networkx as nx  # type: ignore[import-untyped]
import pytest


HERE = Path(__file__).resolve().parent
DUAL_PATH = HERE / "verify_r9_p93_order26_m62_duals.py"
SCALAR_PATH = HERE / "r9_p93_order26_m62_scalar_side_verifier.py"
DATA_PATH = HERE / "r9_p93_order26_m62_duals.jsonl"
EXPECTED_DATA_SHA256 = (
    "d80b2e95446ca6771c6c64591c43addc256e49c4bf099e8e09e7c648ad013796"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_module("erdos617_m62_package_test_dual", DUAL_PATH)
SCALAR = load_module("erdos617_m62_package_test_scalar", SCALAR_PATH)
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


def write_record(path: Path, record: dict[str, Any]) -> dict[str, Any]:
    path.write_text(
        json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="ascii",
    )
    return cast(dict[str, Any], json.loads(path.read_text(encoding="ascii")))


def patched_digest_check(path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    monkeypatch.setattr(SCALAR.DUAL, "EXPECTED_DATA_SHA256", digest)
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


def test_byte_truncation_is_rejected_before_parsing(tmp_path: Path) -> None:
    path = tmp_path / "truncated.jsonl"
    path.write_bytes(CANONICAL_BYTES[:-19])
    with pytest.raises(AssertionError, match="dual data digest mismatch"):
        SCALAR.certified_pairs(path, CORE_CASES, SHELL_CASES)


def test_removed_record_is_rejected_by_line_count(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "removed-record.jsonl"
    write_lines(path, list(CANONICAL_LINES[:-1]))
    with pytest.raises(AssertionError, match="wrong dual line count"):
        patched_digest_check(path, monkeypatch)


def test_duplicate_pair_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    lines[2] = lines[1]
    path = tmp_path / "duplicate-pair.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="duplicate dual pair"):
        patched_digest_check(path, monkeypatch)


@pytest.mark.parametrize(
    ("name", "mutation"),
    (
        ("bad-schema", lambda header: header.__setitem__("schema", "wrong-schema")),
        ("missing-count", lambda header: header.pop("core_count")),
        (
            "bad-catalog-digest",
            lambda header: header.__setitem__("core_catalog_sha256", "0" * 64),
        ),
    ),
)
def test_bad_header_is_rejected(
    name: str,
    mutation: Any,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    lines = list(CANONICAL_LINES)
    header = json.loads(lines[0])
    mutation(header)
    lines[0] = json.dumps(header, sort_keys=True, separators=(",", ":"))
    path = tmp_path / f"{name}.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="certificate header mismatch"):
        patched_digest_check(path, monkeypatch)


def test_unknown_graph_name_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lines = list(CANONICAL_LINES)
    record = json.loads(lines[1])
    record["core"] = "not-a-catalog-graph"
    lines[1] = json.dumps(record, sort_keys=True, separators=(",", ":"))
    path = tmp_path / "unknown-graph.jsonl"
    write_lines(path, lines)
    with pytest.raises(AssertionError, match="outside catalogs"):
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


def test_coefficient_overload_is_rejected(tmp_path: Path) -> None:
    record = dict(CANONICAL_RECORDS[0])
    record["weights"] = [[0, 2, 1]]
    path = tmp_path / "coefficient-overload.json"
    corrupted = write_record(path, record)
    core_name = corrupted["core"]
    shell_name = corrupted["shell"]
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    with pytest.raises(AssertionError, match="coefficient above one"):
        DUAL.verify_record(
            corrupted,
            {core_name: core},
            {shell_name: shell},
        )


def test_scalar_classification_digest_corruption_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    core = nx.complete_bipartite_graph(8, 8)
    shell = nx.empty_graph(9)
    core_case = SCALAR.DUAL.GraphCase(b"C", core)
    shell_case = SCALAR.DUAL.GraphCase(b"S", shell, 0)

    monkeypatch.setattr(SCALAR.DUAL, "generate_cores", lambda _geng: (core_case,))
    monkeypatch.setattr(SCALAR.DUAL, "generate_shells", lambda _geng: (shell_case,))
    monkeypatch.setattr(SCALAR.DUAL, "EXPECTED_CORES", 1)
    monkeypatch.setattr(SCALAR.DUAL, "EXPECTED_SHELLS", 1)
    monkeypatch.setattr(
        SCALAR.DUAL,
        "EXPECTED_CORE_CATALOG_SHA256",
        SCALAR.DUAL.catalog_sha256((core_case,)),
    )
    monkeypatch.setattr(
        SCALAR.DUAL,
        "EXPECTED_SHELL_CATALOG_SHA256",
        SCALAR.DUAL.catalog_sha256((shell_case,)),
    )
    monkeypatch.setattr(SCALAR, "certified_pairs", lambda *_args: frozenset())
    monkeypatch.setattr(SCALAR, "EXPECTED_COMPLEMENT_PAIRS", 1)
    monkeypatch.setattr(
        SCALAR,
        "EXPECTED_COMPLEMENT_SHA256",
        hashlib.sha256(b"0:0\n").hexdigest(),
    )
    monkeypatch.setattr(SCALAR, "row_size_states", lambda _shell: ((0,) * 9,))
    monkeypatch.setattr(SCALAR, "side_demands", lambda _core: (0, 0))
    monkeypatch.setattr(SCALAR, "feasible_side_counts", lambda *_args: True)
    monkeypatch.setattr(SCALAR, "vertex_cover_number", lambda _shell: 0)
    monkeypatch.setattr(SCALAR, "EXPECTED_DISTINCT_SHELLS", 1)
    monkeypatch.setattr(SCALAR, "EXPECTED_RAW_STATES", 1)
    monkeypatch.setattr(SCALAR, "EXPECTED_FEASIBLE_STATES", 1)
    monkeypatch.setattr(SCALAR, "EXPECTED_PAIR_PROFILE", Counter({(0, True): 1}))
    monkeypatch.setattr(SCALAR, "EXPECTED_CLASSIFICATION_SHA256", "0" * 64)
    monkeypatch.setattr(sys, "argv", ["m62-scalar", "--geng", "/not-used"])

    with pytest.raises(AssertionError, match="classification digest mismatch"):
        SCALAR.main()
