#!/usr/bin/env python3
"""Corruption tests for the fixed-r=9, m=63 proof package."""

from __future__ import annotations

from collections import Counter
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
DUAL_PATH = HERE / "verify_r9_p93_order26_m63_duals.py"
SCALAR_PATH = HERE / "r9_p93_order26_m63_scalar_side_verifier.py"
ORBIT_PATH = HERE / "r9_p93_order26_m63_p1_orbit_verifier.py"
Z3_BASE_PATH = HERE / "r9_p93_order26_m60_p1_qstate_z3_audit.py"
Z3_WRAPPER_PATH = HERE / "r9_p93_order26_m63_p1_qstate_z3_audit.py"
DATA_PATH = HERE / "r9_p93_order26_m63_duals.jsonl"
EXPECTED_DATA_SHA256 = (
    "57ef4123b3053689f0dd72aa256bf2975c069aa0d0785e2269e74c513ae52a2f"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_module("erdos617_m63_test_dual", DUAL_PATH)
SCALAR = load_module("erdos617_m63_test_scalar", SCALAR_PATH)
ORBIT = load_module("erdos617_m63_test_orbit", ORBIT_PATH)
Z3_AUDIT = load_module("erdos617_m63_test_z3", Z3_BASE_PATH)
Z3_WRAPPER = load_module("erdos617_m63_test_z3_wrapper", Z3_WRAPPER_PATH)
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


def test_coefficient_overload_is_rejected() -> None:
    record = dict(CANONICAL_RECORDS[0])
    record["weights"] = [[0, 2, 1]]
    core_name = record["core"]
    shell_name = record["shell"]
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    with pytest.raises(AssertionError, match="coefficient above one"):
        DUAL.verify_record(record, {core_name: core}, {shell_name: shell})


def test_scalar_classification_digest_corruption_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    core = nx.complete_bipartite_graph(8, 8)
    core.remove_edge(0, 8)
    shell = nx.empty_graph(9)
    core_case = DUAL.GraphCase(b"C", core)
    shell_case = DUAL.GraphCase(b"S", shell, 0)
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
    monkeypatch.setattr(SCALAR, "EXPECTED_COVER13_REMOVED_STATES", 0)
    monkeypatch.setattr(SCALAR, "EXPECTED_PAIR_PROFILE", Counter({(0, True): 1}))
    monkeypatch.setattr(SCALAR, "EXPECTED_CLASSIFICATION_SHA256", "0" * 64)
    monkeypatch.setattr(sys, "argv", ["m63-scalar", "--geng", "/not-used"])
    with pytest.raises(AssertionError, match="classification digest mismatch"):
        SCALAR.main()


def test_wrong_orbit_profile_digest_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(ORBIT, "EXPECTED_PROFILE_SHA256", "0" * 64)
    with pytest.raises(AssertionError, match="profile digest mismatch"):
        ORBIT.run_self_test(False)


def test_unknown_orbit_core_is_rejected() -> None:
    with pytest.raises(AssertionError, match="unexpected m=63 core"):
        ORBIT.build_orbit_model("not-a-core")


def test_cover13_rejects_a_second_incident_missing_edge() -> None:
    corrupted = nx.complete_bipartite_graph(8, 8)
    corrupted.remove_edge(0, 8)
    corrupted.remove_edge(0, 9)
    with pytest.raises(AssertionError, match="mixed core cover"):
        SCALAR.verify_cover13_lemma(corrupted)


def test_z3_cover13_premise_rejects_a_second_missing_edge() -> None:
    corrupted = nx.complete_bipartite_graph(8, 8)
    corrupted.remove_edge(0, 8)
    corrupted.remove_edge(0, 9)
    with pytest.raises(AssertionError, match="wrong order or size"):
        Z3_WRAPPER.cover13_sides(corrupted)


def test_z3_chunk_rows_are_passed_exactly(monkeypatch: pytest.MonkeyPatch) -> None:
    row_states = ((0,) * 9, (1,) * 9)

    def fake_solve(
        core: nx.Graph,
        shell: nx.Graph,
        core_index: int,
        shell_index: int,
        received: tuple[tuple[int, ...], ...],
    ) -> tuple[tuple[int, ...], ...]:
        assert core.number_of_edges() == 63
        assert shell.number_of_nodes() == 9
        assert (core_index, shell_index) == (0, 2)
        return received

    monkeypatch.setattr(Z3_WRAPPER, "solve_pair_with_cover13", fake_solve)
    result = Z3_WRAPPER.audit_task(
        (0, 2, "O????B}~v}^w~o~o^wF}?", "H???Fr|", row_states)
    )
    assert result == row_states


def test_boolean_model_semantics_reject_wrong_row_size() -> None:
    core = nx.complete_bipartite_graph(8, 8)
    core.remove_edge(0, 8)
    shell = nx.empty_graph(9)
    rows = (0,) * 9
    sides = Z3_AUDIT.bipartition_masks(core)
    with pytest.raises(AssertionError, match="exact row size"):
        Z3_AUDIT.verify_sat_model(core, shell, (1,) + (0,) * 8, rows, sides)
