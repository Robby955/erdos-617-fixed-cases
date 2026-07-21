#!/usr/bin/env python3
"""Semantically verify exact rational duals for strict m=63 pairs.

This checker independently rebuilds the unique core, the 2,245 compatible
shells, and every inequality named by the certificate data.  It imports the
previous proof-facing inequality semantics, not the m=63 generator, and it
does not call an optimizer or a SAT solver.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, cast

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
BASE_PATH = HERE / "verify_r9_p93_order26_m62_duals.py"
R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 63
GLOBAL_OFFSET = 18
EXPECTED_CORES = 1
EXPECTED_SHELLS = 2245
EXPECTED_PAIRS = 2245
EXPECTED_CERTIFICATES = 1911
EXPECTED_UNCERTIFIED = 334
EXPECTED_CORE_CATALOG_SHA256 = (
    "20302c025a85684c659534cc704508b0311c33282dc8d0b19b683fa033855044"
)
EXPECTED_SHELL_CATALOG_SHA256 = (
    "f5e13567a0a977da594eacdaa8b945ba416f13ad507121bb90b91c8f100c43b7"
)
EXPECTED_UNCERTIFIED_PAIR_SHA256 = (
    "f0e775bc61c40d56c54e221f6f47d216939671c6ac2d65c62eace6fa480ebd2b"
)
EXPECTED_SEMANTIC_SHA256 = (
    "877eca5a4a64b1a1484f1036faeb3dbfdc5033c8b6f39b4af8593af86a025acf"
)
EXPECTED_DATA_SHA256 = (
    "57ef4123b3053689f0dd72aa256bf2975c069aa0d0785e2269e74c513ae52a2f"
)
NONCLAIM = (
    "The 334 uncertified pairs remain open in this package; it does not "
    "exclude m=63, prove fixed r=9, or solve Erdos Problem 617."
)
EXPECTED_DEMAND_PROFILE = Counter({(15, 15): 1})
EXPECTED_SHELL_PROFILE = Counter(
    {
        (12, 0): 3,
        (12, 1): 3,
        (12, 2): 1,
        (12, 3): 9,
        (12, 4): 56,
        (12, 5): 114,
        (12, 6): 152,
        (13, 0): 4,
        (13, 1): 2,
        (13, 2): 14,
        (13, 3): 45,
        (13, 4): 106,
        (13, 5): 83,
        (14, 0): 5,
        (14, 1): 9,
        (14, 2): 34,
        (14, 3): 60,
        (14, 4): 364,
        (15, 0): 10,
        (15, 1): 14,
        (15, 2): 112,
        (15, 3): 362,
        (16, 0): 19,
        (16, 1): 84,
        (16, 2): 270,
        (17, 0): 55,
        (17, 1): 146,
        (18, 0): 109,
    }
)


def load_base() -> Any:
    spec = importlib.util.spec_from_file_location("r9_m63_semantic_base", BASE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {BASE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    base = cast(Any, module)
    base.CORE_EDGES = CORE_EDGES
    base.GLOBAL_OFFSET = GLOBAL_OFFSET
    base.EXPECTED_CORES = EXPECTED_CORES
    base.EXPECTED_SHELLS = EXPECTED_SHELLS
    base.EXPECTED_PAIRS = EXPECTED_PAIRS
    base.EXPECTED_CERTIFICATES = EXPECTED_CERTIFICATES
    base.EXPECTED_UNCERTIFIED = EXPECTED_UNCERTIFIED
    return base


BASE = load_base()
GraphCase = BASE.GraphCase


def generate_cores(geng: Path) -> tuple[Any, ...]:
    command = [str(geng), "-q", "-t", "-D8", "16", "63:63"]
    cases = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if BASE.valid_core(graph):
            cases.append(GraphCase(graph6, graph))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def generate_shells(geng: Path) -> tuple[Any, ...]:
    command = [str(geng), "-q", "-k", "9", "12:18"]
    cases = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        compatible, minimum = BASE.shell_compatible(graph)
        if compatible:
            cases.append(GraphCase(graph6, graph, minimum))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def catalog_sha256(cases: tuple[Any, ...]) -> str:
    return cast(str, BASE.catalog_sha256(cases))


def parse_header(raw: Any) -> None:
    expected = {
        "schema": "erdos617-r9-m63-duals-v1",
        "core_count": EXPECTED_CORES,
        "shell_count": EXPECTED_SHELLS,
        "pair_count": EXPECTED_PAIRS,
        "certificate_count": EXPECTED_CERTIFICATES,
        "uncertified_pair_count": EXPECTED_UNCERTIFIED,
        "core_catalog_sha256": EXPECTED_CORE_CATALOG_SHA256,
        "shell_catalog_sha256": EXPECTED_SHELL_CATALOG_SHA256,
        "uncertified_pair_sha256": EXPECTED_UNCERTIFIED_PAIR_SHA256,
        "semantic_sha256": EXPECTED_SEMANTIC_SHA256,
        "nonclaim": NONCLAIM,
    }
    if raw != expected:
        raise AssertionError(f"certificate header mismatch: {raw}")


parse_weights = BASE.parse_weights
verify_record = BASE.verify_record


def independent_eights(graph: nx.Graph) -> tuple[int, ...]:
    adjacency = BASE.adjacency_masks(graph)
    result = []
    for vertices in itertools.combinations(range(CORE_ORDER), 8):
        mask = sum(1 << vertex for vertex in vertices)
        if BASE.independent(mask, adjacency):
            result.append(mask)
    return tuple(result)


def core_demand_profile(core: nx.Graph) -> tuple[int, int]:
    if not nx.is_bipartite(core):
        raise AssertionError("m=63 core is not bipartite")
    coloring = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(vertex for vertex, color in coloring.items() if color == side))
        for side in (0, 1)
    )
    if sorted(map(len, sides)) != [8, 8]:
        raise AssertionError("m=63 core does not have an 8+8 bipartition")
    if len(independent_eights(core)) != 2:
        raise AssertionError("m=63 core does not have exactly two independent eights")
    return tuple(
        sorted(
            sum(max(0, int(core.degree(vertex)) - 6) for vertex in side)
            for side in sides
        )
    )  # type: ignore[return-value]


def uncertified_pair_sha256(
    cores: tuple[Any, ...],
    shells: tuple[Any, ...],
    certified: set[tuple[str, str]],
) -> str:
    payload = "".join(
        f"{core_index}:{shell_index}\n"
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii"))
        not in certified
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--certificates", type=Path, required=True)
    args = parser.parse_args()

    data_hash = hashlib.sha256(args.certificates.read_bytes()).hexdigest()
    if data_hash != EXPECTED_DATA_SHA256:
        raise AssertionError(f"certificate data digest mismatch: {data_hash}")
    cores = generate_cores(args.geng)
    shells = generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(f"catalog mismatch: cores={len(cores)} shells={len(shells)}")
    if catalog_sha256(cores) != EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if catalog_sha256(shells) != EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")

    demand_profile = Counter(core_demand_profile(case.graph) for case in cores)
    if demand_profile != EXPECTED_DEMAND_PROFILE:
        raise AssertionError(f"core demand profile mismatch: {demand_profile}")
    shell_profile = Counter(
        (case.graph.number_of_edges(), case.minimum_slack) for case in shells
    )
    if shell_profile != EXPECTED_SHELL_PROFILE:
        raise AssertionError(f"shell profile mismatch: {shell_profile}")

    core_map = {case.graph6.decode("ascii"): case.graph for case in cores}
    shell_map = {case.graph6.decode("ascii"): case.graph for case in shells}
    lines = tuple(
        line
        for line in args.certificates.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    if len(lines) != EXPECTED_CERTIFICATES + 1:
        raise AssertionError(f"certificate line count mismatch: {len(lines)}")
    parse_header(json.loads(lines[0]))

    certified: set[tuple[str, str]] = set()
    semantic_rows: list[tuple[str, str, Fraction, int]] = []
    margins: Counter[Fraction] = Counter()
    supports: Counter[int] = Counter()
    for line in lines[1:]:
        pair, margin, support_size = verify_record(
            json.loads(line), core_map, shell_map
        )
        if pair in certified:
            raise AssertionError(f"duplicate certificate pair: {pair}")
        certified.add(pair)
        semantic_rows.append((pair[0], pair[1], margin, support_size))
        margins[margin] += 1
        supports[support_size] += 1
    semantic_hash = BASE.semantic_sha256(semantic_rows)
    if semantic_hash != EXPECTED_SEMANTIC_SHA256:
        raise AssertionError(f"semantic digest mismatch: {semantic_hash}")
    remainder_hash = uncertified_pair_sha256(cores, shells, certified)
    if remainder_hash != EXPECTED_UNCERTIFIED_PAIR_SHA256:
        raise AssertionError(f"uncertified-pair digest mismatch: {remainder_hash}")

    print(f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}")
    print(f"core_structure=K8,8-minus-1 demand_profile={dict(demand_profile)}")
    print(f"shell_profile={dict(sorted(shell_profile.items()))}")
    print(
        f"strict_duals_verified={len(certified)} "
        f"uncertified_pairs={EXPECTED_UNCERTIFIED}"
    )
    print(f"semantic_sha256={semantic_hash}")
    print(f"uncertified_pair_sha256={remainder_hash}")
    print(f"data_sha256={data_hash}")
    print(f"margin_profile={dict(sorted(margins.items()))}")
    print(f"support_size_profile={dict(sorted(supports.items()))}")
    print("status=PASS")


if __name__ == "__main__":
    main()
