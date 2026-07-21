#!/usr/bin/env python3
"""Independently verify the exact rational dual package for m=64."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from typing import Any

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
BASE_PATH = HERE / "verify_r9_p93_order26_m62_duals.py"
R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 64
GLOBAL_OFFSET = 19
EXPECTED_CORES = 1
EXPECTED_SHELLS = 7454
EXPECTED_PAIRS = 7454
EXPECTED_CERTIFICATES = 6892
EXPECTED_UNCERTIFIED = 562
EXPECTED_CORE_CATALOG_SHA256 = (
    "07c708c5c0652d72f0247fa67ea661904e84a8e30368669e24708bbd7cb48a29"
)
EXPECTED_SHELL_CATALOG_SHA256 = (
    "fba322c6bb7dad18d9e14c51a1b97a33abd67186e30c5c1a4eb40908ffca9c1a"
)
EXPECTED_UNCERTIFIED_PAIR_SHA256 = (
    "96303541e4dfaf31fab4a61ebefea1390e2cc53f90b2b238e43eb5923638036e"
)
EXPECTED_SEMANTIC_SHA256 = (
    "d77700d00082ebc0370822fcf4f58393891a936cd71a0e1223873fc4f0c43a57"
)
EXPECTED_DATA_SHA256 = (
    "4710a3e7761bcfe319a3af94c92fb228cb98eba0ea2d2ff9753568389ea6465c"
)
EXPECTED_DEMAND_PROFILE = Counter({(16, 16): 1})
NONCLAIM = (
    "The 562 uncertified pairs remain open in this package; it does not "
    "exclude m=64, prove fixed r=9, or solve Erdos Problem 617."
)


def load_base() -> Any:
    spec = importlib.util.spec_from_file_location("erdos617_m64_semantic_base", BASE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {BASE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    base: Any = module
    base.CORE_EDGES = CORE_EDGES
    base.GLOBAL_OFFSET = GLOBAL_OFFSET
    return base


BASE = load_base()
GraphCase = BASE.GraphCase


def generate_cores(geng: Path) -> tuple[Any, ...]:
    cases = []
    command = [str(geng), "-q", "-t", "-D8", "16", "64:64"]
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if BASE.valid_core(graph):
            cases.append(GraphCase(graph6, graph, 0))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def has_independent_eight(graph: nx.Graph) -> bool:
    adjacency = BASE.adjacency_masks(graph)
    full = (1 << SHELL_ORDER) - 1
    return any(
        BASE.independent(full ^ (1 << omitted), adjacency)
        for omitted in range(SHELL_ORDER)
    )


def minimum_shell_slack(graph: nx.Graph) -> int | None:
    """Find the exact minimum by iterative bounded feasibility search.

    This implementation is independent of the generator's optimizing
    branch-and-bound routine. At each violated edge it enumerates every
    split of the exact missing demand; later violations supply any extra
    endpoint increments required by a feasible extension.
    """

    budget = GLOBAL_OFFSET - graph.number_of_edges()
    if budget < 0:
        return None
    degrees = tuple(int(graph.degree(vertex)) for vertex in range(SHELL_ORDER))
    demands = tuple(
        (
            int(first),
            int(second),
            max(0, 8 - degrees[int(first)] - degrees[int(second)]),
        )
        for first, second in graph.edges
    )

    def feasible(limit: int) -> bool:
        visited: set[tuple[int, ...]] = set()

        def search(epsilon: tuple[int, ...]) -> bool:
            if epsilon in visited or sum(epsilon) > limit:
                return False
            visited.add(epsilon)
            violations = tuple(
                (
                    demand - epsilon[first] - epsilon[second],
                    first,
                    second,
                )
                for first, second, demand in demands
                if epsilon[first] + epsilon[second] < demand
            )
            if not violations:
                return True
            deficit, first, second = min(
                violations,
                key=lambda row: (-row[0], row[1] + row[2], row[1], row[2]),
            )
            for first_increment in range(deficit, -1, -1):
                updated = list(epsilon)
                updated[first] += first_increment
                updated[second] += deficit - first_increment
                if search(tuple(updated)):
                    return True
            return False

        return search((0,) * SHELL_ORDER)

    return next((limit for limit in range(budget + 1) if feasible(limit)), None)


def generate_shells(geng: Path) -> tuple[Any, ...]:
    cases = []
    command = [str(geng), "-q", "-k", "9", "8:19"]
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if has_independent_eight(graph):
            continue
        minimum = minimum_shell_slack(graph)
        if minimum is not None:
            cases.append(GraphCase(graph6, graph, minimum))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def catalog_sha256(cases: tuple[Any, ...]) -> str:
    payload = b"\n".join(case.graph6 for case in cases) + b"\n"
    return hashlib.sha256(payload).hexdigest()


def parse_header(raw: Any) -> None:
    expected = {
        "schema": "erdos617-r9-m64-duals-v1",
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

    demand_profile = Counter(BASE.core_demand_profile(case.graph) for case in cores)
    if demand_profile != EXPECTED_DEMAND_PROFILE:
        raise AssertionError(f"core demand profile mismatch: {demand_profile}")
    shell_profile = Counter(
        (case.graph.number_of_edges(), case.minimum_slack) for case in shells
    )
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
    semantic_rows = []
    margins: Counter[Any] = Counter()
    supports: Counter[int] = Counter()
    for line in lines[1:]:
        pair, margin, support_size = BASE.verify_record(
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
    remainder_hash = BASE.uncertified_pair_sha256(cores, shells, certified)
    if remainder_hash != EXPECTED_UNCERTIFIED_PAIR_SHA256:
        raise AssertionError(f"complement digest mismatch: {remainder_hash}")
    if len(certified) != EXPECTED_CERTIFICATES:
        raise AssertionError("wrong certified-pair count")

    print(f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}")
    print(f"certificates_verified={len(certified)} uncertified={EXPECTED_UNCERTIFIED}")
    print(f"core_demand_profile={dict(demand_profile)}")
    print(f"shell_profile_rows={len(shell_profile)}")
    print(f"margin_profile={dict(sorted(margins.items()))}")
    print(f"support_profile={dict(sorted(supports.items()))}")
    print(f"semantic_sha256={semantic_hash}")
    print(f"uncertified_pair_sha256={remainder_hash}")
    print("status=PASS")


if __name__ == "__main__":
    main()
