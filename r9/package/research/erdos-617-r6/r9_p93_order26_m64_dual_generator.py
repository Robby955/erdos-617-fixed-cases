#!/usr/bin/env python3
"""Generate exact rational duals for the full fixed-r=9 m=64 catalog.

The floating-point optimizer only proposes weights. Every retained vector
is normalized and checked over ``Fraction`` before it is written. A separate
semantic verifier must reconstruct the catalogs and check the output before
this file can support a theorem claim.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import subprocess
import sys
from typing import Any

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
ENGINE_PATH = HERE / "r9_p93_order26_m59_dual_generator.py"
R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 64
GLOBAL_OFFSET = 19
EXPECTED_CORES = 1
EXPECTED_SHELLS = 7454
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_CERTIFICATES = 6892
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
NONCLAIM = (
    "The 562 uncertified pairs remain open in this package; it does not "
    "exclude m=64, prove fixed r=9, or solve Erdos Problem 617."
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ENGINE = load_module("erdos617_m64_dual_engine", ENGINE_PATH)


@dataclass(frozen=True)
class GraphCase:
    line: bytes
    graph: nx.Graph
    minimum_slack: int = 0

    @property
    def edges(self) -> int:
        return int(self.graph.number_of_edges())


def p_r(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1, 2
    )


def adjacency_masks(graph: nx.Graph) -> tuple[int, ...]:
    masks = [0] * graph.number_of_nodes()
    for raw_first, raw_second in graph.edges:
        first = int(raw_first)
        second = int(raw_second)
        masks[first] |= 1 << second
        masks[second] |= 1 << first
    return tuple(masks)


def induced_edges(mask: int, adjacency: tuple[int, ...]) -> int:
    return sum(
        (adjacency[vertex] & mask).bit_count()
        for vertex in range(len(adjacency))
        if mask >> vertex & 1
    ) // 2


def independent(mask: int, adjacency: tuple[int, ...]) -> bool:
    remaining = mask
    while remaining:
        bit = remaining & -remaining
        vertex = bit.bit_length() - 1
        if adjacency[vertex] & mask:
            return False
        remaining ^= bit
    return True


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    adjacency = adjacency_masks(graph)
    if any(nx.triangles(graph).values()):
        return False
    if max(int(degree) for _, degree in graph.degree()) > R - 1:
        return False
    if any(
        independent(sum(1 << vertex for vertex in vertices), adjacency)
        for vertices in itertools.combinations(range(CORE_ORDER), R)
    ):
        return False
    for subset_order in range(R + 1, CORE_ORDER + 1):
        minimum = (R - 1) * p_r(subset_order)
        for vertices in itertools.combinations(range(CORE_ORDER), subset_order):
            mask = sum(1 << vertex for vertex in vertices)
            if induced_edges(mask, adjacency) < minimum:
                return False
    return True


def minimum_shell_slack(graph: nx.Graph, limit: int = 11) -> int | None:
    degrees = tuple(int(graph.degree(vertex)) for vertex in range(SHELL_ORDER))
    demands = tuple(
        (
            int(first),
            int(second),
            max(0, 8 - degrees[int(first)] - degrees[int(second)]),
        )
        for first, second in graph.edges
    )
    best = limit + 1
    visited: set[tuple[int, ...]] = set()

    def search(epsilon: tuple[int, ...]) -> None:
        nonlocal best
        total = sum(epsilon)
        if total >= best or total > limit or epsilon in visited:
            return
        visited.add(epsilon)
        violations = [
            (demand - epsilon[first] - epsilon[second], first, second)
            for first, second, demand in demands
            if epsilon[first] + epsilon[second] < demand
        ]
        if not violations:
            best = total
            return
        deficit, first, second = max(
            violations,
            key=lambda item: (
                item[0],
                graph.degree(item[1]) + graph.degree(item[2]),
            ),
        )
        for first_increment in range(deficit + 1):
            updated = list(epsilon)
            updated[first] += first_increment
            updated[second] += deficit - first_increment
            search(tuple(updated))

    search((0,) * SHELL_ORDER)
    return None if best == limit + 1 else best


def generate_cores(geng: Path) -> tuple[Any, ...]:
    cases = []
    command = [str(geng), "-q", "-t", "-D8", "16", "64:64"]
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if valid_core(graph):
            cases.append(GraphCase(graph6, graph))
    return tuple(sorted(cases, key=lambda case: case.line))


def generate_shells(geng: Path) -> tuple[Any, ...]:
    cases = []
    command = [str(geng), "-q", "-k", str(SHELL_ORDER), "8:19"]
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        adjacency = adjacency_masks(graph)
        full = (1 << SHELL_ORDER) - 1
        if any(
            independent(full ^ (1 << omitted), adjacency)
            for omitted in range(SHELL_ORDER)
        ):
            continue
        slack = minimum_shell_slack(graph)
        if slack is not None and graph.number_of_edges() + slack <= GLOBAL_OFFSET:
            cases.append(GraphCase(graph6, graph, slack))
    return tuple(sorted(cases, key=lambda case: case.line))


def catalog_sha256(cases: tuple[Any, ...], attribute: str) -> str:
    payload = b"\n".join(getattr(case, attribute) for case in cases) + b"\n"
    return hashlib.sha256(payload).hexdigest()


def encoded_weights(
    weights: tuple[tuple[int, Fraction], ...],
) -> list[list[int]]:
    return [
        [row_index, weight.numerator, weight.denominator]
        for row_index, weight in weights
    ]


def semantic_sha256(records: list[dict[str, Any]]) -> str:
    rows = []
    for record in records:
        core = nx.from_graph6_bytes(record["core"].encode("ascii"))
        shell = nx.from_graph6_bytes(record["shell"].encode("ascii"))
        inequalities = ENGINE.inequalities(core, shell)
        objective = Fraction(0)
        for row_index, numerator, denominator in record["weights"]:
            objective += inequalities[row_index].right_side * Fraction(
                numerator, denominator
            )
        margin = objective - (shell.number_of_edges() + GLOBAL_OFFSET)
        rows.append(
            f"{record['core']}:{record['shell']}:"
            f"{margin.numerator}/{margin.denominator}:"
            f"{len(record['weights'])}\n"
        )
    return hashlib.sha256("".join(sorted(rows)).encode("ascii")).hexdigest()


def complement_sha256(
    cores: tuple[Any, ...],
    shells: tuple[Any, ...],
    certified: set[tuple[int, int]],
) -> str:
    payload = "".join(
        f"{core_index}:{shell_index}\n"
        for core_index in range(len(cores))
        for shell_index in range(len(shells))
        if (core_index, shell_index) not in certified
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()

    cores = generate_cores(args.geng)
    shells = generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )
    core_hash = catalog_sha256(cores, "line")
    shell_hash = catalog_sha256(shells, "line")
    if core_hash != EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if shell_hash != EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")

    records: list[dict[str, Any]] = []
    certified: set[tuple[int, int]] = set()
    for core_index, core in enumerate(cores):
        for shell_index, shell in enumerate(shells):
            rows = ENGINE.inequalities(core.graph, shell.graph)
            weights = ENGINE.discover_dual(rows)
            objective = sum(
                rows[row_index].right_side * weight
                for row_index, weight in weights
            )
            budget = shell.edges + GLOBAL_OFFSET
            if objective <= budget:
                continue
            certified.add((core_index, shell_index))
            records.append(
                {
                    "core": core.line.decode("ascii"),
                    "shell": shell.line.decode("ascii"),
                    "weights": encoded_weights(weights),
                }
            )
    if len(records) != EXPECTED_CERTIFICATES:
        raise AssertionError(
            f"expected {EXPECTED_CERTIFICATES} certificates, found {len(records)}"
        )

    remainder_hash = complement_sha256(cores, shells, certified)
    semantic_hash = semantic_sha256(records)
    if not args.allow_unpinned:
        if remainder_hash != EXPECTED_UNCERTIFIED_PAIR_SHA256:
            raise AssertionError("uncommitted complement digest")
        if semantic_hash != EXPECTED_SEMANTIC_SHA256:
            raise AssertionError("uncommitted semantic digest")

    header = {
        "schema": "erdos617-r9-m64-duals-v1",
        "core_count": len(cores),
        "shell_count": len(shells),
        "pair_count": len(cores) * len(shells),
        "certificate_count": len(records),
        "uncertified_pair_count": EXPECTED_PAIRS - len(records),
        "core_catalog_sha256": core_hash,
        "shell_catalog_sha256": shell_hash,
        "uncertified_pair_sha256": remainder_hash,
        "semantic_sha256": semantic_hash,
        "nonclaim": NONCLAIM,
    }
    with args.output.open("w", encoding="ascii") as handle:
        handle.write(json.dumps(header, sort_keys=True, separators=(",", ":")))
        handle.write("\n")
        for record in records:
            handle.write(json.dumps(record, sort_keys=True, separators=(",", ":")))
            handle.write("\n")

    data_hash = hashlib.sha256(args.output.read_bytes()).hexdigest()
    print(f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}")
    print(f"certificates={len(records)} uncertified={EXPECTED_PAIRS - len(records)}")
    print(f"semantic_sha256={semantic_hash}")
    print(f"uncertified_pair_sha256={remainder_hash}")
    print(f"data_sha256={data_hash}")
    print(f"output={args.output}")


if __name__ == "__main__":
    main()
