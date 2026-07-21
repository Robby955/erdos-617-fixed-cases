#!/usr/bin/env python3
"""Generate exact rational duals for strict m=63 core-shell pairs.

The floating-point optimizer proposes weights.  Every emitted vector is
normalized and checked with exact fractions before it is written.  The
separate m=63 semantic verifier is the proof-facing check.
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
CORE_EDGES = 63
GLOBAL_OFFSET = 18
EXPECTED_CORES = 1
EXPECTED_SHELLS = 2245
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_CERTIFICATES = 1911
EXPECTED_CORE_CATALOG_SHA256 = (
    "20302c025a85684c659534cc704508b0311c33282dc8d0b19b683fa033855044"
)
EXPECTED_SHELL_CATALOG_SHA256 = (
    "f5e13567a0a977da594eacdaa8b945ba416f13ad507121bb90b91c8f100c43b7"
)
EXPECTED_UNCERTIFIED_PAIR_SHA256 = (
    "f0e775bc61c40d56c54e221f6f47d216939671c6ac2d65c62eace6fa480ebd2b"
)
NONCLAIM = (
    "The 334 uncertified pairs remain open in this package; it does not "
    "exclude m=63, prove fixed r=9, or solve Erdos Problem 617."
)


def load_engine() -> Any:
    spec = importlib.util.spec_from_file_location("r9_m63_dual_engine", ENGINE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {ENGINE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


ENGINE = load_engine()


@dataclass(frozen=True)
class GraphCase:
    graph6: bytes
    graph: nx.Graph


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


def independent(mask: int, adjacency: tuple[int, ...]) -> bool:
    remaining = mask
    while remaining:
        bit = remaining & -remaining
        vertex = bit.bit_length() - 1
        if adjacency[vertex] & mask:
            return False
        remaining ^= bit
    return True


def induced_edges(mask: int, adjacency: tuple[int, ...]) -> int:
    return (
        sum(
            (adjacency[vertex] & mask).bit_count()
            for vertex in range(len(adjacency))
            if mask >> vertex & 1
        )
        // 2
    )


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER or graph.number_of_edges() != CORE_EDGES:
        return False
    if any(nx.triangles(graph).values()):
        return False
    if max(dict(graph.degree()).values()) > R - 1:
        return False
    adjacency = adjacency_masks(graph)
    for vertices in itertools.combinations(range(CORE_ORDER), R):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            return False
    for order in range(R + 1, CORE_ORDER + 1):
        minimum = (R - 1) * p_r(order)
        for vertices in itertools.combinations(range(CORE_ORDER), order):
            mask = sum(1 << vertex for vertex in vertices)
            if induced_edges(mask, adjacency) < minimum:
                return False
    return True


def minimum_shell_slack(graph: nx.Graph, limit: int) -> int | None:
    degrees = tuple(int(graph.degree(vertex)) for vertex in range(SHELL_ORDER))
    demands = tuple(
        (int(first), int(second), max(0, 8 - degrees[int(first)] - degrees[int(second)]))
        for first, second in graph.edges
    )
    visited: set[tuple[int, ...]] = set()
    best: int | None = None

    def search(epsilon: tuple[int, ...]) -> None:
        nonlocal best
        total = sum(epsilon)
        if total > limit or epsilon in visited or (best is not None and total >= best):
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
        deficit, first, second = max(violations)
        for first_increment in range(deficit + 1):
            updated = list(epsilon)
            updated[first] += first_increment
            updated[second] += deficit - first_increment
            search(tuple(updated))

    search((0,) * SHELL_ORDER)
    return best


def generate_cores(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-t", "-D8", "16", "63:63"]
    result = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if valid_core(graph):
            result.append(GraphCase(graph6, graph))
    return tuple(sorted(result, key=lambda case: case.graph6))


def has_independent_eight(graph: nx.Graph) -> bool:
    adjacency = adjacency_masks(graph)
    full = (1 << SHELL_ORDER) - 1
    return any(
        independent(full ^ (1 << omitted), adjacency)
        for omitted in range(SHELL_ORDER)
    )


def generate_shells(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-k", "9", "12:18"]
    result = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if has_independent_eight(graph):
            continue
        limit = GLOBAL_OFFSET - graph.number_of_edges()
        if minimum_shell_slack(graph, limit) is not None:
            result.append(GraphCase(graph6, graph))
    return tuple(sorted(result, key=lambda case: case.graph6))


def catalog_sha256(cases: tuple[GraphCase, ...]) -> str:
    payload = b"\n".join(case.graph6 for case in cases) + b"\n"
    return hashlib.sha256(payload).hexdigest()


def encoded_weights(weights: tuple[tuple[int, Fraction], ...]) -> list[list[int]]:
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
            f"{margin.numerator}/{margin.denominator}:{len(record['weights'])}\n"
        )
    return hashlib.sha256("".join(sorted(rows)).encode("ascii")).hexdigest()


def uncertified_pair_sha256(
    cores: tuple[GraphCase, ...],
    shells: tuple[GraphCase, ...],
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
        raise AssertionError(f"catalog mismatch: cores={len(cores)} shells={len(shells)}")
    core_hash = catalog_sha256(cores)
    shell_hash = catalog_sha256(shells)
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
            budget = shell.graph.number_of_edges() + GLOBAL_OFFSET
            if objective <= budget:
                continue
            certified.add((core_index, shell_index))
            records.append(
                {
                    "core": core.graph6.decode("ascii"),
                    "shell": shell.graph6.decode("ascii"),
                    "weights": encoded_weights(weights),
                }
            )
    if len(records) != EXPECTED_CERTIFICATES:
        raise AssertionError(
            f"expected {EXPECTED_CERTIFICATES} certificates, found {len(records)}"
        )

    remainder_hash = uncertified_pair_sha256(cores, shells, certified)
    if EXPECTED_UNCERTIFIED_PAIR_SHA256:
        if remainder_hash != EXPECTED_UNCERTIFIED_PAIR_SHA256:
            raise AssertionError("uncertified-pair digest mismatch")
    elif not args.allow_unpinned:
        raise AssertionError("uncertified-pair digest is not pinned")
    semantic_hash = semantic_sha256(records)
    header = {
        "schema": "erdos617-r9-m63-duals-v1",
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
    print("status=PASS")


if __name__ == "__main__":
    main()
