#!/usr/bin/env python3
"""Exhaust the exact row-size states left by the m=58 rational duals.

The search is solver-free.  Each remaining shell has a two-vertex edge
cover.  After fixing the two hub rows, every other row has an explicit
finite domain determined by the row-pair cover conditions.  A memoized
dynamic program checks the remaining column demands.  The surviving states
are then checked for the triangle configuration that forces a target K9.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from typing import Any

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
CATALOG_PATH = HERE / "verify_r9_p93_order26_m58_duals.py"
DUAL_PATH = HERE / "r9_p93_order26_m58_duals.jsonl"
CORE_ORDER = 16
SHELL_ORDER = 9
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
EXPECTED_CORES = 50
EXPECTED_SHELLS = 55
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_DUAL_PAIRS = 1858
EXPECTED_REMAINING_PAIRS = EXPECTED_PAIRS - EXPECTED_DUAL_PAIRS
EXPECTED_Q_STATES = 5056
EXPECTED_COVER_UNSAT_STATES = 4981
EXPECTED_COVER_SAT_STATES = 75
EXPECTED_COVER_UNSAT_PAIRS = 849
EXPECTED_COVER_SAT_PAIRS = 43
EXPECTED_BOUNDARY_Q_STATES = 274
EXPECTED_BOUNDARY_UNSAT_STATES = 199
EXPECTED_DUAL_SEMANTIC_SHA256 = (
    "f6d87a372bcea968bfa048746cadbb653a40a9b8512256d044d9906fd85828ce"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "0dff9f3a707e730c3a31e880de7ce32a38404e7b7a92ba4355ec7c97a04d6938"
)


def load_catalog() -> Any:
    spec = importlib.util.spec_from_file_location("r9_m58_q_catalog", CATALOG_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CATALOG_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CATALOG = load_catalog()


@dataclass(frozen=True)
class SearchReceipt:
    satisfiable: bool
    hub_pairs: int
    demand_states: int


@dataclass(frozen=True)
class StateReceipt:
    pair_index: int
    core_graph6: str
    shell_graph6: str
    row_sizes: tuple[int, ...]
    satisfiable: bool
    forcing_triangle: bool
    hub_pairs: int
    demand_states: int


@dataclass(frozen=True)
class CoreReceipt:
    core_index: int
    states: tuple[StateReceipt, ...]


@dataclass(frozen=True)
class DualReceipt:
    pairs: frozenset[tuple[str, str]]
    semantic_sha256: str


COMBINATION_MASKS = tuple(
    tuple(
        sum(1 << vertex for vertex in vertices)
        for vertices in itertools.combinations(range(CORE_ORDER), size)
    )
    for size in range(CORE_ORDER + 1)
)


def verify_duals(
    path: Path,
    core_map: dict[str, nx.Graph],
    shell_map: dict[str, nx.Graph],
) -> DualReceipt:
    lines = tuple(
        line
        for line in path.read_text(encoding="ascii").splitlines()
        if line.strip()
    )
    if len(lines) != EXPECTED_DUAL_PAIRS + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    CATALOG.parse_header(json.loads(lines[0]))
    pairs = set()
    semantic_rows = []
    for line_number, line in enumerate(lines[1:], start=2):
        pair, margin, support_size = CATALOG.verify_record(
            json.loads(line), core_map, shell_map
        )
        if pair in pairs:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        pairs.add(pair)
        semantic_rows.append(
            (
                pair[0],
                pair[1],
                margin.numerator,
                margin.denominator,
                support_size,
            )
        )
    if len(pairs) != EXPECTED_DUAL_PAIRS:
        raise AssertionError(f"wrong dual pair count: {len(pairs)}")
    semantic_payload = "".join(
        f"{core}:{shell}:{numerator}/{denominator}:{support_size}\n"
        for core, shell, numerator, denominator, support_size in sorted(
            semantic_rows
        )
    ).encode("ascii")
    semantic_sha256 = hashlib.sha256(semantic_payload).hexdigest()
    if (
        EXPECTED_DUAL_SEMANTIC_SHA256
        and semantic_sha256 != EXPECTED_DUAL_SEMANTIC_SHA256
    ):
        raise AssertionError(
            "dual semantic digest mismatch: "
            f"{semantic_sha256} != {EXPECTED_DUAL_SEMANTIC_SHA256}"
        )
    return DualReceipt(frozenset(pairs), semantic_sha256)


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    degrees = tuple(shell.degree(vertex) for vertex in range(SHELL_ORDER))
    budget = 13 - shell.number_of_edges()
    if not 0 <= budget <= 5:
        raise AssertionError("shell has the wrong scalar budget")
    states = set()
    for epsilon in CATALOG.COMPOSITIONS[budget]:
        if all(
            degrees[first]
            + degrees[second]
            + epsilon[first]
            + epsilon[second]
            >= 8
            for first, second in shell.edges
        ):
            states.add(
                tuple(
                    degrees[vertex] + epsilon[vertex]
                    for vertex in range(SHELL_ORDER)
                )
            )
    return tuple(sorted(states))


def shell_edge_cover(shell: nx.Graph) -> tuple[int, int]:
    candidates = []
    for first, second in itertools.combinations(range(SHELL_ORDER), 2):
        if all(first in edge or second in edge for edge in shell.edges):
            candidates.append(
                (
                    shell.degree(first) + shell.degree(second),
                    first,
                    second,
                )
            )
    if not candidates:
        raise AssertionError("remaining shell has no two-vertex edge cover")
    _, first, second = max(candidates)
    return first, second


def forcing_triangle(shell: nx.Graph, row_sizes: tuple[int, ...]) -> bool:
    for triangle in itertools.combinations(range(SHELL_ORDER), 3):
        if not all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(triangle, 2)
        ):
            continue
        for high_index in range(3):
            high = triangle[high_index]
            others = tuple(
                triangle[index] for index in range(3) if index != high_index
            )
            if row_sizes[high] == 8 and sum(row_sizes[v] for v in others) == 8:
                return True
    return False


class CoreSearch:
    def __init__(self, core: nx.Graph):
        self.core = core
        adjacency = CATALOG.adjacency_masks(core)
        self.is_cover = tuple(
            CATALOG.independent(FULL_CORE_MASK ^ mask, adjacency)
            for mask in range(1 << CORE_ORDER)
        )
        self.extension_cache: dict[tuple[int, int], tuple[int, ...]] = {}

    def extensions(self, fixed: int, size: int) -> tuple[int, ...]:
        key = (fixed, size)
        if key not in self.extension_cache:
            self.extension_cache[key] = tuple(
                row
                for row in COMBINATION_MASKS[size]
                if self.is_cover[fixed | row]
            )
        return self.extension_cache[key]

    def solve(
        self, shell: nx.Graph, row_sizes: tuple[int, ...]
    ) -> SearchReceipt:
        first_hub, second_hub = shell_edge_cover(shell)
        low_vertices = tuple(
            vertex
            for vertex in range(SHELL_ORDER)
            if vertex not in (first_hub, second_hub)
        )
        if any(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(low_vertices, 2)
        ):
            raise AssertionError("chosen shell hubs do not cover every edge")

        first_neighbors = tuple(
            vertex
            for vertex in low_vertices
            if shell.has_edge(first_hub, vertex)
        )
        second_neighbors = tuple(
            vertex
            for vertex in low_vertices
            if shell.has_edge(second_hub, vertex)
        )

        def hub_candidates(hub: int, neighbors: tuple[int, ...]) -> tuple[int, ...]:
            return tuple(
                row
                for row in COMBINATION_MASKS[row_sizes[hub]]
                if all(self.extensions(row, row_sizes[neighbor]) for neighbor in neighbors)
            )

        first_candidates = hub_candidates(first_hub, first_neighbors)
        second_candidates = hub_candidates(second_hub, second_neighbors)
        column_demands = tuple(
            max(0, self.core.degree(vertex) - 6)
            for vertex in range(CORE_ORDER)
        )
        hub_pairs = 0
        demand_states = 0

        for first_row in first_candidates:
            for second_row in second_candidates:
                hub_pairs += 1
                if shell.has_edge(first_hub, second_hub) and not self.is_cover[
                    first_row | second_row
                ]:
                    continue
                domains = []
                rejected = False
                for low in low_vertices:
                    domain = COMBINATION_MASKS[row_sizes[low]]
                    if shell.has_edge(first_hub, low):
                        first_allowed = frozenset(
                            self.extensions(first_row, row_sizes[low])
                        )
                        domain = tuple(row for row in domain if row in first_allowed)
                    if shell.has_edge(second_hub, low):
                        second_allowed = frozenset(
                            self.extensions(second_row, row_sizes[low])
                        )
                        domain = tuple(row for row in domain if row in second_allowed)
                    if (
                        shell.has_edge(first_hub, second_hub)
                        and shell.has_edge(first_hub, low)
                        and shell.has_edge(second_hub, low)
                    ):
                        domain = tuple(
                            row
                            for row in domain
                            if first_row | second_row | row == FULL_CORE_MASK
                        )
                    if not domain:
                        rejected = True
                        break
                    domains.append(domain)
                if rejected:
                    continue

                residual = tuple(
                    max(
                        0,
                        column_demands[vertex]
                        - ((first_row >> vertex) & 1)
                        - ((second_row >> vertex) & 1),
                    )
                    for vertex in range(CORE_ORDER)
                )
                ordered_domains = tuple(sorted(domains, key=len))
                memo: set[tuple[int, tuple[int, ...]]] = set()

                def meet_demands(
                    domain_index: int, remaining: tuple[int, ...]
                ) -> bool:
                    nonlocal demand_states
                    demand_states += 1
                    if not any(remaining):
                        return True
                    if domain_index == len(ordered_domains):
                        return False
                    key = (domain_index, remaining)
                    if key in memo:
                        return False
                    memo.add(key)
                    tail = ordered_domains[domain_index:]
                    for vertex, demand in enumerate(remaining):
                        possible = sum(
                            any(row >> vertex & 1 for row in domain)
                            for domain in tail
                        )
                        if demand > possible:
                            return False
                    for row in ordered_domains[domain_index]:
                        updated = tuple(
                            max(0, demand - ((row >> vertex) & 1))
                            for vertex, demand in enumerate(remaining)
                        )
                        if meet_demands(domain_index + 1, updated):
                            return True
                    return False

                if meet_demands(0, residual):
                    return SearchReceipt(True, hub_pairs, demand_states)

        return SearchReceipt(False, hub_pairs, demand_states)


def audit_core(task: tuple[int, str, tuple[tuple[int, str], ...]]) -> CoreReceipt:
    core_index, core_graph6, shell_entries = task
    core = nx.from_graph6_bytes(core_graph6.encode("ascii"))
    search = CoreSearch(core)
    states = []
    for pair_index, shell_graph6 in shell_entries:
        shell = nx.from_graph6_bytes(shell_graph6.encode("ascii"))
        for row_sizes in row_size_states(shell):
            result = search.solve(shell, row_sizes)
            states.append(
                StateReceipt(
                    pair_index,
                    core_graph6,
                    shell_graph6,
                    row_sizes,
                    result.satisfiable,
                    forcing_triangle(shell, row_sizes),
                    result.hub_pairs,
                    result.demand_states,
                )
            )
    return CoreReceipt(core_index, tuple(states))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_PATH)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = CATALOG.generate_cores(args.geng)
    shells = CATALOG.generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )
    for core in cores:
        CATALOG.core_demand_profile(core.graph)
    core_map = {core.graph6.decode("ascii"): core.graph for core in cores}
    shell_map = {shell.graph6.decode("ascii"): shell.graph for shell in shells}
    if len(core_map) != EXPECTED_CORES or len(shell_map) != EXPECTED_SHELLS:
        raise AssertionError("graph6 catalog contains a duplicate")
    dual_receipt = verify_duals(args.duals, core_map, shell_map)
    dual_pairs = dual_receipt.pairs
    tasks = []
    remaining_pairs = 0
    for core_index, core in enumerate(cores):
        core_name = core.graph6.decode("ascii")
        entries = []
        for shell_index, shell in enumerate(shells):
            shell_name = shell.graph6.decode("ascii")
            if (core_name, shell_name) in dual_pairs:
                continue
            pair_index = core_index * EXPECTED_SHELLS + shell_index
            entries.append((pair_index, shell_name))
            remaining_pairs += 1
        tasks.append((core_index, core_name, tuple(entries)))
    if remaining_pairs != EXPECTED_REMAINING_PAIRS:
        raise AssertionError(f"wrong remaining pair count: {remaining_pairs}")

    if args.workers == 1:
        receipts = tuple(audit_core(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            receipts = tuple(pool.map(audit_core, tasks))
    receipts = tuple(sorted(receipts, key=lambda receipt: receipt.core_index))
    states = tuple(state for receipt in receipts for state in receipt.states)

    q_state_count = len(states)
    satisfiable = tuple(state for state in states if state.satisfiable)
    unsatisfiable = tuple(state for state in states if not state.satisfiable)
    satisfiable_pairs = {state.pair_index for state in satisfiable}
    all_pairs = {state.pair_index for state in states}
    unsatisfiable_pairs = all_pairs - satisfiable_pairs
    boundary_states = tuple(
        state for state in states if state.pair_index in satisfiable_pairs
    )
    boundary_unsatisfiable = tuple(
        state for state in boundary_states if not state.satisfiable
    )

    if q_state_count != EXPECTED_Q_STATES:
        raise AssertionError(f"wrong q-state count: {q_state_count}")
    if len(unsatisfiable) != EXPECTED_COVER_UNSAT_STATES:
        raise AssertionError(
            f"wrong cover-UNSAT state count: {len(unsatisfiable)}"
        )
    if len(satisfiable) != EXPECTED_COVER_SAT_STATES:
        raise AssertionError(f"wrong cover-SAT state count: {len(satisfiable)}")
    if len(unsatisfiable_pairs) != EXPECTED_COVER_UNSAT_PAIRS:
        raise AssertionError(
            f"wrong cover-UNSAT pair count: {len(unsatisfiable_pairs)}"
        )
    if len(satisfiable_pairs) != EXPECTED_COVER_SAT_PAIRS:
        raise AssertionError(
            f"wrong cover-SAT pair count: {len(satisfiable_pairs)}"
        )
    if len(boundary_states) != EXPECTED_BOUNDARY_Q_STATES:
        raise AssertionError(
            f"wrong boundary q-state count: {len(boundary_states)}"
        )
    if len(boundary_unsatisfiable) != EXPECTED_BOUNDARY_UNSAT_STATES:
        raise AssertionError(
            "wrong boundary cover-UNSAT state count: "
            f"{len(boundary_unsatisfiable)}"
        )
    if any(not state.forcing_triangle for state in satisfiable):
        raise AssertionError("cover-SAT state lacks the forcing triangle")

    pair_state_profile = Counter(
        sum(state.pair_index == pair for state in states) for pair in all_pairs
    )
    classification = "".join(
        f"{state.pair_index}:{','.join(map(str, state.row_sizes))}:"
        f"{int(state.satisfiable)}\n"
        for state in sorted(
            states, key=lambda item: (item.pair_index, item.row_sizes)
        )
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    if (
        EXPECTED_CLASSIFICATION_SHA256
        and classification_sha256 != EXPECTED_CLASSIFICATION_SHA256
    ):
        raise AssertionError(
            "classification digest mismatch: "
            f"{classification_sha256} != {EXPECTED_CLASSIFICATION_SHA256}"
        )
    print(
        f"cores={len(cores)} shells={len(shells)} "
        f"remaining_pairs={remaining_pairs}"
    )
    print(
        f"strict_duals_semantically_verified={len(dual_pairs)} "
        f"uncertified_pairs={remaining_pairs}"
    )
    print(f"dual_semantic_sha256={dual_receipt.semantic_sha256}")
    print(
        f"q_states={q_state_count} cover_UNSAT={len(unsatisfiable)} "
        f"cover_SAT={len(satisfiable)}"
    )
    print(
        f"cover_UNSAT_pairs={len(unsatisfiable_pairs)} "
        f"cover_SAT_pairs={len(satisfiable_pairs)}"
    )
    print(
        f"boundary_q_states={len(boundary_states)} "
        f"boundary_cover_UNSAT={len(boundary_unsatisfiable)} "
        f"boundary_cover_SAT={len(satisfiable)}"
    )
    print(f"pair_q_state_profile={dict(sorted(pair_state_profile.items()))}")
    print(
        "forcing_triangle_cover_SAT="
        f"{sum(state.forcing_triangle for state in satisfiable)}"
    )
    print(f"hub_pairs_examined={sum(state.hub_pairs for state in states)}")
    print(
        "demand_states_examined="
        f"{sum(state.demand_states for state in states)}"
    )
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
