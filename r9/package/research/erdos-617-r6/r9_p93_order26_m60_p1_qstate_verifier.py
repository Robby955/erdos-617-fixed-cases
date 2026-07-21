#!/usr/bin/env python3
"""Verify the r=9, order-26, degree-nine core level m=60.

The verifier rebuilds the exact catalogs and semantically checks all 1,290
rational duals.  It excludes ten exceptional-shell pairs by a direct
set-system argument and exhausts 23,157 row-size states for the other 220
pairs with a solver-free, pair-granular two-hub dynamic program.
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
DUAL_MODULE_PATH = HERE / "verify_r9_p93_order26_m60_duals.py"
DUAL_PATH = HERE / "r9_p93_order26_m60_duals.jsonl"
CORE_ORDER = 16
SHELL_ORDER = 9
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
GLOBAL_OFFSET = 15
EXPECTED_CORES = 10
EXPECTED_SHELLS = 152
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_DUAL_PAIRS = 1290
EXPECTED_REMAINING_PAIRS = 230
EXPECTED_TWO_HUB_PAIRS = 220
EXPECTED_EXCEPTIONAL_PAIRS = 10
EXPECTED_Q_STATES = 23157
EXPECTED_HUB_PAIRS_EXAMINED = 953822464
EXPECTED_DEMAND_STATES_EXAMINED = 146962422
EXPECTED_EXCEPTIONAL_SHELL_INDEX = 119
EXPECTED_EXCEPTIONAL_SHELL_GRAPH6 = "H??Fvrw"
EXPECTED_CLASSIFICATION_SHA256 = (
    "1454b3bb20347bad1cf4e064c0414151c863caa7b4695c168f8f34cc3548fa21"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_module("r9_m60_p1_dual_verifier", DUAL_MODULE_PATH)


@dataclass(frozen=True)
class DualReceipt:
    pairs: frozenset[tuple[str, str]]
    semantic_sha256: str
    remainder_sha256: str
    data_sha256: str


@dataclass(frozen=True)
class StateReceipt:
    core_index: int
    shell_index: int
    row_sizes: tuple[int, ...]
    satisfiable: bool
    hub_pairs: int
    demand_states: int


@dataclass(frozen=True)
class SearchReceipt:
    satisfiable: bool
    hub_pairs: int
    demand_states: int


def verify_duals(
    path: Path,
    cores: tuple[Any, ...],
    shells: tuple[Any, ...],
) -> DualReceipt:
    data_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    if data_sha256 != DUAL.EXPECTED_DATA_SHA256:
        raise AssertionError(f"certificate data digest mismatch: {data_sha256}")
    core_map = {case.graph6.decode("ascii"): case.graph for case in cores}
    shell_map = {case.graph6.decode("ascii"): case.graph for case in shells}
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != EXPECTED_DUAL_PAIRS + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    DUAL.parse_header(json.loads(lines[0]))
    certified: set[tuple[str, str]] = set()
    semantic_rows = []
    for line_number, line in enumerate(lines[1:], start=2):
        pair, margin, support_size = DUAL.verify_record(
            json.loads(line), core_map, shell_map
        )
        if pair in certified:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        certified.add(pair)
        semantic_rows.append((pair[0], pair[1], margin, support_size))
    if len(certified) != EXPECTED_DUAL_PAIRS:
        raise AssertionError(f"wrong dual-pair count: {len(certified)}")
    semantic_sha256 = DUAL.semantic_sha256(semantic_rows)
    if semantic_sha256 != DUAL.EXPECTED_SEMANTIC_SHA256:
        raise AssertionError(f"dual semantic digest mismatch: {semantic_sha256}")
    remainder_sha256 = DUAL.uncertified_pair_sha256(cores, shells, certified)
    if remainder_sha256 != DUAL.EXPECTED_UNCERTIFIED_PAIR_SHA256:
        raise AssertionError(f"dual remainder digest mismatch: {remainder_sha256}")
    return DualReceipt(
        frozenset(certified),
        semantic_sha256,
        remainder_sha256,
        data_sha256,
    )


def weak_compositions_at_most(
    budget: int, length: int
) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = []

    def extend(prefix: tuple[int, ...], remaining: int) -> None:
        if len(prefix) == length:
            result.append(prefix)
            return
        for value in range(remaining + 1):
            extend(prefix + (value,), remaining - value)

    extend((), budget)
    return tuple(result)


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    if not 0 <= budget <= 7:
        raise AssertionError("shell scalar budget is outside zero through seven")
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        row_sizes = tuple(
            degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER)
        )
        if all(
            row_sizes[first] + row_sizes[second] >= 8
            for first, second in shell.edges
        ):
            states.add(row_sizes)
    return tuple(sorted(states))


def two_vertex_edge_cover(shell: nx.Graph) -> tuple[int, int] | None:
    candidates = []
    for first, second in itertools.combinations(range(SHELL_ORDER), 2):
        if all(first in edge or second in edge for edge in shell.edges):
            candidates.append(
                (int(shell.degree(first)) + int(shell.degree(second)), first, second)
            )
    if not candidates:
        return None
    _, first, second = max(candidates)
    return first, second


def bipartition(core: nx.Graph) -> tuple[tuple[int, ...], tuple[int, ...]]:
    if not nx.is_bipartite(core):
        raise AssertionError("m=60 core is not bipartite")
    colours = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(
            sorted(int(vertex) for vertex, colour in colours.items() if colour == side)
        )
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("m=60 core does not have an 8+8 bipartition")
    return sides[0], sides[1]


COMBINATION_MASKS = tuple(
    tuple(
        sum(1 << vertex for vertex in vertices)
        for vertices in itertools.combinations(range(CORE_ORDER), size)
    )
    for size in range(CORE_ORDER + 1)
)


class P1CoreSearch:
    """Two-hub finite search with both core sides forbidden in every row."""

    def __init__(self, core: nx.Graph):
        self.core = core
        side_vertices = bipartition(core)
        self.side_masks = tuple(
            sum(1 << vertex for vertex in side) for side in side_vertices
        )
        adjacency = DUAL.adjacency_masks(core)
        self.is_cover = tuple(
            DUAL.independent(FULL_CORE_MASK ^ mask, adjacency)
            for mask in range(1 << CORE_ORDER)
        )
        self.allowed_masks = tuple(
            tuple(mask for mask in masks if self.p1_allowed(mask))
            for masks in COMBINATION_MASKS
        )
        self.extension_cache: dict[tuple[int, int], tuple[int, ...]] = {}

    def p1_allowed(self, row: int) -> bool:
        return all(row & side != side for side in self.side_masks)

    def extensions(self, fixed: int, size: int) -> tuple[int, ...]:
        key = (fixed, size)
        if key not in self.extension_cache:
            self.extension_cache[key] = tuple(
                row
                for row in self.allowed_masks[size]
                if self.is_cover[fixed | row]
            )
        return self.extension_cache[key]

    def solve(self, shell: nx.Graph, row_sizes: tuple[int, ...]) -> SearchReceipt:
        hubs = two_vertex_edge_cover(shell)
        if hubs is None:
            raise AssertionError("two-hub search received an unsupported shell")
        first_hub, second_hub = hubs
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
            vertex for vertex in low_vertices if shell.has_edge(first_hub, vertex)
        )
        second_neighbors = tuple(
            vertex for vertex in low_vertices if shell.has_edge(second_hub, vertex)
        )

        def hub_candidates(hub: int, neighbors: tuple[int, ...]) -> tuple[int, ...]:
            return tuple(
                row
                for row in self.allowed_masks[row_sizes[hub]]
                if all(self.extensions(row, row_sizes[neighbor]) for neighbor in neighbors)
            )

        first_candidates = hub_candidates(first_hub, first_neighbors)
        second_candidates = hub_candidates(second_hub, second_neighbors)
        column_demands = tuple(
            max(0, int(self.core.degree(vertex)) - 6)
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
                    domain = self.allowed_masks[row_sizes[low]]
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


def verify_exceptional_shell(
    cores: tuple[Any, ...],
    shell_case: Any,
) -> Counter[tuple[int, int]]:
    shell = shell_case.graph
    if shell_case.graph6.decode("ascii") != EXPECTED_EXCEPTIONAL_SHELL_GRAPH6:
        raise AssertionError("exceptional shell graph6 mismatch")
    components = tuple(
        sorted(
            (tuple(sorted(component)) for component in nx.connected_components(shell)),
            key=lambda component: (len(component), component),
        )
    )
    if tuple(map(len, components)) != (1, 8):
        raise AssertionError("exceptional shell does not have components 1+8")
    isolated = components[0][0]
    connected = shell.subgraph(components[1]).copy()
    if not nx.is_bipartite(connected) or connected.number_of_edges() != 15:
        raise AssertionError("exceptional shell component is not K5,3")
    colours = nx.algorithms.bipartite.color(connected)
    parts = tuple(
        tuple(vertex for vertex, colour in colours.items() if colour == side)
        for side in (0, 1)
    )
    if tuple(sorted(map(len, parts))) != (3, 5):
        raise AssertionError("exceptional shell does not have a 3+5 bipartition")
    if any(
        not connected.has_edge(first, second)
        for first in parts[0]
        for second in parts[1]
    ):
        raise AssertionError("exceptional shell is not complete bipartite")
    states = row_size_states(shell)
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    if states != (degrees,) or degrees[isolated] != 0:
        raise AssertionError(f"exceptional shell row state mismatch: {states}")
    if not nx.is_connected(nx.line_graph(connected)):
        raise AssertionError("exceptional edge labels need not propagate")

    demand_profile: Counter[tuple[int, int]] = Counter()
    for core_case in cores:
        core = core_case.graph
        sides = bipartition(core)
        independent_eights = {
            frozenset(vertices)
            for vertices in itertools.combinations(range(CORE_ORDER), 8)
            if core.subgraph(vertices).number_of_edges() == 0
        }
        if independent_eights != {frozenset(sides[0]), frozenset(sides[1])}:
            raise AssertionError("core sides are not the only minimum covers")
        deleted_sums = tuple(
            sum(8 - int(core.degree(vertex)) for vertex in side) for side in sides
        )
        if deleted_sums != (4, 4):
            raise AssertionError(f"deleted-degree sum mismatch: {deleted_sums}")
        demand_sums = tuple(
            sum(max(0, int(core.degree(vertex)) - 6) for vertex in side)
            for side in sides
        )
        if min(demand_sums) < 12:
            raise AssertionError(f"exceptional opposite-side demand fails: {demand_sums}")
        smaller, larger = sorted(demand_sums)
        demand_profile[(smaller, larger)] += 1
    if demand_profile != DUAL.EXPECTED_DEMAND_PROFILE:
        raise AssertionError(f"exceptional demand profile mismatch: {demand_profile}")
    return demand_profile


def audit_pair(
    task: tuple[int, int, str, str],
) -> tuple[StateReceipt, ...]:
    core_index, shell_index, core_name, shell_name = task
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    search = P1CoreSearch(core)
    states = []
    for row_sizes in row_size_states(shell):
        result = search.solve(shell, row_sizes)
        states.append(
            StateReceipt(
                core_index,
                shell_index,
                row_sizes,
                result.satisfiable,
                result.hub_pairs,
                result.demand_states,
            )
        )
    return tuple(states)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_PATH)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )
    if DUAL.catalog_sha256(cores) != DUAL.EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if DUAL.catalog_sha256(shells) != DUAL.EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")
    dual_receipt = verify_duals(args.duals, cores, shells)

    remainder = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (
            core.graph6.decode("ascii"),
            shell.graph6.decode("ascii"),
        )
        not in dual_receipt.pairs
    )
    if len(remainder) != EXPECTED_REMAINING_PAIRS:
        raise AssertionError(f"wrong remainder-pair count: {len(remainder)}")
    supported = tuple(
        pair for pair in remainder if two_vertex_edge_cover(shells[pair[1]].graph)
    )
    exceptional = tuple(pair for pair in remainder if pair not in set(supported))
    if len(supported) != EXPECTED_TWO_HUB_PAIRS:
        raise AssertionError(f"wrong two-hub-pair count: {len(supported)}")
    if len(exceptional) != EXPECTED_EXCEPTIONAL_PAIRS:
        raise AssertionError(f"wrong exceptional-pair count: {len(exceptional)}")
    if {shell_index for _, shell_index in exceptional} != {
        EXPECTED_EXCEPTIONAL_SHELL_INDEX
    }:
        raise AssertionError(f"unexpected exceptional shells: {exceptional}")
    demand_profile = verify_exceptional_shell(
        cores, shells[EXPECTED_EXCEPTIONAL_SHELL_INDEX]
    )

    tasks = tuple(
        (
            core_index,
            shell_index,
            cores[core_index].graph6.decode("ascii"),
            shells[shell_index].graph6.decode("ascii"),
        )
        for core_index, shell_index in supported
    )
    if args.workers == 1:
        nested = tuple(audit_pair(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            nested = tuple(pool.map(audit_pair, tasks))
    states = tuple(state for group in nested for state in group)
    satisfiable = tuple(state for state in states if state.satisfiable)
    if len(states) != EXPECTED_Q_STATES:
        raise AssertionError(f"wrong q-state count: {len(states)}")
    if satisfiable:
        raise AssertionError(f"unexpected p1-SAT states: {len(satisfiable)}")
    hub_pairs = sum(state.hub_pairs for state in states)
    demand_states = sum(state.demand_states for state in states)
    if hub_pairs != EXPECTED_HUB_PAIRS_EXAMINED:
        raise AssertionError(f"wrong hub-pair count: {hub_pairs}")
    if demand_states != EXPECTED_DEMAND_STATES_EXAMINED:
        raise AssertionError(f"wrong demand-state count: {demand_states}")
    classification = "".join(
        f"{state.core_index}:{state.shell_index}:"
        f"{','.join(map(str, state.row_sizes))}:{int(state.satisfiable)}\n"
        for state in sorted(
            states,
            key=lambda item: (item.core_index, item.shell_index, item.row_sizes),
        )
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    if classification_sha256 != EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(
            "classification digest mismatch: "
            f"{classification_sha256} != {EXPECTED_CLASSIFICATION_SHA256}"
        )
    pair_profile = Counter(
        sum(
            state.core_index == core_index and state.shell_index == shell_index
            for state in states
        )
        for core_index, shell_index in supported
    )
    print(f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}")
    print(
        f"strict_duals_semantically_verified={len(dual_receipt.pairs)} "
        f"uncertified_pairs={len(remainder)}"
    )
    print(f"dual_semantic_sha256={dual_receipt.semantic_sha256}")
    print(f"dual_remainder_sha256={dual_receipt.remainder_sha256}")
    print(f"dual_data_sha256={dual_receipt.data_sha256}")
    print(
        f"two_hub_remainder_pairs={len(supported)} "
        f"exceptional_pairs={len(exceptional)}"
    )
    print(
        f"exceptional_shell={EXPECTED_EXCEPTIONAL_SHELL_GRAPH6} "
        f"demand_profile={dict(demand_profile)}"
    )
    print(f"q_states={len(states)} p1_UNSAT={len(states)} p1_SAT=0")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"hub_pairs_examined={hub_pairs}")
    print(f"demand_states_examined={demand_states}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
