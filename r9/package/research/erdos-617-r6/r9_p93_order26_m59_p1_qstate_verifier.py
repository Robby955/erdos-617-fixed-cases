#!/usr/bin/env python3
"""Verify the r=9, order-26, degree-nine core level m=59.

The verifier rebuilds the exact core and shell catalogs, checks all 1,235
rational dual certificates coefficient by coefficient, and exhausts every
row-size state for the remaining 465 pairs by a solver-free two-hub dynamic
program.  The finite search includes the p=1 target-K9 constraint: no row
may contain either eight-vertex side of the bipartite core.

The floating-point optimizer used to discover the duals and the independent
Z3 audit are not proof premises.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from typing import Any, NoReturn

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
CATALOG_PATH = HERE / "verify_r9_p93_order26_m59_duals.py"
DUAL_PATH = HERE / "r9_p93_order26_m59_duals.jsonl"
CORE_ORDER = 16
SHELL_ORDER = 9
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
GLOBAL_OFFSET = 14
VARIABLE_COUNT = CORE_ORDER * SHELL_ORDER
EXPECTED_CORES = 20
EXPECTED_SHELLS = 85
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_DUAL_PAIRS = 1235
EXPECTED_REMAINING_PAIRS = 465
EXPECTED_Q_STATES = 11943
EXPECTED_P1_UNSAT_STATES = 11943
EXPECTED_P1_SAT_STATES = 0
EXPECTED_TWO_HUB_PAIRS = 465
EXPECTED_HUB_PAIRS_EXAMINED = 251251840
EXPECTED_DEMAND_STATES_EXAMINED = 11190852
EXPECTED_DUAL_SEMANTIC_SHA256 = (
    "0c62f8085a539f43c12d23a28aa1320426814eaba5c9c415d19d3a006f84809b"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "688ba89fcb69a6ca76cc8607dd4aaba4cebd4850367d2b9946919648a55067c8"
)


def load_catalog() -> Any:
    spec = importlib.util.spec_from_file_location("r9_m59_p1_catalog", CATALOG_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CATALOG_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CATALOG = load_catalog()


@dataclass(frozen=True)
class Inequality:
    variables: tuple[int, ...]
    right_side: int


@dataclass(frozen=True)
class SearchReceipt:
    satisfiable: bool
    hub_pairs: int
    demand_states: int


@dataclass(frozen=True)
class StateReceipt:
    core_index: int
    shell_index: int
    row_sizes: tuple[int, ...]
    satisfiable: bool
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


def fail(message: str) -> NoReturn:
    raise AssertionError(message)


def exact_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{name} must be an integer")
    return value


def exact_string(value: Any, name: str) -> str:
    if not isinstance(value, str):
        fail(f"{name} must be a string")
    return value


def cross(shell_vertex: int, core_vertex: int) -> int:
    return CORE_ORDER * shell_vertex + core_vertex


def sorted_edges(graph: nx.Graph) -> tuple[tuple[int, int], ...]:
    result = []
    for raw_first, raw_second in graph.edges:
        first = int(raw_first)
        second = int(raw_second)
        result.append((first, second) if first < second else (second, first))
    return tuple(sorted(result))


def inequalities(core: nx.Graph, shell: nx.Graph) -> tuple[Inequality, ...]:
    rows = []
    for shell_vertex in range(SHELL_ORDER):
        rows.append(
            Inequality(
                tuple(cross(shell_vertex, core) for core in range(CORE_ORDER)),
                int(shell.degree(shell_vertex)),
            )
        )
    for core_vertex in range(CORE_ORDER):
        rows.append(
            Inequality(
                tuple(cross(shell, core_vertex) for shell in range(SHELL_ORDER)),
                max(0, int(core.degree(core_vertex)) - 6),
            )
        )
    for first_shell, second_shell in sorted_edges(shell):
        for first_core, second_core in sorted_edges(core):
            rows.append(
                Inequality(
                    (
                        cross(first_shell, first_core),
                        cross(first_shell, second_core),
                        cross(second_shell, first_core),
                        cross(second_shell, second_core),
                    ),
                    1,
                )
            )
    for triangle in itertools.combinations(range(SHELL_ORDER), 3):
        if not all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(triangle, 2)
        ):
            continue
        for core_vertex in range(CORE_ORDER):
            rows.append(
                Inequality(
                    tuple(cross(shell_vertex, core_vertex) for shell_vertex in triangle),
                    1,
                )
            )
    return tuple(rows)


def parse_weights(raw: Any) -> tuple[tuple[int, Fraction], ...]:
    if not isinstance(raw, list):
        fail("weights must be a list")
    result = []
    previous_index = -1
    for position, entry in enumerate(raw):
        if not isinstance(entry, list) or len(entry) != 3:
            fail(f"weight {position} must be a three-item list")
        row_index = exact_int(entry[0], f"weight {position} row")
        numerator = exact_int(entry[1], f"weight {position} numerator")
        denominator = exact_int(entry[2], f"weight {position} denominator")
        if row_index <= previous_index:
            fail("weight row indices must be strictly increasing")
        if numerator <= 0 or denominator <= 0:
            fail("weight fractions must be positive")
        weight = Fraction(numerator, denominator)
        if weight.numerator != numerator or weight.denominator != denominator:
            fail("weight fraction is not reduced")
        result.append((row_index, weight))
        previous_index = row_index
    return tuple(result)


def verify_duals(
    path: Path,
    core_map: dict[str, nx.Graph],
    shell_map: dict[str, nx.Graph],
) -> DualReceipt:
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != EXPECTED_DUAL_PAIRS + 1:
        fail(f"wrong dual line count: {len(lines)}")
    header = json.loads(lines[0])
    expected_header = {
        "schema": "erdos617-r9-m59-duals-v1",
        "core_count": EXPECTED_CORES,
        "shell_count": EXPECTED_SHELLS,
        "pair_count": EXPECTED_PAIRS,
        "certificate_count": EXPECTED_DUAL_PAIRS,
        "uncertified_pair_count": EXPECTED_REMAINING_PAIRS,
        "core_catalog_sha256": CATALOG.EXPECTED_CORE_CATALOG_SHA256,
        "shell_catalog_sha256": CATALOG.EXPECTED_SHELL_CATALOG_SHA256,
        "nonclaim": CATALOG.NONCLAIM,
    }
    if header != expected_header:
        fail(f"dual header mismatch: {header}")

    pairs = set()
    semantic_rows = []
    for line_number, line in enumerate(lines[1:], start=2):
        raw = json.loads(line)
        if not isinstance(raw, dict) or set(raw) != {"core", "shell", "weights"}:
            fail(f"dual record {line_number} has the wrong fields")
        core_name = exact_string(raw["core"], f"dual record {line_number} core")
        shell_name = exact_string(raw["shell"], f"dual record {line_number} shell")
        pair = (core_name, shell_name)
        if core_name not in core_map or shell_name not in shell_map:
            fail(f"dual record {line_number} names a graph outside the catalogs")
        if pair in pairs:
            fail(f"duplicate dual pair at line {line_number}")
        rows = inequalities(core_map[core_name], shell_map[shell_name])
        loads = [Fraction(0) for _ in range(VARIABLE_COUNT)]
        objective = Fraction(0)
        weights = parse_weights(raw["weights"])
        for row_index, weight in weights:
            if not 0 <= row_index < len(rows):
                fail(f"dual record {line_number} has an out-of-range row")
            row = rows[row_index]
            objective += row.right_side * weight
            for variable in row.variables:
                loads[variable] += weight
        if max(loads) > 1:
            fail(f"dual record {line_number} has a variable load above one")
        budget = shell_map[shell_name].number_of_edges() + GLOBAL_OFFSET
        if objective <= budget:
            fail(f"dual record {line_number} does not exceed the budget")
        margin = objective - budget
        semantic_rows.append(
            (
                core_name,
                shell_name,
                margin.numerator,
                margin.denominator,
                len(weights),
            )
        )
        pairs.add(pair)
    if len(pairs) != EXPECTED_DUAL_PAIRS:
        fail(f"wrong dual-pair count: {len(pairs)}")
    payload = "".join(
        f"{core}:{shell}:{numerator}/{denominator}:{support}\n"
        for core, shell, numerator, denominator, support in sorted(semantic_rows)
    ).encode("ascii")
    semantic_sha256 = hashlib.sha256(payload).hexdigest()
    if (
        EXPECTED_DUAL_SEMANTIC_SHA256
        and semantic_sha256 != EXPECTED_DUAL_SEMANTIC_SHA256
    ):
        fail(
            "dual semantic digest mismatch: "
            f"{semantic_sha256} != {EXPECTED_DUAL_SEMANTIC_SHA256}"
        )
    return DualReceipt(frozenset(pairs), semantic_sha256)


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
    if not 0 <= budget <= 6:
        fail("shell scalar budget is outside zero through six")
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


def bipartition_masks(core: nx.Graph) -> tuple[int, int]:
    if not nx.is_bipartite(core):
        fail("m=59 core is not bipartite")
    colours = nx.algorithms.bipartite.color(core)
    sides = tuple(
        sum(1 << int(vertex) for vertex, colour in colours.items() if colour == side)
        for side in (0, 1)
    )
    if tuple(sorted(mask.bit_count() for mask in sides)) != (8, 8):
        fail("m=59 core does not have an 8+8 bipartition")
    if sides[0] | sides[1] != FULL_CORE_MASK or sides[0] & sides[1]:
        fail("invalid core bipartition")
    adjacency = CATALOG.adjacency_masks(core)
    independent_eights = set()
    for vertices in itertools.combinations(range(CORE_ORDER), 8):
        mask = sum(1 << vertex for vertex in vertices)
        if CATALOG.independent(mask, adjacency):
            independent_eights.add(mask)
    if independent_eights != set(sides):
        fail("core does not have exactly its two sides as independent eight-sets")
    return sides[0], sides[1]


def two_vertex_edge_cover(shell: nx.Graph) -> tuple[int, int]:
    candidates = []
    for first, second in itertools.combinations(range(SHELL_ORDER), 2):
        if all(first in edge or second in edge for edge in shell.edges):
            candidates.append(
                (int(shell.degree(first)) + int(shell.degree(second)), first, second)
            )
    if not candidates:
        fail("remaining shell has no two-vertex edge cover")
    _, first, second = max(candidates)
    return first, second


COMBINATION_MASKS = tuple(
    tuple(
        sum(1 << vertex for vertex in vertices)
        for vertices in itertools.combinations(range(CORE_ORDER), size)
    )
    for size in range(CORE_ORDER + 1)
)


class P1CoreSearch:
    def __init__(self, core: nx.Graph):
        self.core = core
        self.side_masks = bipartition_masks(core)
        adjacency = CATALOG.adjacency_masks(core)
        self.is_cover = tuple(
            CATALOG.independent(FULL_CORE_MASK ^ mask, adjacency)
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
        first_hub, second_hub = two_vertex_edge_cover(shell)
        low_vertices = tuple(
            vertex
            for vertex in range(SHELL_ORDER)
            if vertex not in (first_hub, second_hub)
        )
        if any(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(low_vertices, 2)
        ):
            fail("chosen shell hubs do not cover every edge")

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


def audit_core(
    task: tuple[int, str, tuple[tuple[int, str], ...]],
) -> CoreReceipt:
    core_index, core_name, shell_entries = task
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    search = P1CoreSearch(core)
    states = []
    for shell_index, shell_name in shell_entries:
        shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
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
        fail(f"catalog mismatch: cores={len(cores)} shells={len(shells)}")
    core_map = {case.graph6.decode("ascii"): case.graph for case in cores}
    shell_map = {case.graph6.decode("ascii"): case.graph for case in shells}
    if len(core_map) != EXPECTED_CORES or len(shell_map) != EXPECTED_SHELLS:
        fail("graph6 catalog contains a duplicate")
    dual_receipt = verify_duals(args.duals, core_map, shell_map)

    tasks = []
    remaining_pairs = 0
    two_hub_pairs = 0
    for core_index, core_case in enumerate(cores):
        core_name = core_case.graph6.decode("ascii")
        entries = []
        for shell_index, shell_case in enumerate(shells):
            shell_name = shell_case.graph6.decode("ascii")
            if (core_name, shell_name) in dual_receipt.pairs:
                continue
            two_vertex_edge_cover(shell_case.graph)
            two_hub_pairs += 1
            entries.append((shell_index, shell_name))
            remaining_pairs += 1
        tasks.append((core_index, core_name, tuple(entries)))
    if remaining_pairs != EXPECTED_REMAINING_PAIRS:
        fail(f"wrong remaining-pair count: {remaining_pairs}")
    if two_hub_pairs != EXPECTED_TWO_HUB_PAIRS:
        fail(f"wrong two-hub-pair count: {two_hub_pairs}")

    if args.workers == 1:
        receipts = tuple(audit_core(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            receipts = tuple(pool.map(audit_core, tasks))
    receipts = tuple(sorted(receipts, key=lambda receipt: receipt.core_index))
    states = tuple(state for receipt in receipts for state in receipt.states)
    satisfiable = tuple(state for state in states if state.satisfiable)
    unsatisfiable = tuple(state for state in states if not state.satisfiable)
    if len(states) != EXPECTED_Q_STATES:
        fail(f"wrong q-state count: {len(states)}")
    if len(unsatisfiable) != EXPECTED_P1_UNSAT_STATES:
        fail(f"wrong p1-UNSAT state count: {len(unsatisfiable)}")
    if len(satisfiable) != EXPECTED_P1_SAT_STATES:
        fail(f"wrong p1-SAT state count: {len(satisfiable)}")

    hub_pairs = sum(state.hub_pairs for state in states)
    demand_states = sum(state.demand_states for state in states)
    if hub_pairs != EXPECTED_HUB_PAIRS_EXAMINED:
        fail(f"wrong hub-pair count: {hub_pairs}")
    if demand_states != EXPECTED_DEMAND_STATES_EXAMINED:
        fail(f"wrong demand-state count: {demand_states}")
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
        fail(
            "classification digest mismatch: "
            f"{classification_sha256} != {EXPECTED_CLASSIFICATION_SHA256}"
        )

    pair_state_profile = Counter(
        sum(
            state.core_index == core_index and state.shell_index == shell_index
            for state in states
        )
        for core_index, _, entries in tasks
        for shell_index, _ in entries
    )
    print(
        f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}"
    )
    print(
        f"strict_duals_semantically_verified={len(dual_receipt.pairs)} "
        f"uncertified_pairs={remaining_pairs}"
    )
    print(f"dual_semantic_sha256={dual_receipt.semantic_sha256}")
    print(f"two_hub_remainder_pairs={two_hub_pairs}")
    print(
        f"q_states={len(states)} p1_UNSAT={len(unsatisfiable)} "
        f"p1_SAT={len(satisfiable)}"
    )
    print(f"pair_q_state_profile={dict(sorted(pair_state_profile.items()))}")
    print(f"hub_pairs_examined={hub_pairs}")
    print(f"demand_states_examined={demand_states}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
