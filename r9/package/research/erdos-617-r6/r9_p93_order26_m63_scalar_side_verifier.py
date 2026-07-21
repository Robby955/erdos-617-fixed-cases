#!/usr/bin/env python3
"""Verify the integer side-count reduction for the m=63 complement.

The checker enumerates every row-size state with exact integer arithmetic.
It also compares the old cover-at-most-12 condition with the m=63
cover-at-most-13 lemma, recording the four states removed by the stronger
condition.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from typing import Any, Iterator, cast

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
DUAL_PATH = HERE / "verify_r9_p93_order26_m63_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m63_duals.jsonl"
SHELL_ORDER = 9
GLOBAL_OFFSET = 18
EXPECTED_COMPLEMENT_PAIRS = 334
EXPECTED_DISTINCT_SHELLS = 334
EXPECTED_RAW_STATES = 44504
EXPECTED_FEASIBLE_STATES = 10715
EXPECTED_COVER13_REMOVED_STATES = 4
EXPECTED_COVERS_THROUGH_13 = 438
EXPECTED_MINIMUM_MIXED_COVER = 14
EXPECTED_COMPLEMENT_SHA256 = (
    "f0e775bc61c40d56c54e221f6f47d216939671c6ac2d65c62eace6fa480ebd2b"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "675f090f8a175d22e327186c69f578dbeda7fba113ec0e644465a0a4f1260b20"
)
EXPECTED_REMOVED_SHA256 = (
    "41e6c2ac2d22f6dfe43a28458091b39d3bac7991a76d93c9e31d73aa71dc9127"
)
EXPECTED_PAIR_PROFILE: Counter[tuple[int, bool]] = Counter(
    {(2, True): 13, (3, False): 308, (4, False): 13}
)


def load_dual_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("m63_scalar_dual", DUAL_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {DUAL_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_dual_verifier()


def weak_compositions_at_most(
    budget: int, length: int, prefix: tuple[int, ...] = ()
) -> Iterator[tuple[int, ...]]:
    if length == 0:
        yield prefix
        return
    for value in range(budget + 1):
        yield from weak_compositions_at_most(
            budget - value, length - 1, prefix + (value,)
        )


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    if not 0 <= budget <= 6:
        raise AssertionError("m=63 shell budget lies outside zero through six")
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        rows = tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        if all(rows[int(first)] + rows[int(second)] >= 8 for first, second in shell.edges):
            states.add(rows)
    return tuple(sorted(states))


def triangles(shell: nx.Graph) -> tuple[tuple[int, int, int], ...]:
    return tuple(
        triple
        for triple in itertools.combinations(range(SHELL_ORDER), 3)
        if all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(triple, 2)
        )
    )


def side_demands(core: nx.Graph) -> tuple[int, int]:
    colors = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(int(vertex) for vertex, color in colors.items() if color == side)
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("core does not have an 8+8 bipartition")
    return cast(
        tuple[int, int],
        tuple(
            sum(max(0, int(core.degree(vertex)) - 6) for vertex in side)
            for side in sides
        ),
    )


def verify_cover13_lemma(core: nx.Graph) -> tuple[int, int]:
    """Exhaustively check the small-cover lemma on the unique core.

    A cover of ``K_8,8`` minus one edge that omits a vertex on each side
    has size at least fourteen.  This direct replay checks every vertex
    subset, rather than relying on the scalar search to encode the lemma.
    """

    colors = nx.algorithms.bipartite.color(core)
    sides = tuple(
        sum(1 << int(vertex) for vertex, color in colors.items() if color == side)
        for side in (0, 1)
    )
    if tuple(sorted(mask.bit_count() for mask in sides)) != (8, 8):
        raise AssertionError("cover-13 core does not have an 8+8 bipartition")
    edges = tuple((int(first), int(second)) for first, second in core.edges)
    covers_through_13 = 0
    mixed_sizes = []
    for mask in range(1 << core.number_of_nodes()):
        if not all(mask >> first & 1 or mask >> second & 1 for first, second in edges):
            continue
        contains_side = any(mask & side == side for side in sides)
        if mask.bit_count() <= 13:
            covers_through_13 += 1
            if not contains_side:
                raise AssertionError("mixed core cover has size at most thirteen")
        elif not contains_side:
            mixed_sizes.append(mask.bit_count())
    minimum_mixed = min(mixed_sizes)
    if covers_through_13 != EXPECTED_COVERS_THROUGH_13:
        raise AssertionError(f"wrong small-cover count: {covers_through_13}")
    if minimum_mixed != EXPECTED_MINIMUM_MIXED_COVER:
        raise AssertionError(f"wrong minimum mixed-cover size: {minimum_mixed}")
    return covers_through_13, minimum_mixed


def feasible_side_counts(
    shell: nx.Graph,
    rows: tuple[int, ...],
    demand_x: int,
    demand_y: int,
    cover_limit: int = 13,
) -> bool:
    """Test the exact necessary side-count conditions.

    A vertex cover of K_8,8 minus one edge with at most thirteen vertices
    contains one complete bipartition side.  This gives the disjunction on
    each shell edge whose two row sizes sum to at most ``cover_limit``.
    """

    small_edges = tuple(
        (int(first), int(second))
        for first, second in shell.edges
        if rows[int(first)] + rows[int(second)] <= cover_limit
    )
    shell_triangles = triangles(shell)
    domains = tuple(tuple(range(max(0, row - 7), min(7, row) + 1)) for row in rows)
    incident_constraints = tuple(
        sum(vertex in edge for edge in small_edges)
        + 2 * sum(vertex in triple for triple in shell_triangles)
        for vertex in range(SHELL_ORDER)
    )
    order = tuple(
        sorted(
            range(SHELL_ORDER),
            key=lambda vertex: (-incident_constraints[vertex], len(domains[vertex])),
        )
    )
    position = {vertex: index for index, vertex in enumerate(order)}
    values: list[int | None] = [None] * SHELL_ORDER

    def search(index: int, sum_x: int, sum_y: int) -> bool:
        if index == SHELL_ORDER:
            return sum_x >= demand_x and sum_y >= demand_y
        remaining = order[index:]
        if sum_x + sum(max(domains[vertex]) for vertex in remaining) < demand_x:
            return False
        if sum_y + sum(rows[vertex] - min(domains[vertex]) for vertex in remaining) < demand_y:
            return False

        vertex = order[index]
        for x_value in domains[vertex]:
            values[vertex] = x_value
            y_value = rows[vertex] - x_value
            valid = True
            for first, second in small_edges:
                other = second if first == vertex else first if second == vertex else None
                if other is None or position[other] >= index:
                    continue
                other_x = values[other]
                if other_x is None:
                    raise AssertionError("assigned-order invariant failed")
                if x_value + other_x < 8 and y_value + rows[other] - other_x < 8:
                    valid = False
                    break
            if not valid:
                values[vertex] = None
                continue
            for triple in shell_triangles:
                if vertex not in triple:
                    continue
                if any(position[other] >= index for other in triple if other != vertex):
                    continue
                assigned = tuple(
                    x_value if other == vertex else values[other] for other in triple
                )
                if any(value is None for value in assigned):
                    raise AssertionError("triangle assignment invariant failed")
                triple_x = sum(cast(int, value) for value in assigned)
                triple_y = sum(rows[other] for other in triple) - triple_x
                if triple_x < 8 or triple_y < 8:
                    valid = False
                    break
            if valid and search(index + 1, sum_x + x_value, sum_y + y_value):
                values[vertex] = None
                return True
            values[vertex] = None
        return False

    return search(0, 0, 0)


def vertex_cover_number(graph: nx.Graph) -> int:
    edges = tuple((int(first), int(second)) for first, second in graph.edges)
    for size in range(SHELL_ORDER + 1):
        if any(
            all(first in cover or second in cover for first, second in edges)
            for cover in itertools.combinations(range(SHELL_ORDER), size)
        ):
            return size
    raise AssertionError("shell has no vertex cover")


def certified_pairs(
    path: Path, cores: tuple[Any, ...], shells: tuple[Any, ...]
) -> frozenset[tuple[str, str]]:
    data_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    if data_hash != DUAL.EXPECTED_DATA_SHA256:
        raise AssertionError(f"dual data digest mismatch: {data_hash}")
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != DUAL.EXPECTED_CERTIFICATES + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    DUAL.parse_header(json.loads(lines[0]))
    core_names = frozenset(case.graph6.decode("ascii") for case in cores)
    shell_names = frozenset(case.graph6.decode("ascii") for case in shells)
    result = set()
    for line_number, line in enumerate(lines[1:], start=2):
        record = json.loads(line)
        if not isinstance(record, dict) or set(record) != {"core", "shell", "weights"}:
            raise AssertionError(f"bad dual record at line {line_number}")
        core_name = record["core"]
        shell_name = record["shell"]
        if core_name not in core_names or shell_name not in shell_names:
            raise AssertionError(f"dual pair outside catalogs at line {line_number}")
        DUAL.parse_weights(record["weights"])
        pair = core_name, shell_name
        if pair in result:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        result.add(pair)
    return frozenset(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    if len(cores) != DUAL.EXPECTED_CORES or len(shells) != DUAL.EXPECTED_SHELLS:
        raise AssertionError("catalog count mismatch")
    if DUAL.catalog_sha256(cores) != DUAL.EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if DUAL.catalog_sha256(shells) != DUAL.EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")
    cover_counts = Counter(verify_cover13_lemma(case.graph) for case in cores)
    if cover_counts != Counter(
        {(EXPECTED_COVERS_THROUGH_13, EXPECTED_MINIMUM_MIXED_COVER): 1}
    ):
        raise AssertionError(f"wrong cover-13 core profile: {cover_counts}")
    certified = certified_pairs(args.duals, cores, shells)
    complement = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii")) not in certified
    )
    if len(complement) != EXPECTED_COMPLEMENT_PAIRS:
        raise AssertionError(f"wrong complement count: {len(complement)}")
    payload = "".join(f"{first}:{second}\n" for first, second in complement).encode("ascii")
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED_COMPLEMENT_SHA256:
        raise AssertionError("dual-complement digest mismatch")

    shell_states: dict[int, tuple[tuple[int, ...], ...]] = {}
    rows = []
    removed_rows = []
    pair_profile: Counter[tuple[int, bool]] = Counter()
    raw_total = 0
    feasible_total = 0
    for core_index, shell_index in complement:
        core = cores[core_index].graph
        shell = shells[shell_index].graph
        if shell_index not in shell_states:
            shell_states[shell_index] = row_size_states(shell)
        states = shell_states[shell_index]
        demands = side_demands(core)
        feasible12 = tuple(
            state
            for state in states
            if feasible_side_counts(shell, state, demands[0], demands[1], 12)
        )
        feasible13 = tuple(
            state
            for state in states
            if feasible_side_counts(shell, state, demands[0], demands[1], 13)
        )
        if not set(feasible13).issubset(feasible12):
            raise AssertionError("cover-13 survivors are not a subset of cover-12 survivors")
        tau = vertex_cover_number(shell)
        for state in sorted(set(feasible12) - set(feasible13)):
            removed_rows.append(
                f"{core_index}:{shell_index}:{tau}:{','.join(map(str, state))}\n"
            )
        pair_profile[(tau, bool(feasible13))] += 1
        raw_total += len(states)
        feasible_total += len(feasible13)
        rows.append(
            f"{core_index}:{shell_index}:{tau}:{len(states)}:{len(feasible13)}\n"
        )

    classification_digest = hashlib.sha256("".join(rows).encode("ascii")).hexdigest()
    removed_digest = hashlib.sha256("".join(removed_rows).encode("ascii")).hexdigest()
    if len(shell_states) != EXPECTED_DISTINCT_SHELLS:
        raise AssertionError(f"wrong distinct shell count: {len(shell_states)}")
    if raw_total != EXPECTED_RAW_STATES:
        raise AssertionError(f"wrong raw state count: {raw_total}")
    if feasible_total != EXPECTED_FEASIBLE_STATES:
        raise AssertionError(f"wrong feasible state count: {feasible_total}")
    if len(removed_rows) != EXPECTED_COVER13_REMOVED_STATES:
        raise AssertionError(f"wrong cover-13 removal count: {len(removed_rows)}")
    if EXPECTED_PAIR_PROFILE:
        if pair_profile != EXPECTED_PAIR_PROFILE:
            raise AssertionError(f"wrong pair profile: {pair_profile}")
    elif not args.allow_unpinned:
        raise AssertionError("pair profile is not pinned")
    if EXPECTED_CLASSIFICATION_SHA256:
        if classification_digest != EXPECTED_CLASSIFICATION_SHA256:
            raise AssertionError(f"classification digest mismatch: {classification_digest}")
    elif not args.allow_unpinned:
        raise AssertionError("classification digest is not pinned")
    if EXPECTED_REMOVED_SHA256:
        if removed_digest != EXPECTED_REMOVED_SHA256:
            raise AssertionError(f"removed-state digest mismatch: {removed_digest}")
    elif not args.allow_unpinned:
        raise AssertionError("removed-state digest is not pinned")

    print(f"complement_pairs={len(complement)} complement_sha256={digest}")
    print(f"cover13_core_profile={dict(cover_counts)}")
    print(f"distinct_shells={len(shell_states)}")
    print(f"pair_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_digest}")
    print(f"cover13_removed_states={len(removed_rows)} removed_sha256={removed_digest}")
    for row in removed_rows:
        print(f"removed={row.strip()}")
    print(f"raw_q_states={raw_total} scalar_feasible_q_states={feasible_total}")
    print("status=PASS")


if __name__ == "__main__":
    main()
