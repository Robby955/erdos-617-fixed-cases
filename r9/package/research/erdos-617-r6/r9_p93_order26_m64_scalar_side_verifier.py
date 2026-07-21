#!/usr/bin/env python3
"""Verify the exact scalar side-count reduction for the m=64 frontier."""

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
DUAL_PATH = HERE / "verify_r9_p93_order26_m64_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m64_duals.jsonl"
SHELL_ORDER = 9
GLOBAL_OFFSET = 19
EXPECTED_COMPLEMENT_PAIRS = 562
EXPECTED_DISTINCT_SHELLS = 562
EXPECTED_RAW_STATES = 101880
EXPECTED_FEASIBLE_STATES = 10639
EXPECTED_SMALL_COVERS = 511
EXPECTED_COMPLEMENT_SHA256 = (
    "96303541e4dfaf31fab4a61ebefea1390e2cc53f90b2b238e43eb5923638036e"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "c3f369569d4fa8cbc19dd8043e8445dfd723f068c85922e2420c5e270354afcc"
)
EXPECTED_FRONTIER_SHA256 = (
    "c7d527a52b042e6a900252254634b1ee573b1edf72e562312ec6e9b947b0ff92"
)
EXPECTED_PAIR_PROFILE: Counter[tuple[int, bool]] = Counter(
    {
        (2, True): 7,
        (3, False): 469,
        (3, True): 4,
        (4, False): 78,
        (5, False): 4,
    }
)


def load_dual_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("erdos617_m64_scalar_dual", DUAL_PATH)
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
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    if not 0 <= budget <= 11:
        raise AssertionError("m=64 shell budget lies outside zero through eleven")
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        rows = tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        if all(
            rows[int(first)] + rows[int(second)] >= 8
            for first, second in shell.edges
        ):
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


def bipartition(core: nx.Graph) -> tuple[tuple[int, ...], tuple[int, ...]]:
    if not nx.is_bipartite(core):
        raise AssertionError("m=64 core is not bipartite")
    colors = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(int(vertex) for vertex, color in colors.items() if color == side))
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("m=64 core does not have an 8+8 bipartition")
    return cast(tuple[tuple[int, ...], tuple[int, ...]], sides)


def side_demands(core: nx.Graph) -> tuple[int, int]:
    return cast(
        tuple[int, int],
        tuple(
            sum(max(0, int(core.degree(vertex)) - 6) for vertex in side)
            for side in bipartition(core)
        ),
    )


def verify_complete_bipartite_cover_lemma(core: nx.Graph) -> int:
    side_masks = tuple(sum(1 << vertex for vertex in side) for side in bipartition(core))
    edges = tuple((int(first), int(second)) for first, second in core.edges)
    covers = 0
    for mask in range(1 << core.number_of_nodes()):
        if not all(mask >> first & 1 or mask >> second & 1 for first, second in edges):
            continue
        covers += 1
        if not any(mask & side == side for side in side_masks):
            raise AssertionError("K8,8 has a vertex cover containing neither side")
    if covers != EXPECTED_SMALL_COVERS:
        raise AssertionError(f"wrong K8,8 vertex-cover count: {covers}")
    return covers


def feasible_side_counts(
    shell: nx.Graph,
    rows: tuple[int, ...],
    demand_x: int,
    demand_y: int,
) -> bool:
    """Test all necessary side-count conditions with exact integers."""

    shell_edges = tuple((int(first), int(second)) for first, second in shell.edges)
    shell_triangles = triangles(shell)
    domains = tuple(tuple(range(max(0, row - 7), min(7, row) + 1)) for row in rows)
    constraint_counts = tuple(
        sum(vertex in edge for edge in shell_edges)
        + 2 * sum(vertex in triple for triple in shell_triangles)
        for vertex in range(SHELL_ORDER)
    )
    order = tuple(
        sorted(
            range(SHELL_ORDER),
            key=lambda vertex: (-constraint_counts[vertex], len(domains[vertex])),
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
            for first, second in shell_edges:
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
    lines = tuple(line for line in path.read_text(encoding="ascii").splitlines() if line)
    if len(lines) != DUAL.EXPECTED_CERTIFICATES + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    DUAL.parse_header(json.loads(lines[0]))
    core_names = frozenset(case.graph6.decode("ascii") for case in cores)
    shell_names = frozenset(case.graph6.decode("ascii") for case in shells)
    result = set()
    for line in lines[1:]:
        record = json.loads(line)
        if not isinstance(record, dict) or set(record) != {"core", "shell", "weights"}:
            raise AssertionError("malformed dual record")
        DUAL.BASE.parse_weights(record["weights"])
        pair = record["core"], record["shell"]
        if pair[0] not in core_names or pair[1] not in shell_names:
            raise AssertionError("dual record lies outside the catalogs")
        if pair in result:
            raise AssertionError("duplicate dual pair")
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
    verify_complete_bipartite_cover_lemma(cores[0].graph)
    certified = certified_pairs(args.duals, cores, shells)
    complement = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii")) not in certified
    )
    if len(complement) != EXPECTED_COMPLEMENT_PAIRS:
        raise AssertionError(f"wrong complement count: {len(complement)}")
    complement_payload = "".join(
        f"{core_index}:{shell_index}\n" for core_index, shell_index in complement
    ).encode("ascii")
    complement_hash = hashlib.sha256(complement_payload).hexdigest()
    if complement_hash != EXPECTED_COMPLEMENT_SHA256:
        raise AssertionError("dual-complement digest mismatch")

    shell_states: dict[int, tuple[tuple[int, ...], ...]] = {}
    pair_profile: Counter[tuple[int, bool]] = Counter()
    classification_rows = []
    frontier_rows = []
    raw_total = 0
    feasible_total = 0
    survivor_rows = []
    for core_index, shell_index in complement:
        core = cores[core_index].graph
        shell = shells[shell_index].graph
        shell_states.setdefault(shell_index, row_size_states(shell))
        states = shell_states[shell_index]
        demand_x, demand_y = side_demands(core)
        feasible = tuple(
            rows
            for rows in states
            if feasible_side_counts(shell, rows, demand_x, demand_y)
        )
        tau = vertex_cover_number(shell)
        pair_profile[(tau, bool(feasible))] += 1
        raw_total += len(states)
        feasible_total += len(feasible)
        classification_rows.append(
            f"{core_index}:{shell_index}:{tau}:{len(states)}:{len(feasible)}\n"
        )
        for rows in feasible:
            frontier_rows.append(
                f"{core_index}:{shell_index}:{tau}:{','.join(map(str, rows))}\n"
            )
        if feasible:
            survivor_rows.append(
                (
                    shell_index,
                    shells[shell_index].graph6.decode("ascii"),
                    tau,
                    feasible,
                )
            )

    classification_hash = hashlib.sha256(
        "".join(classification_rows).encode("ascii")
    ).hexdigest()
    frontier_hash = hashlib.sha256("".join(frontier_rows).encode("ascii")).hexdigest()
    if len(shell_states) != EXPECTED_DISTINCT_SHELLS:
        raise AssertionError(f"wrong distinct shell count: {len(shell_states)}")
    if raw_total != EXPECTED_RAW_STATES or feasible_total != EXPECTED_FEASIBLE_STATES:
        raise AssertionError(f"wrong state totals: {raw_total}, {feasible_total}")
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"wrong pair profile: {pair_profile}")
    if not args.allow_unpinned:
        if classification_hash != EXPECTED_CLASSIFICATION_SHA256:
            raise AssertionError(f"classification digest mismatch: {classification_hash}")
        if frontier_hash != EXPECTED_FRONTIER_SHA256:
            raise AssertionError(f"frontier digest mismatch: {frontier_hash}")

    print(f"complement_pairs={len(complement)} complement_sha256={complement_hash}")
    print(f"pair_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_hash}")
    print(f"frontier_sha256={frontier_hash}")
    print(f"raw_q_states={raw_total} scalar_feasible_q_states={feasible_total}")
    for shell_index, shell_name, tau, feasible in survivor_rows:
        print(
            f"survivor={shell_index}:{shell_name}:tau={tau}:states={len(feasible)}"
        )
        if tau == 3:
            for rows in feasible:
                print(f"tau3_state={shell_index}:{','.join(map(str, rows))}")
    print("status=PASS")


if __name__ == "__main__":
    main()
