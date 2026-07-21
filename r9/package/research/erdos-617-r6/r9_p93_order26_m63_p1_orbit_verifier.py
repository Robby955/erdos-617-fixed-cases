#!/usr/bin/env python3
"""Verify the m=63 two-hub remainder modulo S_7 x S_7.

The unique core is K_8,8 with one edge removed.  The missing-edge endpoints
are fixed, while the other seven vertices on each side are freely permuted.
An ordered pair of hub rows is represented by the two endpoint membership
codes and one four-bin membership histogram on each regular class.  These
data are complete orbit invariants for the stated group.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import math
from pathlib import Path
import sys
from typing import Any, Iterator

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
BASE_PATH = HERE / "r9_p93_order26_m62_p1_orbit_verifier.py"
SCALAR_PATH = HERE / "r9_p93_order26_m63_scalar_side_verifier.py"
DUAL_DATA = HERE / "r9_p93_order26_m63_duals.jsonl"
CORE_ORDER = 16
GLOBAL_OFFSET = 18
EXPECTED_COMPLEMENT_PAIRS = 334
EXPECTED_PAIRS = 13
EXPECTED_STATES = 10715
EXPECTED_ORBIT_REPRESENTATIVES = 40203600
CORE_NAME = "O????B}~v}^w~o~o^wF}?"
EXPECTED_SUBGROUP_ORDER = math.factorial(7) ** 2
# Filled from deterministic replays and then pinned.
EXPECTED_COMPLEMENT_BUDGET_PROFILE: Counter[int] = Counter(
    {0: 9, 1: 17, 2: 36, 3: 63, 4: 92, 5: 111, 6: 6}
)
EXPECTED_TASK_BUDGET_PROFILE: Counter[int] = Counter({3: 1, 4: 2, 5: 4, 6: 6})
EXPECTED_PAIR_PROFILE: Counter[int] = Counter(
    {220: 1, 449: 1, 456: 1, 477: 2, 640: 2, 699: 2, 1233: 2, 1746: 2}
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "05b98ab8efd125a447a92e1e5d63b0531430dd3a715449c363c0f87cfb7660e0"
)
EXPECTED_CANDIDATE_ORBITS = 2658674
EXPECTED_DEMAND_STATES = 363118868
EXPECTED_DEMAND_TRANSITIONS = 362801242
EXPECTED_ORBIT_RECEIPT_SHA256 = (
    "16ce28c3f5ca0e2c1930aa9def97adcefbdac65339420cd0295209a092be7a35"
)
EXPECTED_TOTAL_ORBITS = 201601
EXPECTED_FIXED_ORBITS = {(7, 8): 3880, (8, 8): 4060}
EXPECTED_PROFILE_SHA256 = (
    "1dc0a1229bee184d2facb4ee0f24e1bb593595a539a6dcca23c83de6d9685908"
)
EXPECTED_SELF_TEST_REPRESENTATIVES = 201601
EXPECTED_SELF_TEST_RECEIPT_SHA256 = (
    "92c6fef2b543fe40e919e38016e4698181c5a495338d1f101f62afbd9af6c45d"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_module("erdos617_m63_orbit_base", BASE_PATH)
SCALAR = load_module("erdos617_m63_orbit_scalar", SCALAR_PATH)
BASE.SCALAR = SCALAR
BASE.QSTATE.GLOBAL_OFFSET = GLOBAL_OFFSET
HubPairRepresentative = BASE.HubPairRepresentative


@dataclass(frozen=True)
class OrbitModel:
    core_name: str
    side_x: tuple[int, ...]
    side_y: tuple[int, ...]
    endpoint_x: int
    endpoint_y: int
    regular_x: tuple[int, ...]
    regular_y: tuple[int, ...]
    generators: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class StateReceipt:
    core_index: int
    shell_index: int
    row_sizes: tuple[int, ...]
    satisfiable: bool
    orbit_representatives: int
    candidate_orbits: int
    demand_states: int
    demand_transitions: int


def adjacent_transpositions(vertices: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
    for first, second in itertools.pairwise(vertices):
        permutation = list(range(CORE_ORDER))
        permutation[first], permutation[second] = second, first
        yield tuple(permutation)


@lru_cache(maxsize=1)
def build_orbit_model(core_name: str) -> OrbitModel:
    if core_name != CORE_NAME:
        raise AssertionError(f"unexpected m=63 core: {core_name}")
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    side_x, side_y = tuple(
        sorted(
            (tuple(sorted(side)) for side in BASE.QSTATE.bipartition(core)),
            key=lambda side: side,
        )
    )
    missing = tuple(
        (first, second)
        for first in side_x
        for second in side_y
        if not core.has_edge(first, second)
    )
    if len(missing) != 1 or core.number_of_edges() != 63:
        raise AssertionError("core is not K8,8 minus one edge")
    endpoint_x, endpoint_y = missing[0]
    regular_x = tuple(vertex for vertex in side_x if vertex != endpoint_x)
    regular_y = tuple(vertex for vertex in side_y if vertex != endpoint_y)
    if tuple(map(len, (regular_x, regular_y))) != (7, 7):
        raise AssertionError("regular classes do not have size seven")
    generators = tuple(
        itertools.chain(
            adjacent_transpositions(regular_x), adjacent_transpositions(regular_y)
        )
    )
    model = OrbitModel(
        core_name,
        side_x,
        side_y,
        endpoint_x,
        endpoint_y,
        regular_x,
        regular_y,
        generators,
    )
    validate_subgroup(model, core)
    return model


def side_mask(side: tuple[int, ...]) -> int:
    return sum(1 << vertex for vertex in side)


def p1_allowed(model: OrbitModel, first: int, second: int) -> bool:
    return all(
        row & side_mask(side) != side_mask(side)
        for row in (first, second)
        for side in (model.side_x, model.side_y)
    )


def membership_code(first: int, second: int, vertex: int) -> int:
    return 2 * ((first >> vertex) & 1) + ((second >> vertex) & 1)


def class_histogram(
    vertices: tuple[int, ...], first: int, second: int
) -> tuple[int, int, int, int]:
    counts = Counter(membership_code(first, second, vertex) for vertex in vertices)
    return tuple(counts[code] for code in range(4))  # type: ignore[return-value]


def orbit_signature(model: OrbitModel, first: int, second: int) -> tuple[Any, ...]:
    return (
        membership_code(first, second, model.endpoint_x),
        membership_code(first, second, model.endpoint_y),
        class_histogram(model.regular_x, first, second),
        class_histogram(model.regular_y, first, second),
    )


def validate_subgroup(model: OrbitModel, core: nx.Graph) -> None:
    vertices = frozenset(range(CORE_ORDER))
    sides = (frozenset(model.side_x), frozenset(model.side_y))
    edges = frozenset(frozenset((int(first), int(second))) for first, second in core.edges)
    demands = tuple(max(0, int(core.degree(vertex)) - 6) for vertex in range(CORE_ORDER))
    for permutation in model.generators:
        if frozenset(permutation) != vertices:
            raise AssertionError("subgroup generator is not a permutation")
        if permutation[model.endpoint_x] != model.endpoint_x or permutation[model.endpoint_y] != model.endpoint_y:
            raise AssertionError("subgroup generator moves a missing-edge endpoint")
        if any(frozenset(permutation[v] for v in side) != side for side in sides):
            raise AssertionError("subgroup generator does not preserve the core sides")
        transported = frozenset(
            frozenset((permutation[first], permutation[second]))
            for first, second in core.edges
        )
        if transported != edges:
            raise AssertionError("subgroup generator is not a core automorphism")
        if any(demands[permutation[v]] != demands[v] for v in vertices):
            raise AssertionError("subgroup generator does not preserve demands")
    if math.factorial(len(model.regular_x)) * math.factorial(len(model.regular_y)) != EXPECTED_SUBGROUP_ORDER:
        raise AssertionError("subgroup order formula mismatch")


def apply_code(first: int, second: int, vertex: int, code: int) -> tuple[int, int]:
    if code & 2:
        first |= 1 << vertex
    if code & 1:
        second |= 1 << vertex
    return first, second


@lru_cache(maxsize=32)
def combined_pattern_index(
    first_class: tuple[int, ...], second_class: tuple[int, ...]
) -> dict[tuple[int, int], tuple[tuple[Any, Any], ...]]:
    index: dict[tuple[int, int], list[tuple[Any, Any]]] = defaultdict(list)
    for first_pattern in BASE.class_patterns(first_class):
        for second_pattern in BASE.class_patterns(second_class):
            key = (
                first_pattern.first_count + second_pattern.first_count,
                first_pattern.second_count + second_pattern.second_count,
            )
            index[key].append((first_pattern, second_pattern))
    return {key: tuple(value) for key, value in index.items()}


@lru_cache(maxsize=225)
def hub_pair_representatives(
    core_name: str, first_size: int, second_size: int
) -> tuple[Any, ...]:
    if not 0 <= first_size <= 14 or not 0 <= second_size <= 14:
        return ()
    model = build_orbit_model(core_name)
    result = []
    pattern_index = combined_pattern_index(model.regular_x, model.regular_y)
    for endpoint_x_code in range(4):
        for endpoint_y_code in range(4):
            first = 0
            second = 0
            first, second = apply_code(
                first, second, model.endpoint_x, endpoint_x_code
            )
            first, second = apply_code(
                first, second, model.endpoint_y, endpoint_y_code
            )
            fixed_first = int(bool(endpoint_x_code & 2)) + int(bool(endpoint_y_code & 2))
            fixed_second = int(bool(endpoint_x_code & 1)) + int(bool(endpoint_y_code & 1))
            needed = first_size - fixed_first, second_size - fixed_second
            for x_pattern, y_pattern in pattern_index.get(needed, ()):
                row_first = first | x_pattern.first_mask | y_pattern.first_mask
                row_second = second | x_pattern.second_mask | y_pattern.second_mask
                if not p1_allowed(model, row_first, row_second):
                    continue
                signature = (
                    endpoint_x_code,
                    endpoint_y_code,
                    x_pattern.histogram,
                    y_pattern.histogram,
                )
                result.append(HubPairRepresentative(row_first, row_second, signature))
    if any(
        rep.first_row.bit_count() != first_size
        or rep.second_row.bit_count() != second_size
        or orbit_signature(model, rep.first_row, rep.second_row) != rep.signature
        for rep in result
    ):
        raise AssertionError("direct orbit representative invariant failed")
    if len({rep.signature for rep in result}) != len(result):
        raise AssertionError("duplicate orbit signature")
    return tuple(result)


def formula_profile(model: OrbitModel) -> Counter[tuple[int, int]]:
    profile: Counter[tuple[int, int]] = Counter()
    for endpoint_x_code in range(4):
        for endpoint_y_code in range(4):
            fixed_first = int(bool(endpoint_x_code & 2)) + int(bool(endpoint_y_code & 2))
            fixed_second = int(bool(endpoint_x_code & 1)) + int(bool(endpoint_y_code & 1))
            for x_histogram in BASE.histograms(7):
                x_first = x_histogram[2] + x_histogram[3]
                x_second = x_histogram[1] + x_histogram[3]
                side_x_first = int(bool(endpoint_x_code & 2)) + x_first
                side_x_second = int(bool(endpoint_x_code & 1)) + x_second
                if side_x_first == 8 or side_x_second == 8:
                    continue
                for y_histogram in BASE.histograms(7):
                    y_first = y_histogram[2] + y_histogram[3]
                    y_second = y_histogram[1] + y_histogram[3]
                    side_y_first = int(bool(endpoint_y_code & 2)) + y_first
                    side_y_second = int(bool(endpoint_y_code & 1)) + y_second
                    if side_y_first == 8 or side_y_second == 8:
                        continue
                    profile[(fixed_first + x_first + y_first, fixed_second + x_second + y_second)] += 1
    return profile


def profile_sha256(profile: Counter[tuple[int, int]]) -> str:
    payload = "".join(
        f"{first}:{second}:{profile[(first, second)]}\n"
        for first in range(15)
        for second in range(15)
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    while mask:
        bit = mask & -mask
        vertex = bit.bit_length() - 1
        result |= 1 << permutation[vertex]
        mask ^= bit
    return result


def run_self_test(allow_unpinned: bool) -> None:
    model = build_orbit_model(CORE_NAME)
    core = nx.from_graph6_bytes(CORE_NAME.encode("ascii"))
    profile = formula_profile(model)
    total = sum(profile.values())
    digest = profile_sha256(profile)
    representatives_checked = 0
    for first_size in range(15):
        for second_size in range(15):
            representatives = hub_pair_representatives(CORE_NAME, first_size, second_size)
            if len(representatives) != profile[(first_size, second_size)]:
                raise AssertionError(f"orbit profile mismatch at {(first_size, second_size)}")
            representatives_checked += len(representatives)
    sample_sizes = ((0, 0), (7, 8), (8, 8), (14, 14))
    transport_checks = 0
    core_search = BASE.QSTATE.P1CoreSearch(core)
    for sizes in sample_sizes:
        representatives = hub_pair_representatives(CORE_NAME, *sizes)
        for representative in representatives:
            for permutation in model.generators:
                first = permute_mask(representative.first_row, permutation)
                second = permute_mask(representative.second_row, permutation)
                if orbit_signature(model, first, second) != representative.signature:
                    raise AssertionError("orbit signature is not transport invariant")
                if core_search.p1_allowed(first) != core_search.p1_allowed(
                    representative.first_row
                ):
                    raise AssertionError("row admissibility is not transport invariant")
                transport_checks += 1
    rows = (
        f"{CORE_NAME}:S7xS7:{EXPECTED_SUBGROUP_ORDER}:{total}:"
        f"{profile[(7, 8)]}:{profile[(8, 8)]}:{digest}\n"
        f"representatives_checked={representatives_checked}:transport_checks={transport_checks}\n"
    )
    receipt = hashlib.sha256(rows.encode("ascii")).hexdigest()
    if not allow_unpinned:
        if total != EXPECTED_TOTAL_ORBITS:
            raise AssertionError(f"total orbit mismatch: {total}")
        if any(profile[sizes] != expected for sizes, expected in EXPECTED_FIXED_ORBITS.items()):
            raise AssertionError("fixed orbit profile mismatch")
        if digest != EXPECTED_PROFILE_SHA256:
            raise AssertionError(f"profile digest mismatch: {digest}")
        if representatives_checked != EXPECTED_SELF_TEST_REPRESENTATIVES:
            raise AssertionError("representative total mismatch")
        if receipt != EXPECTED_SELF_TEST_RECEIPT_SHA256:
            raise AssertionError(f"self-test receipt mismatch: {receipt}")
    print(f"core={CORE_NAME} subgroup=S7xS7 subgroup_order={EXPECTED_SUBGROUP_ORDER}")
    print(f"total_ordered_p1_orbits={total} orbits_7_8={profile[(7, 8)]} orbits_8_8={profile[(8, 8)]}")
    print(f"profile_sha256={digest}")
    print(f"direct_profile_size_comparisons=225 representatives_checked={representatives_checked}")
    print(f"transport_checks={transport_checks}")
    print(f"self_test_receipt_sha256={receipt}")
    print("status=PASS")


BASE.build_orbit_model = build_orbit_model
BASE.hub_pair_representatives = hub_pair_representatives


def scalar_budget(shell: nx.Graph) -> int:
    return GLOBAL_OFFSET - int(shell.number_of_edges())


def build_frontier(geng: Path, duals: Path) -> tuple[Any, ...]:
    cores = SCALAR.DUAL.generate_cores(geng)
    shells = SCALAR.DUAL.generate_shells(geng)
    certified = SCALAR.certified_pairs(duals, cores, shells)
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
    if hashlib.sha256(complement_payload).hexdigest() != SCALAR.EXPECTED_COMPLEMENT_SHA256:
        raise AssertionError("dual complement digest mismatch")

    shell_states: dict[int, tuple[tuple[int, ...], ...]] = {}
    tasks = []
    scalar_rows = []
    pair_profile: Counter[tuple[int, bool]] = Counter()
    raw_states = 0
    feasible_states = 0
    for core_index, shell_index in complement:
        core = cores[core_index].graph
        shell = shells[shell_index].graph
        if shell_index not in shell_states:
            shell_states[shell_index] = SCALAR.row_size_states(shell)
        states = shell_states[shell_index]
        demand_x, demand_y = SCALAR.side_demands(core)
        feasible = tuple(
            rows
            for rows in states
            if SCALAR.feasible_side_counts(shell, rows, demand_x, demand_y, 13)
        )
        tau = SCALAR.vertex_cover_number(shell)
        pair_profile[(tau, bool(feasible))] += 1
        raw_states += len(states)
        feasible_states += len(feasible)
        scalar_rows.append(
            f"{core_index}:{shell_index}:{tau}:{len(states)}:{len(feasible)}\n"
        )
        if feasible:
            tasks.append(
                (
                    core_index,
                    shell_index,
                    cores[core_index].graph6.decode("ascii"),
                    shells[shell_index].graph6.decode("ascii"),
                    feasible,
                )
            )
    if pair_profile != SCALAR.EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"scalar pair profile mismatch: {pair_profile}")
    if raw_states != SCALAR.EXPECTED_RAW_STATES or feasible_states != EXPECTED_STATES:
        raise AssertionError(f"scalar state totals mismatch: {raw_states}, {feasible_states}")
    scalar_digest = hashlib.sha256("".join(scalar_rows).encode("ascii")).hexdigest()
    if scalar_digest != SCALAR.EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"scalar classification digest mismatch: {scalar_digest}")
    if len(tasks) != EXPECTED_PAIRS:
        raise AssertionError(f"wrong task count: {len(tasks)}")
    if any(SCALAR.vertex_cover_number(shells[task[1]].graph) != 2 for task in tasks):
        raise AssertionError("scalar survivor without a two-vertex shell cover")
    complement_budget_profile = Counter(
        scalar_budget(shells[shell_index].graph) for _, shell_index in complement
    )
    task_budget_profile = Counter(scalar_budget(shells[task[1]].graph) for task in tasks)
    return cores, shells, tuple(tasks), complement_budget_profile, task_budget_profile


def audit_task(task: tuple[Any, ...]) -> tuple[StateReceipt, ...]:
    core_index, shell_index, core_name, shell_name, row_states = task
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    search = BASE.OrbitP1CoreSearch(core_name)
    return tuple(
        StateReceipt(
            core_index,
            shell_index,
            row_sizes,
            receipt.satisfiable,
            receipt.orbit_representatives,
            receipt.candidate_orbits,
            receipt.demand_states,
            receipt.demand_transitions,
        )
        for row_sizes in row_states
        for receipt in (search.solve(shell, row_sizes),)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--frontier-only", action="store_true")
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")
    if args.self_test:
        run_self_test(args.allow_unpinned)
        return
    if args.geng is None:
        parser.error("--geng is required unless --self-test is used")

    _, _, tasks, complement_budget_profile, task_budget_profile = build_frontier(
        args.geng, args.duals
    )
    print(f"two_hub_pairs={len(tasks)} scalar_feasible_states={sum(len(task[4]) for task in tasks)}")
    print(f"complement_budget_profile={dict(sorted(complement_budget_profile.items()))}")
    print(f"task_budget_profile={dict(sorted(task_budget_profile.items()))}")
    if args.frontier_only:
        print("status=PASS")
        return

    if args.workers == 1:
        nested = tuple(audit_task(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            nested = tuple(pool.map(audit_task, tasks))
    states = tuple(state for group in nested for state in group)
    if len(states) != EXPECTED_STATES:
        raise AssertionError(f"wrong state count: {len(states)}")
    satisfiable = tuple(state for state in states if state.satisfiable)
    if satisfiable:
        raise AssertionError(f"unexpected orbit-SAT states: {len(satisfiable)}")
    classification = "".join(
        f"{state.core_index}:{state.shell_index}:{','.join(map(str, state.row_sizes))}:{int(state.satisfiable)}\n"
        for state in sorted(states, key=lambda item: (item.core_index, item.shell_index, item.row_sizes))
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    receipt_payload = "".join(
        f"{state.core_index}:{state.shell_index}:{','.join(map(str, state.row_sizes))}:"
        f"{state.orbit_representatives}:{state.candidate_orbits}:"
        f"{state.demand_states}:{state.demand_transitions}\n"
        for state in sorted(states, key=lambda item: (item.core_index, item.shell_index, item.row_sizes))
    ).encode("ascii")
    pair_profile = Counter(len(group) for group in nested)
    orbit_representatives = sum(state.orbit_representatives for state in states)
    candidate_orbits = sum(state.candidate_orbits for state in states)
    demand_states = sum(state.demand_states for state in states)
    demand_transitions = sum(state.demand_transitions for state in states)
    orbit_receipt_sha256 = hashlib.sha256(receipt_payload).hexdigest()
    if orbit_representatives != EXPECTED_ORBIT_REPRESENTATIVES:
        raise AssertionError(f"orbit representative mismatch: {orbit_representatives}")
    if not args.allow_unpinned:
        if complement_budget_profile != EXPECTED_COMPLEMENT_BUDGET_PROFILE:
            raise AssertionError("complement budget profile mismatch")
        if task_budget_profile != EXPECTED_TASK_BUDGET_PROFILE:
            raise AssertionError("task budget profile mismatch")
        if pair_profile != EXPECTED_PAIR_PROFILE:
            raise AssertionError(f"pair profile mismatch: {pair_profile}")
        if classification_sha256 != EXPECTED_CLASSIFICATION_SHA256:
            raise AssertionError(f"classification digest mismatch: {classification_sha256}")
        if candidate_orbits != EXPECTED_CANDIDATE_ORBITS:
            raise AssertionError(f"candidate orbit mismatch: {candidate_orbits}")
        if demand_states != EXPECTED_DEMAND_STATES:
            raise AssertionError(f"demand state mismatch: {demand_states}")
        if demand_transitions != EXPECTED_DEMAND_TRANSITIONS:
            raise AssertionError(f"demand transition mismatch: {demand_transitions}")
        if orbit_receipt_sha256 != EXPECTED_ORBIT_RECEIPT_SHA256:
            raise AssertionError(f"orbit receipt mismatch: {orbit_receipt_sha256}")
    print(f"q_states={len(states)} orbit_UNSAT={len(states)} orbit_SAT=0")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"orbit_representatives={orbit_representatives}")
    print(f"candidate_orbits={candidate_orbits}")
    print(f"demand_states={demand_states}")
    print(f"demand_transitions={demand_transitions}")
    print(f"classification_sha256={classification_sha256}")
    print(f"orbit_receipt_sha256={orbit_receipt_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
