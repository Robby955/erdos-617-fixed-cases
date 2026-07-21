#!/usr/bin/env python3
"""Verify the m=64 two-hub frontier modulo S_8 x S_8."""

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
SCALAR_PATH = HERE / "r9_p93_order26_m64_scalar_side_verifier.py"
TAU3_PATH = HERE / "r9_p93_order26_m64_tau3_verifier.py"
DUAL_DATA = HERE / "r9_p93_order26_m64_duals.jsonl"
CORE_ORDER = 16
GLOBAL_OFFSET = 19
EXPECTED_COMPLEMENT_PAIRS = 562
EXPECTED_PAIRS = 7
EXPECTED_STATES = 10635
CORE_NAME = "O????B~~v}^w~o~o^wF}?"
EXPECTED_SUBGROUP_ORDER = math.factorial(8) ** 2
EXPECTED_TOTAL_ORBITS = 21904
EXPECTED_PROFILE_SHA256 = (
    "f80bfba50c8705a6b9f61cbcc837d31e71f049aacbf14be99f4ce33f823fe300"
)
EXPECTED_SELF_TEST_RECEIPT_SHA256 = (
    "4efc93c4f62b002cd638cb3faffe323c369f3299acd4937b018cadaac38028cd"
)
EXPECTED_ORBIT_REPRESENTATIVES = 3883026
EXPECTED_CANDIDATE_ORBITS = 498326
EXPECTED_DEMAND_STATES = 299684034
EXPECTED_DEMAND_TRANSITIONS = 299609210
EXPECTED_CLASSIFICATION_SHA256 = (
    "cd3805257b22201ab5bc0752ad4a691f48c3f13181cffbee0621b48e5b024820"
)
EXPECTED_ORBIT_RECEIPT_SHA256 = (
    "310705ec896fd69e29f337e259b225873b736c9c223bb95e0bb78835bccfe7bc"
)
EXPECTED_PAIR_PROFILE: Counter[int] = Counter(
    {699: 1, 1233: 2, 1746: 2, 1989: 2}
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_module("erdos617_m64_orbit_base", BASE_PATH)
SCALAR = load_module("erdos617_m64_orbit_scalar", SCALAR_PATH)
TAU3 = load_module("erdos617_m64_orbit_tau3", TAU3_PATH)
BASE.SCALAR = SCALAR
BASE.QSTATE.GLOBAL_OFFSET = GLOBAL_OFFSET
HubPairRepresentative = BASE.HubPairRepresentative


@dataclass(frozen=True)
class OrbitModel:
    core_name: str
    side_x: tuple[int, ...]
    side_y: tuple[int, ...]
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
        raise AssertionError(f"unexpected m=64 core: {core_name}")
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    side_x, side_y = tuple(
        sorted((tuple(sorted(side)) for side in BASE.QSTATE.bipartition(core)))
    )
    if tuple(map(len, (side_x, side_y))) != (8, 8):
        raise AssertionError("core does not have two sides of order eight")
    if core.number_of_edges() != 64 or any(
        not core.has_edge(first, second) for first in side_x for second in side_y
    ):
        raise AssertionError("core is not K8,8")
    generators = tuple(
        itertools.chain(
            adjacent_transpositions(side_x), adjacent_transpositions(side_y)
        )
    )
    model = OrbitModel(core_name, side_x, side_y, generators)
    validate_subgroup(model, core)
    return model


def side_mask(side: tuple[int, ...]) -> int:
    return sum(1 << vertex for vertex in side)


def membership_code(first: int, second: int, vertex: int) -> int:
    return 2 * ((first >> vertex) & 1) + ((second >> vertex) & 1)


def class_histogram(
    vertices: tuple[int, ...], first: int, second: int
) -> tuple[int, int, int, int]:
    counts = Counter(membership_code(first, second, vertex) for vertex in vertices)
    return tuple(counts[code] for code in range(4))  # type: ignore[return-value]


def orbit_signature(model: OrbitModel, first: int, second: int) -> tuple[Any, ...]:
    return (
        class_histogram(model.side_x, first, second),
        class_histogram(model.side_y, first, second),
    )


def p1_allowed(model: OrbitModel, first: int, second: int) -> bool:
    return all(
        row & side_mask(side) != side_mask(side)
        for row in (first, second)
        for side in (model.side_x, model.side_y)
    )


def validate_subgroup(model: OrbitModel, core: nx.Graph) -> None:
    vertices = frozenset(range(CORE_ORDER))
    sides = (frozenset(model.side_x), frozenset(model.side_y))
    edges = frozenset(
        frozenset((int(first), int(second))) for first, second in core.edges
    )
    for permutation in model.generators:
        if frozenset(permutation) != vertices:
            raise AssertionError("subgroup generator is not a permutation")
        if any(frozenset(permutation[v] for v in side) != side for side in sides):
            raise AssertionError("subgroup generator does not preserve the sides")
        transported = frozenset(
            frozenset((permutation[first], permutation[second]))
            for first, second in core.edges
        )
        if transported != edges:
            raise AssertionError("subgroup generator is not a core automorphism")
    if math.factorial(8) ** 2 != EXPECTED_SUBGROUP_ORDER:
        raise AssertionError("subgroup order formula mismatch")


@lru_cache(maxsize=64)
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
    for x_pattern, y_pattern in combined_pattern_index(
        model.side_x, model.side_y
    ).get((first_size, second_size), ()):
        first = x_pattern.first_mask | y_pattern.first_mask
        second = x_pattern.second_mask | y_pattern.second_mask
        if not p1_allowed(model, first, second):
            continue
        result.append(
            HubPairRepresentative(
                first,
                second,
                (x_pattern.histogram, y_pattern.histogram),
            )
        )
    if any(
        rep.first_row.bit_count() != first_size
        or rep.second_row.bit_count() != second_size
        or orbit_signature(model, rep.first_row, rep.second_row) != rep.signature
        for rep in result
    ):
        raise AssertionError("orbit representative invariant failed")
    if len({rep.signature for rep in result}) != len(result):
        raise AssertionError("duplicate orbit signature")
    return tuple(result)


def formula_profile(model: OrbitModel) -> Counter[tuple[int, int]]:
    profile: Counter[tuple[int, int]] = Counter()
    for x_histogram in BASE.histograms(8):
        x_first = x_histogram[2] + x_histogram[3]
        x_second = x_histogram[1] + x_histogram[3]
        if x_first == 8 or x_second == 8:
            continue
        for y_histogram in BASE.histograms(8):
            y_first = y_histogram[2] + y_histogram[3]
            y_second = y_histogram[1] + y_histogram[3]
            if y_first == 8 or y_second == 8:
                continue
            profile[(x_first + y_first, x_second + y_second)] += 1
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
    profile = formula_profile(model)
    digest = profile_sha256(profile)
    total = sum(profile.values())
    representatives_checked = 0
    for first_size in range(15):
        for second_size in range(15):
            representatives = hub_pair_representatives(
                CORE_NAME, first_size, second_size
            )
            if len(representatives) != profile[(first_size, second_size)]:
                raise AssertionError("direct and formula orbit profiles disagree")
            representatives_checked += len(representatives)
    transport_checks = 0
    for sizes in ((7, 7), (7, 8), (8, 8)):
        representatives = hub_pair_representatives(CORE_NAME, *sizes)
        stride = max(1, len(representatives) // 32)
        for representative in representatives[::stride][:32]:
            for permutation in model.generators:
                transported_first = permute_mask(
                    representative.first_row, permutation
                )
                transported_second = permute_mask(
                    representative.second_row, permutation
                )
                if (
                    orbit_signature(model, transported_first, transported_second)
                    != representative.signature
                ):
                    raise AssertionError("orbit signature is not transport invariant")
                transport_checks += 1
    payload = (
        f"{CORE_NAME}:S8xS8:{EXPECTED_SUBGROUP_ORDER}:{total}:{digest}\n"
        f"representatives={representatives_checked}:transport={transport_checks}\n"
    ).encode("ascii")
    receipt = hashlib.sha256(payload).hexdigest()
    if not allow_unpinned:
        if total != EXPECTED_TOTAL_ORBITS:
            raise AssertionError(f"total orbit mismatch: {total}")
        if digest != EXPECTED_PROFILE_SHA256:
            raise AssertionError(f"profile digest mismatch: {digest}")
        if receipt != EXPECTED_SELF_TEST_RECEIPT_SHA256:
            raise AssertionError(f"self-test receipt mismatch: {receipt}")
    print(f"core={CORE_NAME} subgroup=S8xS8 subgroup_order={EXPECTED_SUBGROUP_ORDER}")
    print(f"total_ordered_p1_orbits={total}")
    print(f"profile_sha256={digest}")
    print(f"representatives_checked={representatives_checked}")
    print(f"transport_checks={transport_checks}")
    print(f"self_test_receipt_sha256={receipt}")
    print("status=PASS")


BASE.build_orbit_model = build_orbit_model
BASE.hub_pair_representatives = hub_pair_representatives


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
    shell_states: dict[int, tuple[tuple[int, ...], ...]] = {}
    tasks = []
    scalar_rows = []
    pair_profile: Counter[tuple[int, bool]] = Counter()
    feasible_states = 0
    tau3_states = 0
    tau3_frontier: list[tuple[str, tuple[int, ...]]] = []
    for core_index, shell_index in complement:
        core = cores[core_index].graph
        shell = shells[shell_index].graph
        shell_states.setdefault(shell_index, SCALAR.row_size_states(shell))
        demand_x, demand_y = SCALAR.side_demands(core)
        feasible = tuple(
            rows
            for rows in shell_states[shell_index]
            if SCALAR.feasible_side_counts(shell, rows, demand_x, demand_y)
        )
        tau = SCALAR.vertex_cover_number(shell)
        pair_profile[(tau, bool(feasible))] += 1
        feasible_states += len(feasible)
        scalar_rows.append(
            f"{core_index}:{shell_index}:{tau}:"
            f"{len(shell_states[shell_index])}:{len(feasible)}\n"
        )
        if tau == 2 and feasible:
            tasks.append(
                (
                    core_index,
                    shell_index,
                    cores[core_index].graph6.decode("ascii"),
                    shells[shell_index].graph6.decode("ascii"),
                    feasible,
                )
            )
        elif tau == 3:
            tau3_states += len(feasible)
            tau3_frontier.extend(
                (shells[shell_index].graph6.decode("ascii"), rows)
                for rows in feasible
            )
    scalar_digest = hashlib.sha256("".join(scalar_rows).encode("ascii")).hexdigest()
    if pair_profile != SCALAR.EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"scalar pair profile mismatch: {pair_profile}")
    if feasible_states != SCALAR.EXPECTED_FEASIBLE_STATES:
        raise AssertionError(f"scalar state total mismatch: {feasible_states}")
    if scalar_digest != SCALAR.EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"scalar classification digest mismatch: {scalar_digest}")
    if len(tasks) != EXPECTED_PAIRS or tau3_states != 4:
        raise AssertionError(f"wrong frontier split: tasks={len(tasks)} tau3={tau3_states}")
    if tuple(sorted(tau3_frontier)) != tuple(sorted(TAU3.EXPECTED_CASES)):
        raise AssertionError(f"tau3 frontier mismatch: {tau3_frontier}")
    return cores, shells, tuple(tasks)


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

    _, _, tasks = build_frontier(args.geng, args.duals)
    print(
        f"two_hub_pairs={len(tasks)} "
        f"scalar_feasible_states={sum(len(task[4]) for task in tasks)}"
    )
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

    ordered = tuple(
        sorted(states, key=lambda item: (item.core_index, item.shell_index, item.row_sizes))
    )
    classification = "".join(
        f"{state.core_index}:{state.shell_index}:"
        f"{','.join(map(str, state.row_sizes))}:{int(state.satisfiable)}\n"
        for state in ordered
    ).encode("ascii")
    receipt_payload = "".join(
        f"{state.core_index}:{state.shell_index}:"
        f"{','.join(map(str, state.row_sizes))}:"
        f"{state.orbit_representatives}:{state.candidate_orbits}:"
        f"{state.demand_states}:{state.demand_transitions}\n"
        for state in ordered
    ).encode("ascii")
    classification_hash = hashlib.sha256(classification).hexdigest()
    receipt_hash = hashlib.sha256(receipt_payload).hexdigest()
    pair_profile = Counter(len(group) for group in nested)
    orbit_representatives = sum(state.orbit_representatives for state in states)
    candidate_orbits = sum(state.candidate_orbits for state in states)
    demand_states = sum(state.demand_states for state in states)
    demand_transitions = sum(state.demand_transitions for state in states)
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"pair profile mismatch: {pair_profile}")
    if not args.allow_unpinned:
        expected = (
            EXPECTED_ORBIT_REPRESENTATIVES,
            EXPECTED_CANDIDATE_ORBITS,
            EXPECTED_DEMAND_STATES,
            EXPECTED_DEMAND_TRANSITIONS,
            EXPECTED_CLASSIFICATION_SHA256,
            EXPECTED_ORBIT_RECEIPT_SHA256,
        )
        actual = (
            orbit_representatives,
            candidate_orbits,
            demand_states,
            demand_transitions,
            classification_hash,
            receipt_hash,
        )
        if actual != expected:
            raise AssertionError(f"unpinned orbit receipt: {actual}")
    print(f"q_states={len(states)} orbit_UNSAT={len(states)} orbit_SAT=0")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"orbit_representatives={orbit_representatives}")
    print(f"candidate_orbits={candidate_orbits}")
    print(f"demand_states={demand_states}")
    print(f"demand_transitions={demand_transitions}")
    print(f"classification_sha256={classification_hash}")
    print(f"orbit_receipt_sha256={receipt_hash}")
    print("status=PASS")


if __name__ == "__main__":
    main()
