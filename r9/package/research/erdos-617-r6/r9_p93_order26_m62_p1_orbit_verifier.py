#!/usr/bin/env python3
"""Verify the fixed r=9, m=62 two-hub remainder modulo core symmetries.

The two m=62 cores are K_8,8 with two edges removed.  This checker uses
explicit side-preserving subgroups of their automorphism groups:

* for two disjoint removed edges, S_6 x S_6 x S_2;
* for two removed edges sharing a vertex, S_7 x S_2 x S_6.

An ordered hub-row pair is represented by the four membership codes 00,
01, 10, and 11 on each permuted vertex class.  For the matching core the
two exceptional removed-edge pairs contribute an unordered multiset of
ordered endpoint-code pairs.  For the star core the center code is fixed
and each of the other three classes contributes a four-bin histogram.
These data are complete orbit invariants for the stated subgroups.

Every generator preserves the two core sides, core edges, row sizes,
unions, vertex covers, and the degree demand d(v)-6.  It therefore maps
every low-row domain for (R,S) bijectively to the corresponding domain for
(gR,gS), while merely permuting demand coordinates.  Feasibility is
constant on each ordered hub-pair orbit, so one direct representative per
signature is an exact quotient rather than a relaxation.
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
from typing import Any, Iterable, Iterator

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
QSTATE_PATH = HERE / "r9_p93_order26_m60_p1_qstate_verifier.py"
SCALAR_PATH = HERE / "r9_p93_order26_m62_scalar_side_verifier.py"
DUAL_DATA = HERE / "r9_p93_order26_m62_duals.jsonl"
CORE_ORDER = 16
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
GLOBAL_OFFSET = 17
EXPECTED_COMPLEMENT_PAIRS = 152
EXPECTED_PAIRS = 35
EXPECTED_STATES = 11706
EXPECTED_COMPLEMENT_BUDGET_PROFILE = Counter(
    {0: 12, 1: 20, 2: 30, 3: 34, 4: 35, 5: 12, 6: 9}
)
EXPECTED_TASK_BUDGET_PROFILE = Counter({2: 2, 3: 4, 4: 8, 5: 12, 6: 9})
EXPECTED_CLASSIFICATION_SHA256 = (
    "16d6bc92eb29c884f33da831a5f6aac24aad03dcee44eb51755681efdbdcd408"
)
EXPECTED_PAIR_PROFILE = Counter(
    {
        55: 2,
        121: 1,
        128: 1,
        155: 2,
        192: 2,
        193: 2,
        206: 4,
        216: 4,
        220: 4,
        456: 2,
        477: 3,
        640: 4,
        699: 4,
    }
)
EXPECTED_ORBIT_REPRESENTATIVES = 164021520
EXPECTED_CANDIDATE_ORBITS = 5073750
EXPECTED_DEMAND_STATES = 108285865
EXPECTED_DEMAND_TRANSITIONS = 107883823
EXPECTED_ORBIT_RECEIPT_SHA256 = (
    "cc53bf5ec3d04d68a5a0962eeb2e19bc8f9f4b5e78a6379a9c140b702cffb441"
)
MATCHING_CORE_NAME = "O????B}~V}^w~o~o^wF}?"
STAR_CORE_NAME = "O????B}~f}^w~o~o^wF}?"
EXPECTED_CORE_NAMES = frozenset({MATCHING_CORE_NAME, STAR_CORE_NAME})
EXPECTED_SUBGROUP_ORDERS = {
    "matching": math.factorial(6) * math.factorial(6) * math.factorial(2),
    "star": math.factorial(7) * math.factorial(2) * math.factorial(6),
}
EXPECTED_TOTAL_ORBITS = {"matching": 878501, "star": 358751}
EXPECTED_FIXED_ORBITS = {
    "matching": {(7, 8): 18844, (8, 8): 20000},
    "star": {(7, 8): 7230, (8, 8): 7600},
}
# Filled from the deterministic 0 <= |R|,|S| <= 14 orbit profiles.
EXPECTED_PROFILE_SHA256 = {
    "matching": "edec6085810289544f4fdb4a7799fb081aac6cc840f9c3250f289938116512e0",
    "star": "9d325f6d8b6432a1224cc3c83c1e357f013fba1fd15c8770f4b21a61d56b1bff",
}
EXPECTED_SELF_TEST_SIZE_COMPARISONS = 450
EXPECTED_SELF_TEST_REPRESENTATIVES = 1237252
EXPECTED_SELF_TEST_RECEIPT_SHA256 = (
    "b4a5736b62f0f497b89a29ddb43758d9cf217b2157b39725c0ad7a65f4c4b61a"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


QSTATE = load_module("erdos617_m62_orbit_qstate", QSTATE_PATH)
QSTATE.GLOBAL_OFFSET = GLOBAL_OFFSET
SCALAR = load_module("erdos617_m62_orbit_scalar", SCALAR_PATH)


@dataclass(frozen=True)
class OrbitCoreModel:
    core_name: str
    kind: str
    side_x: tuple[int, ...]
    side_y: tuple[int, ...]
    free_classes: tuple[tuple[int, ...], ...]
    exceptional_pairs: tuple[tuple[int, int], ...]
    center: int | None
    generators: tuple[tuple[int, ...], ...]
    subgroup_order: int
    subgroup_label: str


@dataclass(frozen=True)
class ClassPattern:
    histogram: tuple[int, int, int, int]
    first_count: int
    second_count: int
    first_mask: int
    second_mask: int


@dataclass(frozen=True)
class HubPairRepresentative:
    first_row: int
    second_row: int
    signature: tuple[Any, ...]


@dataclass(frozen=True)
class OrbitSearchReceipt:
    satisfiable: bool
    orbit_representatives: int
    candidate_orbits: int
    demand_states: int
    demand_transitions: int


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


def bipartition(core: nx.Graph) -> tuple[tuple[int, ...], tuple[int, ...]]:
    sides = QSTATE.bipartition(core)
    ordered = tuple(sorted((tuple(sorted(sides[0])), tuple(sorted(sides[1])))))
    return ordered[0], ordered[1]


def adjacent_transpositions(vertices: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
    for first, second in itertools.pairwise(vertices):
        permutation = list(range(CORE_ORDER))
        permutation[first], permutation[second] = second, first
        yield tuple(permutation)


def swap_pairs_generator(
    first: tuple[int, int], second: tuple[int, int]
) -> tuple[int, ...]:
    permutation = list(range(CORE_ORDER))
    for left, right in zip(first, second):
        permutation[left], permutation[right] = right, left
    return tuple(permutation)


@lru_cache(maxsize=None)
def build_orbit_model(core_name: str) -> OrbitCoreModel:
    if core_name not in EXPECTED_CORE_NAMES:
        raise AssertionError(f"unexpected m=62 core: {core_name}")
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    side_x, side_y = bipartition(core)
    missing = tuple(
        sorted(
            (first, second)
            for first in side_x
            for second in side_y
            if not core.has_edge(first, second)
        )
    )
    if len(missing) != 2 or core.number_of_edges() != 62:
        raise AssertionError("core is not K8,8 minus two edges")
    missing_degrees = Counter(vertex for edge in missing for vertex in edge)
    free_classes: tuple[tuple[int, ...], ...]
    exceptional_pairs: tuple[tuple[int, int], ...]

    if sorted(missing_degrees.values()) == [1, 1, 1, 1]:
        kind = "matching"
        exceptional_pairs = missing
        exceptional_x = frozenset(first for first, _ in missing)
        exceptional_y = frozenset(second for _, second in missing)
        regular_x = tuple(vertex for vertex in side_x if vertex not in exceptional_x)
        regular_y = tuple(vertex for vertex in side_y if vertex not in exceptional_y)
        free_classes = (regular_x, regular_y)
        generators = tuple(
            itertools.chain(
                adjacent_transpositions(regular_x),
                adjacent_transpositions(regular_y),
                (swap_pairs_generator(missing[0], missing[1]),),
            )
        )
        center = None
        subgroup_label = "S6xS6xS2"
    elif sorted(missing_degrees.values()) == [1, 1, 2]:
        kind = "star"
        center = next(vertex for vertex, degree in missing_degrees.items() if degree == 2)
        center_side = side_x if center in side_x else side_y
        opposite_side = side_y if center in side_x else side_x
        leaves = tuple(
            sorted(
                vertex
                for vertex in opposite_side
                if (center, vertex) in missing or (vertex, center) in missing
            )
        )
        center_regular = tuple(vertex for vertex in center_side if vertex != center)
        opposite_regular = tuple(vertex for vertex in opposite_side if vertex not in leaves)
        if tuple(map(len, (center_regular, leaves, opposite_regular))) != (7, 2, 6):
            raise AssertionError("star core class sizes are wrong")
        free_classes = (center_regular, leaves, opposite_regular)
        exceptional_pairs = ()
        generators = tuple(
            itertools.chain(
                adjacent_transpositions(center_regular),
                adjacent_transpositions(leaves),
                adjacent_transpositions(opposite_regular),
            )
        )
        subgroup_label = "S7xS2xS6"
    else:
        raise AssertionError(f"unrecognized missing-edge pattern: {missing}")

    expected_name = MATCHING_CORE_NAME if kind == "matching" else STAR_CORE_NAME
    if core_name != expected_name:
        raise AssertionError(f"{kind} core graph6 mismatch: {core_name}")
    model = OrbitCoreModel(
        core_name,
        kind,
        side_x,
        side_y,
        free_classes,
        exceptional_pairs,
        center,
        generators,
        EXPECTED_SUBGROUP_ORDERS[kind],
        subgroup_label,
    )
    validate_subgroup(model, core)
    return model


def permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    while mask:
        bit = mask & -mask
        vertex = bit.bit_length() - 1
        result |= 1 << permutation[vertex]
        mask ^= bit
    return result


def side_mask(side: Iterable[int]) -> int:
    return sum(1 << vertex for vertex in side)


def p1_allowed(model: OrbitCoreModel, first: int, second: int) -> bool:
    for row in (first, second):
        if any(row & side_mask(side) == side_mask(side) for side in (model.side_x, model.side_y)):
            return False
    return True


def membership_code(first: int, second: int, vertex: int) -> int:
    return 2 * ((first >> vertex) & 1) + ((second >> vertex) & 1)


def class_histogram(
    vertices: tuple[int, ...], first: int, second: int
) -> tuple[int, int, int, int]:
    counts = Counter(membership_code(first, second, vertex) for vertex in vertices)
    return tuple(counts[code] for code in range(4))  # type: ignore[return-value]


def orbit_signature(
    model: OrbitCoreModel, first: int, second: int
) -> tuple[Any, ...]:
    histograms = tuple(
        class_histogram(vertices, first, second) for vertices in model.free_classes
    )
    if model.kind == "star":
        if model.center is None:
            raise AssertionError("star center is missing")
        return (membership_code(first, second, model.center),) + histograms
    pair_codes = tuple(
        sorted(
            (
                membership_code(first, second, left),
                membership_code(first, second, right),
            )
            for left, right in model.exceptional_pairs
        )
    )
    return histograms + (pair_codes,)


def validate_subgroup(model: OrbitCoreModel, core: nx.Graph) -> None:
    vertices = frozenset(range(CORE_ORDER))
    sides = (frozenset(model.side_x), frozenset(model.side_y))
    edges = frozenset(frozenset((int(first), int(second))) for first, second in core.edges)
    demands = tuple(max(0, int(core.degree(vertex)) - 6) for vertex in range(CORE_ORDER))
    for permutation in model.generators:
        if frozenset(permutation) != vertices:
            raise AssertionError("subgroup generator is not a permutation")
        if any(frozenset(permutation[vertex] for vertex in side) != side for side in sides):
            raise AssertionError("subgroup generator does not preserve both sides")
        transported_edges = frozenset(
            frozenset((permutation[first], permutation[second]))
            for first, second in core.edges
        )
        if transported_edges != edges:
            raise AssertionError("subgroup generator is not a core automorphism")
        if any(demands[permutation[vertex]] != demands[vertex] for vertex in vertices):
            raise AssertionError("subgroup generator does not preserve demands")
    class_factor = math.prod(math.factorial(len(vertices)) for vertices in model.free_classes)
    exceptional_factor = 2 if model.kind == "matching" else 1
    if class_factor * exceptional_factor != model.subgroup_order:
        raise AssertionError("subgroup order formula mismatch")


@lru_cache(maxsize=None)
def histograms(size: int) -> tuple[tuple[int, int, int, int], ...]:
    return tuple(
        (zero, one, two, size - zero - one - two)
        for zero in range(size + 1)
        for one in range(size - zero + 1)
        for two in range(size - zero - one + 1)
    )


def apply_code(first: int, second: int, vertex: int, code: int) -> tuple[int, int]:
    if code & 2:
        first |= 1 << vertex
    if code & 1:
        second |= 1 << vertex
    return first, second


@lru_cache(maxsize=None)
def class_patterns(vertices: tuple[int, ...]) -> tuple[ClassPattern, ...]:
    patterns = []
    for histogram in histograms(len(vertices)):
        first = 0
        second = 0
        offset = 0
        for code, count in enumerate(histogram):
            for vertex in vertices[offset : offset + count]:
                first, second = apply_code(first, second, vertex, code)
            offset += count
        patterns.append(
            ClassPattern(
                histogram,
                histogram[2] + histogram[3],
                histogram[1] + histogram[3],
                first,
                second,
            )
        )
    return tuple(patterns)


@lru_cache(maxsize=None)
def combined_pattern_index(
    first_class: tuple[int, ...], second_class: tuple[int, ...]
) -> dict[tuple[int, int], tuple[tuple[ClassPattern, ClassPattern], ...]]:
    index: dict[tuple[int, int], list[tuple[ClassPattern, ClassPattern]]] = defaultdict(list)
    for first_pattern in class_patterns(first_class):
        for second_pattern in class_patterns(second_class):
            key = (
                first_pattern.first_count + second_pattern.first_count,
                first_pattern.second_count + second_pattern.second_count,
            )
            index[key].append((first_pattern, second_pattern))
    return {key: tuple(value) for key, value in index.items()}


def star_representatives(
    model: OrbitCoreModel, first_size: int, second_size: int
) -> Iterator[HubPairRepresentative]:
    if model.center is None or len(model.free_classes) != 3:
        raise AssertionError("bad star model")
    center_regular, leaves, opposite_regular = model.free_classes
    opposite_index = combined_pattern_index(leaves, opposite_regular)
    for center_code in range(4):
        center_first = int(bool(center_code & 2))
        center_second = int(bool(center_code & 1))
        center_first_mask, center_second_mask = apply_code(0, 0, model.center, center_code)
        for center_pattern in class_patterns(center_regular):
            needed = (
                first_size - center_first - center_pattern.first_count,
                second_size - center_second - center_pattern.second_count,
            )
            for leaf_pattern, opposite_pattern in opposite_index.get(needed, ()):
                first = (
                    center_first_mask
                    | center_pattern.first_mask
                    | leaf_pattern.first_mask
                    | opposite_pattern.first_mask
                )
                second = (
                    center_second_mask
                    | center_pattern.second_mask
                    | leaf_pattern.second_mask
                    | opposite_pattern.second_mask
                )
                if not p1_allowed(model, first, second):
                    continue
                signature = (
                    center_code,
                    center_pattern.histogram,
                    leaf_pattern.histogram,
                    opposite_pattern.histogram,
                )
                yield HubPairRepresentative(first, second, signature)


def matching_representatives(
    model: OrbitCoreModel, first_size: int, second_size: int
) -> Iterator[HubPairRepresentative]:
    if len(model.free_classes) != 2 or len(model.exceptional_pairs) != 2:
        raise AssertionError("bad matching model")
    regular_x, regular_y = model.free_classes
    regular_index = combined_pattern_index(regular_x, regular_y)
    endpoint_types = tuple(
        (left_code, right_code)
        for left_code in range(4)
        for right_code in range(4)
    )
    for first_type, second_type in itertools.combinations_with_replacement(endpoint_types, 2):
        first = 0
        second = 0
        exceptional_first = 0
        exceptional_second = 0
        for pair, codes in zip(model.exceptional_pairs, (first_type, second_type)):
            for vertex, code in zip(pair, codes):
                first, second = apply_code(first, second, vertex, code)
                exceptional_first += int(bool(code & 2))
                exceptional_second += int(bool(code & 1))
        needed = (first_size - exceptional_first, second_size - exceptional_second)
        for x_pattern, y_pattern in regular_index.get(needed, ()):
            row_first = first | x_pattern.first_mask | y_pattern.first_mask
            row_second = second | x_pattern.second_mask | y_pattern.second_mask
            if not p1_allowed(model, row_first, row_second):
                continue
            signature = (
                x_pattern.histogram,
                y_pattern.histogram,
                (first_type, second_type),
            )
            yield HubPairRepresentative(row_first, row_second, signature)


@lru_cache(maxsize=16)
def hub_pair_representatives(
    core_name: str, first_size: int, second_size: int
) -> tuple[HubPairRepresentative, ...]:
    if not 0 <= first_size <= 14 or not 0 <= second_size <= 14:
        return ()
    model = build_orbit_model(core_name)
    generator = star_representatives if model.kind == "star" else matching_representatives
    result = tuple(generator(model, first_size, second_size))
    if any(
        rep.first_row.bit_count() != first_size
        or rep.second_row.bit_count() != second_size
        or orbit_signature(model, rep.first_row, rep.second_row) != rep.signature
        for rep in result
    ):
        raise AssertionError("direct orbit representative invariant failed")
    if len({rep.signature for rep in result}) != len(result):
        raise AssertionError("duplicate direct orbit signature")
    return result


def orbit_profile(model: OrbitCoreModel) -> Counter[tuple[int, int]]:
    profile: Counter[tuple[int, int]] = Counter()
    if model.kind == "star":
        if model.center is None:
            raise AssertionError("star center is missing")
        center_regular, leaves, opposite_regular = model.free_classes
        for center_code in range(4):
            center_first = int(bool(center_code & 2))
            center_second = int(bool(center_code & 1))
            for center_pattern in class_patterns(center_regular):
                center_side_first = center_first + center_pattern.first_count
                center_side_second = center_second + center_pattern.second_count
                for leaf_pattern in class_patterns(leaves):
                    for opposite_pattern in class_patterns(opposite_regular):
                        opposite_first = leaf_pattern.first_count + opposite_pattern.first_count
                        opposite_second = leaf_pattern.second_count + opposite_pattern.second_count
                        if (
                            max(
                                center_side_first,
                                center_side_second,
                                opposite_first,
                                opposite_second,
                            )
                            >= 8
                        ):
                            continue
                        profile[
                            (
                                center_side_first + opposite_first,
                                center_side_second + opposite_second,
                            )
                        ] += 1
    else:
        regular_x, regular_y = model.free_classes
        endpoint_types = tuple(
            (left_code, right_code)
            for left_code in range(4)
            for right_code in range(4)
        )
        for first_type, second_type in itertools.combinations_with_replacement(endpoint_types, 2):
            exceptional_counts = []
            for side_index in range(2):
                codes = (first_type[side_index], second_type[side_index])
                exceptional_counts.append(
                    (
                        sum(int(bool(code & 2)) for code in codes),
                        sum(int(bool(code & 1)) for code in codes),
                    )
                )
            for x_pattern in class_patterns(regular_x):
                x_first = x_pattern.first_count + exceptional_counts[0][0]
                x_second = x_pattern.second_count + exceptional_counts[0][1]
                if max(x_first, x_second) >= 8:
                    continue
                for y_pattern in class_patterns(regular_y):
                    y_first = y_pattern.first_count + exceptional_counts[1][0]
                    y_second = y_pattern.second_count + exceptional_counts[1][1]
                    if max(y_first, y_second) >= 8:
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


def is_vertex_cover(core: nx.Graph, mask: int) -> bool:
    return all((mask >> first) & 1 or (mask >> second) & 1 for first, second in core.edges)


def transport_receipt(model: OrbitCoreModel) -> tuple[int, int]:
    core = nx.from_graph6_bytes(model.core_name.encode("ascii"))
    special_masks = {
        0,
        FULL_CORE_MASK,
        side_mask(model.side_x),
        side_mask(model.side_y),
        *(1 << vertex for vertex in range(CORE_ORDER)),
    }
    sampled_masks = tuple(sorted(special_masks | set(range(0, 1 << CORE_ORDER, 257))))
    mask_checks = 0
    signature_checks = 0
    sample_representatives: list[HubPairRepresentative] = []
    for sizes in ((7, 8), (8, 8)):
        representatives = hub_pair_representatives(model.core_name, *sizes)
        stride = max(1, len(representatives) // 64)
        sample_representatives.extend(representatives[::stride][:64])
    for permutation in model.generators:
        for mask in sampled_masks:
            transported = permute_mask(mask, permutation)
            if mask.bit_count() != transported.bit_count():
                raise AssertionError("row-size transport failed")
            original_p1 = all(
                mask & side_mask(side) != side_mask(side)
                for side in (model.side_x, model.side_y)
            )
            transported_p1 = all(
                transported & side_mask(side) != side_mask(side)
                for side in (model.side_x, model.side_y)
            )
            if original_p1 != transported_p1:
                raise AssertionError("p1 transport failed")
            if is_vertex_cover(core, mask) != is_vertex_cover(core, transported):
                raise AssertionError("cover transport failed")
            mask_checks += 1
        for representative in sample_representatives:
            transported_first = permute_mask(representative.first_row, permutation)
            transported_second = permute_mask(representative.second_row, permutation)
            if (
                orbit_signature(model, transported_first, transported_second)
                != representative.signature
            ):
                raise AssertionError("signature transport failed")
            if (
                permute_mask(
                    representative.first_row | representative.second_row, permutation
                )
                != transported_first | transported_second
            ):
                raise AssertionError("union transport failed")
            signature_checks += 1
    return mask_checks, signature_checks


class OrbitP1CoreSearch:
    """Run the m=62 two-hub search on canonical ordered row-pair orbits."""

    def __init__(self, core_name: str):
        self.core_name = core_name
        self.model = build_orbit_model(core_name)
        self.core = nx.from_graph6_bytes(core_name.encode("ascii"))
        self.base = QSTATE.P1CoreSearch(self.core)

    def solve(self, shell: nx.Graph, row_sizes: tuple[int, ...]) -> OrbitSearchReceipt:
        hubs = QSTATE.two_vertex_edge_cover(shell)
        if hubs is None:
            raise AssertionError("orbit search received a shell without two hubs")
        first_hub, second_hub = hubs
        low_vertices = tuple(
            vertex for vertex in range(QSTATE.SHELL_ORDER) if vertex not in hubs
        )
        if any(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(low_vertices, 2)
        ):
            raise AssertionError("chosen hubs do not cover all shell edges")
        first_neighbors = tuple(
            vertex for vertex in low_vertices if shell.has_edge(first_hub, vertex)
        )
        second_neighbors = tuple(
            vertex for vertex in low_vertices if shell.has_edge(second_hub, vertex)
        )
        column_demands = tuple(
            max(0, int(self.core.degree(vertex)) - 6)
            for vertex in range(CORE_ORDER)
        )
        orbit_representatives = 0
        candidate_orbits = 0
        demand_states = 0
        demand_transitions = 0

        for representative in hub_pair_representatives(
            self.core_name, row_sizes[first_hub], row_sizes[second_hub]
        ):
            orbit_representatives += 1
            first_row = representative.first_row
            second_row = representative.second_row
            if not all(
                self.base.extensions(first_row, row_sizes[neighbor])
                for neighbor in first_neighbors
            ):
                continue
            if not all(
                self.base.extensions(second_row, row_sizes[neighbor])
                for neighbor in second_neighbors
            ):
                continue
            candidate_orbits += 1
            if shell.has_edge(first_hub, second_hub) and not self.base.is_cover[
                first_row | second_row
            ]:
                continue

            domains = []
            for low in low_vertices:
                domain: tuple[int, ...] = self.base.allowed_masks[row_sizes[low]]
                if shell.has_edge(first_hub, low):
                    first_allowed = frozenset(self.base.extensions(first_row, row_sizes[low]))
                    domain = tuple(row for row in domain if row in first_allowed)
                if shell.has_edge(second_hub, low):
                    second_allowed = frozenset(self.base.extensions(second_row, row_sizes[low]))
                    domain = tuple(row for row in domain if row in second_allowed)
                if (
                    shell.has_edge(first_hub, second_hub)
                    and shell.has_edge(first_hub, low)
                    and shell.has_edge(second_hub, low)
                ):
                    domain = tuple(
                        row for row in domain if first_row | second_row | row == FULL_CORE_MASK
                    )
                if not domain:
                    break
                domains.append(domain)
            if len(domains) != len(low_vertices):
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

            def maximal_effects(domain: tuple[int, ...], support: int) -> tuple[int, ...]:
                """Keep the exact antichain relevant to lower-bound demands.

                Each effect comes from a row already admitted to this domain.  If
                effects E and F satisfy E subset F, replacing the row for E by the
                row for F preserves all local constraints and cannot reduce any
                remaining column count.  E can therefore be deleted in both SAT
                and UNSAT searches.
                """

                effects = sorted(
                    {row & support for row in domain},
                    key=lambda effect: (-effect.bit_count(), effect),
                )
                maximal: list[int] = []
                for effect in effects:
                    if any(effect & kept == effect for kept in maximal):
                        continue
                    maximal.append(effect)
                return tuple(maximal)

            def meet_demands(domain_index: int, remaining: tuple[int, ...]) -> bool:
                nonlocal demand_states, demand_transitions
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
                        any((row >> vertex) & 1 for row in domain) for domain in tail
                    )
                    if demand > possible:
                        return False
                support = sum(
                    1 << vertex for vertex, demand in enumerate(remaining) if demand
                )
                for effect in maximal_effects(ordered_domains[domain_index], support):
                    demand_transitions += 1
                    updated = tuple(
                        max(0, demand - ((effect >> vertex) & 1))
                        for vertex, demand in enumerate(remaining)
                    )
                    if meet_demands(domain_index + 1, updated):
                        return True
                return False

            if meet_demands(0, residual):
                return OrbitSearchReceipt(
                    True,
                    orbit_representatives,
                    candidate_orbits,
                    demand_states,
                    demand_transitions,
                )
        return OrbitSearchReceipt(
            False,
            orbit_representatives,
            candidate_orbits,
            demand_states,
            demand_transitions,
        )


def scalar_budget(shell: nx.Graph) -> int:
    return GLOBAL_OFFSET - int(shell.number_of_edges())


def build_frontier(
    geng: Path, duals: Path
) -> tuple[
    tuple[Any, ...],
    tuple[Any, ...],
    tuple[tuple[Any, ...], ...],
    Counter[int],
    Counter[int],
]:
    cores = SCALAR.DUAL.generate_cores(geng)
    shells = SCALAR.DUAL.generate_shells(geng)
    if len(cores) != SCALAR.DUAL.EXPECTED_CORES or len(shells) != SCALAR.DUAL.EXPECTED_SHELLS:
        raise AssertionError("catalog count mismatch")
    if SCALAR.DUAL.catalog_sha256(cores) != SCALAR.DUAL.EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if SCALAR.DUAL.catalog_sha256(shells) != SCALAR.DUAL.EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")
    if frozenset(case.graph6.decode("ascii") for case in cores) != EXPECTED_CORE_NAMES:
        raise AssertionError("m=62 core names mismatch")
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
    complement_budget_profile = Counter(
        scalar_budget(shells[shell_index].graph) for _, shell_index in complement
    )
    if complement_budget_profile != EXPECTED_COMPLEMENT_BUDGET_PROFILE:
        raise AssertionError(f"complement budget-profile mismatch: {complement_budget_profile}")

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
            if SCALAR.feasible_side_counts(shell, rows, demand_x, demand_y)
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
        raise AssertionError(f"scalar pair-profile mismatch: {pair_profile}")
    if raw_states != SCALAR.EXPECTED_RAW_STATES or feasible_states != EXPECTED_STATES:
        raise AssertionError(f"scalar state totals mismatch: {raw_states}, {feasible_states}")
    scalar_digest = hashlib.sha256("".join(scalar_rows).encode("ascii")).hexdigest()
    if scalar_digest != SCALAR.EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"scalar classification digest mismatch: {scalar_digest}")
    if len(tasks) != EXPECTED_PAIRS:
        raise AssertionError(f"wrong task count: {len(tasks)}")
    if any(SCALAR.vertex_cover_number(shells[task[1]].graph) != 2 for task in tasks):
        raise AssertionError("scalar survivor without a two-hub shell")
    task_budget_profile = Counter(
        scalar_budget(shells[task[1]].graph) for task in tasks
    )
    if task_budget_profile != EXPECTED_TASK_BUDGET_PROFILE:
        raise AssertionError(f"task budget-profile mismatch: {task_budget_profile}")
    return cores, shells, tuple(tasks), complement_budget_profile, task_budget_profile


def audit_task(task: tuple[Any, ...]) -> tuple[StateReceipt, ...]:
    core_index, shell_index, core_name, shell_name, row_states = task
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    search = OrbitP1CoreSearch(core_name)
    results = []
    for row_sizes in row_states:
        receipt = search.solve(shell, row_sizes)
        results.append(
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
        )
    return tuple(results)


def run_self_test() -> None:
    rows = []
    size_comparisons = 0
    representatives_checked = 0
    for core_name in sorted(EXPECTED_CORE_NAMES):
        model = build_orbit_model(core_name)
        profile = orbit_profile(model)
        total = sum(profile.values())
        digest = profile_sha256(profile)
        if total != EXPECTED_TOTAL_ORBITS[model.kind]:
            raise AssertionError(f"{model.kind} total orbit mismatch: {total}")
        for sizes, expected in EXPECTED_FIXED_ORBITS[model.kind].items():
            if profile[sizes] != expected:
                raise AssertionError(f"{model.kind} {sizes} orbit mismatch: {profile[sizes]}")
        for first_size in range(15):
            for second_size in range(15):
                sizes = first_size, second_size
                representatives = hub_pair_representatives(core_name, *sizes)
                direct_count = len(representatives)
                if direct_count != profile[sizes]:
                    raise AssertionError(
                        f"{model.kind} direct representative mismatch at {sizes}: "
                        f"{direct_count} != {profile[sizes]}"
                    )
                size_comparisons += 1
                representatives_checked += direct_count
        mask_checks, signature_checks = transport_receipt(model)
        expected_digest = EXPECTED_PROFILE_SHA256[model.kind]
        if expected_digest and digest != expected_digest:
            raise AssertionError(f"{model.kind} profile digest mismatch: {digest}")
        print(
            f"core={core_name} kind={model.kind} subgroup={model.subgroup_label} "
            f"subgroup_order={model.subgroup_order} generators={len(model.generators)}"
        )
        print(
            f"total_ordered_p1_orbits={total} orbits_7_8={profile[(7, 8)]} "
            f"orbits_8_8={profile[(8, 8)]}"
        )
        print(
            f"transport_mask_checks={mask_checks} "
            f"signature_transport_checks={signature_checks} profile_sha256={digest}"
        )
        rows.append(
            f"{core_name}:{model.kind}:{model.subgroup_label}:{model.subgroup_order}:"
            f"{total}:{profile[(7, 8)]}:{profile[(8, 8)]}:{digest}\n"
        )
    if size_comparisons != EXPECTED_SELF_TEST_SIZE_COMPARISONS:
        raise AssertionError(f"self-test size-comparison mismatch: {size_comparisons}")
    if representatives_checked != EXPECTED_SELF_TEST_REPRESENTATIVES:
        raise AssertionError(
            f"self-test representative mismatch: {representatives_checked}"
        )
    print(
        f"direct_profile_size_comparisons={size_comparisons} "
        f"representatives_checked={representatives_checked}"
    )
    rows.append(
        f"direct_profile_size_comparisons={size_comparisons}:"
        f"representatives_checked={representatives_checked}\n"
    )
    receipt_sha256 = hashlib.sha256("".join(rows).encode("ascii")).hexdigest()
    if receipt_sha256 != EXPECTED_SELF_TEST_RECEIPT_SHA256:
        raise AssertionError(f"self-test receipt mismatch: {receipt_sha256}")
    print(f"self_test_receipt_sha256={receipt_sha256}")
    print("status=PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--frontier-only", action="store_true")
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")
    if args.self_test:
        run_self_test()
        return
    if args.geng is None:
        parser.error("--geng is required unless --self-test is used")

    _, _, tasks, complement_budget_profile, task_budget_profile = build_frontier(
        args.geng, args.duals
    )
    print(
        f"two_hub_pairs={len(tasks)} "
        f"scalar_feasible_states={sum(len(task[4]) for task in tasks)}"
    )
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
        raise AssertionError(f"unexpected p1-SAT states: {len(satisfiable)}")
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
        raise AssertionError(f"classification digest mismatch: {classification_sha256}")
    receipt_payload = "".join(
        f"{state.core_index}:{state.shell_index}:{','.join(map(str, state.row_sizes))}:"
        f"{state.orbit_representatives}:{state.candidate_orbits}:"
        f"{state.demand_states}:{state.demand_transitions}\n"
        for state in sorted(
            states,
            key=lambda item: (item.core_index, item.shell_index, item.row_sizes),
        )
    ).encode("ascii")
    pair_profile = Counter(len(group) for group in nested)
    orbit_representatives = sum(state.orbit_representatives for state in states)
    candidate_orbits = sum(state.candidate_orbits for state in states)
    demand_states = sum(state.demand_states for state in states)
    demand_transitions = sum(state.demand_transitions for state in states)
    orbit_receipt_sha256 = hashlib.sha256(receipt_payload).hexdigest()
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"pair-profile mismatch: {pair_profile}")
    if orbit_representatives != EXPECTED_ORBIT_REPRESENTATIVES:
        raise AssertionError(f"orbit-representative mismatch: {orbit_representatives}")
    if candidate_orbits != EXPECTED_CANDIDATE_ORBITS:
        raise AssertionError(f"candidate-orbit mismatch: {candidate_orbits}")
    if demand_states != EXPECTED_DEMAND_STATES:
        raise AssertionError(f"demand-state mismatch: {demand_states}")
    if demand_transitions != EXPECTED_DEMAND_TRANSITIONS:
        raise AssertionError(f"demand-transition mismatch: {demand_transitions}")
    if orbit_receipt_sha256 != EXPECTED_ORBIT_RECEIPT_SHA256:
        raise AssertionError(f"orbit-receipt mismatch: {orbit_receipt_sha256}")
    print(f"q_states={len(states)} p1_UNSAT={len(states)} p1_SAT=0")
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
