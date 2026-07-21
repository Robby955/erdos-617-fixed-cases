#!/usr/bin/env python3
"""Build deterministic certificate inputs for the r=9, P3(27), d=10 branch.

The formula is the round-zero relaxation from the exploratory variable-shell
search.  It omits the lazy ten-set cuts.  This is deliberate: all 332 cases
were reported UNSAT before any lazy cut, and omitting valid constraints makes
an UNSAT result stronger.

This file does not import the exploratory scout.  It has its own case filter,
variable map, cardinality encoder, formula builder, manifest writer, and
optional DRAT-to-LRAT path.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import shutil
import subprocess
from typing import Iterable, NoReturn

import networkx as nx  # type: ignore[import-untyped]


Clause = tuple[int, ...]
Edge = tuple[int, int]

R = 9
ORDER = 27
DEGREE = 10
SHELL_ORDER = 10
CORE_ORDER = 16
EDGE_CAP = 135
EXPECTED_CASES = 332
EXPECTED_REDUCED_CASES = 50
REDUCED_EDGE_DEGREE_SUM = 13
EXPECTED_REDUCED_INDEX_SHA256 = (
    "e9c743eef1f89309733e1a4eaecd74fb6af862a55dd457dfee8b2604bf30037f"
)
PRIMARY_VARIABLES = math.comb(SHELL_ORDER, 2) + SHELL_ORDER * CORE_ORDER
SCHEMA_VERSION = 1
REPOSITORY_PREFIX = "research/erdos-617-r6"


def fail(message: str) -> NoReturn:
    raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def file_record(path: Path, root: Path) -> dict[str, object]:
    return {
        "path": path.relative_to(root).as_posix(),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def canonical_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def p9(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1, 2
    )


def adjacency_masks(graph: nx.Graph) -> tuple[int, ...]:
    masks = [0] * graph.number_of_nodes()
    for first, second in graph.edges:
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
    return sum(
        (adjacency[vertex] & mask).bit_count()
        for vertex in range(len(adjacency))
        if mask >> vertex & 1
    ) // 2


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    degrees = [degree for _, degree in graph.degree()]
    if min(degrees) < 5 or max(degrees) > 8:
        return False
    if any(nx.triangles(graph).values()):
        return False
    adjacency = adjacency_masks(graph)
    for vertices in itertools.combinations(range(CORE_ORDER), 9):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            return False
    for subset_order in range(10, CORE_ORDER + 1):
        minimum = 8 * p9(subset_order)
        for vertices in itertools.combinations(range(CORE_ORDER), subset_order):
            mask = sum(1 << vertex for vertex in vertices)
            if induced_edges(mask, adjacency) < minimum:
                return False
    return True


@dataclass(frozen=True)
class Case:
    index: int
    graph6: str
    graph: nx.Graph

    @property
    def case_id(self) -> str:
        return hashlib.sha256(self.graph6.encode("ascii")).hexdigest()[:16]

    @property
    def edge_count(self) -> int:
        return int(self.graph.number_of_edges())

    @property
    def directory_name(self) -> str:
        return f"case-{self.index:04d}-{self.case_id}"


def generate_cases(geng: Path) -> tuple[Case, ...]:
    command = [
        str(geng),
        "-q",
        "-t",
        "-d5",
        "-D8",
        str(CORE_ORDER),
        "56:64",
    ]
    valid_lines: list[str] = []
    for raw_line in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(raw_line)
        if valid_core(graph):
            valid_lines.append(raw_line.decode("ascii"))
    valid_lines.sort()
    if len(valid_lines) != EXPECTED_CASES:
        fail(
            f"expected {EXPECTED_CASES} valid cores, found {len(valid_lines)}"
        )
    return tuple(
        Case(index, line, nx.from_graph6_bytes(line.encode("ascii")))
        for index, line in enumerate(valid_lines)
    )


def reduced_core_indices(cases: tuple[Case, ...]) -> tuple[int, ...]:
    indices = tuple(
        case.index
        for case in cases
        if min(
            int(case.graph.degree(first)) + int(case.graph.degree(second))
            for first, second in case.graph.edges
        )
        >= REDUCED_EDGE_DEGREE_SUM
    )
    digest = hashlib.sha256(
        "".join(f"{index}\n" for index in indices).encode("ascii")
    ).hexdigest()
    if len(indices) != EXPECTED_REDUCED_CASES:
        fail(f"expected {EXPECTED_REDUCED_CASES} reduced cores, found {len(indices)}")
    if digest != EXPECTED_REDUCED_INDEX_SHA256:
        fail(f"reduced core index digest mismatch: {digest}")
    return indices


def independent_masks(graph: nx.Graph) -> tuple[tuple[int, ...], ...]:
    groups: list[list[int]] = [[] for _ in range(graph.number_of_nodes() + 1)]
    edges = tuple(graph.edges)
    for mask in range(1, 1 << graph.number_of_nodes()):
        if all(
            not (mask >> first & 1 and mask >> second & 1)
            for first, second in edges
        ):
            groups[mask.bit_count()].append(mask)
    return tuple(tuple(group) for group in groups)


@dataclass(frozen=True)
class Merge:
    left: tuple[int, ...]
    right: tuple[int, ...]
    output: tuple[int, ...]
    clauses: tuple[Clause, ...]


@dataclass
class Formula:
    shell_edges: tuple[Edge, ...]
    shell_index: dict[Edge, int]
    variable_count: int
    clauses: list[Clause]
    category_counts: Counter[str]
    merges: list[Merge]

    @classmethod
    def create(cls) -> "Formula":
        shell_edges = tuple(itertools.combinations(range(SHELL_ORDER), 2))
        return cls(
            shell_edges=shell_edges,
            shell_index={edge: index for index, edge in enumerate(shell_edges)},
            variable_count=PRIMARY_VARIABLES,
            clauses=[],
            category_counts=Counter(),
            merges=[],
        )

    def shell_edge(self, first: int, second: int) -> int:
        if first > second:
            first, second = second, first
        return 1 + self.shell_index[(first, second)]

    def cross(self, shell_vertex: int, core_vertex: int) -> int:
        return (
            1
            + len(self.shell_edges)
            + CORE_ORDER * shell_vertex
            + core_vertex
        )

    def allocate(self, count: int) -> tuple[int, ...]:
        first = self.variable_count + 1
        self.variable_count += count
        return tuple(range(first, first + count))

    def add(self, category: str, clause: Iterable[int]) -> None:
        parsed = tuple(clause)
        self.clauses.append(parsed)
        self.category_counts[category] += 1

    def totalizer(
        self, literals: tuple[int, ...], cap: int, category: str
    ) -> tuple[int, ...]:
        if not literals or cap <= 0:
            fail("totalizer needs literals and a positive cap")
        if len(literals) == 1:
            return literals
        middle = len(literals) // 2
        left = self.totalizer(literals[:middle], cap, category)
        right = self.totalizer(literals[middle:], cap, category)
        output = self.allocate(min(cap, len(left) + len(right)))
        merge_clauses: list[Clause] = []
        for left_count in range(len(left) + 1):
            for right_count in range(len(right) + 1):
                total = left_count + right_count
                if 1 <= total <= len(output):
                    positive_clause = [output[total - 1]]
                    if left_count:
                        positive_clause.append(-left[left_count - 1])
                    if right_count:
                        positive_clause.append(-right[right_count - 1])
                    merge_clauses.append(tuple(positive_clause))
                if total + 1 <= len(output):
                    negative_clause = [-output[total]]
                    if left_count < len(left):
                        negative_clause.append(left[left_count])
                    if right_count < len(right):
                        negative_clause.append(right[right_count])
                    merge_clauses.append(tuple(negative_clause))
        for clause in merge_clauses:
            self.add(f"{category}_merge", clause)
        self.merges.append(Merge(left, right, output, tuple(merge_clauses)))
        return output

    def at_most(
        self, literals: Iterable[int], value: int, category: str
    ) -> None:
        parsed = tuple(literals)
        if value < 0:
            self.add(category, ())
            return
        if value >= len(parsed):
            return
        if value == 0:
            for literal in parsed:
                self.add(category, (-literal,))
            return
        direct_count = math.comb(len(parsed), value + 1)
        if direct_count <= 256:
            for chosen in itertools.combinations(parsed, value + 1):
                self.add(category, (-literal for literal in chosen))
            return
        outputs = self.totalizer(parsed, value + 1, category)
        self.add(f"{category}_root", (-outputs[value],))

    def at_least(
        self, literals: Iterable[int], value: int, category: str
    ) -> None:
        parsed = tuple(literals)
        if value <= 0:
            return
        if value > len(parsed):
            self.add(category, ())
            return
        outputs = self.totalizer(parsed, value, category)
        self.add(f"{category}_root", (outputs[value - 1],))

    def exactly(
        self, literals: Iterable[int], value: int, category: str
    ) -> None:
        parsed = tuple(literals)
        self.at_least(parsed, value, f"{category}_at_least")
        self.at_most(parsed, value, f"{category}_at_most")


def build_formula(case: Case) -> Formula:
    core = case.graph
    formula = Formula.create()
    shell_variables = tuple(
        formula.shell_edge(*edge) for edge in formula.shell_edges
    )
    all_cross = tuple(
        formula.cross(shell_vertex, core_vertex)
        for shell_vertex in range(SHELL_ORDER)
        for core_vertex in range(CORE_ORDER)
    )

    for shell_quadruple in itertools.combinations(range(SHELL_ORDER), 4):
        formula.add(
            "shell_independent_four",
            (
                -formula.shell_edge(first, second)
                for first, second in itertools.combinations(shell_quadruple, 2)
            ),
        )
    for shell_octuple in itertools.combinations(range(SHELL_ORDER), 8):
        formula.add(
            "v_shell_clique_nine",
            (
                formula.shell_edge(first, second)
                for first, second in itertools.combinations(shell_octuple, 2)
            ),
        )

    degree_outputs: list[tuple[int, ...]] = []
    for vertex in range(SHELL_ORDER):
        incident = tuple(
            formula.shell_edge(vertex, other)
            for other in range(SHELL_ORDER)
            if other != vertex
        )
        degree_outputs.append(
            formula.totalizer(incident, SHELL_ORDER - 1, "symmetry_degree")
        )
    for first, second in zip(degree_outputs, degree_outputs[1:]):
        for first_at_least, second_at_least in zip(first, second, strict=True):
            formula.add(
                "symmetry_degree_order",
                (-second_at_least, first_at_least),
            )

    fixed_edges = SHELL_ORDER + math.comb(CORE_ORDER, 2) - case.edge_count
    formula.exactly(
        (*all_cross, *(-literal for literal in shell_variables)),
        EDGE_CAP - fixed_edges,
        "total_target_edges",
    )

    for shell_vertex in range(SHELL_ORDER):
        row = tuple(
            formula.cross(shell_vertex, core_vertex)
            for core_vertex in range(CORE_ORDER)
        )
        incident_h = tuple(
            -formula.shell_edge(shell_vertex, other)
            for other in range(SHELL_ORDER)
            if other != shell_vertex
        )
        formula.exactly(
            (*row, *incident_h),
            SHELL_ORDER - 1,
            "shell_target_degree",
        )

    for core_vertex in range(CORE_ORDER):
        column = tuple(
            formula.cross(shell_vertex, core_vertex)
            for shell_vertex in range(SHELL_ORDER)
        )
        required = DEGREE - (CORE_ORDER - 1 - core.degree(core_vertex))
        formula.exactly(column, required, "core_target_degree")

    for first_shell, second_shell in formula.shell_edges:
        shell_edge = formula.shell_edge(first_shell, second_shell)
        for first_core, second_core in core.edges:
            formula.add(
                "mixed_independent_four_2_2",
                (
                    -shell_edge,
                    formula.cross(first_shell, first_core),
                    formula.cross(first_shell, second_core),
                    formula.cross(second_shell, first_core),
                    formula.cross(second_shell, second_core),
                ),
            )

    for shell_triple in itertools.combinations(range(SHELL_ORDER), 3):
        triangle_edges = tuple(
            formula.shell_edge(first, second)
            for first, second in itertools.combinations(shell_triple, 2)
        )
        for core_vertex in range(CORE_ORDER):
            formula.add(
                "mixed_independent_four_3_1",
                (
                    *(-literal for literal in triangle_edges),
                    *(
                        formula.cross(shell_vertex, core_vertex)
                        for shell_vertex in shell_triple
                    ),
                ),
            )

    core_independent = independent_masks(core)
    shell_masks_by_size = tuple(
        tuple(
            sum(1 << vertex for vertex in vertices)
            for vertices in itertools.combinations(range(SHELL_ORDER), size)
        )
        for size in range(SHELL_ORDER + 1)
    )
    for shell_size in range(1, 9):
        core_size = 9 - shell_size
        for shell_mask in shell_masks_by_size[shell_size]:
            shell_vertices = tuple(
                vertex
                for vertex in range(SHELL_ORDER)
                if shell_mask >> vertex & 1
            )
            shell_f_edges = tuple(
                formula.shell_edge(first, second)
                for first, second in itertools.combinations(shell_vertices, 2)
            )
            for core_mask in core_independent[core_size]:
                missing_cross = tuple(
                    -formula.cross(shell_vertex, core_vertex)
                    for shell_vertex in shell_vertices
                    for core_vertex in range(CORE_ORDER)
                    if core_mask >> core_vertex & 1
                )
                formula.add(
                    "mixed_target_clique_nine",
                    (*shell_f_edges, *missing_cross),
                )

    # The 11-set {v} union A has target cap D_9(11)=39.
    formula.at_most(
        (-literal for literal in shell_variables),
        29,
        "full_color_v_shell_order_11",
    )
    # Ten-regularity gives f=m-40.
    formula.exactly(
        shell_variables,
        case.edge_count - 40,
        "shell_complement_edge_count",
    )
    # Every ten-set {v} union (A minus a) has at most 37 target edges.
    for excluded in range(SHELL_ORDER):
        away = tuple(
            formula.shell_edge(first, second)
            for first, second in formula.shell_edges
            if excluded not in (first, second)
        )
        formula.at_least(away, 8, "local_v_shell_minus_one")

    return formula


def write_dimacs(path: Path, formula: Formula) -> None:
    with path.open("w", encoding="ascii") as handle:
        handle.write(f"p cnf {formula.variable_count} {len(formula.clauses)}\n")
        for clause in formula.clauses:
            handle.write(" ".join(map(str, clause)) + " 0\n")


def deterministic_gzip(source: Path, target: Path) -> None:
    with source.open("rb") as input_handle, target.open("wb") as raw_output:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=raw_output, compresslevel=9, mtime=0
        ) as output_handle:
            shutil.copyfileobj(input_handle, output_handle)


def run_checked(command: list[str], label: str) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        fail(
            f"{label} failed with exit code {result.returncode}:\n"
            f"{result.stdout}{result.stderr}"
        )
    return result


def prove_case(
    cnf: Path,
    case_root: Path,
    solver: Path,
    drat_trim: Path,
    lrat_check: Path,
    seconds: int,
) -> dict[str, object]:
    drat = case_root / "proof.drat"
    lrat = case_root / "proof.lrat"
    solve = subprocess.run(
        [
            str(solver),
            "-q",
            "--no-binary",
            f"--time={seconds}",
            str(cnf),
            str(drat),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if solve.returncode != 20:
        fail(
            f"solver did not prove UNSAT, exit code {solve.returncode}:\n"
            f"{solve.stdout}{solve.stderr}"
        )
    conversion = run_checked(
        [str(drat_trim), str(cnf), str(drat), "-L", str(lrat)],
        "DRAT-to-LRAT conversion",
    )
    replay = run_checked(
        [str(lrat_check), str(cnf), str(lrat)],
        "LRAT replay",
    )
    replay_text = replay.stdout + replay.stderr
    if "VERIFIED" not in replay_text:
        fail(f"LRAT checker did not report VERIFIED:\n{replay_text}")
    (case_root / "solve.out").write_text(
        solve.stdout + solve.stderr, encoding="utf-8"
    )
    (case_root / "convert.out").write_text(
        conversion.stdout + conversion.stderr, encoding="utf-8"
    )
    (case_root / "replay.out").write_text(replay_text, encoding="utf-8")
    return {
        "solver_exit_code": solve.returncode,
        "lrat_replay": "VERIFIED",
        "drat": file_record(drat, case_root),
        "lrat": file_record(lrat, case_root),
        "solve_log": file_record(case_root / "solve.out", case_root),
        "conversion_log": file_record(case_root / "convert.out", case_root),
        "replay_log": file_record(case_root / "replay.out", case_root),
    }


def source_record(path: Path) -> dict[str, object]:
    return {
        "repository_path": f"{REPOSITORY_PREFIX}/{path.name}",
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def binary_record(path: Path) -> dict[str, object]:
    return {
        "name": path.name,
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def build_manifest(
    cases: tuple[Case, ...],
    selected: tuple[int, ...],
    emitted: list[dict[str, object]],
    geng: Path,
    proof_toolchain: dict[str, object] | None,
) -> dict[str, object]:
    source = Path(__file__).resolve()
    verifier = source.with_name("verify_r9_p93_d10_certificate.py")
    all_lrat = len(emitted) == EXPECTED_CASES and all(
        entry.get("proof_status") == "LRAT_VERIFIED" for entry in emitted
    )
    reduced_indices = reduced_core_indices(cases)
    reduced_lrat = tuple(selected) == reduced_indices and all(
        entry.get("proof_status") == "LRAT_VERIFIED" for entry in emitted
    )
    all_cnfs = len(emitted) == EXPECTED_CASES
    if all_lrat:
        status = "ALL_CASES_LRAT_GENERATED_AND_REPLAYED"
    elif reduced_lrat:
        status = "ALL_REDUCED_CASES_LRAT_GENERATED_AND_REPLAYED"
    elif all_cnfs:
        status = "ALL_CNFS_EMITTED"
    elif emitted:
        status = "PARTIAL_ARTIFACTS"
    else:
        status = "ARCHITECTURE_ONLY"
    return {
        "schema_version": SCHEMA_VERSION,
        "package_id": "erdos-617-r9-p93-d10",
        "status": status,
        "claim_target": (
            "No actual 27-vertex target-color graph in the fixed r=9 "
            "P3 branch has minimum degree 10."
        ),
        "nonclaims": [
            "A catalog or CNF without checked LRAT proofs does not prove the d=10 family.",
            "The d=10 family alone does not prove the fixed r=9 case.",
            "This package does not prove the universal statement in Erdos Problem 617.",
            "No artifact represented here has been externally reviewed or published.",
        ],
        "case_generation": {
            "command": [
                "geng",
                "-q",
                "-t",
                "-d5",
                "-D8",
                "16",
                "56:64",
            ],
            "expected_valid_cases": EXPECTED_CASES,
            "ordering": "lexicographic graph6 after the semantic core filter",
            "geng_sha256": sha256(geng),
        },
        "selection": {"indices": list(selected)},
        "degree_sum_reduction": {
            "threshold": REDUCED_EDGE_DEGREE_SUM,
            "expected_survivors": EXPECTED_REDUCED_CASES,
            "survivor_index_sha256": EXPECTED_REDUCED_INDEX_SHA256,
            "theorem_source": (
                f"{REPOSITORY_PREFIX}/R9_P93_D10_CORE_DEGREE_SUM_REDUCTION.md"
            ),
            "verifier_source": (
                f"{REPOSITORY_PREFIX}/verify_r9_p93_d10_core_degree_sum.py"
            ),
        },
        "formula": {
            "primary_variables": PRIMARY_VARIABLES,
            "shell_variables": 45,
            "cross_variables": 160,
            "meaning": (
                "Shell variables are edges of F=complement(H[A]); cross "
                "variables are target H-edges from A to B."
            ),
            "lazy_ten_set_cuts": 0,
            "relaxation_note": (
                "Mixed higher-order full-color constraints and explicit "
                "nontarget color decomposition are omitted."
            ),
        },
        "sources": {
            "generator": source_record(source),
            "semantic_verifier": source_record(verifier),
        },
        "proof_toolchain": proof_toolchain,
        "cases": [
            {
                "index": case.index,
                "case_id": case.case_id,
                "graph6": case.graph6,
                "core_edges": case.edge_count,
                "core_degree_sequence": sorted(
                    (degree for _, degree in case.graph.degree()), reverse=True
                ),
            }
            for case in cases
        ],
        "emitted": emitted,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--case-index", type=int, action="append", default=[])
    parser.add_argument("--all-cases", action="store_true")
    parser.add_argument("--degree-sum-survivors", action="store_true")
    parser.add_argument("--residue", type=int)
    parser.add_argument("--modulus", type=int)
    parser.add_argument("--emit-cnf", action="store_true")
    parser.add_argument("--prove", action="store_true")
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--drat-trim", type=Path)
    parser.add_argument("--lrat-check", type=Path)
    parser.add_argument("--seconds", type=int, default=3600)
    parser.add_argument("--compress", action="store_true")
    args = parser.parse_args()

    if args.prove and not all(
        value is not None for value in (args.solver, args.drat_trim, args.lrat_check)
    ):
        parser.error("--prove requires --solver, --drat-trim, and --lrat-check")
    if args.all_cases and args.prove:
        parser.error("prove all cases through an explicit per-shard invocation")
    if (args.residue is None) != (args.modulus is None):
        parser.error("--residue and --modulus must be supplied together")
    if args.modulus is not None and args.modulus <= 0:
        parser.error("--modulus must be positive")
    if args.residue is not None and not 0 <= args.residue < args.modulus:
        parser.error("--residue must lie in 0..modulus-1")
    if args.residue is not None and args.modulus is None:
        parser.error("--residue requires --modulus")
    if args.modulus is not None and args.residue is None:
        parser.error("--modulus requires --residue")
    if args.modulus is not None and (
        args.modulus <= 0 or not 0 <= args.residue < args.modulus
    ):
        parser.error("need 0 <= residue < modulus")
    if sum((bool(args.case_index), args.all_cases, args.degree_sum_survivors)) > 1:
        parser.error(
            "choose only one of --case-index, --all-cases, or "
            "--degree-sum-survivors"
        )
    if args.residue is not None and (args.case_index or args.all_cases):
        parser.error("sharding may be combined only with degree-sum survivors")

    cases = generate_cases(args.geng)
    args.output.mkdir(parents=True, exist_ok=True)
    if args.degree_sum_survivors:
        selected = reduced_core_indices(cases)
        if args.residue is not None:
            selected = tuple(
                index for index in selected if index % args.modulus == args.residue
            )
    elif args.all_cases:
        selected = tuple(range(len(cases)))
    elif args.residue is not None:
        selected = tuple(
            index
            for index in range(len(cases))
            if index % args.modulus == args.residue
        )
    else:
        selected = tuple(sorted(set(args.case_index)))
    if any(index < 0 or index >= len(cases) for index in selected):
        parser.error(f"case index must lie in 0..{len(cases) - 1}")

    emitted: list[dict[str, object]] = []
    if args.emit_cnf or args.prove:
        for index in selected:
            case = cases[index]
            case_root = args.output / case.directory_name
            case_root.mkdir(parents=True, exist_ok=True)
            formula = build_formula(case)
            cnf = case_root / "formula.cnf"
            write_dimacs(cnf, formula)
            entry: dict[str, object] = {
                "index": case.index,
                "case_id": case.case_id,
                "graph6": case.graph6,
                "variables": formula.variable_count,
                "clauses": len(formula.clauses),
                "category_counts": dict(sorted(formula.category_counts.items())),
                "cnf": file_record(cnf, args.output),
                "proof_status": "NOT_GENERATED",
            }
            if args.prove:
                assert args.solver is not None
                assert args.drat_trim is not None
                assert args.lrat_check is not None
                entry["proof"] = prove_case(
                    cnf,
                    case_root,
                    args.solver,
                    args.drat_trim,
                    args.lrat_check,
                    args.seconds,
                )
                entry["proof_status"] = "LRAT_VERIFIED"
            if args.compress:
                compressed_cnf = cnf.with_suffix(".cnf.gz")
                deterministic_gzip(cnf, compressed_cnf)
                entry["cnf_gzip"] = file_record(compressed_cnf, args.output)
                if args.prove:
                    lrat = case_root / "proof.lrat"
                    compressed_lrat = lrat.with_suffix(".lrat.gz")
                    deterministic_gzip(lrat, compressed_lrat)
                    entry["lrat_gzip"] = file_record(compressed_lrat, args.output)
            emitted.append(entry)
            print(
                f"emitted case={case.index} id={case.case_id} "
                f"vars={formula.variable_count} clauses={len(formula.clauses)}",
                flush=True,
            )

    proof_toolchain: dict[str, object] | None = None
    if args.prove:
        assert args.solver is not None
        assert args.drat_trim is not None
        assert args.lrat_check is not None
        proof_toolchain = {
            "solver": binary_record(args.solver),
            "drat_trim": binary_record(args.drat_trim),
            "lrat_check": binary_record(args.lrat_check),
            "solver_seconds_per_case": args.seconds,
            "solver_command": [
                args.solver.name,
                "-q",
                "--no-binary",
                f"--time={args.seconds}",
                "{cnf}",
                "{drat}",
            ],
            "conversion_command": [
                args.drat_trim.name,
                "{cnf}",
                "{drat}",
                "-L",
                "{lrat}",
            ],
            "replay_command": [args.lrat_check.name, "{cnf}", "{lrat}"],
        }
    manifest = build_manifest(
        cases, selected, emitted, args.geng, proof_toolchain
    )
    manifest_path = args.output / "manifest.json"
    canonical_json(manifest_path, manifest)
    manifest_digest_path = args.output / "manifest.sha256"
    manifest_digest_path.write_text(
        f"{sha256(manifest_path)}  manifest.json\n", encoding="ascii"
    )
    print(
        f"cases={len(cases)} emitted={len(emitted)} manifest={manifest_path}",
        flush=True,
    )


if __name__ == "__main__":
    main()
