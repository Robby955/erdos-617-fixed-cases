#!/usr/bin/env python3
"""Independent semantic verifier for the r=9, P3(27), d=10 package.

This verifier does not import the exploratory scout or the certificate
generator.  It reconstructs the 332 core cases, rebuilds each emitted CNF,
compares clause multisets, checks the threshold meaning of every totalizer
merge, validates artifact hashes, and optionally replays LRAT proofs.
"""

from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
from dataclasses import dataclass
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import shutil
import subprocess
import tempfile
from typing import Iterable, Iterator, Mapping, NoReturn

import networkx as nx  # type: ignore[import-untyped]


Clause = tuple[int, ...]
Edge = tuple[int, int]

R = 9
SHELL_ORDER = 10
CORE_ORDER = 16
EXPECTED_CASES = 332
EXPECTED_REDUCED_CASES = 50
REDUCED_EDGE_DEGREE_SUM = 13
EXPECTED_REDUCED_INDEX_SHA256 = (
    "e9c743eef1f89309733e1a4eaecd74fb6af862a55dd457dfee8b2604bf30037f"
)
PRIMARY_VARIABLES = 205


def fail(message: str) -> NoReturn:
    raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def normalized(clause: Iterable[int]) -> Clause:
    return tuple(sorted(clause, key=lambda literal: (abs(literal), literal < 0)))


def p9(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1, 2
    )


def edge_masks(graph: nx.Graph) -> tuple[int, ...]:
    masks = [0] * graph.number_of_nodes()
    for first, second in graph.edges:
        masks[first] |= 1 << second
        masks[second] |= 1 << first
    return tuple(masks)


def mask_is_independent(mask: int, adjacency: tuple[int, ...]) -> bool:
    vertices = tuple(
        vertex for vertex in range(len(adjacency)) if mask >> vertex & 1
    )
    return all(
        not (adjacency[first] >> second & 1)
        for first, second in itertools.combinations(vertices, 2)
    )


def mask_edge_count(mask: int, adjacency: tuple[int, ...]) -> int:
    return sum(
        (adjacency[vertex] & mask).bit_count()
        for vertex in range(len(adjacency))
        if mask >> vertex & 1
    ) // 2


def core_is_valid(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    degrees = tuple(degree for _, degree in graph.degree())
    if min(degrees) < 5 or max(degrees) > 8:
        return False
    for first, second, third in itertools.combinations(range(CORE_ORDER), 3):
        if (
            graph.has_edge(first, second)
            and graph.has_edge(first, third)
            and graph.has_edge(second, third)
        ):
            return False
    adjacency = edge_masks(graph)
    for vertices in itertools.combinations(range(CORE_ORDER), 9):
        mask = sum(1 << vertex for vertex in vertices)
        if mask_is_independent(mask, adjacency):
            return False
    for size in range(10, CORE_ORDER + 1):
        required = 8 * p9(size)
        for vertices in itertools.combinations(range(CORE_ORDER), size):
            mask = sum(1 << vertex for vertex in vertices)
            if mask_edge_count(mask, adjacency) < required:
                return False
    return True


@dataclass(frozen=True)
class VerifiedCase:
    index: int
    graph6: str
    graph: nx.Graph

    @property
    def case_id(self) -> str:
        return hashlib.sha256(self.graph6.encode("ascii")).hexdigest()[:16]


def reconstruct_cases(geng: Path) -> tuple[VerifiedCase, ...]:
    command = [
        str(geng),
        "-q",
        "-t",
        "-d5",
        "-D8",
        str(CORE_ORDER),
        "56:64",
    ]
    lines: list[str] = []
    for raw_line in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(raw_line)
        if core_is_valid(graph):
            lines.append(raw_line.decode("ascii"))
    lines.sort()
    if len(lines) != EXPECTED_CASES:
        fail(f"expected {EXPECTED_CASES} valid cases, found {len(lines)}")
    return tuple(
        VerifiedCase(index, line, nx.from_graph6_bytes(line.encode("ascii")))
        for index, line in enumerate(lines)
    )


def reduced_core_indices(cases: tuple[VerifiedCase, ...]) -> tuple[int, ...]:
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


def read_dimacs(path: Path) -> tuple[int, list[Clause]]:
    header: tuple[int, int] | None = None
    tokens: list[int] = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="ascii").splitlines(), start=1
    ):
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            if header is not None:
                fail(f"second DIMACS header at line {line_number}")
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                fail(f"bad DIMACS header at line {line_number}: {line}")
            header = (int(fields[2]), int(fields[3]))
            continue
        if header is None:
            fail(f"clause before header at line {line_number}")
        tokens.extend(int(token) for token in line.split())
    if header is None:
        fail("missing DIMACS header")
    clauses: list[Clause] = []
    current: list[int] = []
    for token in tokens:
        if token == 0:
            clauses.append(tuple(current))
            current = []
        else:
            current.append(token)
    if current:
        fail("unterminated final DIMACS clause")
    if len(clauses) != header[1]:
        fail(f"header has {header[1]} clauses, parsed {len(clauses)}")
    for index, clause in enumerate(clauses):
        if not clause:
            fail(f"empty clause at index {index}")
        if any(abs(literal) > header[0] for literal in clause):
            fail(f"variable above header bound in clause {index}")
        if len(set(clause)) != len(clause):
            fail(f"repeated literal in clause {index}")
        if any(-literal in clause for literal in clause):
            fail(f"tautological clause at index {index}")
    return header[0], clauses


@dataclass(frozen=True)
class Merge:
    left: tuple[int, ...]
    right: tuple[int, ...]
    output: tuple[int, ...]
    clauses: tuple[Clause, ...]


@dataclass
class Reference:
    shell_edges: tuple[Edge, ...]
    edge_to_variable: dict[Edge, int]
    next_variable: int
    clauses: list[Clause]
    categories: Counter[str]
    merges: list[Merge]

    @classmethod
    def create(cls) -> "Reference":
        shell_edges = tuple(itertools.combinations(range(SHELL_ORDER), 2))
        return cls(
            shell_edges=shell_edges,
            edge_to_variable={edge: index for index, edge in enumerate(shell_edges, 1)},
            next_variable=PRIMARY_VARIABLES + 1,
            clauses=[],
            categories=Counter(),
            merges=[],
        )

    @property
    def variable_count(self) -> int:
        return self.next_variable - 1

    def shell(self, first: int, second: int) -> int:
        if first > second:
            first, second = second, first
        return self.edge_to_variable[(first, second)]

    def cross(self, shell_vertex: int, core_vertex: int) -> int:
        return 46 + CORE_ORDER * shell_vertex + core_vertex

    def allocate(self, count: int) -> tuple[int, ...]:
        result = tuple(range(self.next_variable, self.next_variable + count))
        self.next_variable += count
        return result

    def add(self, category: str, clause: Iterable[int]) -> None:
        self.clauses.append(tuple(clause))
        self.categories[category] += 1

    def totalizer(
        self, inputs: tuple[int, ...], cap: int, category: str
    ) -> tuple[int, ...]:
        if len(inputs) == 1:
            return inputs
        middle = len(inputs) // 2
        left = self.totalizer(inputs[:middle], cap, category)
        right = self.totalizer(inputs[middle:], cap, category)
        output = self.allocate(min(cap, len(left) + len(right)))
        clauses: list[Clause] = []
        for left_count in range(len(left) + 1):
            for right_count in range(len(right) + 1):
                total = left_count + right_count
                if 1 <= total <= len(output):
                    positive_clause = [output[total - 1]]
                    if left_count:
                        positive_clause.append(-left[left_count - 1])
                    if right_count:
                        positive_clause.append(-right[right_count - 1])
                    clauses.append(tuple(positive_clause))
                if total + 1 <= len(output):
                    negative_clause = [-output[total]]
                    if left_count < len(left):
                        negative_clause.append(left[left_count])
                    if right_count < len(right):
                        negative_clause.append(right[right_count])
                    clauses.append(tuple(negative_clause))
        for clause in clauses:
            self.add(f"{category}_merge", clause)
        self.merges.append(Merge(left, right, output, tuple(clauses)))
        return output

    def at_most(self, inputs: Iterable[int], bound: int, category: str) -> None:
        literals = tuple(inputs)
        if bound >= len(literals):
            return
        if bound == 0:
            for literal in literals:
                self.add(category, (-literal,))
            return
        direct_count = math.comb(len(literals), bound + 1)
        if direct_count <= 256:
            for chosen in itertools.combinations(literals, bound + 1):
                self.add(category, (-literal for literal in chosen))
            return
        output = self.totalizer(literals, bound + 1, category)
        self.add(f"{category}_root", (-output[bound],))

    def at_least(self, inputs: Iterable[int], bound: int, category: str) -> None:
        literals = tuple(inputs)
        if bound <= 0:
            return
        if bound > len(literals):
            self.add(category, ())
            return
        output = self.totalizer(literals, bound, category)
        self.add(f"{category}_root", (output[bound - 1],))

    def exactly(self, inputs: Iterable[int], value: int, category: str) -> None:
        literals = tuple(inputs)
        self.at_least(literals, value, f"{category}_at_least")
        self.at_most(literals, value, f"{category}_at_most")


def core_independent_masks(graph: nx.Graph) -> tuple[tuple[int, ...], ...]:
    groups: list[list[int]] = [[] for _ in range(CORE_ORDER + 1)]
    adjacency = edge_masks(graph)
    for mask in range(1, 1 << CORE_ORDER):
        if mask_is_independent(mask, adjacency):
            groups[mask.bit_count()].append(mask)
    return tuple(tuple(group) for group in groups)


def build_reference(case: VerifiedCase) -> Reference:
    core = case.graph
    reference = Reference.create()
    shell_variables = tuple(reference.shell(*edge) for edge in reference.shell_edges)
    cross_variables = tuple(
        reference.cross(shell_vertex, core_vertex)
        for shell_vertex in range(SHELL_ORDER)
        for core_vertex in range(CORE_ORDER)
    )

    for shell_quadruple in itertools.combinations(range(SHELL_ORDER), 4):
        reference.add(
            "shell_independent_four",
            (
                -reference.shell(first, second)
                for first, second in itertools.combinations(shell_quadruple, 2)
            ),
        )
    for shell_octuple in itertools.combinations(range(SHELL_ORDER), 8):
        reference.add(
            "v_shell_clique_nine",
            (
                reference.shell(first, second)
                for first, second in itertools.combinations(shell_octuple, 2)
            ),
        )

    roots: list[tuple[int, ...]] = []
    for vertex in range(SHELL_ORDER):
        incident = tuple(
            reference.shell(vertex, other)
            for other in range(SHELL_ORDER)
            if other != vertex
        )
        roots.append(reference.totalizer(incident, 9, "symmetry_degree"))
    for first, second in zip(roots, roots[1:]):
        for first_bit, second_bit in zip(first, second, strict=True):
            reference.add("symmetry_degree_order", (-second_bit, first_bit))

    fixed = 10 + math.comb(CORE_ORDER, 2) - core.number_of_edges()
    reference.exactly(
        (*cross_variables, *(-literal for literal in shell_variables)),
        135 - fixed,
        "total_target_edges",
    )
    for shell_vertex in range(SHELL_ORDER):
        row = tuple(
            reference.cross(shell_vertex, core_vertex)
            for core_vertex in range(CORE_ORDER)
        )
        incident_h = tuple(
            -reference.shell(shell_vertex, other)
            for other in range(SHELL_ORDER)
            if other != shell_vertex
        )
        reference.exactly(
            (*row, *incident_h), 9, "shell_target_degree"
        )
    for core_vertex in range(CORE_ORDER):
        column = tuple(
            reference.cross(shell_vertex, core_vertex)
            for shell_vertex in range(SHELL_ORDER)
        )
        reference.exactly(
            column,
            core.degree(core_vertex) - 5,
            "core_target_degree",
        )

    for first_shell, second_shell in reference.shell_edges:
        shell_edge = reference.shell(first_shell, second_shell)
        for first_core, second_core in core.edges:
            reference.add(
                "mixed_independent_four_2_2",
                (
                    -shell_edge,
                    reference.cross(first_shell, first_core),
                    reference.cross(first_shell, second_core),
                    reference.cross(second_shell, first_core),
                    reference.cross(second_shell, second_core),
                ),
            )
    for triple in itertools.combinations(range(SHELL_ORDER), 3):
        triangle = tuple(
            reference.shell(first, second)
            for first, second in itertools.combinations(triple, 2)
        )
        for core_vertex in range(CORE_ORDER):
            reference.add(
                "mixed_independent_four_3_1",
                (
                    *(-literal for literal in triangle),
                    *(
                        reference.cross(shell_vertex, core_vertex)
                        for shell_vertex in triple
                    ),
                ),
            )

    independent_by_size = core_independent_masks(core)
    for shell_size in range(1, 9):
        core_size = 9 - shell_size
        for shell_vertices in itertools.combinations(range(SHELL_ORDER), shell_size):
            shell_edges = tuple(
                reference.shell(first, second)
                for first, second in itertools.combinations(shell_vertices, 2)
            )
            for core_mask in independent_by_size[core_size]:
                reference.add(
                    "mixed_target_clique_nine",
                    (
                        *shell_edges,
                        *(
                            -reference.cross(shell_vertex, core_vertex)
                            for shell_vertex in shell_vertices
                            for core_vertex in range(CORE_ORDER)
                            if core_mask >> core_vertex & 1
                        ),
                    ),
                )

    reference.at_most(
        (-literal for literal in shell_variables),
        29,
        "full_color_v_shell_order_11",
    )
    reference.exactly(
        shell_variables,
        core.number_of_edges() - 40,
        "shell_complement_edge_count",
    )
    for excluded in range(SHELL_ORDER):
        away = tuple(
            reference.shell(first, second)
            for first, second in reference.shell_edges
            if excluded not in (first, second)
        )
        reference.at_least(away, 8, "local_v_shell_minus_one")
    return reference


def expected_merge_clauses(merge: Merge) -> tuple[Clause, ...]:
    expected: list[Clause] = []
    for left_count in range(len(merge.left) + 1):
        for right_count in range(len(merge.right) + 1):
            total = left_count + right_count
            if 1 <= total <= len(merge.output):
                positive = [merge.output[total - 1]]
                if left_count:
                    positive.append(-merge.left[left_count - 1])
                if right_count:
                    positive.append(-merge.right[right_count - 1])
                expected.append(tuple(positive))
            if total + 1 <= len(merge.output):
                negative = [-merge.output[total]]
                if left_count < len(merge.left):
                    negative.append(merge.left[left_count])
                if right_count < len(merge.right):
                    negative.append(merge.right[right_count])
                expected.append(tuple(negative))
    return tuple(expected)


def audit_merge_shape(merge: Merge) -> int:
    clauses = {normalized(clause) for clause in merge.clauses}
    states = 0
    for left_count in range(len(merge.left) + 1):
        for right_count in range(len(merge.right) + 1):
            total = left_count + right_count
            for output_count in range(1, len(merge.output) + 1):
                if output_count <= total:
                    witness_left = max(0, output_count - right_count)
                    witness_right = output_count - witness_left
                    if witness_left > left_count or witness_right > right_count:
                        fail("positive totalizer witness is out of range")
                    witness = [merge.output[output_count - 1]]
                    if witness_left:
                        witness.append(-merge.left[witness_left - 1])
                    if witness_right:
                        witness.append(-merge.right[witness_right - 1])
                else:
                    witness_left = max(
                        left_count, output_count - 1 - len(merge.right)
                    )
                    witness_right = output_count - 1 - witness_left
                    if (
                        witness_left > len(merge.left)
                        or witness_right < right_count
                        or witness_right > len(merge.right)
                    ):
                        fail("negative totalizer witness is out of range")
                    witness = [-merge.output[output_count - 1]]
                    if witness_left < len(merge.left):
                        witness.append(merge.left[witness_left])
                    if witness_right < len(merge.right):
                        witness.append(merge.right[witness_right])
                if normalized(witness) not in clauses:
                    fail(
                        "totalizer lacks a forcing clause for counts "
                        f"({left_count},{right_count}) and output "
                        f"{output_count}"
                    )
            states += 1
    return states


def audit_merges(
    merges: list[Merge], audited_shapes: set[tuple[int, int, int]]
) -> int:
    states = 0
    for merge_index, merge in enumerate(merges):
        expected = expected_merge_clauses(merge)
        if Counter(map(normalized, expected)) != Counter(
            map(normalized, merge.clauses)
        ):
            fail(f"merge {merge_index} does not have the exact unary schema")
        shape = (len(merge.left), len(merge.right), len(merge.output))
        if shape not in audited_shapes:
            states += audit_merge_shape(merge)
            audited_shapes.add(shape)
    return states


def verify_record(root: Path, record: Mapping[str, object]) -> Path:
    relative = Path(str(record["path"]))
    if relative.is_absolute() or ".." in relative.parts:
        fail(f"unsafe artifact path: {relative}")
    path = root / relative
    if not path.is_file():
        fail(f"missing artifact: {path}")
    expected_bytes = record["bytes"]
    if not isinstance(expected_bytes, int):
        fail(f"invalid byte count in record for {path}")
    if path.stat().st_size != expected_bytes:
        fail(f"size mismatch: {path}")
    expected_sha256 = record["sha256"]
    if not isinstance(expected_sha256, str) or len(expected_sha256) != 64:
        fail(f"invalid SHA-256 record for {path}")
    if sha256(path) != expected_sha256:
        fail(f"SHA-256 mismatch: {path}")
    return path


def verify_source_record(record: Mapping[str, object], source: Path) -> None:
    if record.get("repository_path") != f"research/erdos-617-r6/{source.name}":
        fail(f"source path mismatch for {source.name}")
    expected_bytes = record.get("bytes")
    if not isinstance(expected_bytes, int) or expected_bytes != source.stat().st_size:
        fail(f"source byte count mismatch for {source.name}")
    if record.get("sha256") != sha256(source):
        fail(f"source SHA-256 mismatch for {source.name}")


def verify_manifest_digest(package: Path, manifest_path: Path) -> None:
    digest_path = package / "manifest.sha256"
    if not digest_path.is_file():
        fail(f"missing manifest digest: {digest_path}")
    fields = digest_path.read_text(encoding="ascii").split()
    if fields != [sha256(manifest_path), "manifest.json"]:
        fail(f"manifest digest mismatch: {digest_path}")


@contextmanager
def materialized(path: Path) -> Iterator[Path]:
    if path.suffix != ".gz":
        yield path
        return
    with tempfile.TemporaryDirectory(prefix="r9-p93-d10-") as directory:
        target = Path(directory) / path.stem
        with gzip.open(path, "rb") as source, target.open("wb") as output:
            shutil.copyfileobj(source, output)
        yield target


def replay_lrat(checker: Path, cnf: Path, lrat: Path) -> None:
    result = subprocess.run(
        [str(checker), str(cnf), str(lrat)],
        check=False,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    if result.returncode != 0 or "VERIFIED" not in output:
        fail(f"LRAT replay failed:\n{output}")


def verify_case_catalog(
    manifest: Mapping[str, object], cases: tuple[VerifiedCase, ...]
) -> None:
    listed = manifest["cases"]
    if not isinstance(listed, list) or len(listed) != len(cases):
        fail("case catalog has the wrong length")
    for expected, record in zip(cases, listed, strict=True):
        if not isinstance(record, dict):
            fail("case catalog entry is not an object")
        degree_sequence = sorted(
            (degree for _, degree in expected.graph.degree()), reverse=True
        )
        wanted = {
            "index": expected.index,
            "case_id": expected.case_id,
            "graph6": expected.graph6,
            "core_edges": expected.graph.number_of_edges(),
            "core_degree_sequence": degree_sequence,
        }
        if record != wanted:
            fail(f"case catalog mismatch at index {expected.index}")


def verify_manifest_header(
    manifest: Mapping[str, object], geng: Path
) -> None:
    if manifest.get("schema_version") != 1:
        fail("unsupported manifest schema")
    if manifest.get("package_id") != "erdos-617-r9-p93-d10":
        fail("unexpected package identifier")
    nonclaims = manifest.get("nonclaims")
    if not isinstance(nonclaims, list) or not any(
        "universal" in str(item).lower() for item in nonclaims
    ):
        fail("manifest lacks the universal nonclaim")
    if not any("fixed r=9" in str(item).lower() for item in nonclaims):
        fail("manifest lacks the fixed-r=9 nonclaim")
    generation = manifest.get("case_generation")
    if not isinstance(generation, dict):
        fail("manifest case-generation field is not an object")
    wanted_command = ["geng", "-q", "-t", "-d5", "-D8", "16", "56:64"]
    if generation.get("command") != wanted_command:
        fail("manifest geng command mismatch")
    if generation.get("expected_valid_cases") != EXPECTED_CASES:
        fail("manifest expected-case count mismatch")
    if generation.get("geng_sha256") != sha256(geng):
        fail("manifest geng binary hash mismatch")
    formula = manifest.get("formula")
    if not isinstance(formula, dict):
        fail("manifest formula field is not an object")
    if formula.get("primary_variables") != PRIMARY_VARIABLES:
        fail("manifest primary-variable count mismatch")
    if formula.get("shell_variables") != 45 or formula.get("cross_variables") != 160:
        fail("manifest primary-variable split mismatch")
    if formula.get("lazy_ten_set_cuts") != 0:
        fail("manifest does not describe the round-zero relaxation")
    reduction = manifest.get("degree_sum_reduction")
    if not isinstance(reduction, dict):
        fail("manifest degree-sum reduction field is not an object")
    if (
        reduction.get("threshold") != REDUCED_EDGE_DEGREE_SUM
        or reduction.get("expected_survivors") != EXPECTED_REDUCED_CASES
        or reduction.get("survivor_index_sha256")
        != EXPECTED_REDUCED_INDEX_SHA256
    ):
        fail("manifest degree-sum reduction metadata mismatch")


def verify_binary_metadata(record: Mapping[str, object], label: str) -> None:
    if not isinstance(record.get("name"), str):
        fail(f"invalid {label} binary name")
    if not isinstance(record.get("bytes"), int):
        fail(f"invalid {label} binary byte count")
    digest = record.get("sha256")
    if not isinstance(digest, str) or len(digest) != 64:
        fail(f"invalid {label} binary SHA-256")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--package", type=Path, action="append", required=True)
    parser.add_argument("--lrat-check", type=Path)
    parser.add_argument("--require-all", action="store_true")
    parser.add_argument("--require-degree-sum-survivors", action="store_true")
    parser.add_argument("--require-lrat", action="store_true")
    args = parser.parse_args()

    if args.require_lrat and args.lrat_check is None:
        parser.error("--require-lrat needs --lrat-check")
    if args.require_all and args.require_degree_sum_survivors:
        parser.error("choose only one complete-case requirement")
    cases = reconstruct_cases(args.geng)
    reduced_indices = set(reduced_core_indices(cases))
    verifier_source = Path(__file__).resolve()
    generator_source = verifier_source.with_name(
        "r9_p93_d10_certificate_generator.py"
    )
    emitted_records: list[tuple[Path, dict[str, object]]] = []
    for package in args.package:
        manifest_path = package / "manifest.json"
        verify_manifest_digest(package, manifest_path)
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        verify_manifest_header(manifest, args.geng)
        verify_case_catalog(manifest, cases)
        sources = manifest.get("sources")
        if not isinstance(sources, dict):
            fail("manifest sources field is not an object")
        generator_record = sources.get("generator")
        verifier_record = sources.get("semantic_verifier")
        if not isinstance(generator_record, dict) or not isinstance(
            verifier_record, dict
        ):
            fail("manifest source records are missing")
        verify_source_record(generator_record, generator_source)
        verify_source_record(verifier_record, verifier_source)

        emitted = manifest.get("emitted")
        if not isinstance(emitted, list):
            fail("manifest emitted field is not a list")
        selection = manifest.get("selection")
        if not isinstance(selection, dict) or not isinstance(
            selection.get("indices"), list
        ):
            fail("manifest selection field is invalid")
        selected_indices = selection["indices"]
        if any(not isinstance(index, int) for index in selected_indices):
            fail("manifest selection contains a noninteger index")
        if selected_indices != sorted(set(selected_indices)) or any(
            not 0 <= index < EXPECTED_CASES for index in selected_indices
        ):
            fail("manifest selection is not a sorted unique in-range list")
        emitted_indices = [
            entry.get("index") for entry in emitted if isinstance(entry, dict)
        ]
        if len(emitted_indices) != len(emitted):
            fail("emitted entry is not an object")
        if emitted and emitted_indices != selected_indices:
            fail("emitted indices do not match the selected indices")
        if any(
            isinstance(entry, dict)
            and entry.get("proof_status") == "LRAT_VERIFIED"
            for entry in emitted
        ):
            toolchain = manifest.get("proof_toolchain")
            if not isinstance(toolchain, dict):
                fail("proved package lacks proof-tool metadata")
            for field in ("solver", "drat_trim", "lrat_check"):
                binary = toolchain.get(field)
                if not isinstance(binary, dict):
                    fail(f"proved package lacks {field} binary metadata")
                verify_binary_metadata(binary, field)
        emitted_records.extend((package, entry) for entry in emitted)

    if args.require_all and len(emitted_records) != EXPECTED_CASES:
        fail(
            f"require-all expected {EXPECTED_CASES} artifacts, "
            f"found {len(emitted_records)}"
        )
    if (
        args.require_degree_sum_survivors
        and len(emitted_records) != EXPECTED_REDUCED_CASES
    ):
        fail(
            f"reduced requirement expected {EXPECTED_REDUCED_CASES} artifacts, "
            f"found {len(emitted_records)}"
        )

    seen: set[int] = set()
    total_clauses = 0
    total_merges = 0
    merge_states = 0
    audited_shapes: set[tuple[int, int, int]] = set()
    replayed = 0
    for package, entry in emitted_records:
        index_value = entry["index"]
        if not isinstance(index_value, int):
            fail("emitted case index is not an integer")
        index = index_value
        if not 0 <= index < EXPECTED_CASES:
            fail(f"emitted case index is out of range: {index}")
        if index in seen:
            fail(f"duplicate emitted index {index}")
        seen.add(index)
        case = cases[index]
        if entry["case_id"] != case.case_id or entry["graph6"] != case.graph6:
            fail(f"emitted case identity mismatch at index {index}")
        cnf_record = entry.get("cnf")
        if not isinstance(cnf_record, dict):
            fail(f"missing CNF record at case {index}")
        cnf = verify_record(package, cnf_record)
        cnf_gzip_record = entry.get("cnf_gzip")
        if cnf_gzip_record is not None:
            if not isinstance(cnf_gzip_record, dict):
                fail(f"invalid compressed CNF record at case {index}")
            verify_record(package, cnf_gzip_record)
        variables, actual_clauses = read_dimacs(cnf)
        reference = build_reference(case)
        if variables != reference.variable_count:
            fail(
                f"variable count mismatch at case {index}: "
                f"{variables} != {reference.variable_count}"
            )
        if Counter(map(normalized, actual_clauses)) != Counter(
            map(normalized, reference.clauses)
        ):
            fail(f"clause multiset mismatch at case {index}")
        if entry["variables"] != reference.variable_count:
            fail(f"manifest variable mismatch at case {index}")
        if entry["clauses"] != len(reference.clauses):
            fail(f"manifest clause mismatch at case {index}")
        if entry["category_counts"] != dict(sorted(reference.categories.items())):
            fail(f"category count mismatch at case {index}")
        total_merges += len(reference.merges)
        merge_states += audit_merges(reference.merges, audited_shapes)
        total_clauses += len(reference.clauses)

        proof_status = entry.get("proof_status")
        if proof_status == "LRAT_VERIFIED":
            proof = entry.get("proof")
            if not isinstance(proof, dict):
                fail(f"missing proof object at case {index}")
            case_root = cnf.parent
            proof_paths: dict[str, Path] = {}
            for field in (
                "drat",
                "lrat",
                "solve_log",
                "conversion_log",
                "replay_log",
            ):
                record = proof.get(field)
                if not isinstance(record, dict):
                    fail(f"missing {field} record at case {index}")
                proof_paths[field] = verify_record(case_root, record)
            lrat_gzip_record = entry.get("lrat_gzip")
            if lrat_gzip_record is not None:
                if not isinstance(lrat_gzip_record, dict):
                    fail(f"invalid compressed LRAT record at case {index}")
                verify_record(package, lrat_gzip_record)
            if args.lrat_check is not None:
                replay_lrat(args.lrat_check, cnf, proof_paths["lrat"])
                replayed += 1
        else:
            if entry.get("proof") is not None:
                fail(f"unverified proof object at case {index}")
            if args.require_lrat:
                fail(f"case {index} has no verified LRAT status")

    if args.require_all and seen != set(range(EXPECTED_CASES)):
        fail("emitted case indices are not exactly 0..331")
    if args.require_degree_sum_survivors and seen != reduced_indices:
        fail("emitted case indices are not exactly the 50 degree-sum survivors")
    print("r9 P3 d10 certificate semantic audit: PASS")
    print(f"packages_verified={len(args.package)}")
    print(f"cases_reconstructed={len(cases)}")
    print(f"cnfs_verified={len(emitted_records)}")
    print(f"clauses_verified={total_clauses}")
    print(f"totalizer_merges_verified={total_merges}")
    print(f"totalizer_shapes_verified={len(audited_shapes)}")
    print(f"totalizer_states_verified={merge_states}")
    print(f"lrat_proofs_replayed={replayed}")


if __name__ == "__main__":
    main()
