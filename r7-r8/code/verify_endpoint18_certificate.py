#!/usr/bin/env python3
"""Direct encoding audit for the 18-vertex regular endpoint certificate.

This verifier does not import ``endpoint18_lazy.py``.  It reconstructs the
mathematical CNF specification independently, compares clause multisets, and
checks the recursive totalizer meaning by induction over every merge state.

The checked formula asserts that a graph on vertices 0,...,17 is 7-regular,
triangle-free, and has independence number at most seven.  The fixed
neighborhood of vertex zero is a safe relabeling symmetry break.
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
from pathlib import Path
import shutil
import subprocess
import tempfile
from typing import Any, Iterable, Iterator, Mapping, NoReturn


Clause = tuple[int, ...]
Edge = tuple[int, int]

VERTEX_COUNT = 18
EDGE_VARIABLE_COUNT = 153
EXPECTED_VARIABLE_COUNT = 1233
EXPECTED_CLAUSE_COUNT = 50225


def fail(message: str) -> NoReturn:
    raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def read_dimacs(path: Path) -> tuple[int, int, list[Clause]]:
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
                fail(f"invalid DIMACS header at line {line_number}: {line}")
            header = (int(fields[2]), int(fields[3]))
            continue
        if header is None:
            fail(f"clause precedes DIMACS header at line {line_number}")
        tokens.extend(int(token) for token in line.split())

    if header is None:
        fail("missing DIMACS header")

    clauses: list[Clause] = []
    clause: list[int] = []
    for literal in tokens:
        if literal == 0:
            clauses.append(tuple(clause))
            clause = []
        else:
            clause.append(literal)
    if clause:
        fail("last DIMACS clause has no terminating zero")
    if len(clauses) != header[1]:
        fail(
            f"header declares {header[1]} clauses, parsed {len(clauses)}"
        )
    for index, parsed_clause in enumerate(clauses, start=1):
        if not parsed_clause:
            fail(f"input formula contains an empty clause at index {index}")
        if any(abs(literal) > header[0] for literal in parsed_clause):
            fail(f"clause {index} uses a variable above the header bound")
        if len(set(parsed_clause)) != len(parsed_clause):
            fail(f"clause {index} repeats a literal")
        if any(-literal in parsed_clause for literal in parsed_clause):
            fail(f"clause {index} is tautological")
    return header[0], header[1], clauses


def normalized(clause: Iterable[int]) -> Clause:
    return tuple(sorted(clause, key=lambda literal: (abs(literal), literal < 0)))


@dataclass(frozen=True)
class Merge:
    left: tuple[int, ...]
    right: tuple[int, ...]
    output: tuple[int, ...]
    clauses: tuple[Clause, ...]


@dataclass
class ReferenceFormula:
    edge_variables: dict[Edge, int]
    next_variable: int
    clauses: list[Clause]
    merges: list[Merge]
    category_counts: Counter[str]

    @classmethod
    def create(cls) -> "ReferenceFormula":
        edges = tuple(itertools.combinations(range(VERTEX_COUNT), 2))
        return cls(
            edge_variables={edge: index for index, edge in enumerate(edges, 1)},
            next_variable=EDGE_VARIABLE_COUNT + 1,
            clauses=[],
            merges=[],
            category_counts=Counter(),
        )

    def edge(self, first: int, second: int) -> int:
        if first > second:
            first, second = second, first
        return self.edge_variables[(first, second)]

    def allocate(self, count: int) -> tuple[int, ...]:
        variables = tuple(range(self.next_variable, self.next_variable + count))
        self.next_variable += count
        return variables

    def add(self, category: str, clause: Iterable[int]) -> None:
        parsed = tuple(clause)
        self.clauses.append(parsed)
        self.category_counts[category] += 1

    def totalizer(self, inputs: tuple[int, ...], cap: int) -> tuple[int, ...]:
        if len(inputs) == 1:
            return inputs
        middle = len(inputs) // 2
        left = self.totalizer(inputs[:middle], cap)
        right = self.totalizer(inputs[middle:], cap)
        output = self.allocate(min(cap, len(left) + len(right)))

        merge_clauses: list[Clause] = []
        for left_count in range(len(left) + 1):
            for right_count in range(len(right) + 1):
                total = left_count + right_count
                if 1 <= total <= len(output):
                    clause = [output[total - 1]]
                    if left_count:
                        clause.append(-left[left_count - 1])
                    if right_count:
                        clause.append(-right[right_count - 1])
                    merge_clauses.append(tuple(clause))

                if total + 1 <= len(output):
                    clause = [-output[total]]
                    if left_count < len(left):
                        clause.append(left[left_count])
                    if right_count < len(right):
                        clause.append(right[right_count])
                    merge_clauses.append(tuple(clause))

        for merge_clause in merge_clauses:
            self.add("totalizer_merge", merge_clause)
        self.merges.append(Merge(left, right, output, tuple(merge_clauses)))
        return output


def build_reference() -> ReferenceFormula:
    reference = ReferenceFormula.create()

    # A 7-regular graph may be relabeled so that these are exactly N(0).
    for vertex in range(1, VERTEX_COUNT):
        edge = reference.edge(0, vertex)
        reference.add("symmetry", (edge if vertex <= 7 else -edge,))

    # Every vertex has degree exactly seven.
    for vertex in range(VERTEX_COUNT):
        incident = tuple(
            reference.edge(vertex, other)
            for other in range(VERTEX_COUNT)
            if other != vertex
        )
        output = reference.totalizer(incident, 8)
        reference.add("degree_units", (output[6],))
        reference.add("degree_units", (-output[7],))

    # No triangle is present.
    for triple in itertools.combinations(range(VERTEX_COUNT), 3):
        reference.add(
            "triangle",
            (
                -reference.edge(first, second)
                for first, second in itertools.combinations(triple, 2)
            ),
        )

    # Every eight vertices contain an edge, equivalently alpha <= 7.
    for vertices in itertools.combinations(range(VERTEX_COUNT), 8):
        reference.add(
            "independence",
            (
                reference.edge(first, second)
                for first, second in itertools.combinations(vertices, 2)
            ),
        )

    return reference


def threshold_assignment(variables: tuple[int, ...], count: int) -> dict[int, bool]:
    if not 0 <= count <= len(variables):
        fail(f"threshold count {count} outside 0..{len(variables)}")
    return {
        variable: index < count
        for index, variable in enumerate(variables)
    }


def clause_value(clause: Clause, assignment: Mapping[int, bool]) -> bool:
    return any(
        assignment[abs(literal)] == (literal > 0)
        for literal in clause
    )


def audit_merge_semantics(merges: list[Merge]) -> int:
    """Check the threshold-sum meaning of each merge without a SAT solver."""

    states = 0
    for merge_index, merge in enumerate(merges):
        for left_count in range(len(merge.left) + 1):
            for right_count in range(len(merge.right) + 1):
                total = left_count + right_count
                output_count = min(total, len(merge.output))
                assignment: dict[int, bool] = {}
                assignment.update(threshold_assignment(merge.left, left_count))
                assignment.update(threshold_assignment(merge.right, right_count))
                assignment.update(threshold_assignment(merge.output, output_count))

                if not all(
                    clause_value(clause, assignment)
                    for clause in merge.clauses
                ):
                    fail(
                        f"merge {merge_index} rejects canonical counts "
                        f"({left_count}, {right_count})"
                    )

                # With canonical child thresholds, every output bit is forced.
                for output in merge.output:
                    flipped = assignment.copy()
                    flipped[output] = not flipped[output]
                    if all(
                        clause_value(clause, flipped)
                        for clause in merge.clauses
                    ):
                        fail(
                            f"merge {merge_index} does not force output {output} "
                            f"at counts ({left_count}, {right_count})"
                        )
                states += 1
    return states


def audit_exact_seven_root() -> None:
    # The root has thresholds for counts one through eight.  The two unit
    # clauses require threshold seven and forbid threshold eight.
    accepted = []
    for degree in range(18):
        at_least_seven = degree >= 7
        at_least_eight = degree >= 8
        if at_least_seven and not at_least_eight:
            accepted.append(degree)
    if accepted != [7]:
        fail(f"root units accept unexpected degrees: {accepted}")


def verify_manifest(manifest_path: Path, package_root: Path) -> dict[str, Any]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    for relative_path, metadata in manifest["artifacts"].items():
        path = package_root / relative_path
        if not path.is_file():
            fail(f"manifest artifact is missing: {path}")
        actual_size = path.stat().st_size
        if actual_size != metadata["bytes"]:
            fail(
                f"size mismatch for {relative_path}: "
                f"expected {metadata['bytes']}, got {actual_size}"
            )
        actual_hash = sha256(path)
        if actual_hash != metadata["sha256"]:
            fail(
                f"SHA-256 mismatch for {relative_path}: "
                f"expected {metadata['sha256']}, got {actual_hash}"
            )
    return manifest


@contextmanager
def materialized_pair(
    package_root: Path,
) -> Iterator[tuple[Path, Path]]:
    raw_cnf = package_root / "round-000.cnf"
    raw_lrat = package_root / "round-000.lrat"
    if raw_cnf.is_file() and raw_lrat.is_file():
        yield raw_cnf, raw_lrat
        return

    compressed_cnf = package_root / "round-000.cnf.gz"
    compressed_lrat = package_root / "round-000.lrat.gz"
    if not compressed_cnf.is_file() or not compressed_lrat.is_file():
        fail("neither a raw nor a compressed CNF/LRAT pair is complete")

    with tempfile.TemporaryDirectory(prefix="endpoint18-") as directory:
        temporary_root = Path(directory)
        cnf = temporary_root / "round-000.cnf"
        lrat = temporary_root / "round-000.lrat"
        with gzip.open(compressed_cnf, "rb") as source, cnf.open("wb") as target:
            shutil.copyfileobj(source, target)
        with gzip.open(compressed_lrat, "rb") as source, lrat.open("wb") as target:
            shutil.copyfileobj(source, target)
        yield cnf, lrat


def replay_lrat(checker: Path, cnf: Path, lrat: Path) -> str:
    result = subprocess.run(
        [str(checker), str(cnf), str(lrat)],
        check=False,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    if result.returncode != 0 or "c VERIFIED" not in output:
        fail(
            f"LRAT replay failed with exit code {result.returncode}:\n{output}"
        )
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--artifacts",
        type=Path,
        default=Path(__file__).resolve().parent / "artifacts" / "endpoint18",
    )
    parser.add_argument("--lrat-check", type=Path)
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()

    manifest = args.artifacts / "manifest.json"
    manifest_data: dict[str, Any] | None = None
    if not args.skip_manifest:
        manifest_data = verify_manifest(manifest, args.artifacts)

    with materialized_pair(args.artifacts) as (cnf, lrat):
        variable_count, clause_count, actual_clauses = read_dimacs(cnf)
        if variable_count != EXPECTED_VARIABLE_COUNT:
            fail(
                f"expected {EXPECTED_VARIABLE_COUNT} variables, got {variable_count}"
            )
        if clause_count != EXPECTED_CLAUSE_COUNT:
            fail(f"expected {EXPECTED_CLAUSE_COUNT} clauses, got {clause_count}")

        if manifest_data is not None:
            raw = manifest_data["uncompressed"]
            if sha256(cnf) != raw["cnf_sha256"]:
                fail("uncompressed CNF hash differs from the manifest")
            if cnf.stat().st_size != raw["cnf_bytes"]:
                fail("uncompressed CNF size differs from the manifest")
            if sha256(lrat) != raw["lrat_sha256"]:
                fail("uncompressed LRAT hash differs from the manifest")
            if lrat.stat().st_size != raw["lrat_bytes"]:
                fail("uncompressed LRAT size differs from the manifest")

        reference = build_reference()
        if reference.next_variable - 1 != EXPECTED_VARIABLE_COUNT:
            fail(
                "reference allocation ended at variable "
                f"{reference.next_variable - 1}"
            )
        if len(reference.clauses) != EXPECTED_CLAUSE_COUNT:
            fail(
                f"reference produced {len(reference.clauses)} clauses, "
                f"expected {EXPECTED_CLAUSE_COUNT}"
            )

        actual_counter = Counter(normalized(clause) for clause in actual_clauses)
        reference_counter = Counter(normalized(clause) for clause in reference.clauses)
        missing = reference_counter - actual_counter
        extra = actual_counter - reference_counter
        if missing or extra:
            fail(
                "CNF clause multiset differs from the independent specification: "
                f"missing={sum(missing.values())}, extra={sum(extra.values())}"
            )

        merge_states = audit_merge_semantics(reference.merges)
        audit_exact_seven_root()

        print("encoding=VERIFIED")
        print(f"cnf_sha256={sha256(cnf)}")
        print(f"variables={variable_count}")
        print(f"clauses={clause_count}")
        print(f"edge_variables={len(reference.edge_variables)}")
        print(
            f"auxiliary_variables={variable_count - len(reference.edge_variables)}"
        )
        print(f"totalizer_merges={len(reference.merges)}")
        print(f"totalizer_states_checked={merge_states}")
        for category in sorted(reference.category_counts):
            print(f"clauses_{category}={reference.category_counts[category]}")

        if args.lrat_check is not None:
            output = replay_lrat(args.lrat_check, cnf, lrat)
            print("lrat=VERIFIED")
            for line in output.splitlines():
                if line.startswith("c parsed") or line == "c VERIFIED":
                    print(f"lrat_checker: {line}")


if __name__ == "__main__":
    main()
