#!/usr/bin/env python3
"""Independently audit all raw m=64 incidence states with CaDiCaL."""

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
import time
from typing import Any, Iterator, cast

import networkx as nx  # type: ignore[import-untyped]
import pysat  # type: ignore[import-not-found]
from pysat.card import ITotalizer  # type: ignore[import-not-found]
from pysat.solvers import Solver  # type: ignore[import-not-found]


HERE = Path(__file__).resolve().parent
DUAL_PATH = HERE / "verify_r9_p93_order26_m64_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m64_duals.jsonl"
SHELL_ORDER = 9
CORE_ORDER = 16
GLOBAL_OFFSET = 19
EXPECTED_COMPLEMENT_PAIRS = 562
EXPECTED_RAW_STATES = 101_880
EXPECTED_CLASSIFICATION_SHA256 = (
    "e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331"
)
EXPECTED_RECEIPT_SHA256 = (
    "d08cee42dcfbab41f8caaa3fec7a7133059577d63ec7a02ebe81db496a04c218"
)
EXPECTED_PYSAT_VERSION = "1.9.dev7"
EXPECTED_NETWORKX_VERSION = "3.4.2"
EXPECTED_COMPLEMENT_BUDGET_PROFILE = Counter(
    {0: 9, 1: 20, 2: 34, 3: 51, 4: 91, 5: 146, 6: 211}
)


def load_dual_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("erdos617_m64_cadical_dual", DUAL_PATH)
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
    states = {
        tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        for epsilon in weak_compositions_at_most(budget, SHELL_ORDER)
        if all(
            degrees[int(first)]
            + epsilon[int(first)]
            + degrees[int(second)]
            + epsilon[int(second)]
            >= 8
            for first, second in shell.edges
        )
    }
    return tuple(sorted(states))


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
    result: set[tuple[str, str]] = set()
    for line in lines[1:]:
        record = json.loads(line)
        if not isinstance(record, dict) or set(record) != {"core", "shell", "weights"}:
            raise AssertionError("malformed dual record")
        DUAL.BASE.parse_weights(record["weights"])
        pair = cast(tuple[str, str], (record["core"], record["shell"]))
        if pair[0] not in core_names or pair[1] not in shell_names:
            raise AssertionError("dual record lies outside the catalogs")
        if pair in result:
            raise AssertionError("duplicate dual pair")
        result.add(pair)
    return frozenset(result)


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
    if core.number_of_nodes() != CORE_ORDER or core.number_of_edges() != 64:
        raise AssertionError("m=64 core has the wrong order or size")
    colors = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(int(vertex) for vertex, color in colors.items() if color == side))
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("m=64 core does not have an 8+8 bipartition")
    if any(
        not core.has_edge(first, second)
        for first in sides[0]
        for second in sides[1]
    ):
        raise AssertionError("m=64 core is not K8,8")
    return cast(tuple[tuple[int, ...], tuple[int, ...]], sides)


def variable(row: int, column: int) -> int:
    return row * CORE_ORDER + column + 1


@dataclass(frozen=True)
class ExactCountAssumptions:
    positive_rhs: tuple[int, ...]
    negative_rhs: tuple[int, ...]

    def for_count(self, count: int) -> tuple[int, ...]:
        if not 0 <= count <= CORE_ORDER:
            raise AssertionError(f"row count outside zero through {CORE_ORDER}: {count}")
        assumptions = []
        if count < CORE_ORDER:
            assumptions.append(-self.positive_rhs[count])
        negative_count = CORE_ORDER - count
        if negative_count < CORE_ORDER:
            assumptions.append(-self.negative_rhs[negative_count])
        return tuple(assumptions)


def build_pair_cnf(
    core: nx.Graph, shell: nx.Graph
) -> tuple[tuple[tuple[int, ...], ...], tuple[ExactCountAssumptions, ...], int]:
    sides = bipartition(core)
    clauses: list[tuple[int, ...]] = []
    top_id = SHELL_ORDER * CORE_ORDER

    # Every core column has demand two. Nine length-eight clauses encode
    # at least two incidences without importing a cardinality encoder.
    for column in range(CORE_ORDER):
        column_variables = tuple(variable(row, column) for row in range(SHELL_ORDER))
        clauses.extend(
            tuple(literal for index, literal in enumerate(column_variables) if index != omit)
            for omit in range(SHELL_ORDER)
        )

    for raw_first, raw_second in shell.edges:
        first, second = int(raw_first), int(raw_second)
        for raw_core_first, raw_core_second in core.edges:
            core_first, core_second = int(raw_core_first), int(raw_core_second)
            clauses.append(
                (
                    variable(first, core_first),
                    variable(first, core_second),
                    variable(second, core_first),
                    variable(second, core_second),
                )
            )
        top_id += 1
        selector = top_id
        clauses.extend(
            (-selector, variable(first, column), variable(second, column))
            for column in sides[0]
        )
        clauses.extend(
            (selector, variable(first, column), variable(second, column))
            for column in sides[1]
        )

    for triangle in triangles(shell):
        for column in range(CORE_ORDER):
            clauses.append(tuple(variable(row, column) for row in triangle))

    for row in range(SHELL_ORDER):
        for side in sides:
            clauses.append(tuple(-variable(row, column) for column in side))

    exact_counts = []
    for row in range(SHELL_ORDER):
        literals = [variable(row, column) for column in range(CORE_ORDER)]
        with ITotalizer(lits=literals, ubound=CORE_ORDER, top_id=top_id) as positive:
            clauses.extend(tuple(clause) for clause in positive.cnf.clauses)
            positive_rhs = tuple(int(literal) for literal in positive.rhs)
            top_id = int(positive.top_id)
        with ITotalizer(
            lits=[-literal for literal in literals],
            ubound=CORE_ORDER,
            top_id=top_id,
        ) as negative:
            clauses.extend(tuple(clause) for clause in negative.cnf.clauses)
            negative_rhs = tuple(int(literal) for literal in negative.rhs)
            top_id = int(negative.top_id)
        if len(positive_rhs) != CORE_ORDER or len(negative_rhs) != CORE_ORDER:
            raise AssertionError("incremental totalizer has the wrong output order")
        exact_counts.append(ExactCountAssumptions(positive_rhs, negative_rhs))
    return tuple(clauses), tuple(exact_counts), top_id


def verify_model(
    model: list[int], shell: nx.Graph, row_sizes: tuple[int, ...]
) -> None:
    positive = frozenset(literal for literal in model if literal > 0)
    actual = tuple(
        sum(variable(row, column) in positive for column in range(CORE_ORDER))
        for row in range(SHELL_ORDER)
    )
    if actual != row_sizes:
        raise AssertionError(f"CaDiCaL model has wrong row sizes: {actual} != {row_sizes}")
    if row_sizes not in row_size_states(shell):
        raise AssertionError("CaDiCaL model lies outside the raw state catalog")


def audit_pair(task: tuple[int, int, str, str]) -> tuple[int, int, int, int, str]:
    core_index, shell_index, core_name, shell_name = task
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    states = row_size_states(shell)
    clauses, exact_counts, variable_count = build_pair_cnf(core, shell)
    unsat = 0
    with Solver(name="cadical195", bootstrap_with=clauses) as solver:
        for row_sizes in states:
            assumptions = tuple(
                literal
                for row, count in enumerate(row_sizes)
                for literal in exact_counts[row].for_count(count)
            )
            if solver.solve(assumptions=assumptions):
                model = solver.get_model()
                if model is None:
                    raise AssertionError("CaDiCaL returned SAT without a model")
                verify_model(model, shell, row_sizes)
                raise AssertionError(
                    f"unexpected SAT state at {core_index}:{shell_index}:{row_sizes}"
                )
            unsat += 1
    formula_payload = "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses
    ).encode("ascii")
    return (
        core_index,
        shell_index,
        len(states),
        unsat,
        hashlib.sha256(
            f"{variable_count}\n".encode("ascii") + formula_payload
        ).hexdigest(),
    )


def main() -> None:
    started = time.perf_counter()
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("workers must be positive")
    if pysat.__version__ != EXPECTED_PYSAT_VERSION:
        raise AssertionError(f"wrong python-sat version: {pysat.__version__}")
    if nx.__version__ != EXPECTED_NETWORKX_VERSION:
        raise AssertionError(f"wrong NetworkX version: {nx.__version__}")

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    certified = certified_pairs(args.duals, cores, shells)
    complement = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii")) not in certified
    )
    if len(complement) != EXPECTED_COMPLEMENT_PAIRS:
        raise AssertionError(f"wrong complement count: {len(complement)}")
    tasks = tuple(
        (
            core_index,
            shell_index,
            cores[core_index].graph6.decode("ascii"),
            shells[shell_index].graph6.decode("ascii"),
        )
        for core_index, shell_index in complement
    )
    if args.workers == 1:
        results = tuple(audit_pair(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            results = tuple(pool.map(audit_pair, tasks))

    raw_states = sum(result[2] for result in results)
    unsat_states = sum(result[3] for result in results)
    if raw_states != EXPECTED_RAW_STATES or unsat_states != EXPECTED_RAW_STATES:
        raise AssertionError(
            f"wrong audit totals: raw={raw_states} UNSAT={unsat_states}"
        )
    state_catalog = tuple(
        (core_index, shell_index, row_sizes)
        for core_index, shell_index in complement
        for row_sizes in row_size_states(shells[shell_index].graph)
    )
    classification = "".join(
        f"{core_index}:{shell_index}:{','.join(map(str, row_sizes))}:0\n"
        for core_index, shell_index, row_sizes in state_catalog
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    if classification_sha256 != EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"classification digest mismatch: {classification_sha256}")

    budget_profile = Counter(
        GLOBAL_OFFSET - shells[shell_index].graph.number_of_edges()
        for _, shell_index in complement
    )
    if budget_profile != EXPECTED_COMPLEMENT_BUDGET_PROFILE:
        raise AssertionError(f"budget profile mismatch: {budget_profile}")
    pair_profile = Counter(result[2] for result in results)
    receipt_payload = "".join(
        f"{core_index}:{shell_index}:{states}:{unsat}:{formula_sha256}\n"
        for core_index, shell_index, states, unsat, formula_sha256 in results
    ).encode("ascii")
    receipt_sha256 = hashlib.sha256(receipt_payload).hexdigest()
    if receipt_sha256 != EXPECTED_RECEIPT_SHA256:
        raise AssertionError(f"CaDiCaL receipt digest mismatch: {receipt_sha256}")

    wall_seconds = time.perf_counter() - started
    receipt = {
        "schema": "erdos617-r9-m64-cadical-audit-v1",
        "theorem_scope": "fixed-r9-order26-degree9-m64",
        "status": "PASS",
        "cores": len(cores),
        "shells": len(shells),
        "complement_pairs": len(complement),
        "raw_states": raw_states,
        "unsat": unsat_states,
        "sat": 0,
        "unknown": 0,
        "complement_budget_profile": dict(sorted(budget_profile.items())),
        "pair_q_state_profile": dict(sorted(pair_profile.items())),
        "classification_sha256": classification_sha256,
        "cadical_receipt_sha256": receipt_sha256,
        "toolchain": {
            "python": sys.version.split()[0],
            "python_sat": pysat.__version__,
            "networkx": nx.__version__,
            "solver": "cadical195",
            "encoding": "independent_incremental_totalizer",
        },
        "workers": args.workers,
        "wall_seconds": round(wall_seconds, 3),
        "nonclaims": [
            "The audit is independent confirmation of the solver-free m=64 proof.",
            "It does not prove Erdős Problem 617 for arbitrary r.",
        ],
    }
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    print(
        f"python={sys.version.split()[0]} python_sat={pysat.__version__} "
        f"networkx={nx.__version__}"
    )
    print("solver=cadical195 encoding=independent_incremental_totalizer")
    print(f"cores={len(cores)} shells={len(shells)} complement_pairs={len(complement)}")
    print(
        f"q_states={raw_states} cadical_UNSAT={unsat_states} "
        "cadical_SAT=0 cadical_UNKNOWN=0"
    )
    print(f"complement_budget_profile={dict(sorted(budget_profile.items()))}")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_sha256}")
    print(f"cadical_receipt_sha256={receipt_sha256}")
    print(f"wall_seconds={wall_seconds:.3f}")
    if args.receipt is not None:
        print(f"receipt={args.receipt}")
    print("status=PASS")


if __name__ == "__main__":
    main()
