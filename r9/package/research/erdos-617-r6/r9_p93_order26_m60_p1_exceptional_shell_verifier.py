#!/usr/bin/env python3
"""Verify the premises of the direct m=60 exceptional-shell argument."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
VERIFIER_PATH = HERE / "r9_p93_order26_m60_p1_qstate_verifier.py"


def load_verifier() -> Any:
    spec = importlib.util.spec_from_file_location(
        "r9_m60_exceptional_premise_verifier", VERIFIER_PATH
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFIER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


VERIFIER = load_verifier()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    args = parser.parse_args()

    cores = VERIFIER.DUAL.generate_cores(args.geng)
    shells = VERIFIER.DUAL.generate_shells(args.geng)
    if len(cores) != VERIFIER.EXPECTED_CORES:
        raise AssertionError(f"wrong core count: {len(cores)}")
    if len(shells) != VERIFIER.EXPECTED_SHELLS:
        raise AssertionError(f"wrong shell count: {len(shells)}")
    if (
        VERIFIER.DUAL.catalog_sha256(cores)
        != VERIFIER.DUAL.EXPECTED_CORE_CATALOG_SHA256
    ):
        raise AssertionError("core catalog digest mismatch")
    if (
        VERIFIER.DUAL.catalog_sha256(shells)
        != VERIFIER.DUAL.EXPECTED_SHELL_CATALOG_SHA256
    ):
        raise AssertionError("shell catalog digest mismatch")
    shell = shells[VERIFIER.EXPECTED_EXCEPTIONAL_SHELL_INDEX]
    demand_profile = VERIFIER.verify_exceptional_shell(cores, shell)
    states = VERIFIER.row_size_states(shell.graph)
    print(
        f"cores={len(cores)} shells={len(shells)} "
        f"exceptional_shell_index={VERIFIER.EXPECTED_EXCEPTIONAL_SHELL_INDEX}"
    )
    print(
        f"exceptional_shell={VERIFIER.EXPECTED_EXCEPTIONAL_SHELL_GRAPH6} "
        "structure=K5,3+K1"
    )
    print(f"row_states={states}")
    print(f"side_column_demand_profile={dict(demand_profile)}")
    print("status=PASS")


if __name__ == "__main__":
    main()
