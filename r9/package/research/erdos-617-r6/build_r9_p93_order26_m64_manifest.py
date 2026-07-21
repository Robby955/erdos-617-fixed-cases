#!/usr/bin/env python3
"""Build the dependency-closed manifest for the fixed-r=9 m=64 package."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys


HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
DEFAULT_OUTPUT = HERE / "artifacts" / "r9-order26-m64" / "manifest.json"
DEFAULT_RECEIPTS = HERE / "artifacts" / "r9-order26-m64" / "replay_receipts.json"

PROOF_FILES = (
    ("R9_P93_ORDER26_M64_REDUCED_FRONTIER.md", "theorem_note"),
    ("R9_P93_ORDER26_M64_DEPENDENCY_AUDIT.md", "dependency_audit"),
    ("r9_p93_order26_m64_dual_generator.py", "certificate_generator"),
    ("r9_p93_order26_m64_duals.jsonl", "exact_dual_data"),
    ("verify_r9_p93_order26_m64_duals.py", "semantic_dual_verifier"),
    ("r9_p93_order26_m64_scalar_side_verifier.py", "solver_free_scalar_verifier"),
    ("r9_p93_order26_m64_tau3_verifier.py", "three_hub_verifier"),
    ("r9_p93_order26_m64_p1_orbit_verifier.py", "solver_free_orbit_verifier"),
    ("r9_p93_order26_m64_cadical_audit.py", "independent_cadical_audit"),
    ("test_r9_p93_order26_m64_package.py", "corruption_tests"),
    ("verify_r9_p93_order26_m64_manifest.py", "manifest_verifier"),
)

SOURCE_DEPENDENCIES = (
    "r9_p93_order26_m59_dual_generator.py",
    "verify_r9_p93_order26_m62_duals.py",
    "r9_p93_order26_m62_p1_orbit_verifier.py",
    "r9_p93_order26_m62_scalar_side_verifier.py",
    "r9_p93_order26_m60_p1_qstate_verifier.py",
    "verify_r9_p93_order26_m60_duals.py",
    "r9_p93_order26_m60_duals.jsonl",
    "r9_p93_order26_m62_duals.jsonl",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def relative(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT.resolve()))


def file_record(name: str, role: str | None = None) -> dict[str, str]:
    path = HERE / name
    if not path.is_file():
        raise AssertionError(f"missing package source: {path}")
    result = {"path": relative(path), "sha256": sha256(path)}
    if role is not None:
        result["role"] = role
    return result


def command_version(command: list[str]) -> str:
    result = subprocess.run(command, check=True, capture_output=True, text=True)
    return (result.stdout or result.stderr).strip().splitlines()[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--receipts", type=Path, default=DEFAULT_RECEIPTS)
    args = parser.parse_args()

    geng = args.geng.resolve()
    if not geng.is_file():
        raise AssertionError(f"missing geng binary: {geng}")
    receipts = args.receipts.resolve()
    receipt_data = json.loads(receipts.read_text(encoding="utf-8"))
    if receipt_data.get("package_status") != "locally_proved":
        raise AssertionError("replay receipts do not record a locally proved package")
    if receipt_data.get("independent_cadical_audit", {}).get("status") != "PASS":
        raise AssertionError("independent CaDiCaL receipt is not PASS")

    cadical_receipt = HERE / "artifacts" / "r9-order26-m64" / "cadical_receipt.json"
    files = [file_record(name, role) for name, role in PROOF_FILES]
    files.append(
        {
            "path": relative(cadical_receipt),
            "sha256": sha256(cadical_receipt),
            "role": "independent_cadical_receipt",
        }
    )
    dependencies = [file_record(name) for name in SOURCE_DEPENDENCIES]
    manifest = {
        "artifact": "erdos-617-r9-order26-degree9-m64",
        "created_at": "2026-07-21",
        "status": {
            "m64": "locally_proved",
            "fixed_r9": "locally_proved_computer_assisted",
            "erdos_617": "open",
        },
        "proof_premise": [
            "exact rational dual verification for 7454 core-shell pairs",
            "solver-free scalar reduction over 101880 raw states",
            "human three-hub exclusion for 4 states",
            "solver-free orbit exhaustion for 10635 states",
        ],
        "independent_search_audit": (
            "independent incremental CaDiCaL reconstruction passed all "
            "101880 raw states with zero SAT and zero UNKNOWN"
        ),
        "files": files,
        "source_dependencies": dependencies,
        "external_dependency": {
            "name": "nauty geng",
            "version": command_version([str(geng), "-help"]),
            "sha256": sha256(geng),
        },
        "tool_versions": {
            "python": sys.version.split()[0],
            "platform": platform.platform(),
            "networkx": "3.4.2",
            "numpy": "2.4.4",
            "scipy": "1.17.1",
            "python_sat": "1.9.dev7",
            "cadical": "1.9.5 through python-sat cadical195",
            "pytest": "9.0.3",
            "ruff": command_version(["ruff", "--version"]),
            "mypy": command_version(["mypy", "--version"]),
        },
        "receipts": {"path": relative(receipts), "sha256": sha256(receipts)},
        "nonclaims": [
            "This package is a local computer-assisted proof package.",
            "It is not external mathematical review.",
            "It does not prove Erdős Problem 617 for arbitrary r.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    digest = sha256(args.output)
    args.output.with_name("manifest.sha256").write_text(
        f"{digest}  manifest.json\n", encoding="ascii"
    )
    print(f"manifest={args.output}")
    print(f"manifest_sha256={digest}")
    print(f"proof_files={len(files)} source_dependencies={len(dependencies)}")
    print("status=PASS")


if __name__ == "__main__":
    main()
