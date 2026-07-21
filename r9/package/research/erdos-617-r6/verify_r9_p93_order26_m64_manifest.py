#!/usr/bin/env python3
"""Verify the dependency-closed manifest for the m=64 package."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
DEFAULT_MANIFEST = HERE / "artifacts" / "r9-order26-m64" / "manifest.json"
EXPECTED_ARTIFACT = "erdos-617-r9-order26-degree9-m64"
EXPECTED_FILE_PATHS = {
    f"research/erdos-617-r6/{name}"
    for name in (
        "R9_P93_ORDER26_M64_REDUCED_FRONTIER.md",
        "R9_P93_ORDER26_M64_DEPENDENCY_AUDIT.md",
        "r9_p93_order26_m64_dual_generator.py",
        "r9_p93_order26_m64_duals.jsonl",
        "verify_r9_p93_order26_m64_duals.py",
        "r9_p93_order26_m64_scalar_side_verifier.py",
        "r9_p93_order26_m64_tau3_verifier.py",
        "r9_p93_order26_m64_p1_orbit_verifier.py",
        "r9_p93_order26_m64_cadical_audit.py",
        "test_r9_p93_order26_m64_package.py",
        "verify_r9_p93_order26_m64_manifest.py",
        "artifacts/r9-order26-m64/cadical_receipt.json",
    )
}
EXPECTED_DEPENDENCY_PATHS = {
    f"research/erdos-617-r6/{name}"
    for name in (
        "r9_p93_order26_m59_dual_generator.py",
        "verify_r9_p93_order26_m62_duals.py",
        "r9_p93_order26_m62_p1_orbit_verifier.py",
        "r9_p93_order26_m62_scalar_side_verifier.py",
        "r9_p93_order26_m60_p1_qstate_verifier.py",
        "verify_r9_p93_order26_m60_duals.py",
        "r9_p93_order26_m60_duals.jsonl",
        "r9_p93_order26_m62_duals.jsonl",
    )
}
EXPECTED_CLASSIFICATION_SHA256 = (
    "e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def checked_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise AssertionError(f"{label} must be a nonempty string")
    return value


def checked_entries(raw: Any, label: str) -> tuple[dict[str, Any], ...]:
    if not isinstance(raw, list):
        raise AssertionError(f"{label} must be a list")
    result = []
    for index, entry in enumerate(raw):
        if not isinstance(entry, dict):
            raise AssertionError(f"{label}[{index}] must be an object")
        if "path" not in entry or "sha256" not in entry:
            raise AssertionError(f"{label}[{index}] lacks path or sha256")
        result.append(entry)
    return tuple(result)


def resolve_repo_path(raw: Any, label: str) -> Path:
    relative = Path(checked_string(raw, label))
    if relative.is_absolute():
        raise AssertionError(f"{label} must be repository-relative")
    path = (REPO_ROOT / relative).resolve()
    if not path.is_relative_to(REPO_ROOT):
        raise AssertionError(f"{label} escapes the repository")
    return path


def verify_digest_file(manifest: Path) -> str:
    digest_path = manifest.with_name("manifest.sha256")
    fields = digest_path.read_text(encoding="ascii").strip().split()
    if fields != [sha256(manifest), "manifest.json"]:
        raise AssertionError("manifest.sha256 does not match manifest.json")
    return fields[0]


def verify_entry(entry: dict[str, Any], label: str) -> Path:
    path = resolve_repo_path(entry["path"], f"{label}.path")
    expected = checked_string(entry["sha256"], f"{label}.sha256")
    if len(expected) != 64:
        raise AssertionError(f"{label}.sha256 has the wrong length")
    actual = sha256(path)
    if actual != expected:
        raise AssertionError(f"{label} digest mismatch: {path}")
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--geng", type=Path)
    args = parser.parse_args()

    manifest = args.manifest.resolve()
    manifest_digest = verify_digest_file(manifest)
    raw = json.loads(manifest.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise AssertionError("manifest must be an object")
    if raw.get("artifact") != EXPECTED_ARTIFACT:
        raise AssertionError("wrong artifact identifier")
    status = raw.get("status")
    if status != {
        "m64": "locally_proved",
        "fixed_r9": "locally_proved_computer_assisted",
        "erdos_617": "open",
    }:
        raise AssertionError(f"wrong theorem status: {status}")

    files = checked_entries(raw.get("files"), "files")
    dependencies = checked_entries(raw.get("source_dependencies"), "source_dependencies")
    paths = []
    for index, entry in enumerate(files):
        paths.append(verify_entry(entry, f"files[{index}]"))
    for index, entry in enumerate(dependencies):
        paths.append(verify_entry(entry, f"source_dependencies[{index}]"))
    if len(paths) != len(set(paths)):
        raise AssertionError("manifest repeats a file")
    file_names = {str(path.relative_to(REPO_ROOT)) for path in paths[: len(files)]}
    dependency_names = {
        str(path.relative_to(REPO_ROOT)) for path in paths[len(files) :]
    }
    if file_names != EXPECTED_FILE_PATHS:
        raise AssertionError(f"wrong proof-file closure: {sorted(file_names)}")
    if dependency_names != EXPECTED_DEPENDENCY_PATHS:
        raise AssertionError(
            f"wrong source-dependency closure: {sorted(dependency_names)}"
        )

    cadical_path = REPO_ROOT / (
        "research/erdos-617-r6/artifacts/r9-order26-m64/cadical_receipt.json"
    )
    cadical = json.loads(cadical_path.read_text(encoding="utf-8"))
    expected_cadical = {
        "status": "PASS",
        "raw_states": 101880,
        "unsat": 101880,
        "sat": 0,
        "unknown": 0,
        "classification_sha256": EXPECTED_CLASSIFICATION_SHA256,
    }
    for key, value in expected_cadical.items():
        if cadical.get(key) != value:
            raise AssertionError(f"wrong CaDiCaL receipt field {key}")

    external = raw.get("external_dependency")
    if not isinstance(external, dict):
        raise AssertionError("external_dependency must be an object")
    expected_geng = checked_string(external.get("sha256"), "external_dependency.sha256")
    if args.geng is not None and sha256(args.geng.resolve()) != expected_geng:
        raise AssertionError("nauty geng digest mismatch")

    receipts = raw.get("receipts")
    if not isinstance(receipts, dict):
        raise AssertionError("receipts must be an object")
    receipt_path = verify_entry(receipts, "receipts")
    expected_receipt_path = (
        REPO_ROOT
        / "research/erdos-617-r6/artifacts/r9-order26-m64/replay_receipts.json"
    )
    if receipt_path != expected_receipt_path:
        raise AssertionError("manifest points to the wrong replay receipt")

    print(f"artifact={EXPECTED_ARTIFACT}")
    print(f"manifest_sha256={manifest_digest}")
    print(f"proof_files={len(files)} source_dependencies={len(dependencies)}")
    print(f"geng_checked={int(args.geng is not None)}")
    print("status=PASS")


if __name__ == "__main__":
    main()
