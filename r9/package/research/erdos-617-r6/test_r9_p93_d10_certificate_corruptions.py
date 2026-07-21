#!/usr/bin/env python3
"""Run deliberate corruption checks against the P3(27), d=10 verifier."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
from typing import Any, Callable, cast


HERE = Path(__file__).resolve().parent
VERIFIER_PATH = HERE / "verify_r9_p93_d10_certificate.py"


def load_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("erdos617_d10_corrupt", VERIFIER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {VERIFIER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


VERIFY = load_verifier()


def must_fail(action: Callable[[], None], label: str) -> None:
    try:
        action()
    except AssertionError:
        return
    raise AssertionError(f"corruption was accepted: {label}")


def emitted_entries(package: Path) -> tuple[dict[str, object], ...]:
    manifest = json.loads((package / "manifest.json").read_text(encoding="utf-8"))
    raw = manifest.get("emitted")
    if not isinstance(raw, list) or not all(isinstance(entry, dict) for entry in raw):
        raise AssertionError("manifest emitted field is malformed")
    return cast(tuple[dict[str, object], ...], tuple(raw))


def artifact_path(package: Path, record: dict[str, object]) -> Path:
    path = record.get("path")
    if not isinstance(path, str):
        raise AssertionError("artifact record lacks a path")
    return package / path


def smallest_lrat_case(
    packages: tuple[Path, ...],
) -> tuple[Path, dict[str, object]]:
    candidates = []
    for package in packages:
        for entry in emitted_entries(package):
            proof = entry.get("proof")
            if not isinstance(proof, dict):
                continue
            lrat = proof.get("lrat")
            cnf = entry.get("cnf")
            if not isinstance(lrat, dict) or not isinstance(cnf, dict):
                continue
            candidates.append((artifact_path(artifact_path(package, cnf).parent, lrat).stat().st_size, package, entry))
    if not candidates:
        raise AssertionError("no LRAT case found")
    _, package, entry = min(candidates, key=lambda item: item[0])
    return package, entry


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, action="append", required=True)
    parser.add_argument("--lrat-check", type=Path, required=True)
    args = parser.parse_args()
    packages = tuple(args.package)

    first = packages[0]
    manifest = first / "manifest.json"
    VERIFY.verify_manifest_digest(first, manifest)

    with tempfile.TemporaryDirectory(prefix="r9-d10-corrupt-") as raw_tmp:
        tmp = Path(raw_tmp)

        manifest_root = tmp / "manifest"
        manifest_root.mkdir()
        shutil.copy2(manifest, manifest_root / "manifest.json")
        shutil.copy2(first / "manifest.sha256", manifest_root / "manifest.sha256")
        with (manifest_root / "manifest.json").open("ab") as handle:
            handle.write(b"\n")
        must_fail(
            lambda: VERIFY.verify_manifest_digest(
                manifest_root, manifest_root / "manifest.json"
            ),
            "manifest byte",
        )

        first_entry = emitted_entries(first)[0]
        cnf_record = first_entry.get("cnf")
        if not isinstance(cnf_record, dict):
            raise AssertionError("first entry lacks a CNF record")
        source_cnf = artifact_path(first, cnf_record)

        content_root = tmp / "content"
        target_cnf = content_root / str(cnf_record["path"])
        target_cnf.parent.mkdir(parents=True)
        shutil.copy2(source_cnf, target_cnf)
        VERIFY.verify_record(content_root, cnf_record)
        with target_cnf.open("r+b") as handle:
            original = handle.read(1)
            handle.seek(0)
            handle.write(b"c" if original != b"c" else b"p")
        must_fail(
            lambda: VERIFY.verify_record(content_root, cnf_record),
            "same-size CNF byte",
        )

        shutil.copy2(source_cnf, target_cnf)
        with target_cnf.open("r+b") as handle:
            handle.truncate(target_cnf.stat().st_size - 1)
        must_fail(
            lambda: VERIFY.verify_record(content_root, cnf_record),
            "CNF truncation",
        )

        bad_source = {
            "repository_path": f"research/erdos-617-r6/{VERIFIER_PATH.name}",
            "bytes": VERIFIER_PATH.stat().st_size,
            "sha256": "0" * 64,
        }
        must_fail(
            lambda: VERIFY.verify_source_record(bad_source, VERIFIER_PATH),
            "source digest",
        )

        lrat_package, lrat_entry = smallest_lrat_case(packages)
        lrat_cnf_record = lrat_entry.get("cnf")
        proof = lrat_entry.get("proof")
        if not isinstance(lrat_cnf_record, dict) or not isinstance(proof, dict):
            raise AssertionError("smallest LRAT entry is malformed")
        lrat_record = proof.get("lrat")
        if not isinstance(lrat_record, dict):
            raise AssertionError("smallest LRAT entry lacks a proof")
        source_lrat_cnf = artifact_path(lrat_package, lrat_cnf_record)
        source_lrat = artifact_path(source_lrat_cnf.parent, lrat_record)
        lrat_root = tmp / "lrat"
        lrat_root.mkdir()
        test_cnf = lrat_root / "formula.cnf"
        test_lrat = lrat_root / "proof.lrat"
        shutil.copy2(source_lrat_cnf, test_cnf)
        shutil.copy2(source_lrat, test_lrat)
        VERIFY.replay_lrat(args.lrat_check, test_cnf, test_lrat)
        with test_lrat.open("r+b") as handle:
            handle.truncate(max(0, test_lrat.stat().st_size - 100))
        must_fail(
            lambda: VERIFY.replay_lrat(args.lrat_check, test_cnf, test_lrat),
            "LRAT truncation",
        )

    print("r9 P3 d10 corruption suite: PASS tests=5 baseline_lrat=PASS")


if __name__ == "__main__":
    main()
