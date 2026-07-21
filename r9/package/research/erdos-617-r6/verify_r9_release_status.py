#!/usr/bin/env python3
"""Verify the fixed-r=9 release ledger and its lightweight dependencies."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
HANDOFF = REPO_ROOT / "output" / "ERDOS_617_R9_RELEASE_HANDOFF.md"
CHECKPOINT = REPO_ROOT / "output" / "ERDOS_617_R9_CURRENT_CHECKPOINT.md"
PAPER = REPO_ROOT / "research" / "erdos-617-r9-manuscript" / "main.tex"
M64_ARTIFACT = HERE / "artifacts" / "r9-order26-m64"
M64_RECEIPT = M64_ARTIFACT / "cadical_receipt.json"
M64_MANIFEST = M64_ARTIFACT / "manifest.json"
M64_CLASSIFICATION_SHA256 = (
    "e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331"
)
ORDER27_ROOT = (
    REPO_ROOT
    / "output"
    / "erdos-617-artifacts"
    / "r9-p93-order27-d10-20260721"
)
ORDER27_MANIFEST_DIGESTS = (
    "f332adb9327c02b2b9964a1d781baae75d27371a83995dc3c1f7393b35c09cba",
    "0df642bb21e52310ec19f479d5ec62fe179a0b075738643bb165baeef7dcda40",
    "7427d8c307411374f332056bdd3638ff26c9d70c6c1283458d87f6313fd1bc2f",
    "e1cc2b4b6f2643d16bc3ba64d50e7e1e9cf73d7043a19f632571bf328c158d1d",
)
HISTORICAL_STATUS_FILES = (
    REPO_ROOT / "output" / "ERDOS_617_CODEX_HANDOFF.md",
    HERE / "R9_OUTER_D8_NEIGHBORHOOD_DEFECT_WALL.md",
    HERE / "R9_P93_ORDER26_M58_REDUCED_FRONTIER.md",
    HERE / "R9_P93_ORDER26_M59_REDUCED_FRONTIER.md",
    HERE / "R9_P93_ORDER26_D8_SHELL_CLASSIFICATION.md",
    HERE / "R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md",
    HERE / "R9_P93_ORDER26_D8_DEPENDENCY_AUDIT.md",
    HERE / "R9_P93_ORDER26_M64_REDUCED_FRONTIER.md",
    HERE / "R9_P93_D10_CERTIFICATE_ARCHITECTURE.md",
    HERE / "R9_P93_D10_CORE_DEGREE_SUM_REDUCTION.md",
    HERE / "R9_P93_ORDER27_CLOSURE.md",
    HERE / "R9_P93_ORDER27_DEPENDENCY_AUDIT.md",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require_text(path: Path, fragments: tuple[str, ...]) -> None:
    text = path.read_text(encoding="utf-8")
    for fragment in fragments:
        if fragment not in text:
            raise AssertionError(f"{path} lacks required text: {fragment}")


def check_handoff() -> None:
    require_text(
        HANDOFF,
        (
            "LOCALLY PROVED; PUBLIC PACKAGE VERIFIED; EXTERNAL REVIEW PENDING",
            "Every nine-coloring",
            "P_3(26)\\ge121",
            "\\mathcal P_3(27)=\\varnothing",
            "P_4(37)\\ge192",
            "192,\\ 227,\\ 264,\\ 301,\\ 338",
            "5,\\ 4,\\ 3,\\ 2,\\ 3",
            "All 45 outer cells are strict or empty",
            "arbitrary \\(r\\) remains open",
        ),
    )
    require_text(
        CHECKPOINT,
        (
            "LOCALLY PROVED; PUBLIC PACKAGE VERIFIED; EXTERNAL REVIEW PENDING",
            "176+M\\ge192",
            "5,4,3,2,3",
        ),
    )
    require_text(
        PAPER,
        (
            "The Nine-Color Case",
            "\\begin{theorem}\\label{thm:main}",
            "M=45-e(H[A])",
            "176+M",
            "101,880-state CaDiCaL reconstruction",
            "does not settle Erd\\H{o}s Problem 617",
        ),
    )


def check_historical_banners() -> None:
    for path in HISTORICAL_STATUS_FILES:
        first_lines = "\n".join(
            path.read_text(encoding="utf-8").splitlines()[:30]
        )
        if "SUPERSEDED" not in first_lines:
            raise AssertionError(f"historical status lacks banner: {path}")


def check_order27_manifests() -> None:
    digest_files = sorted(ORDER27_ROOT.glob("*/manifest.sha256"))
    if len(digest_files) != 4:
        raise AssertionError(f"expected four order-27 manifests, got {len(digest_files)}")
    actual = []
    for digest_file in digest_files:
        manifest = digest_file.with_name("manifest.json")
        fields = digest_file.read_text(encoding="ascii").strip().split()
        digest = sha256(manifest)
        if fields != [digest, "manifest.json"]:
            raise AssertionError(f"manifest digest mismatch: {manifest}")
        actual.append(digest)
    if tuple(actual) != ORDER27_MANIFEST_DIGESTS:
        raise AssertionError(f"wrong order-27 manifest sequence: {actual}")


def checked_receipt(raw: Any) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raise AssertionError("m=64 receipt must be an object")
    expected = {
        "raw_states": 101880,
        "unsat": 101880,
        "sat": 0,
        "unknown": 0,
        "classification_sha256": M64_CLASSIFICATION_SHA256,
        "status": "PASS",
    }
    for key, value in expected.items():
        if raw.get(key) != value:
            raise AssertionError(f"wrong m=64 receipt field {key}: {raw.get(key)!r}")
    return raw


def check_m64(allow_pending: bool) -> str:
    if not M64_RECEIPT.exists() or not M64_MANIFEST.exists():
        if allow_pending:
            return "PENDING"
        raise AssertionError("m=64 receipt or manifest is missing")
    checked_receipt(json.loads(M64_RECEIPT.read_text(encoding="utf-8")))
    command = [
        sys.executable,
        str(HERE / "verify_r9_p93_order26_m64_manifest.py"),
        "--manifest",
        str(M64_MANIFEST),
    ]
    subprocess.run(command, cwd=REPO_ROOT, check=True)
    return "PASS"


def run_lightweight_replays() -> None:
    for script in (
        HERE / "verify_colored_core_ladder.py",
        HERE / "verify_r9_d8_full_color_bridge.py",
    ):
        subprocess.run([sys.executable, str(script)], cwd=REPO_ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-pending-m64", action="store_true")
    parser.add_argument("--skip-runtime", action="store_true")
    args = parser.parse_args()

    check_handoff()
    check_historical_banners()
    check_order27_manifests()
    m64_status = check_m64(args.allow_pending_m64)
    if not args.skip_runtime:
        run_lightweight_replays()

    print("fixed_r9_theorem=LOCALLY_PROVED")
    print(f"m64_independent_audit={m64_status}")
    print("order27_manifests=4")
    print("historical_status_banners=PASS")
    print("universal_erdos_617=OPEN")
    print("status=PASS" if m64_status == "PASS" else "status=PASS_PENDING_M64")


if __name__ == "__main__":
    main()
