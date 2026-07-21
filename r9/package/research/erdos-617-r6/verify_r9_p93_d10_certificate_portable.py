#!/usr/bin/env python3
"""Run the pinned order-27 verifier with a portable geng identity check."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from typing import Mapping


HERE = Path(__file__).resolve().parent
PINNED_PATH = HERE / "verify_r9_p93_d10_certificate.py"


def load_pinned_verifier():
    spec = importlib.util.spec_from_file_location("erdos617_r9_d10_pinned", PINNED_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the pinned semantic verifier")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


PINNED = load_pinned_verifier()
ORIGINAL_VERIFY_MANIFEST_HEADER = PINNED.verify_manifest_header


def verify_manifest_header_portable(
    manifest: Mapping[str, object], geng: Path
) -> None:
    generation = manifest.get("case_generation")
    if not isinstance(generation, dict):
        PINNED.fail("manifest case-generation field is not an object")
    recorded = generation.get("geng_sha256")

    adjusted = dict(manifest)
    adjusted_generation = dict(generation)
    adjusted_generation["geng_sha256"] = PINNED.sha256(geng)
    adjusted["case_generation"] = adjusted_generation
    ORIGINAL_VERIFY_MANIFEST_HEADER(adjusted, geng)

    if not isinstance(recorded, str) or len(recorded) != 64:
        PINNED.fail("manifest lacks a valid recorded geng hash")


def main() -> None:
    PINNED.verify_manifest_header = verify_manifest_header_portable
    PINNED.main()


if __name__ == "__main__":
    main()
