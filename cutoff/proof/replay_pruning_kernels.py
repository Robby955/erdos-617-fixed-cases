"""Compile and replay the Appendix A overlap or width proof in a pinned Lake environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


OVERLAP_NAMES = (
    "charge_at_oversized",
    "overlap_pos_iff",
    "overlap_le_deleted_quotas",
    "incidence_budget",
    "deleted_quota_rebate",
    "overlap_le_paper_allowance",
    "normalized_ordinary_bound",
)
WIDTH_NAMES = (
    "Erdos617.WidthIntegral.failure_budget",
    "Erdos617.WidthEndpoint.small",
    "Erdos617.WidthIntegral.exists_heaviest",
    "Erdos617.WidthIntegral.omitted_slots_of_row_charges",
    "Erdos617.WidthIntegral.selection_of_level",
    "Erdos617.WidthIntegral.budget_of_counts",
    "Erdos617.WidthIntegral.at_scale",
    "Erdos617.WidthIntegral.width_at_144",
    "Erdos617.WidthIntegral.width_at_reduced_cutoff",
    "Erdos617.WidthIntegral.width_from_row_counts",
)


def replay(part: str = "overlap", lean_only: bool = False) -> None:
    source_dir = Path(__file__).resolve().parent
    if part == "width":
        modules = ("RetainedWidth", "WeightedWidth", "WidthEndpoint", "WidthIntegral",
                   "RowWidth", "CommonWidth")
        names = WIDTH_NAMES
    else:
        modules = ("PruningOverlap",)
        names = tuple("Erdos617.PruningOverlap.Trace." + name for name in OVERLAP_NAMES)

    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([tmp, env["LEAN_PATH"]])
        for module in modules:
            subprocess.run(["lean", "-R", source_dir, "-o", directory / f"{module}.olean",
                            source_dir / f"{module}.lean"], env=env, check=True)
        audit = f"import {modules[-1]}\n" + "".join(f"#print axioms {name}\n" for name in names)
        subprocess.run(["lean", "--stdin"], input=audit, text=True, env=env, check=True)
        if lean_only:
            return

        export = directory / f"{part}.ndjson"
        with export.open("wb") as stream:
            subprocess.run(["leanexport", modules[-1], "--", *names], env=env, stdout=stream,
                           check=True)

        config = directory / "nanoda.json"
        config.write_text(json.dumps({
            "export_file_path": str(export),
            "use_stdin": False,
            "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "unpermitted_axiom_hard_error": True,
            "num_threads": 2,
            "nat_extension": True,
            "string_extension": True,
        }))
        subprocess.run(["leanchecker", "--from-export", export], check=True)
        subprocess.run(["lean4lean", "--import", export], check=True)
        subprocess.run(["nanoda_bin", config], check=True)
        digest = hashlib.sha256()
        with export.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
        print(f"All three kernels accepted the export of {len(names)} {part} theorems.")
        print("Export SHA-256", digest.hexdigest())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("part", choices=("overlap", "width"), nargs="?", default="overlap")
    parser.add_argument("--lean-only", action="store_true", help="compile and print axioms")
    args = parser.parse_args()
    replay(args.part, args.lean_only)
