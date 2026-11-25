"""Run with lake env python3 -B proof/replay_pruning_kernels.py in the cutoff project."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


DECLARATIONS = (
    "charge_at_oversized",
    "overlap_pos_iff",
    "overlap_le_deleted_quotas",
    "incidence_budget",
    "deleted_quota_rebate",
    "overlap_le_paper_allowance",
    "normalized_ordinary_bound",
)


def replay() -> None:
    source = Path(__file__).resolve().with_name("PruningOverlap.lean")
    names = ["Erdos617.PruningOverlap.Trace." + name for name in DECLARATIONS]
    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        module = directory / "PruningOverlap.olean"
        export = directory / "overlap.ndjson"
        subprocess.run(["lean", "-R", source.parent, "-o", module, source], check=True)
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([tmp, env["LEAN_PATH"]])
        with export.open("wb") as stream:
            subprocess.run(["leanexport", "PruningOverlap", "--", *names],
                           env=env, stdout=stream, check=True)

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
        print(f"All three kernels accepted the export of {len(names)} overlap theorems.")
        print("Export SHA-256", hashlib.sha256(export.read_bytes()).hexdigest())


if __name__ == "__main__":
    replay()
