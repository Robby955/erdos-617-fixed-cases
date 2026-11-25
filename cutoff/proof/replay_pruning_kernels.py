"""Compile and replay the Appendix A pruning and width proofs in a pinned Lake environment."""

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

LIST_NAMES = (
    "Erdos617.Transversal.exists_partial",
    "Erdos617.PackingLists.exists_packing",
    "Erdos617.PackingLists.real_representatives",
    "Erdos617.PackingLists.pairs_le_shortfall",
    "Erdos617.PackingLists.count_survivors",
    "Erdos617.PackingLists.exists_list_bounds",
    "Erdos617.PackingLists.chosen_oversize_bound",
    "Erdos617.PackingLists.ListBounds.count_le",
    "Erdos617.PackingLists.omitted_ordinary",
    "Erdos617.PruningOverlap.Trace.source_cost",
    "Erdos617.ColoredLists.balanced_iff",
    "Erdos617.ColoredLists.caps_of_no_witness",
    "Erdos617.ColoredLists.witness_or_lists",
    "Erdos617.ColoredLists.incidence_total",
    "Erdos617.ColoredLists.pruning_rates",
    "Erdos617.ColoredLists.witness_or_width",
    "Erdos617.RowExtraction.exists_ordered_rows",
    "Erdos617.ColoredLists.witness_or_raw_rows",
    "Erdos617.ColoredLists.edge_lower_of_independence",
    "Erdos617.ColoredLists.sum_other_colors",
    "Erdos617.ColoredLists.other_color_floor",
    "Erdos617.ColoredLists.unused_nonneg_of_no_witness",
    "Erdos617.ColoredLists.forward_total",
    "Erdos617.ColoredLists.forward_floor_of_pivots",
    "Erdos617.ColoredLists.witness_or_width_of_pivots",
)

WIDTH_MODULES = ("RetainedWidth", "WeightedWidth", "WidthEndpoint", "WidthIntegral",
                 "RowWidth", "CommonWidth")

LIST_MODULES = (*WIDTH_MODULES, "CutoffStatement", "PruningOverlap", "PartialTransversal",
                "PackingLists", "ListDeficit", "ChosenRows", "ColoringLists", "PrunedWidth",
                "RowExtraction", "OrderedRows", "RawColorBudget", "RawColorRows")

COLORING_MODULES = (*LIST_MODULES, "RawEdgeIdentity", "PivotCross", "SparseColorCount",
                    "RawMoments", "GlobalRowBudgets", "ExteriorRowEdges", "DestinationCost",
                    "ConstructPruning", "ColoringWidth")
COLORING_NAMES = tuple("Erdos617.ColoredLists." + name for name in (
    "raw_edge_identity", "pivot_cross_count", "sparse_edge_cap", "raw_stability",
    "global_raw_budgets", "exterior_row_edges", "destination_cost_of_cross_count",
    "exists_pruning_trace", "FirstStageStopped.live_bound", "assigned_le_omega", "witness_or_prepared",
))

EXTERIOR_MODULES = (*COLORING_MODULES, "CountingTransversal", "OrdinaryRepresentatives",
                    "OrdinaryTrim", "AuxiliaryColoring", "GraphPartitionCount", "AuxiliaryDeficit",
                    "AuxiliaryMoments", "ExteriorAuxiliary")
EXTERIOR_NAMES = (
    "Erdos617.Transversal.exists_of_row_conflicts",
    "Erdos617.ColoredLists.sublist_conflict_bound",
    "Erdos617.ColoredLists.retained_representatives",
    "Erdos617.ColoredLists.exterior_independence_cap",
    "Erdos617.ColoredLists.temporary_row_bounds",
    "Erdos617.ColoredLists.exists_auxiliary_coloring",
    "Erdos617.GraphPartitionCount.pivot_edge_budget",
    "Erdos617.GraphPartitionCount.pivot_missing_budget",
    "Erdos617.GraphPartitionCount.auxiliary_deficit",
    "Erdos617.AuxiliaryMoments.tangent_floor",
    "Erdos617.AuxiliaryMoments.auxiliary_square_budget",
    "Erdos617.AuxiliaryMoments.auxiliary_normalized",
    "Erdos617.ColoredLists.witness_or_exterior_auxiliary",
)

CLIQUE_MODULES = (*EXTERIOR_MODULES, "AuxiliaryPeeling", "SublistEdges", "AuxiliaryRowFloor",
                  "AuxiliaryCliques")
CLIQUE_NAMES = (
    "Erdos617.ColoredLists.witness_or_exterior_auxiliary",
    "Erdos617.AuxiliaryPeeling.exists_live",
    "Erdos617.Transversal.conflicts_le_induced_cross_edges",
    "Erdos617.AuxiliaryMoments.deficit_plus_deletions",
    "Erdos617.AuxiliaryMoments.live_row_floor",
    "Erdos617.ColoredLists.surviving_auxiliary_cliques",
    "Erdos617.ColoredLists.exists_surviving_auxiliary_cliques",
    "Erdos617.ColoredLists.auxiliary_cliques_of_failed_shortage",
)


def replay(part: str = "overlap", lean_only: bool = False) -> None:
    source_dir = Path(__file__).resolve().parent
    if part == "cliques":
        modules, names = CLIQUE_MODULES, CLIQUE_NAMES
    elif part == "exterior":
        modules, names = EXTERIOR_MODULES, EXTERIOR_NAMES
    elif part == "coloring":
        modules, names = COLORING_MODULES, COLORING_NAMES
    elif part == "lists":
        modules = LIST_MODULES
        names = LIST_NAMES
    elif part == "width":
        modules = WIDTH_MODULES
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
    parser.add_argument("part", choices=("overlap", "width", "lists", "coloring", "exterior", "cliques"), nargs="?", default="overlap")
    parser.add_argument("--lean-only", action="store_true", help="compile and print axioms")
    args = parser.parse_args()
    replay(args.part, args.lean_only)
