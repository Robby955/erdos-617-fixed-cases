"""Compile and replay the Appendix A graph and width proofs in a pinned Lake environment."""

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
                    "ConstructPruning", "ColoringWidth", "CutInputs")
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

ENLARGEMENT_MODULES = (*CLIQUE_MODULES, "PrescribedProducts", "EdgeProductTransversal",
                       "PrescribedListCounts", "AuxiliaryExtension", "OrdinaryExtension",
                       "ColoredAuxiliaryExtension", "PrescribedCompletion", "UniqueAttachment",
                       "AttachmentArena", "OmittedRepresentatives", "ColoredAttachment",
                       "ColoringEnlargement")
ENLARGEMENT_NAMES = (
    "Erdos617.Transversal.exists_of_edge_products",
    "Erdos617.PrescribedProducts.two_exterior_product",
    "Erdos617.PrescribedProducts.one_exterior_product",
    "Erdos617.PrescribedLists.auxiliary_representatives",
    "Erdos617.ColoredLists.colored_auxiliary_representatives",
    "Erdos617.ColoredLists.extend_prescribed_ordinary",
    "Erdos617.ColoredLists.complete_prescribed_rows",
    "Erdos617.UniqueAttachment.two_row_rectangle",
    "Erdos617.UniqueAttachment.enlarged_deficit_sum",
    "Erdos617.ColoredLists.actual_can_extend",
    "Erdos617.ColoredLists.witness_or_shortage_or_enlargement",
)

SHORTAGE_MODULES = (*ENLARGEMENT_MODULES, "AuxiliaryDeficitCaps", "TaggedDeficitCaps",
                    "CliqueArrivalPrice", "MultipleArrivalPrice", "ArrivalSummation",
                    "SenderPayment", "ExteriorShortage")
SHORTAGE_NAMES = (
    "Erdos617.ColoredLists.clique_arrival_capacity",
    "Erdos617.ColoredLists.clique_pair_capacity",
    "Erdos617.AuxiliaryMoments.peeled_deficit_cap",
    "Erdos617.ColoredLists.tagged_deficit_cap",
    "Erdos617.ColoredLists.clique_arrival_price_in_edges",
    "Erdos617.ColoredLists.two_large_row_price",
    "Erdos617.ColoredLists.three_large_rows_price",
    "Erdos617.ColoredLists.arrival_sum_contradiction",
    "Erdos617.ColoredLists.priced_arena_impossible",
    "Erdos617.ColoredLists.excludes_enlarged_rows",
    "Erdos617.ColoredLists.witness_or_exterior_shortage",
)

SENDER_MODULES = (*SHORTAGE_MODULES, "StrongRowCharge", "SenderDestinations",
                  "HeavyRowSenders", "SenderPopulation", "SenderRetry", "RetainedSenders")
SENDER_NAMES = (
    "Erdos617.ColoredLists.witness_or_exterior_shortage",
    "Erdos617.ColoredLists.mem_senderSet",
    "Erdos617.ColoredLists.sender_ledger",
    "Erdos617.ColoredLists.retained_heavy_senders",
    "Erdos617.ColoredLists.retained_row_charge",
    "Erdos617.ColoredLists.distinct_sender_shortfall",
    "Erdos617.SenderRetry.mass_one",
    "Erdos617.SenderRetry.mass_nonnegative",
    "Erdos617.SenderRetry.success_probability",
    "Erdos617.SenderRetry.output_atom",
    "Erdos617.ColoredLists.retained_retry_surplus",
)


SAMPLE_MODULES = (*SENDER_MODULES, "StrongAssignments", "EligibleSenders", "JointSenderLaw",
                  "MarkedSenderLaw", "SenderSampleMoments", "RepresentativeMass", "ColoringSenderLaw",
                  "DistinctRowConflicts", "SameRowPairs", "SameRowConflicts", "RepresentativeRepairs",
                  "ColoringSample")
SAMPLE_NAMES = (
    "Erdos617.ColoredLists.eligible_mass_with_surplus",
    "Erdos617.ColoredLists.eligible_thinning",
    "Erdos617.MarkedSender.mark_count_variance",
    "Erdos617.ColoredLists.sender_atom_bound",
    "Erdos617.SameRowConflicts.expected_edges_le_cut",
    "Erdos617.RepresentativeCut.between_row_groups",
    "Erdos617.RepresentativeRepairs.compatible",
    "Erdos617.ColoredLists.sampled_exterior_order",
    "Erdos617.ColoredLists.sampled_representative_cost",
    "Erdos617.ColoredLists.witness_or_sender_sample",
)


CUT_MODULES = (*SAMPLE_MODULES, "SenderSupport", "ExcessCircle", "CircleStartLaw",
               "ExcessArcRepairs", "ArcRepairUnion", "RepairedIndependence", "LoadCap",
               "SampleRepairGraph", "ForeignRowLoads", "ColoringRepairCost", "SignedSampleCut",
               "SignedCutExpectation", "ColoringSignedCut", "TestedRowMoments",
               "EdgeRecovery", "ColoringTestedCut", "RecoveredTest")
CUT_NAMES = (
    "Erdos617.ColoredLists.represented_support",
    "Erdos617.ColoredLists.sender_load_fits",
    "Erdos617.ArcRepair.expected_excess_union",
    "Erdos617.ColoredLists.sample_repair_cap",
    "Erdos617.ColoredLists.foreign_load_le_interrow_cut",
    "Erdos617.ColoredLists.sampled_union_repair_cost",
    "Erdos617.SignedSampleCut.exterior_interrow_identity",
    "Erdos617.SignedSampleCut.full_incidence_cut",
    "Erdos617.ColoredLists.expected_fixed_cut",
    "Erdos617.TestedRows.expected_cross_deficit",
    "Erdos617.TestedRows.expected_slots",
    "Erdos617.EdgeRecovery.coloring_pair_recovery",
    "Erdos617.ColoredLists.tested_cut_bound",
    "Erdos617.ColoredLists.recovered_tested_cut",
)


LOAD_MODULES = (*CUT_MODULES, "HeavyLoadIncidence", "HeavyLoadBound", "HeavyLoadTotals",
                "HeavyLoadTests", "ManuscriptRowTest")
LOAD_NAMES = tuple("Erdos617.ColoredLists." + name for name in (
    "disjoint_load_incidence", "threshold_heavy_count", "foreign_load_le_distinct_edges",
    "heavy_load_height", "retained_load_budgets", "heavy_load_total", "manuscript_row_test",
    "manuscript_test_mass", "manuscript_tested_cut",
))


OVERSAMPLE_MODULES = (*LOAD_MODULES, "PairThinning", "RepairThinning", "OversamplingFloor",
                      "OversamplingPass", "RepairEnvelope", "OversamplingBudget", "EligibilitySurplus",
                      "RetryDeficit", "TwoOversamplingPasses", "OneRowCapacity", "ModerateDestinations")
OVERSAMPLE_NAMES = (
    "Erdos617.MarkedSender.oversample_weight",
    "Erdos617.FiniteLaw.expect_pair_set_card_le",
    "Erdos617.ColoredLists.sample_pair_local",
    "Erdos617.ColoredLists.oversample_repairs",
    "Erdos617.SignedSampleCut.oversample_floor",
    "Erdos617.ColoredLists.oversample_expected_floor",
    "Erdos617.ColoredLists.oversampling_pass",
    "Erdos617.ColoredLists.untruncated_eligibility",
    "Erdos617.ColoredLists.coloring_repair_envelope",
    "Erdos617.ColoredLists.first_pass_unique_weight",
    "Erdos617.ColoredLists.normalized_repair_budget",
    "Erdos617.ColoredLists.oversample_guards",
    "Erdos617.ColoredLists.eligibility_surplus",
    "Erdos617.ColoredLists.unique_miss_charge",
    "Erdos617.ColoredLists.retry_deficit_weight",
    "Erdos617.ColoredLists.two_oversampling_passes",
    "Erdos617.ColoredLists.witness_or_two_passes",
    "Erdos617.ColoredLists.normalized_one_row_cut",
    "Erdos617.ColoredLists.moderate_partition",
    "Erdos617.ColoredLists.moderate_cut_payment",
    "Erdos617.ColoredLists.moderate_square_sum",
)


CAPACITY_MODULES = (*OVERSAMPLE_MODULES, "MixedSenderCapacity")
CAPACITY_NAMES = tuple("Erdos617.ColoredLists." + name for name in (
    "eligible_mass_of_row_allowances", "mixed_row_capacity",
    "marked_sender_payment", "mixed_sender_capacity",
))


CUTOFF_MODULES = (*CAPACITY_MODULES, "FinalSignedCut", "SignedCutInterval", "CutoffCells",
                  "CertifiedWidthCell", "BalancedColoringCutoff")
CUTOFF_NAMES = (
    "Erdos617.ColoredLists.mixed_sender_capacity",
    "Erdos617.ColoredLists.coloring_signed_cut",
    "Erdos617.ColoredLists.signed_interval",
    "Erdos617.CutoffCells.all_cells_pass",
    "Erdos617.CutoffCells.real_endpoints",
    "Erdos617.missing_color_of_large_order",
    "Erdos617.erdos_617_of_ge_cutoff",
    "Erdos617.balancedColoringAt_of_ge_reduced_cutoff",
    "Erdos617.paper_cutoff",
    "Erdos617.finite_counterexample_orders",
)


def local_dependencies(source_dir: Path, root: str) -> tuple[str, ...]:
    """Return local Lean imports before their dependents for a clean replay."""
    ordered = []
    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        for line in (source_dir / f"{module}.lean").read_text().splitlines():
            if line.startswith("import "):
                for name in line.split()[1:]:
                    if (source_dir / f"{name}.lean").is_file():
                        visit(name)
        ordered.append(module)

    visit(root)
    return tuple(ordered)


THIRD_CORE_NAMES = (
    "Erdos617.ColoredLists.witness_or_pruned",
    "Erdos617.PackingLists.budget_at_degree",
    "Erdos617.ColoredLists.missing_floor_of_counts",
    "Erdos617.ThirdPruning.three_pass_cost",
    "Erdos617.ThirdPruning.restrict_live",
    "Erdos617.ThirdPruning.restrict_recorded",
    "Erdos617.ThirdPruning.restrict_first_stopped",
    "Erdos617.ThirdPruning.hole_blocks_other_rows",
    "Erdos617.ThirdPruning.charge_actual_holes",
    "Erdos617.ThirdPruning.missing_mass",
    "Erdos617.ThirdPruning.deleted_second_moment",
    "Erdos617.ThirdPruning.paired_margin",
    "Erdos617.ThirdPruning.zero_branch_impossible",
    "Erdos617.ThirdPruning.selected_at_143",
    "Erdos617.contradiction_of_selected_rows",
)


def replay(part: str = "overlap", lean_only: bool = False) -> None:
    source_dir = Path(__file__).resolve().parent
    if part == "cutoff-143":
        modules = local_dependencies(source_dir, "ThirdPruningCutoff")
        names = (
            "Erdos617.missing_color_at_143",
            "Erdos617.erdos_617_of_ge_two_pow_143",
            "Erdos617.balancedColoringAt_of_ge_two_pow_143",
        )
    elif part == "third-core":
        modules = local_dependencies(source_dir, "ThirdPruningCore")
        names = THIRD_CORE_NAMES
    elif part == "cutoff":
        modules, names = CUTOFF_MODULES, CUTOFF_NAMES
    elif part == "capacity":
        modules, names = CAPACITY_MODULES, CAPACITY_NAMES
    elif part == "oversampling":
        modules, names = OVERSAMPLE_MODULES, OVERSAMPLE_NAMES
    elif part == "loads":
        modules, names = LOAD_MODULES, LOAD_NAMES
    elif part == "cut":
        modules, names = CUT_MODULES, CUT_NAMES
    elif part == "sampling":
        modules, names = SAMPLE_MODULES, SAMPLE_NAMES
    elif part == "senders":
        modules, names = SENDER_MODULES, SENDER_NAMES
    elif part == "shortage":
        modules, names = SHORTAGE_MODULES, SHORTAGE_NAMES
    elif part == "enlargement":
        modules, names = ENLARGEMENT_MODULES, ENLARGEMENT_NAMES
    elif part == "cliques":
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
    parser.add_argument("part", choices=("overlap", "width", "lists", "coloring", "exterior", "cliques", "enlargement", "shortage", "senders", "sampling", "cut", "loads", "oversampling", "capacity", "cutoff", "third-core", "cutoff-143"), nargs="?", default="overlap")
    parser.add_argument("--lean-only", action="store_true", help="compile and print axioms")
    args = parser.parse_args()
    replay(args.part, args.lean_only)
