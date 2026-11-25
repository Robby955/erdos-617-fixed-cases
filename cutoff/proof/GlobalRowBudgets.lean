import RawMoments
import RawEdgeIdentity
import SparseColorCount
import PivotCross

/-! Equation (1) and the three global budgets on the same raw partition. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- On the original graph, the inter-row target edges and twice the internal
missing edges each fit below the sparsity allowance minus the row variance. -/
theorem raw_stability (hr : 2 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ x, T.row x < r) (least : Sparsest T.color T.target)
    (pivots : PivotRows T.color T.target T.row) :
    let B := (r:ℝ)^2-r+1-∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2
    (T.crossGraph.edgeFinset.card:ℝ) ≤ B ∧ 2*(∑ i ∈ range r, (internalMissing T i:ℝ)) ≤ B :=
  raw_stability_of_counts T hr order rows (raw_edge_identity T rows) (pivot_cross_count T rows pivots)
    (sparse_edge_cap T.color T.target least)

/-- The width theorem's three raw budgets follow from the coloring, including
the variance rebate in the total unused allowance. -/
theorem global_raw_budgets (hr : 2 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ x, T.row x < r) (least : Sparsest T.color T.target)
    (pivots : PivotRows T.color T.target T.row) (no : ¬Witness T.color) :
    (∑ i ∈ range r, rawSurplus T i) ≤ 1/2 ∧
      (∑ i ∈ range r, unused T i) ≤ (1-variance T)/2 ∧
      (T.crossGraph.edgeFinset.card:ℝ) ≤ (1-variance T)*(r:ℝ)^2 := by
  obtain ⟨cross,missing⟩ := raw_stability T hr order rows least pivots
  exact budgets_of_stability T hr order rows no cross missing

/-- Once the two stages of pruning have been justified, no global budget
needs to be supplied to obtain the threshold. -/
theorem width_of_pruning (hr : 255*2^136 ≤ r) (order : Fintype.card V = r^2+1)
    (no : ¬Witness T.color) (rows : ∀ x, T.row x < r) (least : Sparsest T.color T.target)
    (pivots : PivotRows T.color T.target T.row) (legal : T.Legal)
    (dest : ∀ v ∈ T.firstSources, T.destination v < r)
    (stop : ∀ v ∈ live T, (Transversal.neighbors T.crossGraph (live T) v).card ≤ degreeBound r)
    (localCost : ∀ i ∈ range r, (61/250)*assigned T i ≤ unused T i)
    (qual : ∀ v ∈ T.firstSources, unused T (T.destination v) ≤ 1/1200) : HasWidth T := by
  obtain ⟨sizes,costs,cross⟩ := global_raw_budgets T (by omega) order rows least pivots no
  have hv : 0 ≤ variance T := by unfold variance; positivity
  exact (witness_or_width_of_pivots T hr order rows pivots legal dest stop sizes
    (costs.trans (by linarith only [hv])) cross localCost qual).resolve_left no

end
end Erdos617.ColoredLists
