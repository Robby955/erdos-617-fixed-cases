import GlobalRowBudgets
import ExteriorRowEdges
import DestinationCost
import ConstructPruning

/-! Appendix A, §§1–3 from an arbitrary loop-free edge coloring. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V]

/-- Uniform first-stage source cap per destination, measured in units of r. -/
theorem assigned_le_omega (T : Trace V r)
    (qual : ∀ v ∈ T.firstSources, unused T (T.destination v) ≤ 1/1200)
    (paid : ∀ i, (61/250)*assigned T i ≤ unused T i) (i : ℕ) :
    assigned T i ≤ 5/1464 := by
  by_cases h : (T.firstSources.filter fun x ↦ T.destination x = i).Nonempty
  · obtain ⟨x,hx⟩ := h
    obtain ⟨mem,eq⟩ := mem_filter.mp hx
    have budget := qual x mem
    rw [eq] at budget
    linarith only [budget,paid i]
  · simp [assigned,not_nonempty_iff_eq_empty.mp h]
    norm_num

/-- Graph data kept with the width selection for use in the exterior argument. -/
structure Prepared (T : Trace V r) : Prop where
  rows : ∀ x, T.row x < r
  least : Sparsest T.color T.target
  pivots : PivotRows T.color T.target T.row
  legal : T.Legal
  destinations : ∀ x ∈ T.firstSources, T.destination x ∈ qualifying T
  sequential : Sequential T
  first_stopped : FirstStageStopped T
  stopped : ∀ x ∈ live T, (Transversal.neighbors T.crossGraph (live T) x).card ≤ degreeBound r
  paid : ∀ i, (61/250)*assigned T i ≤ unused T i
  source_cap : ∀ i, assigned T i ≤ 5/1464
  width : HasWidth T

/-- The only inputs are the order, the cutoff and the original coloring.
Either an (r+1)-set already misses a color, or the actual retained cliques
satisfy the three width estimates at one common threshold. -/
theorem witness_or_prepared (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color = color ∧ Prepared T := by
  by_cases no : Witness color
  · exact Or.inl no
  obtain ⟨j,row,least,labels,pivots⟩ := (witness_or_raw_rows color (by omega)).resolve_left no
  have pos : 0 < r := by omega
  obtain ⟨T,color_eq,target_eq,row_eq,legal,dest,stop,first,seq⟩ :=
    exists_pruning_trace color j row pos
  have noT : ¬Witness T.color := color_eq ▸ no
  have inRange (v) (hv : v ∈ T.firstSources) := (qualifying_bounds T pos (dest v hv)).1
  have qual (v) (hv : v ∈ T.firstSources) := (qualifying_bounds T pos (dest v hv)).2.2
  have cost := destination_cost_of_cross_count T legal (by omega) qual
    (exterior_row_edges T (by omega) noT)
  have rowsT : ∀ x, T.row x < r := row_eq ▸ labels
  have leastT : Sparsest T.color T.target := by rwa [color_eq,target_eq]
  have pivotsT : PivotRows T.color T.target T.row := by rwa [color_eq,target_eq,row_eq]
  exact Or.inr ⟨T,color_eq,rowsT,leastT,pivotsT,legal,dest,seq,first,stop,cost,
    assigned_le_omega T qual cost,width_of_pruning T hr order noT rowsT leastT pivotsT legal
      inRange stop (fun i _ ↦ cost i) qual⟩

end
end Erdos617.ColoredLists
