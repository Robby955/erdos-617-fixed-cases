import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The row estimate in Appendix A, Section 1 of the cutoff paper.
The graph H consists of all edges whose color differs from the target color.
Its complement consists of the target edges. -/

namespace Erdos617.RowExtraction

open Finset

variable {V : Type*} [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
private theorem sum_internal_degrees (row : Finset V) :
    ∑ x ∈ row, (row.filter (H.Adj x)).card =
        2 * (H.induce (row : Set V)).edgeFinset.card := by
  classical
  have degree (x : row) :
      (H.induce (row : Set V)).degree x = (row.filter (H.Adj x)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun (y : row) _ => (y : V))
    · intro y hy
      exact Finset.mem_filter.mpr
        ⟨y.property, (SimpleGraph.mem_neighborFinset (H.induce (row : Set V)) x y).mp hy⟩
    · intro y _ z _ h
      exact Subtype.ext h
    · intro y hy
      obtain ⟨inside, adj⟩ := Finset.mem_filter.mp hy
      exact ⟨⟨y, inside⟩,
        (SimpleGraph.mem_neighborFinset (H.induce (row : Set V)) x ⟨y, inside⟩).mpr adj, rfl⟩
  rw [← (H.induce (row : Set V)).sum_degrees_eq_twice_card_edges]
  simp_rw [degree]
  exact (Finset.sum_coe_sort row _).symm

/-- For any maximum-degree pivot, a vertex in its row has at least as many
target neighbors in later rows as nontarget neighbors in its own row. An internal
edge has two ends in the row and a forward edge has one. -/
theorem forward_edges_of_max_degree (remaining : Finset V) (pivot : V)
    (hmax : ∀ x ∈ remaining,
      (remaining.filter (H.Adj x)).card ≤ (remaining.filter (H.Adj pivot)).card) :
    let later := remaining.filter (H.Adj pivot)
    let row := remaining \ later
    (∀ x ∈ row, (row.filter (H.Adj x)).card ≤ (later.filter (Hᶜ.Adj x)).card) ∧
    2 * (H.induce (row : Set V)).edgeFinset.card ≤
      ∑ x ∈ row, (later.filter (Hᶜ.Adj x)).card := by
  classical
  let later := remaining.filter (H.Adj pivot)
  let row := remaining \ later
  have partition : row ∪ later = remaining :=
    Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have disjoint : Disjoint row later := Finset.sdiff_disjoint
  have outgoing (x : V) (hx : x ∈ row) :
      (row.filter (H.Adj x)).card ≤ (later.filter (Hᶜ.Adj x)).card := by
    obtain ⟨hxS, hxL⟩ := Finset.mem_sdiff.mp hx
    have split : (row.filter (H.Adj x)).card + (later.filter (H.Adj x)).card =
        (remaining.filter (H.Adj x)).card := by
      rw [← Finset.card_union_of_disjoint (disjoint.mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _)), ← Finset.filter_union, partition]
    have cross : (later.filter (fun y => ¬ H.Adj x y)) = later.filter (Hᶜ.Adj x) := by
      ext y
      simp only [Finset.mem_filter, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨hy, hxy⟩
        exact ⟨hy, fun e => hxL (e ▸ hy), hxy⟩
      · rintro ⟨hy, _, hxy⟩
        exact ⟨hy, hxy⟩
    have available := Finset.card_filter_add_card_filter_not (s := later) (H.Adj x)
    rw [cross] at available
    have cap := hmax x hxS
    change (remaining.filter (H.Adj x)).card ≤ later.card at cap
    omega
  refine ⟨outgoing, ?_⟩
  change 2 * (H.induce (row : Set V)).edgeFinset.card ≤ _
  rw [← sum_internal_degrees H row]
  exact Finset.sum_le_sum outgoing

/-- Every nonempty residual graph supplies such a pivot and its forward edge bound. -/
theorem exists_pivot_with_forward_edges (remaining : Finset V) (nonempty : remaining.Nonempty) :
    ∃ pivot ∈ remaining,
      let later := remaining.filter (H.Adj pivot)
      let row := remaining \ later
      (∀ x ∈ remaining, (remaining.filter (H.Adj x)).card ≤ later.card) ∧
      2 * (H.induce (row : Set V)).edgeFinset.card ≤
        ∑ x ∈ row, (later.filter (Hᶜ.Adj x)).card := by
  obtain ⟨pivot, hp, hmax⟩ :=
    remaining.exists_max_image (fun x => (remaining.filter (H.Adj x)).card) nonempty
  exact ⟨pivot, hp, hmax, (forward_edges_of_max_degree H remaining pivot hmax).2⟩

end Erdos617.RowExtraction
