import RawEdgeIdentity

/-! Greedy pivot partitions on an arbitrary finite graph and any number of rows. -/

namespace Erdos617.GraphPartitionCount

open Finset RowExtraction PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V]

def size (row : V → ℕ) (i : ℕ) := (fiber univ row i).card

theorem sum_sizes (row : V → ℕ) (k : ℕ) (covers : ∀ x, row x < k) :
    ∑ i ∈ range k, size row i = Fintype.card V := by
  simpa only [size, fiber, card_univ] using
    (Finset.card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := range k) (f := row)
      (fun x _ ↦ mem_range.mpr (covers x))).symm

private def earlier (H : SimpleGraph V) (row : V → ℕ) (x y : V) : ℝ :=
  if row y < row x ∧ H.Adj x y then 1 else 0

private theorem all_ends (H : SimpleGraph V) :
    (∑ x, ∑ y, if H.Adj x y then (1:ℝ) else 0) = 2*(H.edgeFinset.card:ℝ) := by
  have eqv (x : V) : (∑ y, if H.Adj x y then (1:ℝ) else 0) = (H.degree x:ℝ) := by
    simp [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  simp_rw [eqv]
  exact_mod_cast H.sum_degrees_eq_twice_card_edges

/-- A cross edge has precisely one end pointing to a strictly earlier row. -/
private theorem all_earlier (H : SimpleGraph V) (row : V → ℕ) :
    (∑ x, ∑ y, earlier H row x y) = ((cross H row).edgeFinset.card:ℝ) := by
  have pair (x y : V) : earlier H row x y + earlier H row y x =
      if (cross H row).Adj x y then (1:ℝ) else 0 := by
    rcases lt_trichotomy (row x) (row y) with h | h | h
    · by_cases adj : H.Adj x y <;>
        simp [earlier,cross,h,h.ne,not_lt.mpr h.le,adj,H.adj_comm y x]
    · simp [earlier,cross,h]
    · by_cases adj : H.Adj x y <;>
        simp [earlier,cross,h,h.ne.symm,not_lt.mpr h.le,adj,H.adj_comm y x]
  have ends := all_ends (cross H row)
  simp_rw [← pair, Finset.sum_add_distrib] at ends
  rw [Finset.sum_comm (f := fun x y ↦ earlier H row y x)] at ends
  linarith only [ends]

/-- Inside a row the pivot pays one later target neighbor for every missing
internal target neighbor. Earlier target neighbors are still available in
the full degree count. -/
private theorem at_vertex (H : SimpleGraph V) (row : V → ℕ) (x : V)
    (p : RowStep Hᶜ (fiber univ row (row x)) (laterRows univ row (row x))) :
    (size row (row x):ℝ)-1 + (∑ y, earlier H row x y) ≤
      ∑ y, if H.Adj x y then (1:ℝ) else 0 := by
  let P := fiber univ row (row x)
  let L := laterRows univ row (row x)
  have hx : x ∈ P := by simp [P,fiber]
  have pivot := p.at_vertex x hx
  have edge_bound : (∑ y ∈ P, if Hᶜ.Adj x y then (1:ℝ) else 0) ≤
      ∑ y ∈ L, if Hᶜᶜ.Adj x y then (1:ℝ) else 0 := by
    simp only [Finset.sum_boole]
    apply Nat.cast_le.mpr
    convert pivot using 2 <;> congr 3
  simp only [compl_compl] at edge_bound
  have both (y : V) :
      (if H.Adj x y then (1:ℝ) else 0) +
      (if row y = row x then (if Hᶜ.Adj x y then 1 else 0) else 0) +
      (if y=x then 1 else 0) =
      (if row y = row x then 1 else 0) + earlier H row x y +
      (if row x < row y then (if H.Adj x y then 1 else 0) else 0) := by
    by_cases eq : x=y
    · subst y; simp [earlier]
    · rcases lt_trichotomy (row x) (row y) with h | h | h
      · by_cases adj : H.Adj x y <;> simp [earlier,Ne.symm eq,h,h.ne.symm,not_lt.mpr h.le,adj]
      · by_cases adj : H.Adj x y <;> simp [earlier,SimpleGraph.compl_adj,eq,Ne.symm eq,h,adj]
      · by_cases adj : H.Adj x y <;> simp [earlier,Ne.symm eq,h,h.ne,not_lt.mpr h.le,adj]
  have total := sum_congr (s₁ := (univ:Finset V)) rfl fun y _ ↦ both y
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at total
  have counter : (∑ y, if row y = row x then (1:ℝ) else 0) = size row (row x) := by
    simp [size,fiber]
  rw [counter] at total
  simp only [P,L,fiber,laterRows,Finset.sum_filter] at edge_bound
  linarith only [total,edge_bound]

/-- For every pivot partition, summing the per-vertex estimate leaves the
full row pair count and an extra copy of every inter-row target edge. -/
theorem pivot_edge_budget (H : SimpleGraph V) (row : V → ℕ) (k : ℕ)
    (covers : ∀ x, row x < k)
    (pivots : ∀ i < k, RowStep Hᶜ (fiber univ row i) (laterRows univ row i)) :
    ((cross H row).edgeFinset.card:ℝ) + (∑ i ∈ range k, (size row i:ℝ)*((size row i:ℝ)-1)) ≤
      2*(H.edgeFinset.card:ℝ) := by
  have weight : (∑ x, ((size row (row x):ℝ)-1)) =
      ∑ i ∈ range k, (size row i:ℝ)*((size row i:ℝ)-1) := by
    rw [← sum_fiberwise_of_maps_to (s := (univ:Finset V)) (t := range k) (g := row)
      (fun x _ ↦ mem_range.mpr (covers x))]
    apply sum_congr rfl
    intro i _
    calc (∑ x ∈ fiber univ row i, ((size row (row x):ℝ)-1)) =
          ∑ _x ∈ fiber univ row i, ((size row i:ℝ)-1) :=
            sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2]
         _ = _ := by simp [size]; ring
  have bound := sum_le_sum (s := (univ:Finset V)) fun x _ ↦ at_vertex H row x (pivots _ (covers x))
  rw [sum_add_distrib,weight,all_earlier,all_ends] at bound
  linarith only [bound]

/-- Every internal missing edge contributes two ends to its own pivot's
bound. The sum of the forward allowances counts each cross edge once. -/
theorem pivot_missing_budget (H : SimpleGraph V) (row : V → ℕ) (k : ℕ)
    (covers : ∀ x, row x < k)
    (pivots : ∀ i < k, RowStep Hᶜ (fiber univ row i) (laterRows univ row i)) :
    2*(∑ i ∈ range k, ((Hᶜ.induce (fiber univ row i:Set V)).edgeFinset.card:ℝ)) ≤
      ((cross H row).edgeFinset.card:ℝ) := by
  have outgoing (i : ℕ) (x : V) (hx : x ∈ fiber univ row i) :
      (((laterRows univ row i).filter (H.Adj x)).card:ℝ) = ∑ y, earlier H row y x := by
    have h : row x = i := (mem_filter.mp hx).2
    simp [earlier,laterRows,Finset.filter_filter,h,H.adj_comm x]
  have bound (i : ℕ) (hi : i ∈ range k) :
      2*((Hᶜ.induce (fiber univ row i:Set V)).edgeFinset.card:ℝ) ≤
      ∑ x ∈ fiber univ row i, ∑ y, earlier H row y x := by
    have natbound : 2*(Hᶜ.induce (fiber univ row i:Set V)).edgeFinset.card ≤
        ∑ x ∈ fiber univ row i, ((laterRows univ row i).filter (H.Adj x)).card := by
      convert (pivots i (mem_range.mp hi)).forward using 1
      · congr 5
        exact Subsingleton.elim _ _
      · apply Finset.sum_congr rfl
        intro x _
        apply congrArg Finset.card
        refine @Finset.filter_congr V _ _ ?_ ?_ _ ?_
        intro y _
        rw [compl_compl]
    calc _ ≤ ∑ x ∈ fiber univ row i, (((laterRows univ row i).filter (H.Adj x)).card:ℝ) := by
           exact_mod_cast natbound
         _ = _ := sum_congr rfl (outgoing i)
  rw [Finset.mul_sum]
  apply (sum_le_sum bound).trans
  rw [show (∑ i ∈ range k, ∑ x ∈ fiber univ row i, ∑ y, earlier H row y x) =
      ∑ x, ∑ y, earlier H row y x from
    sum_fiberwise_of_maps_to (fun x _ ↦ mem_range.mpr (covers x)) _]
  rw [sum_comm,all_earlier]

end
end Erdos617.GraphPartitionCount
