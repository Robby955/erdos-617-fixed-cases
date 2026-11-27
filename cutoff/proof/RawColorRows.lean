import OrderedRows
import PrunedWidth
import RawColorBudget

/-! The raw rows in the original complete graph and their outgoing target edges. -/

namespace Erdos617.ColoredLists

open Finset RowExtraction PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V]

def PivotRows (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r) (row : V → ℕ) : Prop :=
  ∀ i < r, RowStep (targetGraph color j)ᶜ (fiber univ row i) (laterRows univ row i)

def Sparsest (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r) : Prop :=
  ∀ k, (targetGraph color j).edgeFinset.card ≤ (targetGraph color k).edgeFinset.card

/-- Begin directly with the coloring. Choose a sparsest color and construct
the entire ordered pivot partition, padding with empty rows up to r. -/
theorem witness_or_raw_rows (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (hr : 2 ≤ r) :
    Witness color ∨ ∃ (j : Fin r) (row : V → ℕ), Sparsest color j ∧
      (∀ x, row x < r) ∧ PivotRows color j row := by
  by_cases no : Witness color
  · exact Or.inl no
  have ne : (univ : Finset (Fin r)).Nonempty := ⟨⟨0, by omega⟩,mem_univ _⟩
  obtain ⟨j,_,least⟩ := univ.exists_min_image (fun k ↦ (targetGraph color k).edgeFinset.card) ne
  have cap := (caps_of_no_witness color j hr no).1
  obtain ⟨row,labels,steps⟩ := exists_ordered_rows (targetGraph color j)ᶜ r univ
    (fun S _ cl ↦ cap S (by simpa using cl))
  exact Or.inr ⟨j,row,fun k ↦ least k (mem_univ _),fun x ↦ labels x (mem_univ _),steps⟩

variable (T : Trace V r)

def forwardDegree (i : ℕ) (x : V) :=
  ((laterRows univ T.row i).filter ((targetGraph T.color T.target).Adj x)).card

/-- Original forward edge ends decompose by oversized row, with each edge
counted at its earlier endpoint. -/
theorem forward_total (C : Finset ℕ) :
    countEnds (T.forward C) = ∑ i ∈ oversizedRows univ T.row C r,
      ∑ x ∈ fiber univ T.row i, (forwardDegree T i x:ℝ) := by
  let B := oversizedRows univ T.row C r
  have oversized_iff (x : V) : T.oversized C x ↔ T.row x ∈ B := by
    change T.row x ∈ C ∧ 257*r < 256*rowCard univ T.row (T.row x) ↔ _
    have eqv : T.row x ∈ B ↔ T.row x ∈ C ∧ 257*r < 256*rowCard univ T.row (T.row x) := Finset.mem_filter
    exact eqv.symm
  have edge (x y : V) : T.forward C x y ↔ T.row x ∈ B ∧ T.row x < T.row y ∧
      (targetGraph T.color T.target).Adj x y := by
    rw [Trace.forward, oversized_iff, ← cross_target T]
    constructor
    · exact fun ⟨hb,lt,_,adj⟩ ↦ ⟨hb,lt,adj⟩
    · exact fun ⟨hb,lt,adj⟩ ↦ ⟨hb,lt,lt.ne,adj⟩
  have per (x : V) : (∑ y, if T.forward C x y then (1:ℝ) else 0) =
      if T.row x ∈ B then (forwardDegree T (T.row x) x:ℝ) else 0 := by
    simp_rw [edge]
    by_cases h : T.row x ∈ B
    · simp [h,forwardDegree,laterRows,Finset.filter_filter]
    · simp [h]
  have replace (i) : (∑ x ∈ fiber univ T.row i, (forwardDegree T i x:ℝ)) =
      ∑ x ∈ fiber univ T.row i, (forwardDegree T (T.row x) x:ℝ) := by
    exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2]
  have union_rows : B.biUnion (fiber univ T.row) = univ.filter (fun x ↦ T.row x ∈ B) := by
    ext x
    simp [fiber]
  have dis : (B : Set ℕ).PairwiseDisjoint (fiber univ T.row) := by
    intro i _ j _ hne
    exact disjoint_left.mpr (fun _ hi hj ↦ hne ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))
  unfold countEnds total
  simp_rw [per,replace]
  rw [← Finset.sum_biUnion dis,union_rows,Finset.sum_filter]

/-- Every actual row has nonnegative unused allowance in a putative
counterexample, by counting each other color on its original edges. -/
theorem unused_nonneg_of_no_witness (hr : 2 ≤ r) (no : ¬Witness T.color) (i : ℕ) :
    0 ≤ unused T i := by
  let A := univ.filter fun x ↦ T.row x = i
  have floor : (r-1)*(T.rowSize i-r) ≤ internalMissing T i := by
    convert other_color_floor T.color T.target A hr no using 2
    · rfl
    · dsimp only [internalMissing,A]
  unfold unused
  apply div_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  by_cases h : r ≤ T.rowSize i
  · have n : (((r-1)*(T.rowSize i-r):ℕ):ℝ) ≤ (internalMissing T i:ℝ) := by exact_mod_cast floor
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ r by omega),Nat.cast_sub h,Nat.cast_one] using n
  · have le : (T.rowSize i:ℝ) ≤ r := by exact_mod_cast (le_of_not_ge h)
    apply le_trans (mul_nonpos_of_nonneg_of_nonpos _ (sub_nonpos.mpr le)) (Nat.cast_nonneg _)
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ r by omega))

/-- The per-row pivot inequality pays the forward floor for every choice
of chosen rows in one trace. Nonnegative unused allowance pays the internal
edges required by the other colors. -/
theorem forward_floor_of_pivots (hr : 2 ≤ r) (no : ¬Witness T.color)
    (pivots : PivotRows T.color T.target T.row) (C : Finset ℕ) (sub : C ⊆ range r) :
    2*((r:ℝ)-1)*oversizedExcess univ T.row C r*r ≤ countEnds (T.forward C) := by
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  rw [forward_total, oversizedExcess, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h := sub (mem_filter.mp hi).1
  have rawCost := unused_nonneg_of_no_witness T hr no i
  unfold unused at rawCost
  have need := (le_div_iff₀ (sq_pos_of_pos pos)).mp rawCost
  rw [zero_mul] at need
  have hrow := (pivots i (mem_range.mp h)).forward
  have integral : 2*internalMissing T i ≤ ∑ x ∈ fiber univ T.row i, forwardDegree T i x := by
    convert hrow using 1
    · unfold internalMissing
      dsimp only [fiber]
      congr 5
      exact Subsingleton.elim _ _
    · apply Finset.sum_congr rfl
      intro x _
      apply congrArg Finset.card
      refine @Finset.filter_congr V _ _ ?_ ?_ _ ?_
      intro y _
      rw [compl_compl]
  have counts : (2:ℝ)*(internalMissing T i:ℝ) ≤ ∑ x ∈ fiber univ T.row i, (forwardDegree T i x:ℝ) := by
    exact_mod_cast integral
  change 0 ≤ (internalMissing T i:ℝ)-((r:ℝ)-1)*((T.rowSize i:ℝ)-r) at need
  change 2*((r:ℝ)-1)*((T.rowSize i:ℝ)/r-1)*r ≤ _
  calc _ = 2*(((r:ℝ)-1)*((T.rowSize i:ℝ)-r)) := by field_simp
       _ ≤ _ := by linarith only [need,counts]

/-- The five raw estimates remaining after construction of the pivot rows
suffice for a common threshold on the actual colored lists. -/
theorem witness_or_width_of_pivots (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ v, T.row v < r) (pivots : PivotRows T.color T.target T.row) (legal : T.Legal)
    (dest : ∀ v ∈ T.firstSources, T.destination v < r)
    (stop : ∀ v ∈ live T, (Transversal.neighbors T.crossGraph (live T) v).card ≤ degreeBound r)
    (sizes : ∑ i ∈ range r, rawSurplus T i ≤ 1/2) (costs : ∑ i ∈ range r, unused T i ≤ 1/2)
    (crossCap : (T.crossGraph.edgeFinset.card:ℝ) ≤ (1-variance T)*(r:ℝ)^2)
    (localCost : ∀ i ∈ range r, (61/250)*assigned T i ≤ unused T i)
    (qual : ∀ v ∈ T.firstSources, unused T (T.destination v) ≤ 1/1200) :
    Witness T.color ∨ HasWidth T := by
  by_cases no : Witness T.color
  · exact Or.inl no
  exact witness_or_width T hr order rows legal dest
    ⟨sizes,costs,crossCap,forward_floor_of_pivots T (by omega) no pivots,localCost,qual⟩ stop

end
end Erdos617.ColoredLists
