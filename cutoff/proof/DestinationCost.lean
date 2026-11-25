import PrunedWidth

/-! Each first-stage source spends unused allowance in its chosen destination. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- A legal first-stage source lies outside its destination. Its original
target neighbors in the destination include its entire recorded star. -/
theorem first_source_neighbors (legal : T.Legal) {x : V} (source : x ∈ T.firstSources) :
    T.row x ≠ T.destination x ∧ (r:ℝ)/4 <
      ((univ.filter fun y ↦ T.row y = T.destination x).filter
        ((targetGraph T.color T.target).Adj x)).card := by
  have ht : T.time x < T.firstEnd := (mem_filter.mp source).2
  have degree := legal.degree x (ht.trans_le T.stages)
  simp only [Trace.quota, ite_eq_left ht] at degree
  have star (y) (hy : y ∈ T.star x) :
      T.crossGraph.Adj x y ∧ T.row y = T.destination x := by
    obtain ⟨_,adj,_,_,row⟩ := mem_filter.mp hy
    exact ⟨adj,row ht⟩
  obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (T.star x).card by
    exact_mod_cast lt_of_le_of_lt (by positivity : 0 ≤ (r:ℝ)/4) degree)
  obtain ⟨adj,hyrow⟩ := star y hy
  refine ⟨hyrow ▸ adj.1, degree.trans_le ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro v hv
  obtain ⟨ha,hr⟩ := star v hv
  rw [← cross_target] at ha
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hr⟩,ha.2⟩

/-- For a legal pruning, the exterior edge cap bounds the normalized load
assigned to each destination. Empty destinations are covered by the same cap. -/
theorem destination_cost_of_cross_count (legal : T.Legal) (hr : 2^20 ≤ r)
    (qual : ∀ v ∈ T.firstSources, unused T (T.destination v) ≤ 1/1200)
    (cross : ∀ (i : ℕ) (Z : Finset V), (∀ x ∈ Z, T.row x ≠ i) →
      (∑ x ∈ Z, ((((univ.filter fun y ↦ T.row y = i).filter
        ((targetGraph T.color T.target).Adj x)).card:ℝ))) ≤
      (internalMissing T i:ℝ)-((r:ℝ)-1)*((T.rowSize i:ℝ)-r) +
      (1+(T.rowSize i:ℝ)-r)*(Z.card:ℝ) + (Z.card:ℝ)*((Z.card:ℝ)-1)/2)
    (i : ℕ) : (61/250)*assigned T i ≤ unused T i := by
  let A := T.firstSources.filter (fun v ↦ T.destination v = i)
  let B := (internalMissing T i:ℝ)-((r:ℝ)-1)*((T.rowSize i:ℝ)-r)
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have huge : (1048576:ℝ) ≤ r := by exact_mod_cast hr
  by_cases ne : A.Nonempty
  · obtain ⟨v,hv⟩ := ne
    obtain ⟨hf,hd⟩ := mem_filter.mp hv
    have small := legal.destinationSmall v (mem_filter.mp hf).2
    rw [hd] at small
    have size : (T.rowSize i:ℝ)-r ≤ (r:ℝ)/256 := by
      have h : (256:ℝ)*T.rowSize i ≤ 257*r := by exact_mod_cast small
      linarith
    have ub := qual v hf
    rw [hd, unused, div_le_iff₀ (sq_pos_of_pos pos)] at ub
    change B ≤ _ at ub
    have cost (Z : Finset V) (sub : Z ⊆ A) (limit : 256*Z.card ≤ r) :
        (61/250:ℝ)*r*Z.card ≤ B := by
      have src (x) (hx : x ∈ Z) := first_source_neighbors T legal (mem_filter.mp (sub hx)).1
      have out (x) (hx : x ∈ Z) : T.row x ≠ i := (mem_filter.mp (sub hx)).2 ▸ (src x hx).1
      have stars := Finset.sum_le_sum (s := Z) fun x hx ↦
        (mem_filter.mp (sub hx)).2 ▸ (src x hx).2.le
      have lower : (Z.card:ℝ)*((r:ℝ)/4) ≤
          ∑ x ∈ Z, (((univ.filter fun y ↦ T.row y = i).filter
            ((targetGraph T.color T.target).Adj x)).card:ℝ) := by simpa using stars
      have upper := cross i Z out
      change _ ≤ B + _ + _ at upper
      have lim : (Z.card:ℝ) ≤ (r:ℝ)/256 := by
        have h : (256:ℝ)*Z.card ≤ r := by exact_mod_cast limit
        linarith
      have rate : (61/250:ℝ)*r+(1+(r:ℝ)/256)+((r:ℝ)/256-1)/2 ≤ (r:ℝ)/4 := by linarith only [huge]
      nlinarith only [lower,upper,
        mul_le_mul_of_nonneg_right size (Nat.cast_nonneg (α := ℝ) Z.card),
        mul_le_mul_of_nonneg_right lim (Nat.cast_nonneg (α := ℝ) Z.card),
        mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg (α := ℝ) Z.card)]
    have few : A.card < r/256 := by
      by_contra! many
      obtain ⟨Z,hZ,nZ⟩ := Finset.exists_subset_card_eq many
      have h := cost Z hZ (by rw [nZ]; omega)
      rw [nZ] at h
      have hn : (r:ℝ)-256 ≤ 256*((r/256:ℕ):ℝ) := by
        have nat : r ≤ 256*(r/256)+256 := by omega
        have re : (r:ℝ) ≤ 256*((r/256:ℕ):ℝ)+256 := by exact_mod_cast nat
        linarith
      nlinarith only [h,ub,mul_le_mul_of_nonneg_right hn pos.le,
        mul_le_mul_of_nonneg_right huge pos.le,pos]
    have paid := cost A (by rfl) (by omega)
    unfold unused assigned
    apply (le_div_iff₀ (sq_pos_of_pos pos)).2
    change (61/250)*((A.card:ℝ)/r)*(r:ℝ)^2 ≤ B
    convert paid using 1
    field_simp
  · have h := cross i ∅ (by simp)
    simp at h
    have zero := Finset.not_nonempty_iff_eq_empty.mp ne
    change (61/250)*((A.card:ℝ)/r) ≤ B/(r:ℝ)^2
    simp only [zero,card_empty,Nat.cast_zero,zero_div,mul_zero]
    exact div_nonneg (sub_nonneg.mpr h) (sq_nonneg _)

end
end Erdos617.ColoredLists
