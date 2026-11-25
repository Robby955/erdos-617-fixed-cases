import AuxiliaryCliques
import Mathlib.Algebra.Order.Chebyshev

/-! Positive deficits in at most three auxiliary rows after peeling, Appendix A §4. -/

namespace Erdos617.AuxiliaryMoments

open Finset PackingLists RowExtraction GraphPartitionCount ColoredLists PruningOverlap
open scoped Classical
noncomputable section

/-- Normalized upper bounds for subsets of zero, one, two or three auxiliary rows. -/
def peeledCap (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j = 1 then 158406/1000000
  else if j = 2 then 205440/1000000 else 225599/1000000

/-- Cauchy–Schwarz controls the raw deficits on the chosen rows. Each
subsequent deletion is charged only once over the whole chosen subfamily. -/
private theorem quadratic_cap {j : ℕ} (pos : j ≠ 0) (hj : j ≤ 3) {u z x v : ℝ}
    (linear : u ≤ 8063/50000) (paid : (43/200:ℝ)*z ≤ x)
    (variance : u^2 ≤ j*v) (edges : x+v ≤ (3/20:ℝ)^2+1/2^20) : u+z ≤ peeledCap j := by
  interval_cases j
  · exact (pos rfl).elim
  · norm_num [peeledCap] at variance ⊢
    nlinarith only [variance,edges,paid,sq_nonneg (u-43/400)]
  · norm_num [peeledCap] at variance ⊢
    nlinarith only [variance,edges,paid,linear,sq_nonneg (u-8063/50000)]
  · norm_num [peeledCap] at variance ⊢
    nlinarith only [variance,edges,paid,linear,sq_nonneg (u-8063/50000)]

variable {V : Type*} {r : ℕ} (T : Trace V r)

/-- The projected bound applies directly to the actual auxiliary partition and
its actual set of survivors, with the signed order deficit bounded by 3r/20.
It also applies to enlarged rows of any type via their larger cardinalities. -/
theorem peeled_deficit_cap {B : Finset V} {row : B → ℕ} {A : Finset B}
    {s : ℕ} {Y exp α β : ℝ} (band : RetainedWidth.Band Y exp α β)
    (slo : 1120 ≤ s) (scale : (2:ℝ)^exp*(s:ℝ)^4 < r)
    (orderLo : -(3/20:ℝ)*r ≤ (B.card:ℝ)-((s-1:ℕ):ℝ)*r)
    (part : AuxiliaryPartition T s B row)
    (surv : AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (s-1) r A)
    (J : Finset ℕ) (included : J ⊆ range (s-1)) (few : J.card ≤ 3)
    (enlargedSize : ℕ → ℕ) (grows : ∀ i ∈ J, (fiber A row i).card ≤ enlargedSize i) :
    (∑ i ∈ J, max (1-(enlargedSize i:ℝ)/r) 0) ≤ peeledCap J.card := by
  by_cases empty : J = ∅
  · simp [empty,peeledCap]
  have nonempty : J.card ≠ 0 := by simpa using empty
  let G := targetGraph (inducedColor T.color B) T.target
  let X := ((cross G row).edgeFinset.card:ℝ)
  let x := X/(r:ℝ)^2
  let u := fun i ↦ max (1-(size row i:ℝ)/r) 0
  let L : Finset B := univ \ A
  let z := (L.card:ℝ)/r
  obtain ⟨r7,h1,_,hsmall⟩ := scale_facts band slo scale
  have rp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h1' : (1:ℝ) ≤ ((s-1:ℕ):ℝ) := by exact_mod_cast h1
  have rLarge : (4096:ℝ) ≤ r := by
    norm_num at hsmall
    nlinarith only [hsmall,h1',sq_nonneg (((s-1:ℕ):ℝ)-1)]
  have total : x + (∑ i ∈ range (s-1), (u i)^2) ≤ (3/20:ℝ)^2+1/2^20 := part.normalized
  have edgeBound : X ≤ ((3/20:ℝ)^2+1/2^20)*(r:ℝ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos rp)).mp
    exact (le_add_of_nonneg_right (sum_nonneg fun i _ ↦ sq_nonneg (u i))).trans total
  have scaled (i) : u i*r = max ((r:ℝ)-size row i) 0 := by
    dsimp [u]
    rw [max_mul_of_nonneg _ _ rp.le,sub_mul,div_mul_cancel₀ _ rp.ne',one_mul,zero_mul]
  have raw : (∑ i ∈ J, u i) ≤ 8063/50000 := by
    have top : (∑ i ∈ range (s-1), max ((r:ℝ)-size row i) 0) ≤
        -((B.card:ℝ)-((s-1:ℕ):ℝ)*r)+X/(2*((r:ℝ)-1)) := part.linear
    have cut : X/(2*((r:ℝ)-1)) ≤ (563/50000:ℝ)*r := by
      apply (div_le_iff₀ (show (0:ℝ) < 2*((r:ℝ)-1) by linarith only [rLarge])).mpr
      nlinarith only [edgeBound, mul_nonneg rp.le (sub_nonneg.mpr rLarge)]
    have sub := sum_le_sum_of_subset_of_nonneg included
      (f := fun i ↦ max ((r:ℝ)-size row i) 0) (fun _ _ _ ↦ le_max_right _ _)
    apply le_of_mul_le_mul_right _ rp
    rw [sum_mul]
    simp_rw [scaled]
    linarith only [orderLo,sub,top,cut]
  have loss : (L.card:ℝ) + A.card = Fintype.card B := by
    exact_mod_cast (card_sdiff_add_card_eq_card (subset_univ A)).trans (card_univ (α := B))
  have pay : (43/200:ℝ)*z ≤ x := by
    have live := (le_add_of_nonneg_left (Nat.cast_nonneg
      ((cross G row).induce (A:Set B)).edgeFinset.card)).trans surv.residual
    have measured : (43/200:ℝ)*r*(L.card:ℝ) ≤ X := by
      convert live using 2
      linarith only [loss]
    apply (le_div_iff₀ (sq_pos_of_pos rp)).mpr
    convert measured using 1
    dsimp [z]
    field_simp
  have per (i) (inside : i ∈ J) :
      max (1-(enlargedSize i:ℝ)/r) 0 ≤ u i + ((fiber L row i).card:ℝ)/r := by
    have cover : fiber univ row i ⊆ fiber A row i ∪ fiber L row i := by
      intro v hv
      have ri := (mem_filter.mp hv).2
      by_cases mem : v ∈ A
      · exact mem_union_left _ (mem_filter.mpr ⟨mem,ri⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,mem⟩,ri⟩)
    have count : (size row i:ℝ) ≤ (fiber A row i).card+((fiber L row i).card:ℝ) := by
      exact_mod_cast (card_le_card cover).trans (card_union_le ..)
    have greater : ((fiber A row i).card:ℝ) ≤ enlargedSize i := by exact_mod_cast grows i inside
    have fractions := div_le_div_of_nonneg_right
      (count.trans (add_le_add_left greater ((fiber L row i).card:ℝ))) rp.le
    rw [add_div] at fractions
    exact max_le (by linarith only [fractions,le_max_left (1-(size row i:ℝ)/r) (0:ℝ)]) (by
      exact add_nonneg (le_max_right ..) (by positivity))
  have spent : (∑ i ∈ J, (fiber L row i).card) ≤ L.card := by
    change (∑ i ∈ J, (L.filter fun v ↦ row v=i).card) ≤ _
    rw [sum_card_fiberwise_eq_card_filter]
    exact card_le_card (filter_subset ..)
  have joint : (∑ i ∈ J, max (1-(enlargedSize i:ℝ)/r) 0) ≤ (∑ i ∈ J, u i)+z := by
    have added := sum_le_sum per
    rw [sum_add_distrib,← sum_div] at added
    apply added.trans (add_le_add_right (div_le_div_of_nonneg_right ?_ rp.le) _)
    exact_mod_cast spent
  have moments : x+(∑ i ∈ J, (u i)^2) ≤ (3/20:ℝ)^2+1/2^20 := by
    exact (add_le_add_right (sum_le_sum_of_subset_of_nonneg included (fun i _ _ ↦ sq_nonneg (u i))) x).trans total
  exact joint.trans (quadratic_cap nonempty few raw pay (sq_sum_le_card_mul_sum_sq (s := J) (f := u))
    moments)

end
end Erdos617.AuxiliaryMoments
