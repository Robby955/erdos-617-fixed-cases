import ExteriorRowEdges
import OrdinaryTrim
import StrongRowCharge

/-! Heavy sender counts in Appendix A, §5, on the original ordinary cliques.
All degrees count actual neighbors in the target color. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

/-- On a target clique of size r−d, any chosen family of exterior senders
with more than r/2 neighbors has at most 2d members. Together their target
degrees into the clique sum to at most rd. -/
theorem heavy_row_senders (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (C Z : Finset V) (hr : 2 ≤ r) (no : ¬Witness color) (cl : (targetGraph color j).IsClique (C:Set V))
    (dis : Disjoint C Z) (short : 2*((r-C.card)+1) ≤ r)
    (heavy : ∀ x ∈ Z, (r:ℝ)/2 < ((C.filter ((targetGraph color j).Adj x)).card:ℝ)) :
    Z.card ≤ 2*(r-C.card) ∧
      (∑ x ∈ Z, ((C.filter ((targetGraph color j).Adj x)).card:ℝ)) ≤ (r:ℝ)*(r-C.card:ℕ) := by
  let d := r-C.card
  let deg := fun x ↦ ((C.filter ((targetGraph color j).Adj x)).card:ℝ)
  have fits := (caps_of_no_witness color j hr no).2 C cl
  have dx : (d:ℝ) = (r:ℝ)-C.card := Nat.cast_sub fits
  have s : 2*((d:ℝ)+1) ≤ r := by exact_mod_cast short
  have bound : Z.card ≤ 2*d := by
    by_contra! too_many
    obtain ⟨Y,sub,size⟩ := exists_subset_card_eq (show 2*d+1 ≤ Z.card by omega)
    have ne : Y.Nonempty := card_pos.mp (by omega)
    have lower := sum_lt_sum_of_nonempty ne fun x hx ↦ heavy x (sub hx)
    change (∑ _x ∈ Y, (r:ℝ)/2) < ∑ x ∈ Y, deg x at lower
    rw [sum_const,nsmul_eq_mul] at lower
    have constraint := clique_arrival_capacity color j C Y hr no (dis.mono_right sub) cl
    change (∑ x ∈ Y, deg x) + (Y.card:ℝ)*((r:ℝ)-C.card) ≤
      ((r:ℝ)-1)*((r:ℝ)-C.card)+(Y.card:ℝ)*((Y.card:ℝ)+1)/2 at constraint
    rw [← dx] at constraint
    have sz : (Y.card:ℝ) = 2*(d:ℝ)+1 := by exact_mod_cast size
    rw [sz] at lower constraint
    nlinarith only [lower,constraint,s]
  refine ⟨bound,?_⟩
  have capacity := clique_arrival_capacity color j C Z hr no dis cl
  change (∑ x ∈ Z, deg x)+(Z.card:ℝ)*((r:ℝ)-C.card) ≤
    ((r:ℝ)-1)*((r:ℝ)-C.card)+(Z.card:ℝ)*((Z.card:ℝ)+1)/2 at capacity
  rw [← dx] at capacity
  have b : (Z.card:ℝ) ≤ 2*d := by exact_mod_cast bound
  change ∑ x ∈ Z, deg x ≤ (r:ℝ)*d
  nlinarith only [capacity,b,mul_le_mul_of_nonneg_left b (Nat.cast_nonneg (α := ℝ) Z.card)]

variable [Fintype V] (T : Trace V r)

/-- The size of each original retained row pays for the integer endpoint
2(d+1)≤r in the heavy-sender trial. -/
theorem retained_heavy_deficit (prep : Prepared T) (hr : 3 ≤ r) {E : Finset V}
    {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β) {i : ℕ} (hi : i ∈ S.retained) :
    2*((r-(rowList T E i).card)+1) ≤ r := by
  let C := rowList T E i
  have floor := (temporary_row_bounds T prep (by omega) E band S hi).1
  have included : (temporaryRow T E i).card ≤ C.card := card_le_card (filter_subset ..)
  have cover : (255/256:ℝ)*r ≤ (C.card:ℝ) := floor.trans (by exact_mod_cast included)
  have r3 : (3:ℝ) ≤ r := by exact_mod_cast hr
  by_cases small : C.card ≤ r
  · have needed : 2*((r:ℝ)-C.card+1) ≤ r := by linarith only [cover,r3]
    rw [← Nat.cast_sub (R := ℝ) small] at needed
    exact_mod_cast needed
  · change 2*((r-C.card)+1) ≤ r
    omega

/-- Apply the heavy-sender bounds to any actual family assigned to one of
the selected original rows. The width construction supplies the size test. -/
theorem retained_heavy_senders (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β) {i : ℕ} (hi : i ∈ S.retained)
    (Z : Finset V) (dis : Disjoint (rowList T E i) Z)
    (heavy : ∀ x ∈ Z, (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj x)).card:ℝ)) :
    Z.card ≤ 2*(r-(rowList T E i).card) ∧
      (∑ x ∈ Z, (((rowList T E i).filter ((targetGraph T.color T.target).Adj x)).card:ℝ)) ≤
        (r:ℝ)*(r-(rowList T E i).card:ℕ) := by
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  exact heavy_row_senders T.color T.target _ Z (by omega) no (lists.clique i unused) dis
    (retained_heavy_deficit T prep hr S band hi) heavy

/-- The local variance inequality of the 320 supplement, §3(5), with all
sender counts and the surplus J read from the original colored row. Here v
is any nonnegative real. The global signed cut of Appendix A is a subsequent
argument involving multiple rows. -/
theorem retained_row_charge (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y t : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y t α β) {i : ℕ} (hi : i ∈ S.retained)
    (Z : Finset V) (dis : Disjoint (rowList T E i) Z)
    (heavy : ∀ y ∈ Z, (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj y)).card:ℝ))
    (v : ℝ) (hv : 0 ≤ v) :
    let C := rowList T E i
    let d := (r:ℝ)-C.card
    let J := ∑ y ∈ Z, 2*d*(1-((C.filter ((targetGraph T.color T.target).Adj y)).card:ℝ)/C.card)
    (Z.card:ℝ)^2/2+((Z.card:ℝ)-d)*v-J ≤ (501/1000:ℝ)*d^2+v^2/2 := by
  let C := rowList T E i
  let d := (r:ℝ)-C.card
  let x := d/r
  let deg := fun y ↦ ((C.filter ((targetGraph T.color T.target).Adj y)).card:ℝ)
  let J := ∑ y ∈ Z, 2*d*(1-deg y/C.card)
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  have fits : C.card ≤ r := (caps_of_no_witness T.color T.target (by omega) no).2 C (lists.clique i unused)
  have d0 : 0 ≤ d := sub_nonneg.mpr (by exact_mod_cast fits)
  have x0 : 0 ≤ x := div_nonneg d0 pos.le
  have rx : x = rowDeficit T E i := by
    change ((r:ℝ)-C.card)/r = 1-(C.card:ℝ)/r
    rw [sub_div,div_self pos.ne']
  have sx : (S.s:ℝ)*x ≤ 2*β*S.w := rx ▸ S.deficit i hi
  have smin : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have βlo : 0 ≤ β := by cases band <;> norm_num
  have βhi : β ≤ 925/4000 := by cases band <;> norm_num
  have thin : x ≤ 1/2001 := by
    nlinarith only [sx,mul_le_mul_of_nonneg_right smin x0,βhi,
      mul_le_mul_of_nonneg_left S.width_lt.le βlo]
  have xlt : x < 1 := by linarith only [thin]
  have cpos : (0:ℝ) < C.card := by
    have dx : d < r := (div_lt_one pos).mp xlt
    dsimp only [d] at dx
    linarith only [dx]
  have small : 2*x/(1-x) ≤ 1/1000 := by
    apply (div_le_iff₀ (sub_pos.mpr xlt)).mpr
    linarith only [thin]
  obtain ⟨count,budget⟩ := retained_heavy_senders T prep hr no lists S band hi Z dis heavy
  have nb : (Z.card:ℝ) ≤ 2*d := by
    change (Z.card:ℝ) ≤ 2*((r:ℝ)-C.card)
    rw [← Nat.cast_sub (R := ℝ) fits]
    exact_mod_cast count
  have total : (∑ y ∈ Z, deg y) ≤ (r:ℝ)*d := by
    change (∑ y ∈ Z, deg y) ≤ (r:ℝ)*((r:ℝ)-C.card)
    rw [← Nat.cast_sub (R := ℝ) fits]
    exact budget
  have J0 : 0 ≤ J := sum_nonneg fun y _ ↦ by
    have dy : deg y ≤ C.card := by
      dsimp only [deg]
      exact_mod_cast (card_le_card (filter_subset ((targetGraph T.color T.target).Adj y) C))
    exact mul_nonneg (by positivity) (sub_nonneg.mpr ((div_le_one cpos).mpr dy))
  have ratio : d/(1-x) = (r:ℝ)*d/C.card := by
    apply (div_eq_iff (sub_pos.mpr xlt).ne').2
    dsimp only [x,d]
    field_simp
    ring
  have sumJ : J = 2*d*((Z.card:ℝ)-(∑ y ∈ Z, deg y)/C.card) := by
    simp only [J,← mul_sum,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,sum_div]
  have pay : 2*d*((Z.card:ℝ)-d/(1-x)) ≤ J := by
    rw [sumJ,ratio]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sub_le_sub_left (div_le_div_of_nonneg_right total cpos.le) _
  exact StrongRowCharge.row_charge (Nat.cast_nonneg _) d0 hv nb J0 xlt small pay

end
end Erdos617.ColoredLists
