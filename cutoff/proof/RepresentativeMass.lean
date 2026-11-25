import RetainedSenders

/-! Representative atom bound on the original retained clique, with the
width-dependent constant used in the final signed cut. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- X may be the upper row-deficit envelope of the current width interval. -/
def representativeFactor (X : ℝ) : ℝ :=
  (1+100*((9/40:ℝ)/1120))/(1-X/1120)

theorem representativeFactor_one {X : ℝ} (lo : 0 ≤ X) (hi : X < 1120) :
    1 ≤ representativeFactor X := by
  apply (le_div_iff₀ (by linarith only [hi] : 0 < 1-X/1120)).mpr
  linarith only [lo]

/-- The exact one-point probability is bounded uniformly for every sender
at this row. The same X is valid for every retained row. -/
theorem retained_atom_bound {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    {i : ℕ} (retained : i ∈ S.retained) (y v : V) :
    (rowList T E i).Nonempty ∧
    successIn (targetGraph T.color T.target) (rowList T E i) y (100*((9/40:ℝ)/S.s))
      (fun z ↦ z=v) ≤ representativeFactor X/r := by
  let C := rowList T E i
  let G := targetGraph T.color T.target
  let ρ := (9/40:ℝ)/S.s
  let a := 1-X/1120
  let q := neighborFraction G C y
  have rp : (0:ℝ)<r := by exact_mod_cast hr
  have sm : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<S.s := by linarith only [sm]
  have ap : 0 < a := by dsimp [a]; linarith only [hi]
  have low : 1-(C.card:ℝ)/r ≤ X/1120 := by
    have d := (S.deficit i retained).trans width
    change (S.s:ℝ)*(1-(C.card:ℝ)/r) ≤ X at d
    by_cases h : 0 ≤ 1-(C.card:ℝ)/r
    · linarith only [d,mul_le_mul_of_nonneg_right sm h]
    · linarith only [le_of_not_ge h,lo]
  have floor : a*r ≤ C.card := (le_div_iff₀ rp).mp (by dsimp [a]; linarith only [low])
  have cp : (0:ℝ)<C.card := (mul_pos ap rp).trans_le floor
  have ne : C.Nonempty := card_pos.mp (by exact_mod_cast cp)
  have qq : q ≤ 1 := (div_le_one cp).mpr (by exact_mod_cast card_le_card (filter_subset ..))
  have ρ₀ : ρ ≤ (9/40:ℝ)/1120 := (div_le_iff₀ sp).mpr (by linarith only [sm])
  have ρpos : 0 ≤ ρ := div_nonneg (by norm_num) sp.le
  have factor : 0 ≤ representativeFactor X := (representativeFactor_one lo hi).trans' (by norm_num)
  refine ⟨ne,?_⟩
  rw [output_atom _ _ _ _ _ ne]
  split_ifs
  · change (1+100*ρ*q)/(C.card:ℝ) ≤ representativeFactor X/r
    apply (div_le_div_iff₀ cp rp).mpr
    have top : 1+100*ρ*q ≤ 1+100*((9/40:ℝ)/1120) := by
      nlinarith only [mul_le_mul_of_nonneg_left qq ρpos,ρ₀]
    have id : representativeFactor X*a = 1+100*((9/40:ℝ)/1120) :=
      div_mul_cancel₀ _ ap.ne'
    calc (1+100*ρ*q)*r ≤ (1+100*((9/40:ℝ)/1120))*r := mul_le_mul_of_nonneg_right top rp.le
         _ = representativeFactor X*(a*r) := by rw [← id,mul_assoc]
         _ ≤ _ := mul_le_mul_of_nonneg_left floor factor
  · exact div_nonneg factor rp.le

end
end Erdos617.ColoredLists
