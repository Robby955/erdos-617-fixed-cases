import Mathlib.Tactic

/-! The two prescribed-extension estimates in Appendix A, §4.
All variables are fractions of the row scale; edge counts are divided by its square.
The sum of losses in two different rows charges each deleted or forbidden vertex at most once.
-/

namespace Erdos617.PrescribedProducts

private theorem deficit_cost {u x : ℝ} (budget : x+u^2 ≤ (3/20:ℝ)^2+1/2^20) :
    u+x/(43/200) < 4/25 := by
  nlinarith only [budget, sq_nonneg (u-43/400)]

/-- Each auxiliary list stays nonempty after two small exterior attachments. -/
theorem two_exterior_positive {u x z p L : ℝ}
    (budget : x+u^2 ≤ (3/20:ℝ)^2+1/2^20) (paid : (43/200)*z ≤ x)
    (lost : p ≤ z) (size : 19/100-u-p ≤ L) : 0 < L := by
  linarith only [deficit_cost budget, paid, lost, size]

/-- Two small exterior attachments. The loss in the product per deleted vertex
is at most 19/100, below its 43/200 contribution to the edge budget. -/
theorem two_exterior_product {u v x z p q L M : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (budget : x+u^2+v^2 ≤ (3/20:ℝ)^2+1/2^20) (paid : (43/200)*z ≤ x)
    (lost : p+q ≤ z) (left : 19/100-u-p ≤ L) (right : 19/100-v-q ≤ M) :
    x-(43/200)*z < L*M := by
  have bu : x+u^2 ≤ (3/20:ℝ)^2+1/2^20 := by linarith only [budget,sq_nonneg v]
  have bv : x+v^2 ≤ (3/20:ℝ)^2+1/2^20 := by linarith only [budget,sq_nonneg u]
  have lp := two_exterior_positive bu paid (show p ≤ z by linarith only [lost,hq])
      (le_refl (19/100-u-p))
  have mp := two_exterior_positive bv paid (show q ≤ z by linarith only [lost,hp])
      (le_refl (19/100-v-q))
  have base : x < (19/100-u)*(19/100-v) := by
    nlinarith only [budget, sq_nonneg (u-v), sq_nonneg (u+v-(2:ℝ)/3*(19/100))]
  have reduced : x-(43/200)*z < (19/100-u-p)*(19/100-v-q) := by
    nlinarith only [base,lost,hp,hq,mul_nonneg hu hq,mul_nonneg hv hp,mul_nonneg hp hq]
  exact reduced.trans_le (mul_le_mul left right mp.le (lp.le.trans left))

/-- After one small exterior attachment and at most two prescribed representatives,
the pruning and representatives together can cost z+43/100 in one row. -/
theorem one_exterior_positive {u x z p L : ℝ}
    (budget : x+u^2 ≤ (3/20:ℝ)^2+1/2^20) (paid : (43/200)*z ≤ x)
    (lost : p ≤ z+43/100) (size : 119/200-u-p ≤ L) : 0 < L := by
  linarith only [deficit_cost budget, paid, lost, size]

/-- One small exterior attachment and at most two compatible representatives.
The representatives cost at most 43/100 across the two unfilled lists together. -/
theorem one_exterior_product {u v x z p q L M : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (budget : x+u^2+v^2 ≤ (3/20:ℝ)^2+1/2^20) (paid : (43/200)*z ≤ x)
    (hz : 0 ≤ z) (lost : p+q ≤ z+43/100)
    (left : 119/200-u-p ≤ L) (right : 119/200-v-q ≤ M) :
    x-(43/200)*z < L*M := by
  let b := (119/200:ℝ)-max u v
  have bu : x+u^2 ≤ (3/20:ℝ)^2+1/2^20 := by linarith only [budget,sq_nonneg v]
  have bv : x+v^2 ≤ (3/20:ℝ)^2+1/2^20 := by linarith only [budget,sq_nonneg u]
  have large : x/(43/200)+43/100 < b := by
    dsimp [b]
    rcases le_total u v with h|h
    · rw [max_eq_right h]
      linarith only [deficit_cost bv]
    · rw [max_eq_left h]
      linarith only [deficit_cost bu]
  have one : b-p ≤ L := by dsimp [b]; linarith only [left,le_max_left u v]
  have two : b-q ≤ M := by dsimp [b]; linarith only [right,le_max_right u v]
  have remain : 0 < b-z-43/100 := by linarith only [large,paid]
  have big : (43/200:ℝ) ≤ b := by linarith only [remain,hz]
  have edge : x-(43/200)*z < (43/200)*(b-z-43/100) := by linarith only [large]
  have place : (43/200)*(b-z-43/100) ≤ b*(b-z-43/100) :=
    mul_le_mul_of_nonneg_right big remain.le
  have distribute : b*(b-z-43/100) ≤ (b-p)*(b-q) := by
    nlinarith only [mul_nonneg hp hq, mul_nonneg (show 0 ≤ b by linarith only [big])
      (sub_nonneg.mpr lost)]
  have pleft : 0 ≤ b-p := by linarith only [remain,lost,hq]
  have pright : 0 ≤ b-q := by linarith only [remain,lost,hp]
  exact ((edge.trans_le place).trans_le distribute).trans_le
    (mul_le_mul one two pright (pleft.trans one))

end Erdos617.PrescribedProducts
