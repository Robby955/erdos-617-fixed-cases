import Mathlib.Tactic

/-! Local real inequalities for the weighted-transversal cutoff in Erdős 617. -/

namespace Erdos617.WeightedWidth

/-- With the lower endpoint rescaled to 1, the integral for a row of
weight a ≤ 1 below the endpoint pays at least its endpoint value. -/
theorem lower_tail {a q : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hq : 0 ≤ q) (hcap : q ≤ a^2) : q ≤ a + q/a - q := by
  have h := mul_nonneg hq (sub_nonneg.mpr ha1)
  have hdiv : 2*q-a ≤ q/a := (le_div_iff₀ ha).2 (by nlinarith only [hcap, h])
  linarith

/-- The intermediate range of the upper-end saving. -/
theorem upper_tail {u g : ℝ} (hu : 1/2 ≤ u) (h1 : u ≤ 1)
    (hg : 1/4 ≤ g) : 1/4 ≤ g*u + u*(1-u) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (by linarith : 0 ≤ u-1/4),
    mul_nonneg (sub_nonneg.mpr hg) (by linarith : 0 ≤ u)]

/-- The weighted-transversal bound q ≤ W pays for half the combined
short and chosen list count. S is the total deficit of the short lists. -/
theorem short_lists {D S C T F W q : ℝ}
    (hD : D + S ≤ C + T*q)
    (hS : (1-(1+T)/2)*F + ((1+T)/2)*W ≤ S)
    (hT : 0 ≤ 1+T) (hq : q ≤ W) :
    D + (1-T)/2*(q+F) ≤ C := by
  nlinarith only [hD, hS, mul_nonneg hT (sub_nonneg.mpr hq)]

/-- Combining the missing incidence and vertex budgets cancels the oversized
surplus O and the deletions A inside the chosen oversized parts. -/
theorem omitted_incidences {Y D Y₀ D₀ O A k t cost α β : ℝ}
    (hY : Y ≤ Y₀-k*O+t*A) (hD : D ≤ D₀+O-A-cost)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hO : 0 ≤ O) (hA : 0 ≤ A)
    (hk : α ≤ β*k) (ht : β*t ≤ α) :
    β*Y+α*D ≤ β*Y₀+α*(D₀-cost) := by
  nlinarith only [mul_le_mul_of_nonneg_left hY hβ, mul_le_mul_of_nonneg_left hD hα,
    mul_nonneg hO (sub_nonneg.mpr hk), mul_nonneg hA (sub_nonneg.mpr ht)]

/-- The product of the two auxiliary list fractions plus their squared
deficits dominates a quadratic in their sum. -/
theorem auxiliary_pair {w u v : ℝ} :
    w^2 - w*(u+v) + 3*(u+v)^2/4 ≤ (w-u)*(w-v) + u^2 + v^2 := by
  nlinarith only [sq_nonneg (u-v)]

end Erdos617.WeightedWidth
