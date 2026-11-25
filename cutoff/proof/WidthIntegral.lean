import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The width argument of Appendix A, §3. The variable t is measured in units
of H = α/m. At equality a row is retained. -/

open Set Filter
open scoped Topology BigOperators

namespace Erdos617.WidthIntegral

/-- Contribution of a row whose normalized breakpoint is a. -/
noncomputable def load (m a q t : ℝ) : ℝ := if t < a then t/m else q/t

/-- Remaining integral of that row above t. The maximum makes continuity at
the breakpoint explicit, including rows with a = 0. -/
noncomputable def tail (m a q t : ℝ) : ℝ :=
  (max a t - t)/m + q / max a t

private theorem tail_right {m a q t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (tail m a q) (-(load m a q t)/t) (Ici t) t := by
  by_cases h : t < a
  · have hd := (((hasDerivAt_const t a).sub (hasDerivAt_id t)).div_const m).add_const (q/a)
    have he : -(load m a q t)/t = (0 - 1)/m := by
      simp only [load, ite_eq_left h]
      field_simp; ring
    rw [he]
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp : t ∈ Ici t)
    filter_upwards [((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds :
      ∀ᶠ z in 𝓝[Ici t] t, z < a)] with z hz
    simp [tail, max_eq_left hz.le]
  · have hd := (hasDerivAt_const t q).div (hasDerivAt_id t) ht.ne'
    have he : -(load m a q t)/t = (0 * t - q * 1)/t^2 := by
      simp only [load, ite_eq_right h]
      ring
    rw [he]
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp : t ∈ Ici t)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have haz : a ≤ z := (le_of_not_gt h).trans hz
    simp [tail, max_eq_right haz]

private theorem tail_cost {m a q t : ℝ} (_hm : 0 < m) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hcap : q ≤ a^2/m) (_ht : 0 < t) :
    tail m a q t + load m a q t ≤ a/m + q/a := by
  by_cases h : t < a
  · simp only [tail, load, ite_eq_left h, max_eq_left h.le, sub_div]
    linarith
  · have hat := le_of_not_gt h
    simp only [tail, load, ite_eq_right h, max_eq_right hat, sub_self, zero_div, zero_add]
    rcases ha.eq_or_lt with rfl | ha
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hcap
      simp [le_antisymm hcap hq]
    · have h₁ : q / t ≤ q / a := div_le_div_of_nonneg_left hq ha hat
      have h₂ : q / a ≤ a / m := (div_le_iff₀ ha).2 (by rwa [div_mul_eq_mul_div, ← sq])
      linarith

variable {ι : Type*}

/-- Failure at every threshold from l to h bounds the logarithmic width.
The endpoint term is the sum of the exact remaining row integrals. -/
theorem failure_budget (rows : Finset ι) (a q : ι → ℝ) {m l h : ℝ}
    (hm : 0 < m) (hl : 0 < l) (hlh : l ≤ h)
    (ha : ∀ i ∈ rows, 0 ≤ a i) (hq : ∀ i ∈ rows, 0 ≤ q i)
    (cap : ∀ i ∈ rows, q i ≤ (a i)^2/m)
    (failure : ∀ t ∈ Icc l h, 1 ≤ t + ∑ i ∈ rows, load m (a i) (q i) t) :
    -Real.log l ≤ (∑ i ∈ rows, (a i/m + q i/a i)) -
      (1-h + (∑ i ∈ rows, tail m (a i) (q i) h) + Real.log h) := by
  let G := fun t : ℝ ↦ t - Real.log t - ∑ i ∈ rows, tail m (a i) (q i) t
  have cont : ContinuousOn G (Icc l h) := by
    apply ContinuousOn.sub
    · exact continuousOn_id.sub (Real.continuousOn_log.mono (fun t ht ↦ (hl.trans_le ht.1).ne'))
    · apply continuousOn_finsetSum
      intro i hi
      unfold tail
      apply ContinuousOn.add
      · fun_prop
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro t ht
          exact (lt_of_lt_of_le (hl.trans_le ht.1) (le_max_right _ _)).ne'
  let d := fun t : ℝ ↦ 1 - t⁻¹ - ∑ i ∈ rows, (-(load m (a i) (q i) t)/t)
  have hd (t : ℝ) (ht : t ∈ Ico l h) : HasDerivWithinAt G (d t) (Ici t) t := by
    exact ((hasDerivAt_id t).sub (Real.hasDerivAt_log (hl.trans_le ht.1).ne')).hasDerivWithinAt.sub
      (HasDerivWithinAt.fun_sum fun i _ ↦ tail_right (hl.trans_le ht.1))
  have hn (t : ℝ) (ht : t ∈ Ico l h) : 0 ≤ d t := by
    have hx := failure t ⟨ht.1, ht.2.le⟩
    have ht' := hl.trans_le ht.1
    dsimp [d]
    simp_rw [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [← one_div, sub_neg_eq_add]
    field_simp
    linarith
  have hmono : G l ≤ G h := by
    apply image_le_of_deriv_right_le_deriv_boundary (f := fun _ ↦ G l) (B := G)
      (f' := fun _ ↦ 0) (B' := d) continuousOn_const (fun t _ ↦ (hasDerivAt_const t _).hasDerivWithinAt)
      le_rfl cont hd hn ⟨hlh, le_rfl⟩
  have hc := Finset.sum_le_sum (s := rows) (fun i hi ↦
    tail_cost hm (ha i hi) (hq i hi) (cap i hi) hl)
  rw [Finset.sum_add_distrib] at hc
  have hf := failure l ⟨le_rfl, hlh⟩
  dsimp [G] at hmono
  linarith

end Erdos617.WidthIntegral
