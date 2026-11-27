import CutInputs
import HeavyLoadBound

/-! Sum the original destination counts before truncating by their uniform
cap. The resulting bound controls how many rows are tested in expectation. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PruningOverlap.Trace PackingLists FiniteLaw
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {e t : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

theorem retained_load_budgets {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r) :
    let I := S.retained
    (∑ i ∈ I, rowDeficit T E i)+(∑ i ∈ I, rawSurplus T i)+(∑ i ∈ I, assigned T i) ≤ 7 ∧
      2*(∑ i ∈ I, rowDeficit T E i) ≤ 9 ∧
      (∑ i ∈ I, rowIncidence T E i) ≤ Ycap :=
  prep.retained S hr no order lists

/-- With f=9/40 the total number of heavy loads divided by sr is at most
Y/f+7/1120. Y is evaluated from the actual deletion rates. -/
theorem heavy_load_total {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let I := S.retained
    let G := targetGraph T.color T.target
    let C := rowList T E
    let L := lowExterior T E I S.s
    let μ := senderLaw T E I S.s p rate hp hp1
    let n := heavyLoadMean G C L S.s r μ
    let Y₀ := Ycap
    (∑ i ∈ I, n i) ≤ ((Y₀/(9/40:ℝ))+7/1120)*S.s*r := by
  intro I G C L μ n Y₀
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<S.s := by linarith
  let ρ := (9/40:ℝ)/S.s
  have rho : 0<ρ := by dsimp [ρ]; positivity
  have h := sum_le_sum (s:=I) fun i hi ↦ heavy_load_height T S prep hr no lists band p rate hp hp1 hi
  change (∑ i ∈ I, n i/r) ≤ ∑ i ∈ I,
    (rowDeficit T E i+rawSurplus T i+assigned T i+rowIncidence T E i/ρ) at h
  simp only [sum_add_distrib,← sum_div] at h
  obtain ⟨exc,_,inc⟩ := retained_load_budgets T S prep hr no order lists
  have inc' : (∑ i ∈ I, rowIncidence T E i)/ρ ≤ Y₀/ρ := div_le_div_of_nonneg_right inc rho.le
  have main : (∑ i ∈ I, n i)/r ≤ 7+Y₀/ρ := by linarith only [h,exc,inc']
  apply (div_le_iff₀ rp).mp
  apply main.trans
  change 7+Y₀/((9/40:ℝ)/S.s) ≤ (Y₀/(9/40)+7/1120)*S.s
  rw [div_div_eq_mul_div]
  linarith only [slo]

end
end Erdos617.ColoredLists
