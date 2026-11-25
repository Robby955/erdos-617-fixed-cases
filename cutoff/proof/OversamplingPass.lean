import OversamplingFloor

/-! The oversampling comparison at the manuscript's actual probabilities. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- At every thinning probability, the expected count of marks is p times
the actual eligible mass in the original sender set. -/
theorem sender_count_at_rate (E : Finset V) (I : Finset ℕ) (s : ℕ) (p : ℝ)
    (rate : 100*((9/40:ℝ)/s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let H := senderSet T E I s
    (product (senderLaw T E I s p rate hp hp1)).expect (markCount H) =
      p*(∑ y ∈ H, senderEligibility T E I s y) := by
  intro H
  unfold markCount
  rw [Law.expect_sum,mul_sum]
  apply sum_congr rfl
  intro y hy
  rw [expect_coord,sender_mark_mean,ite_eq_left hy]

/-- At the base thinning p=Δ/A the signed repair budget, with its negative
quadratic term, controls the truncated surplus in eligible senders. The cap
z ≤ Δ/128 allows k = 129/128, or k = 2 for the manuscript certificate. -/
theorem oversampling_pass (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^b*(S.s:ℝ)^4 < r)
    (X : ℝ) (x0 : 0 ≤ X) (x1 : X < 1120) (width : 2*β*S.w ≤ X) (k : ℝ) (hk : 129/128 ≤ k) :
    let I := S.retained
    let H := senderSet T E I S.s
    let L := lowExterior T E I S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-L.card
    let A := ∑ y ∈ H, senderEligibility T E I S.s y
    ∀ (short : 0 < Δ) (extra : Δ < A),
    let p := Δ/A
    let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo)
      (div_nonneg short.le (short.trans extra).le) ((div_le_one (short.trans extra)).mpr extra.le)
    let budget := sampleRepairBudget (targetGraph T.color T.target) I (rowList T E) H
      (uniqueGroup T E I S.s) L S.s r μ (representativeFactor X)
    let z := min (A-Δ) (min (Δ/128) ((r:ℝ)/16))
    r*z ≤ 2*k^2*budget+2*r*(S.s:ℝ)^2 := by
  intro I H L Δ A short extra p μ budget z
  have Apos := short.trans extra
  have rp : 0 < r := by omega
  have sp : 0 < S.s := by have := S.scale_lo; omega
  let _ : NeZero (30*S.s*r) := ⟨by positivity⟩
  have hp : 0 ≤ p := div_nonneg short.le Apos.le
  have hp1 : p ≤ 1 := (div_le_one Apos).mpr extra.le
  have z0 : 0 ≤ z := le_min (sub_nonneg.mpr extra.le) (le_min (by positivity) (by positivity))
  have za : z ≤ A-Δ := min_le_left ..
  have zd : z ≤ Δ/128 := (min_le_right ..).trans (min_le_left ..)
  have zr : z ≤ r/16 := (min_le_right ..).trans (min_le_right ..)
  let q := (Δ+z)/A
  have hq : 0 ≤ q := div_nonneg (add_nonneg short.le z0) Apos.le
  have hq1 : q ≤ 1 := (div_le_one Apos).mpr (by linarith only [za])
  have inc : p ≤ q := div_le_div_of_nonneg_right (le_add_of_nonneg_right z0) Apos.le
  have growth : q ≤ k*p := by
    dsimp only [p,q]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [zd,mul_le_mul_of_nonneg_right hk short.le]) Apos.le
  let rate := retry_rate_of_scale S.scale_lo
  let μ' := senderLaw T E I S.s q rate hq hq1
  have mean : (product μ').expect (markCount H) = Δ+z := by
    rw [sender_count_at_rate]
    exact div_mul_cancel₀ _ Apos.ne'
  obtain ⟨_,h1,_,hscale⟩ := AuxiliaryMoments.scale_facts band S.scale_lo scale
  norm_num at hscale
  have one : (1:ℝ) ≤ ((S.s-1:ℕ):ℝ) := by exact_mod_cast h1
  have small : 4*(S.s-1) ≤ r := by
    exact_mod_cast (show 4*((S.s-1:ℕ):ℝ) ≤ r by
      nlinarith only [hscale,one,sq_nonneg (((S.s-1:ℕ):ℝ)-1)])
  have floor := oversample_expected_floor T prep hr no S band slots small q hq hq1 z z0 zr mean
  have increase := oversample_repairs T E I S.s p q k rate hp hp1 hq hq1 (by linarith only [hk]) inc growth
  have base := sampled_union_repair_cost T S rp X x0 x1 width p hp hp1
  let ν := product fun _ : I ↦ ArcRepair.starts V (30*S.s*r)
  let cost := fun w z ↦ ((samplePairs T E I S.s w z).card:ℝ)
  change r*z/2-r*(S.s:ℝ)^2 ≤ (product μ').expect (fun w ↦ ν.expect (cost w)) at floor
  change (product μ').expect (fun w ↦ ν.expect (cost w)) ≤ k^2*(product μ).expect (fun w ↦ ν.expect (cost w)) at increase
  change (product μ).expect (fun w ↦ ν.expect (cost w)) ≤ budget at base
  linarith only [floor,increase,mul_le_mul_of_nonneg_left base (sq_nonneg k)]

/-- Once the numerical upper bound lies below both truncation levels, the
actual eligibility surplus is the active term. Includes A≤Δ. -/
theorem untruncated_eligibility {A Δ r bound : ℝ} (rp : 0 < r)
    (nonneg : 0 ≤ bound) (capΔ : bound < r*(Δ/128)) (capR : bound < r*(r/16))
    (pass : Δ < A → r*min (A-Δ) (min (Δ/128) (r/16)) ≤ bound) :
    max (A-Δ) 0 ≤ bound/r := by
  apply (le_div_iff₀ rp).mpr
  by_cases h : Δ < A
  · rw [max_eq_left (sub_nonneg.mpr h.le),mul_comm]
    have f := pass h
    rw [mul_min_of_nonneg _ _ rp.le,mul_min_of_nonneg _ _ rp.le] at f
    rcases min_le_iff.mp f with done | tooLarge
    · exact done
    · rcases min_le_iff.mp tooLarge with hΔ | hR
      · exact (capΔ.not_ge hΔ).elim
      · exact (capR.not_ge hR).elim
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt h)),zero_mul]
    exact nonneg

end
end Erdos617.ColoredLists
