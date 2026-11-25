import RepairThinning

/-! The repaired graph on the enlarged exterior and every other color on
that same exterior give the lower half of the oversampling estimate. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The original graph supplies the two moments and both Turán floors.
Here z is the expected excess of the enlarged exterior over hr. -/
theorem oversample_expected_floor (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card=r)
    (small : 4*(S.s-1) ≤ r) [NeZero (30*S.s*r)]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : ℝ) (z0 : 0 ≤ z) (zcap : z ≤ r/16)
    (mean : (product (senderLaw T E S.retained S.s q (retry_rate_of_scale S.scale_lo) hq hq1)).expect
      (markCount (senderSet T E S.retained S.s)) =
        ((S.s-1:ℕ):ℝ)*r-(lowExterior T E S.retained S.s).card+z) :
    let I := S.retained
    let μ := product (senderLaw T E I S.s q (retry_rate_of_scale S.scale_lo) hq hq1)
    let ν := product fun _ : I ↦ ArcRepair.starts V (30*S.s*r)
    r*z/2-r*(S.s:ℝ)^2 ≤ μ.expect (fun w ↦ ν.expect fun a ↦ ((samplePairs T E I S.s w a).card:ℝ)) := by
  intro I μ ν
  let s := S.s
  let h := s-1
  let H := senderSet T E I s
  let L := lowExterior T E I s
  let W := exterior H L
  let v := fun w ↦ (h:ℝ)*r-((W w).card:ℝ)
  let m := μ.expect (markCount H)
  let P := fun w a ↦ ((samplePairs T E I s w a).card:ℝ)
  let c := 2*((r:ℝ)-h)+1
  let d := (r:ℝ)*h*((h:ℝ)-1)
  have mom := exterior_shortage_moments T E I s q (retry_rate_of_scale S.scale_lo) hq hq1
  change μ.expect v = (h:ℝ)*r-L.card-m ∧ μ.expect (fun w ↦ (v w)^2) ≤ ((h:ℝ)*r-L.card-m)^2+m at mom
  change m = (h:ℝ)*r-L.card+z at mean
  have ev : μ.expect v = -z := by linarith only [mom.1,mean]
  have var : μ.expect (fun w ↦ (v w)^2) ≤ z^2+m := by
    have eq : (h:ℝ)*r-L.card-m = -z := by linarith only [mean]
    simpa only [eq,neg_sq] using mom.2
  have point (w) (pos : 0 < μ.weight w) (a) : c*(-v w)-(v w)^2-d ≤ 2*P w a := by
    let G := targetGraph T.color T.target
    let pairs := samplePairs T E I s w a
    have cap := sample_repair_cap T prep S hr no band slots pos a
    have order : ((W w).card:ℝ) = (h:ℝ)*r+(-v w) := by dsimp [v]; ring
    have cost := inducedRepair_card G (W w) pairs
    have floor := SignedSampleCut.oversample_floor T.color T.target (W w) h
      (inducedRepair G (W w) pairs) (P w a) (-v w) hr no order cap (by
        change ((inducedRepair G (W w) pairs).edgeFinset.card:ℝ) ≤ ((G.induce (W w:Set V)).edgeFinset.card:ℝ)+(pairs.card:ℝ)
        exact_mod_cast cost)
    simpa only [neg_sq] using floor
  have per (w) (pos : 0 < μ.weight w) : c*(-v w)-(v w)^2-d ≤ 2*ν.expect (P w) := by
    have h := ν.expect_mono (point w pos)
    simpa only [Law.expect_const,Law.expect_const_mul] using h
  have algebra (w) : c*(-v w)-(v w)^2-d ≤ 2*ν.expect (P w) ↔
      (-c)*(v w) ≤ 2*ν.expect (P w)+((v w)^2+d) := by constructor <;> intro h <;> linarith only [h]
  have avg := μ.expect_mono_on_support fun w pos ↦ (algebra w).mp (per w pos)
  rw [Law.expect_const_mul,Law.expect_add,Law.expect_const_mul,
    Law.expect_add,Law.expect_const,ev] at avg
  have scale : 0<s := by have := S.scale_lo; dsimp [s]; omega
  have hs : (s:ℝ) = (h:ℝ)+1 := by exact_mod_cast (show s = h+1 by dsimp [h]; omega)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hh : 4*(h:ℝ) ≤ r := by exact_mod_cast small
  have mlim : m ≤ (s:ℝ)*r := by rw [hs,add_mul]; linarith only [mean,zcap,hr0,Nat.cast_nonneg (α:=ℝ) L.card]
  dsimp only [c,d] at avg
  change (r:ℝ)*z/2-r*(s:ℝ)^2 ≤ μ.expect (fun w ↦ ν.expect (P w))
  rw [hs] at mlim ⊢
  nlinarith only [avg,var,mlim,mul_nonneg (sub_nonneg.mpr hh) z0,
    mul_nonneg (sub_nonneg.mpr zcap) z0, z0, mul_nonneg hr0 (sq_nonneg (h:ℝ)),
    mul_nonneg hr0 (Nat.cast_nonneg (α:=ℝ) h),hr0,mul_nonneg hr0 z0]

end
end Erdos617.ColoredLists
