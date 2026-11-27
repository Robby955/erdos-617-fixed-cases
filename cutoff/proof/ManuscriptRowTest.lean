import CutInputs
import HeavyLoadTests

/-! The actual endpoint test in the signed-cut inequality of Appendix A. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Total probability mass of the endpoint tests, hence their expected count.
The destination counts are summed before taking a uniform per-row bound. -/
theorem manuscript_test_mass {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let I := S.retained
    let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1
    let Y₀ := Ycap
    (∑ i ∈ I, loadTest T E I S.s μ a b i) ≤
      (a*(Y₀/(9/40:ℝ)+7/1120)+9*b/1120)*S.s := by
  intro I μ Y₀
  let n := heavyLoadMean (targetGraph T.color T.target) (rowList T E) (lowExterior T E I S.s) S.s r μ
  let N := fun i ↦ ((uniqueGroup T E I S.s i).card:ℝ)
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have allN := sum_le_sum (s:=I) fun i hi ↦
    div_le_div_of_nonneg_right (unique_count_le_deficit T S prep hr no lists band hi) rp.le
  change (∑ i ∈ I, N i/r) ≤ ∑ i ∈ I, 2*((r:ℝ)-(rowList T E i).card)/r at allN
  simp_rw [mul_div_assoc, sub_div, div_self rp.ne'] at allN
  rw [← mul_sum] at allN
  have totalN : (∑ i ∈ I, N i/r) ≤ 9 := allN.trans (retained_load_budgets T S prep hr no order lists).2.1
  have alln := heavy_load_total T S prep hr no order lists band p (retry_rate_of_scale S.scale_lo) hp hp1
  have smalln : (∑ i ∈ I, n i/r) ≤ (Y₀/(9/40:ℝ)+7/1120)*S.s := by
    rw [← sum_div]
    exact (div_le_iff₀ rp).mpr alln
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  change (∑ i ∈ I, (a*n i+b*N i)/r) ≤ _
  simp_rw [add_div,mul_div_assoc]
  rw [sum_add_distrib,← mul_sum,← mul_sum]
  have paid := add_le_add (mul_le_mul_of_nonneg_left smalln ha) (mul_le_mul_of_nonneg_left totalN hb)
  nlinarith only [paid,mul_le_mul_of_nonneg_right slo hb]

/-- The coloring supplies the test probabilities. The second falling moment
is evaluated here for independent tests on precisely these retained rows. -/
theorem manuscript_tested_cut {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let a := heavyTestWeight A X
    let b := uniqueTestWeight A X
    let I := S.retained
    let s := S.s
    let h := s-1
    let G := targetGraph T.color T.target
    let C := rowList T E
    let L := lowExterior T E I s
    let send := senderSet T E I s
    let U := uniqueGroup T E I s
    let μ := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
    let π := loadTest T E I s μ a b
    let E' := fun i ↦ (product μ).expect fun w ↦ rowToExterior T E (exterior send L w) i
    let F := fun i ↦ ∑ y, (μ y).expect (foreignDegree G C i)
    let n := heavyLoadMean G C L s r μ
    let N := fun i ↦ ((U i).card:ℝ)
    let Q := ∑ i ∈ I, n i*(E' i+F i)/r
    let T₁ := ∑ i ∈ I, N i*E' i/r
    let K := ∑ q ∈ rowPairs I, N q.1*N q.2*betweenRows T E q
    let j := representativeFactor X
    let m := (product μ).expect (markCount send)
    let u := (h:ℝ)*r-L.card-m
    let d := fun i ↦ (r:ℝ)-(C i).card
    let B := ∑ i ∈ I, π i*d i
    let q := ∑ i ∈ I, π i
    let slots₂ := (h:ℝ)*((h:ℝ)-1)+2*(h:ℝ)*q+q^2-(∑ i ∈ I, (π i)^2)
    2*((a-4/3)*Q+(b-j)*T₁+((b/r)^2-(j/r)^2)*K+
        (4/3:ℝ)*((9/40:ℝ)/s)*(∑ i ∈ I, (n i)^2)) ≤
      r*slots₂+
        (B+u)^2+m-u-(∑ i ∈ I, (π i*d i)^2) := by
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let I := S.retained
  let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1
  let π := loadTest T E I S.s μ a b
  let h := S.s-1
  have valid := manuscript_row_test T S prep hr no lists band A X a0 a1 x0 x1 inc defi p hp hp1
  obtain ⟨alow,_,blow,_⟩ := test_weight_bounds a0 a1 x0 x1
  have main := recovered_tested_cut T prep (by omega) no lists S band slots X x0
    (by linarith only [x1]) defi p hp hp1 a b (by dsimp [a]; linarith only [alow]) blow valid
  have moment : (TestedRows.law I π valid).expect
      (fun w ↦ ((h+(TestedRows.tested I w).card:ℕ):ℝ)*(((h+(TestedRows.tested I w).card:ℕ):ℝ)-1)) =
      (h:ℝ)*((h:ℝ)-1)+2*(h:ℝ)*(∑ i ∈ I, π i)+(∑ i ∈ I, π i)^2-(∑ i ∈ I, (π i)^2) := by
    simpa only [Nat.cast_add] using TestedRows.expected_slots I π valid (h:ℝ)
  dsimp only at main ⊢
  rw [moment] at main
  exact main

end
end Erdos617.ColoredLists
