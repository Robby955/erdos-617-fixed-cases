import CutInputs
import ColoringSignedCut
import ColoringRepairCost
import TestedRowMoments
import EdgeRecovery

/-! Test retained rows independently after the sender experiment. The same
actual target edges occur in the repair budget and in the signed cut. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section

/-- Applying an independent row test keeps both the diagonal savings in the
deficits and the signed linear term in u. -/
private theorem average_row_tests (I : Finset ℕ) (π : ℕ → ℝ) (valid : ∀ i ∈ I, π i ∈ Set.Icc 0 1)
    (E : ℕ → ℝ) (c : ℕ × ℕ → ℝ) (d : ℕ → ℝ) (h : ℕ) (r P u m : ℝ)
    (fixed : ∀ K ⊆ I, let D := ∑ i ∈ K, d i
      let H := h+K.card
      2*((∑ i ∈ K, E i)+∑ a ∈ rowPairs K, c a) ≤
        2*P+(r*H*((H:ℝ)-1)+D^2-(∑ i ∈ K, (d i)^2))+2*u*D+u^2+m-u) :
    let ψ := TestedRows.law I π valid
    let H := fun w ↦ h+(TestedRows.tested I w).card
    let B := ∑ i ∈ I, π i*d i
    2*((∑ i ∈ I, π i*E i)+∑ q ∈ rowPairs I, π q.1*π q.2*c q) ≤
      2*P+r*ψ.expect (fun w ↦ (H w:ℝ)*((H w:ℝ)-1))+(B+u)^2+m-u-
        ∑ i ∈ I, (π i*d i)^2 := by
  intro ψ H B
  let K := TestedRows.tested I
  let D := fun w ↦ ∑ i ∈ K w, d i
  let J := fun w ↦ (D w)^2-(∑ i ∈ K w, (d i)^2)
  let size := fun w ↦ (H w:ℝ)*((H w:ℝ)-1)
  have point (w) : 2*((∑ i ∈ K w, E i)+∑ q ∈ rowPairs (K w), c q) ≤
      2*P+(r*size w+J w)+(2*u*D w+(u^2+m-u)) := by
    have f := fixed (K w) (TestedRows.tested_subset I w)
    dsimp only at f
    dsimp only [D,J,size,H,K]
    linarith only [f]
  have res := ψ.expect_mono point
  have diag : ψ.expect J = B^2-∑ i ∈ I, (π i*d i)^2 := (TestedRows.expected_cross_deficit I π valid d).1
  rw [Law.expect_const_mul,Law.expect_add,Law.expect_add,Law.expect_add,
      Law.expect_add,Law.expect_add,Law.expect_const,Law.expect_const,
      Law.expect_const_mul,Law.expect_const_mul] at res
  rw [show ψ.expect (fun w ↦ ∑ i ∈ K w, E i) = _ from TestedRows.expected_sum I π valid E,
      show ψ.expect (fun w ↦ ∑ q ∈ rowPairs (K w), c q) = _ from TestedRows.expected_row_pairs I π valid c,
      show ψ.expect D = B from TestedRows.expected_sum I π valid d,diag] at res
  change _ ≤ 2*P+r*ψ.expect size+(B+u)^2+m-u-_
  linarith only [res]

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The signed tested-cut inequality of Appendix A on the original
coloring. The repair allowance is the explicit sum of actual row loads and
interrow edge charges. The test probabilities may be any values in [0,1]. -/
theorem tested_cut_bound {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card=r)
    (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (π : ℕ → ℝ) (valid : ∀ i ∈ S.retained, π i ∈ Set.Icc 0 1) :
    let I := S.retained
    let s := S.s
    let h := s-1
    let G := targetGraph T.color T.target
    let C := rowList T E
    let L := lowExterior T E I s
    let send := senderSet T E I s
    let U := uniqueGroup T E I s
    let μ := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
    let P := sampleRepairBudget G I C send U L s r μ (representativeFactor X)
    let E' := fun i ↦ (product μ).expect fun w ↦ rowToExterior T E (exterior send L w) i
    let m := (product μ).expect (markCount send)
    let u := (h:ℝ)*r-L.card-m
    let d := fun i ↦ (r:ℝ)-(C i).card
    let B := ∑ i ∈ I, π i*d i
    let H := fun w ↦ h+(TestedRows.tested I w).card
    2*((∑ i ∈ I, π i*E' i)+∑ q ∈ rowPairs I, π q.1*π q.2*betweenRows T E q) ≤
      2*P+r*(TestedRows.law I π valid).expect (fun w ↦ (H w:ℝ)*((H w:ℝ)-1))+
        (B+u)^2+m-u-(∑ i ∈ I, (π i*d i)^2) := by
  intro I s h G C L send U μ P E' m u d B H
  have sp : 0 < S.s := by have := S.scale_lo; omega
  have rp : 0 < r := by omega
  let _ : NeZero (30*S.s*r) := ⟨by positivity⟩
  let _ : DecidableEq I := Classical.decEq _
  let ν := product fun _ : I ↦ ArcRepair.starts V (30*s*r)
  let R := (product μ).expect fun w ↦ ν.expect fun z ↦ ((samplePairs T E I s w z).card:ℝ)
  have paid : R ≤ P := sampled_union_repair_cost T S rp X lo hi width p hp hp1
  apply average_row_tests I π valid E' (betweenRows T E) d h r P u m
  intro K sub D H'
  have realCut := expected_fixed_cut T S prep hr no lists band slots K sub p hp hp1
  change 2*((∑ i ∈ K, E' i)+∑ q ∈ rowPairs K, betweenRows T E q) ≤
    2*R+(r*H'*((H':ℝ)-1)+D^2-(∑ i ∈ K, (d i)^2))+2*u*D+u^2+m-u at realCut
  linarith only [realCut,paid]

end
end Erdos617.ColoredLists
