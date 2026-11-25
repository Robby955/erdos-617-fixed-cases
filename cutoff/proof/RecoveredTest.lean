import ColoringTestedCut

/-! Recover the foreign and representative-pair costs on the original
tested edges before applying the numerical bounds of Appendix A, §5. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The manuscript test uses the expected number of heavy loads and the
number of unique senders in the same retained row. -/
def loadTest (E : Finset V) (I : Finset ℕ) (s : ℕ) (μ : V → Law (State V)) (a b : ℝ) (i : ℕ) : ℝ :=
  let n := heavyLoadMean (targetGraph T.color T.target) (rowList T E) (lowExterior T E I s) s r μ
  (a*n i+b*(uniqueGroup T E I s i).card)/r

/-- For every admissible row test, the signed cut simultaneously pays the
foreign and pair costs on the same original interrow edges. H is the number
of omitted and tested rows. All randomness on the right is in the row test. -/
theorem recovered_tested_cut (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℝ) (ha : 0 ≤ a) (hb : representativeFactor X ≤ b)
    (valid : ∀ i ∈ S.retained, loadTest T E S.retained S.s
      (senderLaw T E S.retained S.s p (retry_rate_of_scale S.scale_lo) hp hp1) a b i ∈ Set.Icc 0 1) :
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
    let H := fun w ↦ h+(TestedRows.tested I w).card
    2*((a-4/3)*Q+(b-j)*T₁+((b/r)^2-(j/r)^2)*K+
        (4/3:ℝ)*((9/40:ℝ)/s)*(∑ i ∈ I, (n i)^2)) ≤
      r*(TestedRows.law I π valid).expect (fun w ↦ (H w:ℝ)*((H w:ℝ)-1))+
        (B+u)^2+m-u-(∑ i ∈ I, (π i*d i)^2) := by
  intro I s h G C L send U μ π E' F n N Q T₁ K j m u d B H
  let single := ∑ i ∈ I, π i*E' i
  let pairs := ∑ q ∈ rowPairs I, π q.1*π q.2*betweenRows T E q
  let foreign := ∑ i ∈ I, n i*F i
  let R := r*(TestedRows.law I π valid).expect (fun w ↦ (H w:ℝ)*((H w:ℝ)-1))
  have recovered : (a/r)*foreign+(b/r)^2*K ≤ pairs :=
    EdgeRecovery.coloring_pair_recovery T S (by omega) X lo hi width p _ hp hp1 a b ha hb
  have rows : single+(a/r)*foreign = a*Q+b*T₁ := by
    dsimp only [single,foreign,Q,T₁]
    rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    change ((a*n i+b*N i)/r)*E' i+(a/r)*(n i*F i) =
      a*(n i*(E' i+F i)/r)+b*(N i*E' i/r)
    ring
  have rep : (∑ i ∈ I, (j/r)*N i*E' i) = j*T₁ := by
    unfold T₁
    rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  have main := tested_cut_bound T prep hr no lists S band slots X lo hi width p hp hp1 π valid
  change 2*(single+pairs) ≤
    2*((4/3:ℝ)*(Q-(9/40:ℝ)/s*(∑ i ∈ I, (n i)^2))+
      (∑ i ∈ I, (j/r)*N i*E' i)+(j/r)^2*K)+R+(B+u)^2+m-u-(∑ i ∈ I, (π i*d i)^2) at main
  rw [rep] at main
  change _ ≤ R+(B+u)^2+m-u-_
  linarith only [main,recovered,rows]

end
end Erdos617.ColoredLists
