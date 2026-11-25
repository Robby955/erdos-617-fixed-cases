import ForeignRowLoads
import ColoringSample
import SampleRepairGraph

/-! The complete expected repair cost on one set of sampled vertices and the
same retained ordinary rows. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} [Fintype V]

/-- n_i is the expected number of vertices with positive excess at row i. -/
def heavyLoadMean (G : SimpleGraph V) (C : ℕ → Finset V) (L : Finset V)
    (s r : ℕ) (μ : V → Law (State V)) (i : ℕ) : ℝ :=
  ∑ y, (μ y).expect fun a ↦ ArcRepair.active (ExcessCircle.excess s r (repairLoad G C L i y a))

/-- The scalar 4(Q−H)/3 + jT + H_E, in vertex and edge units. E_i and F_i
are the exterior and foreign-representative degree sums into the same row i. -/
def sampleRepairBudget (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (s r : ℕ) (μ : V → Law (State V)) (j : ℝ) : ℝ :=
  let n := heavyLoadMean G C L s r μ
  let E := fun i ↦ (product μ).expect (fun w ↦ ∑ y ∈ exterior H L w, SameRowConflicts.degree G (C i) y)
  let F := fun i ↦ ∑ y, (μ y).expect (foreignDegree G C i)
  (4/3:ℝ)*((∑ i ∈ I, n i*(E i+F i)/r) - (9/40:ℝ)/s*(∑ i ∈ I, (n i)^2)) +
      (∑ i ∈ I, (j/r)*(U i).card*E i) + (j/r)^2 * ∑ q ∈ rowPairs I,
        ((U q.1).card:ℝ)*(U q.2).card*((RepresentativeCut.cut G (C q.1) (C q.2)).card:ℝ)

variable {r : ℕ} (T : Trace V r)

/-- The same sender law controls both terms in the deterministic additive edge
bound; its distinct-pair and arc estimates are averaged on the same outcome. -/
theorem sampled_total_repair_cost {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) [NeZero (30*S.s*r)] :
    let I := S.retained
    let C := rowList T E
    let G := targetGraph T.color T.target
    let H := senderSet T E I S.s
    let U := uniqueGroup T E I S.s
    let L := lowExterior T E I S.s
    let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1
    let ν := product fun _ : I ↦ ArcRepair.starts V (30*S.s*r)
    (product μ).expect (fun w ↦ ν.expect fun z ↦
      ((edges G I C H U L w).card:ℝ) + ((sampleArcGraph G I C L S.s r w z).edgeFinset.card:ℝ)) ≤
      sampleRepairBudget G I C H U L S.s r μ (representativeFactor X) := by
  intro I C G H U L μ ν
  let s := S.s
  let load := fun i y ↦ repairLoad G C L i y
  let n := heavyLoadMean G C L s r μ
  let E' := fun i ↦ (product μ).expect (fun w ↦ ∑ y ∈ exterior H L w, SameRowConflicts.degree G (C i) y)
  let F := fun i ↦ ∑ y, (μ y).expect (foreignDegree G C i)
  let j := representativeFactor X
  let rep := fun w ↦ ((edges G I C H U L w).card:ℝ)
  let arc := fun w z ↦ ((sampleArcGraph G I C L s r w z).edgeFinset.card:ℝ)
  have hs : 0<s := by have := S.scale_lo; dsimp [s]; omega
  have bound := ArcRepair.expected_excess_union μ s r hs hr (univ : Finset I) (fun i ↦ load i.val)
  let total := fun i ↦ ∑ y, (μ y).expect (fun a ↦ (load i y a:ℝ))
  change (product μ).expect (fun w ↦ ν.expect (arc w)) ≤
    (4/3:ℝ)*((∑ i : I, n i.val*total i.val/r)-(9/40:ℝ)/s*(∑ i : I, (n i.val)^2)) at bound
  rw [sum_coe_sort I (fun i ↦ n i*total i/r),sum_coe_sort I (fun i ↦ (n i)^2)] at bound
  have cost (i : ℕ) : total i ≤ E' i+F i := expected_load_le_cut_add_foreign T E I s p _ hp hp1 i
  have n0 (i : ℕ) : 0 ≤ n i := by
    apply sum_nonneg
    intro y _
    apply sum_nonneg
    intro a _
    apply mul_nonneg ((μ y).nonneg a)
    dsimp only [ArcRepair.active]
    split <;> norm_num
  have increase : (∑ i ∈ I, n i*total i/r) ≤ ∑ i ∈ I, n i*(E' i+F i)/r :=
    sum_le_sum fun i _ ↦ div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (cost i) (n0 i)) (Nat.cast_nonneg r)
  have repBound := sampled_representative_cost T S hr X lo hi width p hp hp1
  change (product μ).expect rep ≤
    (∑ i ∈ I, (j/r)*(U i).card*E' i) + (j/r)^2 * ∑ q ∈ rowPairs I,
        ((U q.1).card:ℝ)*(U q.2).card*((RepresentativeCut.cut G (C q.1) (C q.2)).card:ℝ) at repBound
  have conditional (w : V → State V) : (ν.expect fun z ↦ rep w+arc w z) = rep w+ν.expect (arc w) := by
    rw [Law.expect_add,Law.expect_const]
  change (product μ).expect (fun w ↦ ν.expect (fun z ↦ rep w+arc w z)) ≤ _
  simp_rw [conditional]
  rw [Law.expect_add]
  change _ ≤ (4/3:ℝ)*((∑ i ∈ I, n i*(E' i+F i)/r) - (9/40:ℝ)/s*(∑ i ∈ I, (n i)^2)) +
    (∑ i ∈ I, (j/r)*(U i).card*E' i) + (j/r)^2 * ∑ q ∈ rowPairs I,
        ((U q.1).card:ℝ)*(U q.2).card*((RepresentativeCut.cut G (C q.1) (C q.2)).card:ℝ)
  linarith only [bound,increase,repBound]

/-- Counting the distinct unordered repairs only once also obeys the
manuscript budget, including when the two repair mechanisms meet. -/
theorem sampled_union_repair_cost {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) [NeZero (30*S.s*r)] :
    let I := S.retained
    let C := rowList T E
    let G := targetGraph T.color T.target
    let H := senderSet T E I S.s
    let U := uniqueGroup T E I S.s
    let L := lowExterior T E I S.s
    let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1
    let ν := product fun _ : I ↦ ArcRepair.starts V (30*S.s*r)
    (product μ).expect (fun w ↦ ν.expect fun z ↦
      (((edges G I C H U L w ∪ (sampleArcGraph G I C L S.s r w z).edgeFinset).card):ℝ)) ≤
        sampleRepairBudget G I C H U L S.s r μ (representativeFactor X) := by
  intro I C G H U L μ ν
  apply le_trans _ (sampled_total_repair_cost T S hr X lo hi width p hp hp1)
  apply (product μ).expect_mono
  intro w
  apply ν.expect_mono
  intro z
  exact_mod_cast card_union_le (edges G I C H U L w) (sampleArcGraph G I C L S.s r w z).edgeFinset

end
end Erdos617.ColoredLists
