import ModerateDestinations

/-! Strong senders and marked moderate senders use the same clique capacity.
The count of moderate arrivals is random; the strong set is fixed in advance. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The variance and the linear term in the moderate count cost at most one
copy of its mean. All their target edges enter the same arrival bound as
the strong senders' edges. -/
theorem mixed_row_capacity (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β bound Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β bound)
    (band : RetainedWidth.Band Y ex α β) {i : ℕ} (hi : i ∈ S.retained)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let I := S.retained
    let s := S.s
    let μ := product (senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1)
    let v := μ.expect (markCount (moderateGroup T E I s i))
    let d := (r:ℝ)-(rowList T E i).card
    (∑ y ∈ strongGroup T E I s i, rowSenderPayment T E i y) + ((9/40:ℝ)/s*r)*v ≤
      r*d+(501/1000:ℝ)*d^2+v^2+v := by
  intro I s μ v d
  let C := rowList T E i
  let G := targetGraph T.color T.target
  let Z := strongGroup T E I s i
  let M := moderateGroup T E I s i
  let deg := fun y ↦ ((C.filter (G.Adj y)).card:ℝ)
  let J := ∑ y ∈ Z, 2*d*(1-neighborFraction G C y)
  let n := markCount (V:=V) M
  let z := (Z.card:ℝ)
  let unit := (9/40:ℝ)/s*r
  let pay := ∑ y ∈ Z, rowSenderPayment T E i y
  have paid : pay = (∑ y ∈ Z, deg y)+z*d-J := by
    change (∑ y ∈ Z, (deg y+d-2*d*(1-neighborFraction G C y))) = _
    rw [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul]
  have extDis : Disjoint C (senderSet T E I s) := disjoint_left.mpr fun y hy h ↦
    ((mem_senderSet T).mp h).1 (mem_biUnion.mpr ⟨i,hi,hy⟩)
  have strongDis : Disjoint C Z := extDis.mono_right (filter_subset ..)
  have apart : Disjoint Z M := by
    apply disjoint_left.mpr
    intro y hz hm
    have mem := assignedStrong_subset _ (mem_filter.mp hz).2
    rw [(mem_filter.mp hm).2.1] at mem
    exact notMem_empty _ mem
  have heavy (y) (hy : y ∈ Z) : (r:ℝ)/2 < deg y :=
    (mem_filter.mp (assignedStrong_subset _ (mem_filter.mp hy).2)).2
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have cl : G.IsClique (C:Set V) :=
    lists.clique i (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  have fit := (caps_of_no_witness T.color T.target (by omega) no).2 _ cl
  have count : z ≤ 2*d := by
    dsimp only [z,d]
    rw [← Nat.cast_sub (R:=ℝ) fit]
    exact_mod_cast (retained_heavy_senders T prep hr no lists S band hi Z strongDis heavy).1
  have count_id (w : V → State V) : n w = ((M.filter fun y ↦ (w y).isSome).card:ℝ) := by
    change (∑ y ∈ M, if (w y).isSome then (1:ℝ) else 0) = _
    simp only [sum_boole]
  have v0 : 0 ≤ v := by
    apply sum_nonneg
    intro w _
    change 0 ≤ μ.weight w*n w
    rw [count_id]
    positivity [μ.nonneg w]
  have correction := retained_row_charge T prep hr no lists S band hi Z strongDis heavy v v0
  change z^2/2+(z-d)*v-J ≤ (501/1000:ℝ)*d^2+v^2/2 at correction
  let limit := (r:ℝ)*d+(501/1000:ℝ)*d^2+v^2
  let coeff := 2*(z-d+v-unit)+1
  have point (w) : 2*(pay+unit*v) ≤
      (2*limit+v)+(n w-v)^2+(n w-v)*coeff := by
    let A := M.filter fun y ↦ (w y).isSome
    have dis := apart.mono_right (filter_subset (fun y ↦ (w y).isSome) M)
    have outside : Disjoint C (Z ∪ A) := disjoint_union_right.mpr
      ⟨strongDis,extDis.mono_right ((filter_subset ..).trans (filter_subset ..))⟩
    have arrivals := clique_arrival_capacity T.color T.target C (Z ∪ A) (by omega) no outside cl
    change (∑ y ∈ Z ∪ A, deg y)+((Z ∪ A).card:ℝ)*d ≤
      ((r:ℝ)-1)*d+((Z ∪ A).card:ℝ)*(((Z ∪ A).card:ℝ)+1)/2 at arrivals
    rw [sum_union dis,card_union_of_disjoint dis,Nat.cast_add] at arrivals
    have size : (A.card:ℝ)=n w := (count_id w).symm
    rw [size] at arrivals
    have edges := sum_le_sum (s:=A) fun y hy ↦ (moderate_destination_degree T (mem_filter.mp hy).1).le
    change (∑ _ ∈ A, unit) ≤ ∑ y ∈ A, deg y at edges
    rw [sum_const,nsmul_eq_mul,size] at edges
    change (∑ y ∈ Z, deg y)+(∑ y ∈ A, deg y)+(z+n w)*d ≤
      ((r:ℝ)-1)*d+(z+n w)*(z+n w+1)/2 at arrivals
    dsimp only [coeff,limit]
    linarith only [arrivals,edges,correction,count,paid]
  have variance : μ.expect (fun w ↦ (n w-v)^2) ≤ v :=
    mark_count_variance_le_mean G id (senderKind T E I s) ((9/40:ℝ)/s) p
      (by positivity) (retry_rate_of_scale S.scale_lo) hp hp1 M
  have mean : μ.expect (fun w ↦ n w-v) = 0 := by
    simp only [sub_eq_add_neg,Law.expect_add,Law.expect_const]
    change v + -v = 0
    ring
  have avg := μ.expect_mono point
  rw [Law.expect_const,Law.expect_add,Law.expect_add,Law.expect_const,Law.expect_mul_const,
    mean,zero_mul,add_zero] at avg
  change pay+unit*v ≤ limit+v
  linarith only [avg,variance]

/-- A marked sender either uses one moderate destination or has already paid
the unit price through its unique strong destination's retry charge. -/
theorem marked_sender_payment (E : Finset V) (I : Finset ℕ) (s : ℕ) (hs : 1120 ≤ s)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let H := senderSet T E I s
    let μ := product (senderLaw T E I s p (retry_rate_of_scale hs) hp hp1)
    let m := μ.expect (markCount H)
    let v := fun i ↦ μ.expect (markCount (moderateGroup T E I s i))
    let unit := (9/40:ℝ)/s*r
    (∑ i ∈ I, v i) ≤ m ∧
      unit*m ≤ (∑ y ∈ H, senderRetryCharge T E I s y)+unit*∑ i ∈ I, v i := by
  intro H μ m v unit
  let laws := senderLaw T E I s p (retry_rate_of_scale hs) hp hp1
  let weight := fun y ↦ (laws y).expect marked
  let M := H.filter fun y ↦ strongRows T E I y = ∅
  have expand (A : Finset V) : μ.expect (markCount A) = ∑ y ∈ A, weight y := by
    change (product laws).expect (fun w ↦ ∑ y ∈ A, marked (w y)) = _
    rw [Law.expect_sum]
    exact sum_congr rfl fun y _ ↦ expect_coord laws y marked
  have split := moderate_partition T E I s
  have total : (∑ i ∈ I, v i) = ∑ y ∈ M, weight y := by
    dsimp only [v]
    simp_rw [expand]
    rw [← sum_biUnion split.1,split.2]
  have raw : m = ∑ y ∈ H, weight y := expand _
  have nonneg (y) : 0 ≤ weight y := by
    apply sum_nonneg
    intro w _
    have hw : 0 ≤ marked w := by cases w <;> simp [marked]
    exact mul_nonneg ((laws y).nonneg w) hw
  rw [total,raw]
  refine ⟨sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun y _ _ ↦ nonneg y),?_⟩
  let charge := senderRetryCharge T E I s
  have point (y) (hy : y ∈ H) : unit*weight y ≤
      charge y+(if strongRows T E I y = ∅ then unit*weight y else 0) := by
    by_cases empty : strongRows T E I y = ∅
    · rw [ite_eq_left empty]
      exact le_add_of_nonneg_left (senderRetryCharge_nonneg T E I hs y)
    rw [ite_eq_right empty,add_zero]
    have pos := sender_mark_mean T E I s p (retry_rate_of_scale hs) hp hp1 y
    change weight y = p*(if y ∈ H then senderEligibility T E I s y else 0) at pos
    rw [ite_eq_left hy] at pos
    rw [pos]
    by_cases single : (strongRows T E I y).card = 1
    · obtain ⟨i,one⟩ := card_eq_one.mp single
      have mass : 0 ≤ rowSuccess T E s y i := by
        unfold rowSuccess successIn
        apply mass_nonnegative
        · positivity
        · exact retry_rate_of_scale hs
        · intro a
          cases a <;> simp
      have dominated := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left mass hp1) (show 0 ≤ unit by dsimp [unit]; positivity)
      have miss := one_sub_neighborFraction_nonneg (targetGraph T.color T.target) (rowList T E i) y
      have extra := mul_nonneg (show 0 ≤ 37*((9/40:ℝ)/s)*r by positivity) miss
      simp only [charge,senderRetryCharge,uniqueCharge,senderEligibility,eligibleWeight,one,
        card_singleton,ite_true,one_ne_zero,ite_false,sum_singleton]
      dsimp only [unit] at dominated
      linarith only [dominated,extra]
    · have ne : (strongRows T E I y).card ≠ 0 := fun h ↦ empty (card_eq_zero.mp h)
      simp [charge,senderRetryCharge,uniqueCharge,senderEligibility,eligibleWeight,single,ne]
  have h := sum_le_sum point
  rw [sum_add_distrib,← sum_filter,← mul_sum,← mul_sum] at h
  exact h

/-- The combined capacity inequality after cancelling the common raw deficit
from both sides. It holds at every thinning probability for this selection. -/
theorem mixed_sender_capacity (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e t : ℕ} {α β bound Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β bound)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let I := S.retained
    let s := S.s
    let H := senderSet T E I s
    let Δ := ((s-1:ℕ):ℝ)*r-(lowExterior T E I s).card
    let A := ∑ y ∈ H, senderEligibility T E I s y
    let μ := product (senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1)
    let m := μ.expect (markCount H)
    let v := fun i ↦ μ.expect (markCount (moderateGroup T E I s i))
    let unit := (9/40:ℝ)/s*r
    r*(1+Δ-A)+unit*m ≤
      (501/1000:ℝ)*(∑ i ∈ I, ((r:ℝ)-(rowList T E i).card)^2)+(∑ i ∈ I, (v i)^2)+m := by
  intro I s H Δ A μ m v unit
  let slack := fun i ↦ (v i)^2+v i-unit*v i
  have cost (i) (hi : i ∈ I) := mixed_row_capacity T prep hr no lists S band hi p hp hp1
  have cover := eligible_mass_of_row_allowances T hr no order lists S band slots slack (fun i hi ↦ by
    have h := cost i hi
    dsimp only at h
    dsimp only [slack,v,unit,I,s,μ] at ⊢
    linarith only [h])
  change r*(1+Δ-A)+(∑ y ∈ H, senderRetryCharge T E I s y) ≤
    (501/1000:ℝ)*(∑ i ∈ I, ((r:ℝ)-(rowList T E i).card)^2)+∑ i ∈ I, slack i at cover
  simp only [slack,sum_sub_distrib,sum_add_distrib,← mul_sum] at cover
  obtain ⟨subset,charged⟩ := marked_sender_payment T E I s S.scale_lo p hp hp1
  change (∑ i ∈ I, v i) ≤ m at subset
  change unit*m ≤ (∑ y ∈ H, senderRetryCharge T E I s y)+unit*∑ i ∈ I, v i at charged
  linarith only [cover,subset,charged]

end
end Erdos617.ColoredLists
