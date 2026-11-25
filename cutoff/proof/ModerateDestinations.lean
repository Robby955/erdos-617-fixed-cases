import OneRowCapacity

/-! Assign moderate senders using the original target edges before sampling.
A one-row expected cut then pays their squared mean counts. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private def moderateDestination (E : Finset V) (I : Finset ℕ) (s : ℕ) (y : V) : ℕ :=
  if h : y ∈ senderSet T E I s then ((mem_senderSet T).mp h).2.choose else 0

def moderateGroup (E : Finset V) (I : Finset ℕ) (s i : ℕ) : Finset V :=
  (senderSet T E I s).filter fun y ↦ strongRows T E I y = ∅ ∧ moderateDestination T E I s y = i

/-- The groups partition exactly the moderate senders. The assignment is fixed
by the coloring and does not depend on any subsequent trial. -/
theorem moderate_partition (E : Finset V) (I : Finset ℕ) (s : ℕ) :
    let M := moderateGroup T E I s
    (I:Set ℕ).PairwiseDisjoint M ∧
    I.biUnion M = (senderSet T E I s).filter (fun y ↦ strongRows T E I y = ∅) := by
  intro M
  constructor
  · intro i _ j _ ne
    exact disjoint_left.mpr fun y hi hj ↦ ne ((mem_filter.mp hi).2.2.symm.trans (mem_filter.mp hj).2.2)
  · ext y
    constructor
    · intro hy
      obtain ⟨i,_,mem⟩ := mem_biUnion.mp hy
      exact mem_filter.mpr ⟨(mem_filter.mp mem).1,(mem_filter.mp mem).2.1⟩
    · intro hy
      obtain ⟨send,moderate⟩ := mem_filter.mp hy
      have belongs : moderateDestination T E I s y ∈ I := by
        simp only [moderateDestination,dite_eq_left send]
        exact ((mem_senderSet T).mp send).2.choose_spec.1
      exact mem_biUnion.mpr ⟨_,belongs,mem_filter.mpr ⟨send,moderate,rfl⟩⟩

theorem moderate_destination_degree {E : Finset V} {I : Finset ℕ} {s i : ℕ} {y : V}
    (hy : y ∈ moderateGroup T E I s i) :
    (9/40:ℝ)/s*r < SameRowConflicts.degree (targetGraph T.color T.target) (rowList T E i) y := by
  obtain ⟨send,_,eq⟩ := mem_filter.mp hy
  rw [← eq]
  simp only [moderateDestination,dite_eq_left send]
  exact ((mem_senderSet T).mp send).2.choose_spec.2

/-- Every moderate mark adds its own degree to the true exterior cut at its
assigned row. Taking expectations requires no independence within a row. -/
theorem moderate_cut_payment (E : Finset V) (I : Finset ℕ) (s i : ℕ)
    (μ : Law (V → State V)) :
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let M := moderateGroup T E I s i
    ((9/40:ℝ)/s*r)*μ.expect (markCount M) ≤
      μ.expect (fun w ↦ rowToExterior T E (exterior H L w) i) := by
  intro H L M
  rw [← Law.expect_const_mul]
  apply μ.expect_mono
  intro w
  let A := M.filter fun y ↦ (w y).isSome
  let price := (9/40:ℝ)/s*r
  have count : markCount M w = (A.card:ℝ) := by
    change (∑ y ∈ M, (if (w y).isSome then (1:ℝ) else 0)) = _
    simp only [A,sum_boole]
  have inside : A ⊆ exterior H L w := fun y hy ↦ mem_union_right _ (mem_filter.mpr
    ⟨(mem_filter.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩)
  have paid := sum_le_sum (s:=A) fun y hy ↦ (moderate_destination_degree T (mem_filter.mp hy).1).le
  rw [sum_const,nsmul_eq_mul] at paid
  rw [count,mul_comm]
  exact paid.trans (sum_le_sum_of_subset_of_nonneg inside fun _ _ _ ↦ Nat.cast_nonneg _)

/-- Uniform one-row cut bounds control the sum of the squared moderate
counts at their actual destinations. All variables use one exterior law. -/
theorem moderate_square_sum (E : Finset V) (I : Finset ℕ) (s : ℕ) (sp : 0<s) (rp : 0<r)
    (μ : Law (V → State V)) (ε : ℝ) (ep : 0 ≤ ε) :
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let unit := (9/40:ℝ)/s*r
    let v := fun i ↦ μ.expect (markCount (moderateGroup T E I s i))
    (∀ i ∈ I, μ.expect (fun w ↦ rowToExterior T E (exterior H L w) i) ≤ ε*unit^2) →
      (∑ i ∈ I, (v i)^2) ≤ ε*unit*μ.expect (markCount H) := by
  intro H L unit v cuts
  have up : 0 < unit := by dsimp [unit]; positivity
  have nonneg (w : V → State V) (y : V) : 0 ≤ marked (w y) := by
    unfold marked
    split <;> norm_num
  have v0 (i) : 0 ≤ v i := by
    apply sum_nonneg
    intro w _
    exact mul_nonneg (μ.nonneg w) (sum_nonneg fun y _ ↦ nonneg w y)
  have cap (i) (hi : i ∈ I) : v i ≤ ε*unit := by
    apply le_of_mul_le_mul_left (a:=unit) _ up
    have h := (moderate_cut_payment T E I s i μ).trans (cuts i hi)
    change unit*v i ≤ ε*unit^2 at h
    linarith only [h]
  have total : (∑ i ∈ I, v i) ≤ μ.expect (markCount H) := by
    change (∑ i ∈ I, μ.expect (markCount (moderateGroup T E I s i))) ≤ _
    rw [← Law.expect_sum]
    apply μ.expect_mono
    intro w
    unfold markCount
    obtain ⟨apart,eq⟩ := moderate_partition T E I s
    rw [← sum_biUnion apart,eq]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun y _ _ ↦ nonneg w y
  calc
    _ ≤ ∑ i ∈ I, (ε*unit)*v i := sum_le_sum fun i hi ↦ by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (cap i hi) (v0 i)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left total (mul_nonneg ep up.le)

end
end Erdos617.ColoredLists
