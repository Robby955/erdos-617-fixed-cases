import RepresentativeRepairs

/-! Independent tests of the retained rows in the expected signed cut. -/

namespace Erdos617.TestedRows

open Finset FiniteLaw RepresentativeRepairs
open scoped Classical
noncomputable section

private def coin (p : ℝ) (range : p ∈ Set.Icc 0 1) : Law Bool where
  weight b := if b then p else 1-p
  nonneg b := by cases b <;> simp [range.1,range.2]
  total := by simp [Fintype.univ_bool]

/-- Each coordinate belongs to an actual retained row. -/
def law (I : Finset ℕ) (π : ℕ → ℝ) (valid : ∀ i ∈ I, π i ∈ Set.Icc 0 1) :
    Law (I → Bool) where
  weight w := ∏ i : I, (coin (π i) (valid i i.property)).weight (w i)
  nonneg w := prod_nonneg fun i _ ↦ (coin (π i) (valid i i.property)).nonneg (w i)
  total := by rw [← Fintype.prod_sum]; simp only [Law.total,prod_const_one]

private def productExpect {A : Type*} [Fintype A] (μ : A → Law Bool) (f : (A → Bool) → ℝ) :=
  (product μ).expect f

private theorem law_expect (I : Finset ℕ) (π : ℕ → ℝ) (valid : ∀ i ∈ I, π i ∈ Set.Icc 0 1)
    (f : (I → Bool) → ℝ) : (law I π valid).expect f =
      productExpect (fun i : I ↦ coin (π i) (valid i i.property)) f := by
  unfold productExpect Law.expect law product
  apply sum_congr _ fun _ _ ↦ rfl
  exact congrArg (@Finset.univ (I → Bool)) (Subsingleton.elim _ _)

/-- The tested subset, on the same natural-number row labels as the signed cut. -/
def tested (I : Finset ℕ) (w : I → Bool) : Finset ℕ :=
  I.filter fun i ↦ ∃ h : i ∈ I, w ⟨i,h⟩ = true

theorem tested_subset (I : Finset ℕ) (w : I → Bool) : tested I w ⊆ I := filter_subset ..

private theorem tested_mem {I : Finset ℕ} (w : I → Bool) {i : ℕ} (hi : i ∈ I) :
    i ∈ tested I w ↔ w ⟨i,hi⟩ = true := by simp [tested,hi]

private def yes (b : Bool) : ℝ := if b then 1 else 0

private theorem coin_mean (p : ℝ) (rng : p ∈ Set.Icc 0 1) :
    (coin p rng).expect yes = p := by simp [Law.expect,Fintype.univ_bool,coin,yes]

variable (I : Finset ℕ) (π : ℕ → ℝ) (valid : ∀ i ∈ I, π i ∈ Set.Icc 0 1)

theorem single (i : ℕ) (hi : i ∈ I) :
    (law I π valid).expect (fun w ↦ if i ∈ tested I w then (1:ℝ) else 0) = π i := by
  let μ := fun i : I ↦ coin (π i) (valid i i.property)
  have eq (w : I → Bool) : (if i ∈ tested I w then (1:ℝ) else 0) = yes (w ⟨i,hi⟩) := by
    simp only [tested_mem w hi,yes]
  simp_rw [eq,law_expect]
  exact (expect_coord μ ⟨i,hi⟩ yes).trans (coin_mean ..)

theorem pair (i k : ℕ) (hi : i ∈ I) (hk : k ∈ I) (ne : i ≠ k) :
    (law I π valid).expect (fun w ↦ if i ∈ tested I w ∧ k ∈ tested I w then (1:ℝ) else 0) = π i * π k := by
  let μ := fun i : I ↦ coin (π i) (valid i i.property)
  have eq (w : I → Bool) : (if i ∈ tested I w ∧ k ∈ tested I w then (1:ℝ) else 0) =
      yes (w ⟨i,hi⟩) * yes (w ⟨k,hk⟩) := by
    simp only [tested_mem w hi,tested_mem w hk]
    cases w ⟨i,hi⟩ <;> cases w ⟨k,hk⟩ <;> norm_num [yes]
  have neq : (⟨i,hi⟩:I) ≠ ⟨k,hk⟩ := fun h ↦ ne (congrArg Subtype.val h)
  simp_rw [eq,law_expect]
  exact (expect_pair μ neq yes yes).trans (by simp only [μ,coin_mean])

/-- The expected tested cut, or any other sum of one weight per tested row. -/
theorem expected_sum (c : ℕ → ℝ) :
    (law I π valid).expect (fun w ↦ ∑ i ∈ tested I w, c i) = ∑ i ∈ I, π i * c i := by
  have point (w : I → Bool) : (∑ i ∈ tested I w, c i) =
      ∑ i ∈ I, (if i ∈ tested I w then (1:ℝ) else 0)*c i := by
    have eq : I.filter (· ∈ tested I w) = tested I w := by
      ext i
      exact mem_filter.trans ⟨And.right,fun h ↦ ⟨tested_subset I w h,h⟩⟩
    simp only [ite_mul,one_mul,zero_mul,← sum_filter,eq]
  simp_rw [point,Law.expect_sum,Law.expect_mul_const]
  exact sum_congr rfl fun i hi ↦ by rw [single I π valid i hi]

/-- Any system of distinct ordered pairs can be charged by its two test
probabilities. This works both for i<k edges and for the ordered off-diagonal. -/
private theorem expected_pair_filter (P : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℝ)
    (ends : ∀ q ∈ P, q.1 ∈ I ∧ q.2 ∈ I ∧ q.1 ≠ q.2) :
    (law I π valid).expect (fun w ↦ ∑ q ∈ P.filter (fun q ↦ q.1 ∈ tested I w ∧ q.2 ∈ tested I w), c q) =
      ∑ q ∈ P, π q.1*π q.2*c q := by
  have point (w : I → Bool) :
      (∑ q ∈ P.filter (fun q ↦ q.1 ∈ tested I w ∧ q.2 ∈ tested I w), c q) =
      ∑ q ∈ P, (if q.1 ∈ tested I w ∧ q.2 ∈ tested I w then (1:ℝ) else 0)*c q := by
    simp [sum_filter,ite_mul]
  simp_rw [point,Law.expect_sum,Law.expect_mul_const]
  apply sum_congr rfl
  intro q hq
  obtain ⟨h1,h2,ne⟩ := ends q hq
  rw [pair I π valid _ _ h1 h2 ne]

/-- Each interrow cut appears in the one orientation i<k used by the original
repair graph, with coefficient π_i π_k. -/
theorem expected_row_pairs (c : ℕ × ℕ → ℝ) :
    (law I π valid).expect (fun w ↦ ∑ q ∈ rowPairs (tested I w), c q) =
      ∑ q ∈ rowPairs I, π q.1*π q.2*c q := by
  have eq (w : I → Bool) : rowPairs (tested I w) =
      (rowPairs I).filter fun q ↦ q.1 ∈ tested I w ∧ q.2 ∈ tested I w := by
    ext q
    simp only [rowPairs,mem_filter,mem_product]
    exact ⟨fun ⟨⟨a,b⟩,lt⟩ ↦ ⟨⟨⟨tested_subset I w a,tested_subset I w b⟩,lt⟩,a,b⟩,
      fun ⟨⟨_,lt⟩,both⟩ ↦ ⟨both,lt⟩⟩
  simp_rw [eq]
  exact expected_pair_filter I π valid _ _ fun q h ↦
    ⟨(mem_product.mp (mem_filter.mp h).1).1,(mem_product.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2.ne⟩

private theorem off_diag (S : Finset ℕ) (d : ℕ → ℝ) :
    (∑ i ∈ S, d i)^2 - ∑ i ∈ S, (d i)^2 =
      ∑ q ∈ S.offDiag, d q.1*d q.2 := by
  have diag := sum_union (s₁:=S.diag) (s₂:=S.offDiag) (f:=fun q ↦ d q.1*d q.2) S.disjoint_diag_offDiag
  rw [diag_union_offDiag,sum_product,sum_diag] at diag
  simp_rw [← mul_sum] at diag
  rw [← sum_mul] at diag
  simp only [pow_two]
  linarith only [diag]

/-- Exact diagonal rebate in the expected signed cut. This identity permits
arbitrary real deficits. In particular its upper bound needs no sign condition. -/
theorem expected_cross_deficit (d : ℕ → ℝ) :
    let E := (law I π valid).expect (fun w ↦ (∑ i ∈ tested I w, d i)^2 - ∑ i ∈ tested I w, (d i)^2)
    let B := (∑ i ∈ I, π i*d i)^2
    E = B-∑ i ∈ I, (π i*d i)^2 ∧ E ≤ B := by
  intro E B
  have eq (w : I → Bool) : (tested I w).offDiag =
      I.offDiag.filter fun q ↦ q.1 ∈ tested I w ∧ q.2 ∈ tested I w := by
    ext q
    simp only [mem_offDiag,mem_filter]
    exact ⟨fun ⟨a,b,ne⟩ ↦ ⟨⟨tested_subset I w a,tested_subset I w b,ne⟩,a,b⟩,
      fun ⟨⟨_,_,ne⟩,a,b⟩ ↦ ⟨a,b,ne⟩⟩
  have bound : E = B-∑ i ∈ I, (π i*d i)^2 := by
    dsimp only [E,B]
    simp_rw [off_diag,eq]
    rw [expected_pair_filter I π valid I.offDiag _ (fun _ h ↦ mem_offDiag.mp h)]
    exact sum_congr rfl fun q _ ↦ by ring
  exact ⟨bound,bound.le.trans (sub_le_self _ (sum_nonneg fun _ _ ↦ sq_nonneg _))⟩

/-- The signed-cut slot parameter is h plus the number of tested rows.
Its second falling moment keeps the full diagonal rebate. -/
theorem expected_slots (h : ℝ) :
    (law I π valid).expect (fun w ↦ (h+(tested I w).card)*(h+(tested I w).card-1)) =
      h*(h-1) + 2*h*(∑ i ∈ I, π i) + (∑ i ∈ I, π i)^2 - ∑ i ∈ I, (π i)^2 := by
  let c := fun w : I → Bool ↦ ((tested I w).card:ℝ)
  have first : (law I π valid).expect c = ∑ i ∈ I, π i := by
    simpa [c] using expected_sum I π valid (fun _ ↦ 1)
  have second : (law I π valid).expect (fun w ↦ c w^2-c w) =
      (∑ i ∈ I, π i)^2 - ∑ i ∈ I, (π i)^2 := by
    simpa [c] using (expected_cross_deficit I π valid (fun _ ↦ 1)).1
  have expand (w : I → Bool) : (h+(tested I w).card)*(h+(tested I w).card-1) =
      h*(h-1)+2*h*c w+(c w^2-c w) := by dsimp only [c]; ring
  simp_rw [expand]
  rw [Law.expect_add _ _ (fun w ↦ c w^2-c w),Law.expect_add _ (fun _ ↦ h*(h-1)),
    Law.expect_const,Law.expect_const_mul,first,second]
  ring

end
end Erdos617.TestedRows
