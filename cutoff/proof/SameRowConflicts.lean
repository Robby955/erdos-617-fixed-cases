import SameRowPairs
import JointSenderLaw

/-! The expected cost of representative conflicts at one row under the joint sampling law. -/

namespace Erdos617.SameRowConflicts

open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

def markProb (μ : V → Law (Option (Option V))) (x : V) := (μ x).expect marked

private theorem markProb_nonneg (μ : V → Law (Option (Option V))) (x : V) : 0 ≤ markProb μ x := by
  rw [← (μ x).expect_const 0]
  exact (μ x).expect_mono marked_nonneg

private theorem markProb_le_one (μ : V → Law (Option (Option V))) (x : V) : markProb μ x ≤ 1 := by
  rw [← (μ x).expect_const 1]
  exact (μ x).expect_mono marked_le_one

private theorem mean_hit (G : SimpleGraph V) (C : Finset V) (μ : V → Law (Option (Option V)))
    {x : V} (y : V) {a : ℝ} (cap : ∀ v ∈ C, (μ x).weight (some (some v)) ≤ a) :
    (μ x).expect (hit G C y) ≤ a*degree G C y := by
  rw [show hit G C y = fun o ↦ ∑ v ∈ C.filter (G.Adj y),
      if o = some (some v) then (1:ℝ) else 0 from funext (hit_as_atoms G C y)]
  rw [Law.expect_sum]
  trans ∑ v ∈ C.filter (G.Adj y), (μ x).weight (some (some v))
  · apply le_of_eq
    apply sum_congr rfl
    intro v _
    convert Law.expect_atom (μ x) (some (some v)) using 2
    funext o
    by_cases h : o = some (some v) <;> simp [h]
  · apply (sum_le_sum fun v hv ↦ cap v (mem_filter.mp hv).1).trans_eq
    simp [degree,mul_comm]

/-- The expected number of unordered marked pairs in U is bounded by
one half of the square of their total marking probability. Only distinct
coordinates occur in the factorization. -/
theorem same_pairs (U : Finset V) (μ : V → Law (Option (Option V))) :
    (product μ).expect (fun w ↦ (∑ p ∈ U.offDiag, marked (w p.1)*marked (w p.2))/2) ≤
      (∑ x ∈ U, markProb μ x)^2/2 := by
  simp_rw [div_eq_mul_inv]
  rw [Law.expect_mul_const,Law.expect_sum]
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  calc _ = ∑ p ∈ U.offDiag, markProb μ p.1 * markProb μ p.2 := by
           apply sum_congr rfl
           intro p hp
           exact expect_pair μ (mem_offDiag.mp hp).2.2 marked marked
       _ ≤ ∑ p ∈ U ×ˢ U, markProb μ p.1 * markProb μ p.2 :=
           sum_le_sum_of_subset_of_nonneg (fun _ hp ↦
            mem_product.mpr ⟨(mem_offDiag.mp hp).1,(mem_offDiag.mp hp).2.1⟩)
            (fun _ _ _ ↦ mul_nonneg (markProb_nonneg ..) (markProb_nonneg ..))
       _ = _ := by rw [sum_product,sq,sum_mul]; exact sum_congr rfl fun x _ ↦ (mul_sum U (markProb μ) (markProb μ x)).symm

/-- L is the fixed low-attachment exterior. Every vertex in U or O is
included exactly when its own coordinate is marked. -/
def sampled (U O L : Finset V) (w : V → Option (Option V)) :=
  L ∪ ((U ∪ O).filter (fun y ↦ (w y).isSome))

def weightedCut (G : SimpleGraph V) (C M : Finset V) (μ : V → Law (Option (Option V))) : ℝ :=
  ∑ y ∈ M, degree G C y * markProb μ y

def fixedCut (G : SimpleGraph V) (C L : Finset V) : ℝ := ∑ y ∈ L, degree G C y

theorem expected_cut (G : SimpleGraph V) (C U O L : Finset V) (μ : V → Law (Option (Option V)))
    (sep : Disjoint U O) (fixed : Disjoint L (U ∪ O)) :
    (product μ).expect (fun w ↦ ∑ y ∈ sampled U O L w, degree G C y) =
      fixedCut G C L + weightedCut G C O μ + weightedCut G C U μ := by
  have identity (w : V → Option (Option V)) :
      (∑ y ∈ sampled U O L w, degree G C y) =
        fixedCut G C L + ∑ y ∈ U ∪ O, degree G C y * marked (w y) := by
    rw [sampled,sum_union (fixed.mono_right (filter_subset ..)),sum_filter]
    congr 1
    exact sum_congr rfl fun y _ ↦ by by_cases a : (w y).isSome <;> simp [marked,a]
  simp_rw [identity]
  rw [Law.expect_add,Law.expect_const,Law.expect_sum]
  have marginal (y : V) : (product μ).expect (fun w ↦ degree G C y * marked (w y)) =
      degree G C y * markProb μ y := by rw [Law.expect_const_mul,expect_coord]; rfl
  simp_rw [marginal]
  rw [sum_union sep]
  dsimp only [weightedCut]
  ring

/-- Hits from U to O use distinct coordinates. Hits to fixed vertices
require just the marginal distribution of the representative. -/
theorem other_hits (G : SimpleGraph V) (C U O L : Finset V) (μ : V → Law (Option (Option V)))
    (sep : Disjoint U O) (a : ℝ)
    (cap : ∀ x ∈ U, ∀ v ∈ C, (μ x).weight (some (some v)) ≤ a) :
    (product μ).expect (fun w ↦ ∑ x ∈ U, ((∑ y ∈ L, hit G C y (w x))+
      ∑ y ∈ O, hit G C y (w x)*marked (w y))) ≤
        a*U.card*(fixedCut G C L + weightedCut G C O μ) := by
  rw [Law.expect_sum]
  calc _ ≤ ∑ _x ∈ U, a*(fixedCut G C L + weightedCut G C O μ) := by
         apply sum_le_sum
         intro x hx
         rw [Law.expect_add,Law.expect_sum,Law.expect_sum]
         have first : (∑ y ∈ L, (product μ).expect (fun w ↦ hit G C y (w x))) ≤
             a*fixedCut G C L := by
           rw [fixedCut,mul_sum]
           exact sum_le_sum fun y _ ↦ (expect_coord μ x (hit G C y)).le.trans (mean_hit G C μ y (cap x hx))
         have second : (∑ y ∈ O, (product μ).expect (fun w ↦ hit G C y (w x)*marked (w y))) ≤
             a*weightedCut G C O μ := by
           rw [weightedCut,mul_sum]
           apply sum_le_sum
           intro y hy
           have ne : x ≠ y := fun eq ↦ disjoint_left.mp sep hx (eq ▸ hy)
           rw [expect_pair μ ne (hit G C y) marked]
           change _ * markProb μ y ≤ _
           rw [← mul_assoc]
           exact mul_le_mul_of_nonneg_right (mean_hit G C μ y (cap x hx)) (markProb_nonneg ..)
         linarith only [first,second]
       _ = _ := by simp; ring

/-- All representative conflicts at a single row cost at most (j/r) N E.
E is the expected true cut into the actual sampled exterior set; N is the
number of unique senders at this row, before thinning. -/
theorem expected_edges_le_cut (G : SimpleGraph V) (C U O L : Finset V)
    (μ : V → Law (Option (Option V))) (sep : Disjoint U O) (fixed : Disjoint L (U ∪ O))
    (r j : ℝ) (hr : 0 < r) (hj : 1 ≤ j)
    (cap : ∀ x ∈ U, ∀ v ∈ C, (μ x).weight (some (some v)) ≤ j/r)
    (heavy : ∀ x ∈ U, r/2 ≤ degree G C x) :
    (product μ).expect (fun w ↦ ((edges G C U O L w).card:ℝ)) ≤
      (j/r)*U.card*(product μ).expect (fun w ↦ ∑ y ∈ sampled U O L w, degree G C y) := by
  rw [expected_cut G C U O L μ sep fixed]
  apply ((product μ).expect_mono (edges_le_cost G C U O L)).trans
  change (product μ).expect (fun w ↦ _ + _) ≤ _
  rw [Law.expect_add]
  have plain := add_le_add (same_pairs U μ) (other_hits G C U O L μ sep (j/r) cap)
  apply plain.trans
  let t := ∑ x ∈ U, markProb μ x
  have t0 : 0 ≤ t := sum_nonneg fun _ _ ↦ markProb_nonneg ..
  have card : t ≤ (U.card:ℝ) := by simpa [t] using
    (sum_le_sum (s := U) (fun x _ ↦ markProb_le_one μ x))
  have ec : (r/2)*t ≤ weightedCut G C U μ := by
    rw [weightedCut,show t = ∑ x ∈ U, markProb μ x from rfl,mul_sum]
    exact sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_right (heavy x hx) (markProb_nonneg ..)
  have tj : t ≤ j*(U.card:ℝ) := card.trans ((le_mul_of_one_le_left (Nat.cast_nonneg _) hj))
  have nonneg : 0 ≤ (j/r)*(U.card:ℝ) := by positivity
  have scaled := mul_le_mul_of_nonneg_left ec nonneg
  have cancel : (j/r)*(U.card:ℝ)*(r/2*t) = j*(U.card:ℝ)*t/2 := by field_simp
  rw [cancel] at scaled
  have paid : t^2/2 ≤ (j/r)*(U.card:ℝ)*weightedCut G C U μ := by
    nlinarith only [scaled,mul_le_mul_of_nonneg_right tj t0]
  change t^2/2 + _ ≤ _
  linarith only [paid]

end
end Erdos617.SameRowConflicts
