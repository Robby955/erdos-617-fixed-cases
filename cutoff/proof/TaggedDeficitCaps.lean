import CutInputs
import AttachmentArena
import AuxiliaryDeficitCaps

/-! The combined deficit budgets for auxiliary and ordinary rows at the attachment stage. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap RowExtraction AuxiliaryMoments
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- For at most three rows, sum the positive deficits in vertex units. The
auxiliary group pays its joint cap and each ordinary row pays at most r/256.
The sizes may refer to the original rows or to any enlargement of them. -/
theorem tagged_deficit_cap {Ycap : ℝ} (prep : CutInputs T Ycap) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β) (scale : (2:ℝ)^b*(S.s:ℝ)^4 < r)
    {B : Finset V} (orderLo : -(3/20:ℝ)*r ≤ (B.card:ℝ)-((S.s-1:ℕ):ℝ)*r)
    {row : B → ℕ} (part : AuxiliaryPartition T S.s B row) {A : Finset B}
    (surv : AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A)
    {parts : Finset (ℕ ⊕ ℕ)} (ai : parts.toLeft ⊆ range (S.s-1)) (oi : parts.toRight ⊆ S.retained)
    (J : Finset (ℕ ⊕ ℕ)) (sub : J ⊆ parts) (few : J.card ≤ 3)
    (size : ℕ ⊕ ℕ → ℕ) (grows : ∀ i ∈ J, (attachmentRow T E A row i).card ≤ size i) :
    (∑ i ∈ J, max ((r:ℝ)-size i) 0) ≤ (r:ℝ)*(peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256) := by
  have sp : 0 < S.s := by have := S.scale_lo; omega
  have rp : (0:ℝ) < r := lt_trans (by positivity) scale
  have hr : 0 < r := by exact_mod_cast rp
  let d := fun i ↦ max (1-(size i:ℝ)/r) 0
  have aux := peeled_deficit_cap T band S.scale_lo scale orderLo part surv J.toLeft
    ((toLeft_subset_toLeft sub).trans ai) (card_toLeft_le.trans few) (fun i ↦ size (.inl i)) (by
      intro i hi
      have g := grows (.inl i) (mem_toLeft.mp hi)
      simpa only [attachmentRow,Sum.elim_inl,card_image_of_injective _ Subtype.val_injective] using g)
  have ord (i) (hi : i ∈ J.toRight) : d (.inr i) ≤ 1/256 := by
    have ret := oi ((toRight_subset_toRight sub) hi)
    have floor := (temporary_row_bounds T prep hr E band S ret).1
    have g : ((temporaryRow T E i).card:ℝ) ≤ size (.inr i) := by
      exact_mod_cast grows (.inr i) (mem_toRight.mp hi)
    have fraction := (le_div_iff₀ rp).2 (floor.trans g)
    exact max_le (by linarith only [fraction]) (by norm_num)
  have ordinary := sum_le_sum ord
  simp only [sum_const, nsmul_eq_mul] at ordinary
  have joined : (∑ i ∈ J, d i) ≤ peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256 := by
    rw [sum_sum_eq_sum_toLeft_add_sum_toRight]
    apply (add_le_add aux ordinary).trans_eq
    ring
  have identity (i) : d i*r = max ((r:ℝ)-size i) 0 := by
    dsimp only [d]
    rw [max_mul_of_nonneg _ _ rp.le,sub_mul,one_mul,div_mul_cancel₀ _ rp.ne',zero_mul]
  calc
    (∑ i ∈ J, max ((r:ℝ)-size i) 0) = (∑ i ∈ J, d i)*r := by simp_rw [sum_mul,identity]
    _ ≤ _ := by simpa only [mul_comm (r:ℝ)] using mul_le_mul_of_nonneg_right joined rp.le

/-- The one-row bounds in vertex units used to price each separate arrival. -/
theorem individual_of_tagged_deficit_cap {r : ℕ} {parts : Finset (ℕ ⊕ ℕ)} {size : ℕ ⊕ ℕ → ℕ}
    (joint : ∀ J ⊆ parts, J.card ≤ 3 →
      (∑ i ∈ J, max ((r:ℝ)-size i) 0) ≤ (r:ℝ)*(peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256))
    {i : ℕ ⊕ ℕ} (hi : i ∈ parts) :
    (r:ℝ)-size i ≤ i.elim (fun _ ↦ (317/2000:ℝ)) (fun _ ↦ (1/256:ℝ))*r := by
  have h := joint {i} (singleton_subset_iff.mpr hi) (by simp)
  rcases i with i|i
  · have l : ({Sum.inl i} : Finset (ℕ ⊕ ℕ)).toLeft = {i} := by ext; simp
    have o : ({Sum.inl i} : Finset (ℕ ⊕ ℕ)).toRight = ∅ := by ext; simp
    norm_num [l,o,peeledCap] at h ⊢
    linarith only [h,Nat.cast_nonneg (α := ℝ) r]
  · have l : ({Sum.inr i} : Finset (ℕ ⊕ ℕ)).toLeft = ∅ := by ext; simp
    have o : ({Sum.inr i} : Finset (ℕ ⊕ ℕ)).toRight = {i} := by ext; simp
    norm_num [l,o,peeledCap] at h ⊢
    linarith only [h]

end
end Erdos617.ColoredLists
