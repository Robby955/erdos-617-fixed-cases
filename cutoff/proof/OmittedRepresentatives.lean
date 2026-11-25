import AuxiliaryCliques
import Mathlib.Data.Finset.Sum

/-! Splitting a prescribed set on omitted rows between the auxiliary and ordinary families. -/

namespace Erdos617.ColoredLists

open Finset RowExtraction
open scoped Classical
noncomputable section
variable {V : Type*} {B : Finset V}

/-- Read the vertices of a tagged family of auxiliary and ordinary rows in the ambient graph. -/
theorem tagged_union (A : Finset B) (row : B → ℕ) (O : ℕ → Finset V) (U : Finset (ℕ ⊕ ℕ)) :
    U.biUnion (Sum.elim (fun i ↦ (fiber A row i).image Subtype.val) O) =
      (A.filter fun q ↦ row q ∈ U.toLeft).image Subtype.val ∪ U.toRight.biUnion O := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,w⟩ := mem_biUnion.mp hv
    rcases i with i|j
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp w
      obtain ⟨qa,eq⟩ := mem_filter.mp hq
      exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨qa,eq ▸ mem_toLeft.mpr hi⟩))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_toRight.mpr hi,w⟩)
  · intro hv
    rcases mem_union.mp hv with a|o
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp a
      obtain ⟨qa,qi⟩ := mem_filter.mp hq
      exact mem_biUnion.mpr ⟨.inl (row q),mem_toLeft.mp qi,
        mem_image_of_mem _ (mem_filter.mpr ⟨qa,rfl⟩)⟩
    · obtain ⟨j,hj,vj⟩ := mem_biUnion.mp o
      exact mem_biUnion.mpr ⟨.inr j,mem_toRight.mp hj,vj⟩

/-- Split the fixtures on omitted rows. The exact cardinal identity charges a
fixture only once even when using only the stated membership hypotheses. -/
theorem split_omitted (A : Finset B) (row : B → ℕ) (O : ℕ → Finset V)
    (allRows U : Finset (ℕ ⊕ ℕ)) (P : Finset V)
    (sub : P ⊆ (allRows \ U).biUnion (Sum.elim (fun i ↦ (fiber A row i).image Subtype.val) O)) :
    ∃ (Q : Finset B) (D : Finset V),
      Q.image Subtype.val ∪ D = P ∧ Q.card+D.card = P.card ∧
      (∀ q ∈ Q, q ∈ A ∧ row q ∉ U.toLeft) ∧
      ∀ v ∈ D, ∃ j ∈ allRows.toRight, j ∉ U.toRight ∧ v ∈ O j := by
  let Q := A.filter fun q ↦ q.val ∈ P ∧ .inl (row q) ∈ allRows \ U
  let D := P \ Q.image Subtype.val
  have pv : Q.image Subtype.val ⊆ P := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hq).2.1
  have cover : Q.image Subtype.val ∪ D = P := union_sdiff_of_subset pv
  have count := card_sdiff_add_card_eq_card pv
  rw [card_image_of_injective _ Subtype.val_injective] at count
  refine ⟨Q,D,cover,by dsimp [D]; omega,?_,?_⟩
  · intro q hq
    obtain ⟨qa,_,diff⟩ := mem_filter.mp hq
    exact ⟨qa,fun inside ↦ (mem_sdiff.mp diff).2 (mem_toLeft.mp inside)⟩
  · intro v hv
    obtain ⟨vp,none⟩ := mem_sdiff.mp hv
    obtain ⟨idx,idxMem,vrow⟩ := mem_biUnion.mp (sub vp)
    rcases idx with i|j
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp vrow
      obtain ⟨qa,eq⟩ := mem_filter.mp hq
      exact (none (mem_image_of_mem _ (mem_filter.mpr ⟨qa,vp,eq ▸ idxMem⟩))).elim
    · obtain ⟨good,bad⟩ := mem_sdiff.mp idxMem
      exact ⟨j,mem_toRight.mpr good,fun hit ↦ bad (mem_toRight.mp hit),vrow⟩

end
end Erdos617.ColoredLists
