import OmittedRepresentatives
import AttachmentArena
import PrescribedCompletion
import UniqueAttachment

/-! Prescribed extension and clique enlargement on the selected rows of the actual coloring. -/

namespace Erdos617.ColoredLists

open Finset RowExtraction PruningOverlap UniqueAttachment
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Both the auxiliary-only and mixed arenas satisfy the extension property
used for clique enlargement, with attachments measured before enlargement. -/
theorem actual_can_extend (prep : Prepared T) (hr : 0 < r)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β)
    {B : Finset V} (subB : B ⊆ lowExterior T E S.retained S.s)
    (row : B → ℕ) (part : AuxiliaryPartition T S.s B row)
    (A : Finset B) (live : AuxiliarySurvivors
      (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A)
    (arena : Finset V) (parts : Finset (ℕ ⊕ ℕ))
    (ai : parts.toLeft ⊆ range (S.s-1)) (oi : parts.toRight ⊆ S.retained) :
    CanExtend (targetGraph T.color T.target) arena parts (attachmentRow T E A row)
      (attachmentLarge T E A row) := by
  let G := targetGraph T.color T.target
  let C := attachmentRow T E A row
  intro P F U ext fix sub shape ind small
  have auxSub := (toLeft_subset_toLeft sub).trans ai
  have ordSub := (toRight_subset_toRight sub).trans oi
  obtain ⟨Q,D,union,count,qa,od⟩ := split_omitted A row (temporaryRow T E) parts U F fix
  have ids : U.biUnion C = auxiliaryRowsOn A row U.toLeft ∪ U.toRight.biUnion (temporaryRow T E) :=
    tagged_union A row (temporaryRow T E) U
  have parent : U.biUnion C ⊆ parts.biUnion C := by
    intro v hv
    obtain ⟨i,hi,vi⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨i,sub hi,vi⟩
  have outside : Disjoint P (U.biUnion C) := disjoint_left.mpr fun x hx hit ↦
    (mem_sdiff.mp (ext hx)).2 (parent hit)
  rw [ids,disjoint_union_right] at outside
  have smallA (v) (hv : v ∈ P) (i) (hi : i ∈ U.toLeft) :
      (((fiber A row i).filter fun q ↦ G.Adj v q.val).card:ℝ) ≤ (81/200:ℝ)*r := by
    have adj := le_of_not_gt (small v hv (.inl i) (mem_toLeft.mp hi))
    have inject : ((fiber A row i).filter fun q ↦ G.Adj v q.val).card ≤
        ((C (.inl i)).filter (G.Adj v)).card := by
      apply card_le_card_of_injOn Subtype.val _ (fun _ _ _ _ eq ↦ Subtype.ext eq)
      intro q hq
      obtain ⟨qi,g⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨mem_image_of_mem _ qi,g⟩
    exact (Nat.cast_le.mpr inject).trans adj
  have smallO (v) (hv : v ∈ P) (i) (hi : i ∈ U.toRight) :
      (((temporaryRow T E i).filter (G.Adj v)).card:ℝ) ≤ (369/1000:ℝ)*r :=
    le_of_not_gt (small v hv (.inr i) (mem_toRight.mp hi))
  have occupied (x) (hx : x ∈ D) : ∃ j ∈ S.retained, j ∉ U.toRight ∧ x ∈ temporaryRow T E j := by
    obtain ⟨i,hi,abs,v⟩ := od x hx
    exact ⟨i,oi hi,abs,v⟩
  have shape' : (P.card ≤ 2 ∧ Q = ∅ ∧ D = ∅) ∨ (P.card ≤ 1 ∧ Q.card+D.card ≤ 2) := by
    rcases shape with ⟨one,f⟩|⟨two,empty⟩
    · exact Or.inr ⟨one.le,by omega⟩
    · rw [empty,card_empty] at count
      exact Or.inl ⟨two.le,card_eq_zero.mp (by omega),card_eq_zero.mp (by omega)⟩
  have fixEq : P ∪ Q.image Subtype.val ∪ D = P ∪ F := by rw [union_assoc,union]
  obtain ⟨Z,inc,cnt,dis,whole,_⟩ := complete_prescribed_rows T prep hr S band subB row part A live
    U.toLeft U.toRight auxSub ordSub P Q D outside.1 outside.2 smallA smallO qa occupied shape' (fixEq ▸ ind)
  rw [fixEq] at dis whole
  exact ⟨Z,ids ▸ inc,cnt.trans card_toLeft_add_card_toRight,dis,whole⟩

end
end Erdos617.ColoredLists
