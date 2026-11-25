import ColoringSenderLaw

/-! Positive-weight outcomes use only the destinations permitted by the original coloring. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem positive_mark {E I s p rate hp hp1} {x : V} {a : Option V}
    (pos : 0 < (senderLaw T E I s p rate hp hp1 x).weight (some a)) :
    (a = none ∧ senderKind T E I s x = .moderate) ∨
    ∃ i ∈ I, ∃ v ∈ rowList T E i, a = some v ∧
      x ∈ uniqueGroup T E I s i ∧ ¬(targetGraph T.color T.target).Adj x v := by
  have inactive (h : senderKind T E I s x = .multiple) : False := by
    unfold senderLaw at pos
    rw [h] at pos
    cases a <;> change 0 < p*0 at pos <;> linarith only [pos]
  by_cases send : x ∈ senderSet T E I s
  · by_cases empty : strongRows T E I x = ∅
    · have h : senderKind T E I s x = .moderate := by simp [senderKind,send,empty]
      cases a with
      | none => exact Or.inl ⟨rfl,h⟩
      | some v =>
        unfold senderLaw at pos
        rw [h] at pos
        change 0 < p*0 at pos
        linarith only [pos]
    · by_cases one : (strongRows T E I x).card = 1
      · obtain ⟨i,rows⟩ := card_eq_one.mp one
        have member : x ∈ uniqueGroup T E I s i := mem_filter.mpr ⟨send,rows⟩
        obtain ⟨ne,h⟩ := unique_kind T member
        unfold senderLaw at pos
        rw [h] at pos
        cases a with
        | none =>
          change 0 < p*0 at pos
          linarith only [pos]
        | some v =>
          rw [unique_atom] at pos
          split at pos
          · rename_i hv
            exact Or.inr ⟨i,(unique_destination T member).1,v,hv.1,rfl,member,hv.2⟩
          · exact False.elim (lt_irrefl _ pos)
      · exact (inactive (by simp [senderKind,send,nonempty_iff_ne_empty.mpr empty,one])).elim
  · exact (inactive (by simp [senderKind,send])).elim

/-- A positive product weight forces each sender coordinate to have positive
weight, even for a product on all the vertices of the graph. -/
theorem positive_sender_coordinate {E I s p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E I s p rate hp hp1)).weight w) (x : V) :
    0 < (senderLaw T E I s p rate hp hp1 x).weight (w x) := by
  apply lt_of_le_of_ne ((senderLaw T E I s p rate hp hp1 x).nonneg _)
  intro z
  have zero := prod_eq_zero (s:=univ) (f:=fun v ↦ (senderLaw T E I s p rate hp hp1 v).weight (w v))
    (mem_univ x) z.symm
  exact positive.ne' zero

theorem represented_support {E I s p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E I s p rate hp hp1)).weight w)
    {x v : V} (h : w x = some (some v)) :
    ∃ i ∈ I, x ∈ uniqueGroup T E I s i ∧ v ∈ rowList T E i ∧
      ¬(targetGraph T.color T.target).Adj x v := by
  have pos := positive_sender_coordinate T positive x
  rw [h] at pos
  rcases positive_mark T pos with ⟨bad,_⟩|⟨i,hi,a,ha,eq,member,non⟩
  · cases bad
  · cases eq
    exact ⟨i,hi,member,ha,non⟩

theorem moderate_support {E I s p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E I s p rate hp hp1)).weight w)
    {x : V} (h : w x = some none) :
    x ∈ senderSet T E I s ∧ strongRows T E I x = ∅ := by
  have pos := positive_sender_coordinate T positive x
  rw [h] at pos
  rcases positive_mark T pos with ⟨_,kind⟩|⟨_,_,_,_,bad,_⟩
  · by_cases hh : x ∈ senderSet T E I s
    · refine ⟨hh,?_⟩
      by_contra nh
      have ne := nonempty_iff_ne_empty.mpr nh
      by_cases one : (strongRows T E I x).card = 1 <;> simp [senderKind,hh,ne,one] at kind
    · simp [senderKind,hh] at kind
  · cases bad

end
end Erdos617.ColoredLists
