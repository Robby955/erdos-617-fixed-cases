import ChosenRows
import PruningOverlap
import CutoffStatement

/-! The maximal-pair construction on the vertices of the colored complete graph. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

/-- A missing-color set for this individual loop-free edge coloring. -/
def Witness (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) : Prop :=
  ∃ (S : Finset V) (j : Fin r), S.card = r+1 ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ h : x ≠ y,
    color ⟨s(x,y), fun d ↦ h (Sym2.mk_isDiag_iff.mp d)⟩ ≠ j

theorem balanced_iff (r : ℕ) : BalancedColoringAt r ↔
    ∀ color : {e : Sym2 (Fin (r^2+1)) // ¬e.IsDiag} → Fin r, Witness color := Iff.rfl

def targetGraph (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r) : SimpleGraph V where
  Adj x y := ∃ h : x ≠ y, color ⟨s(x,y), fun d ↦ h (Sym2.mk_isDiag_iff.mp d)⟩ = j
  symm := ⟨by
    rintro x y ⟨h,hc⟩
    exact ⟨h.symm,(congrArg color (Subtype.ext Sym2.eq_swap)).trans hc⟩⟩
  loopless := ⟨fun _ ⟨h,_⟩ ↦ h rfl⟩

/-- The absence of a witness bounds both independent sets and cliques in
each target graph. A target clique misses any of the other colors. -/
theorem caps_of_no_witness (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (hr : 2 ≤ r) (no : ¬Witness color) :
    (∀ S : Finset V, (targetGraph color j).IsIndepSet (S:Set V) → S.card ≤ r) ∧
    (∀ S : Finset V, (targetGraph color j).IsClique (S:Set V) → S.card ≤ r) := by
  classical
  have cap (S : Finset V) (k : Fin r) (avoid : ∀ x ∈ S, ∀ y ∈ S, ∀ h : x ≠ y,
      color ⟨s(x,y), fun d ↦ h (Sym2.mk_isDiag_iff.mp d)⟩ ≠ k) : S.card ≤ r := by
    by_contra h
    obtain ⟨T,sub,card⟩ := S.exists_subset_card_eq (show r+1 ≤ S.card by omega)
    exact no ⟨T,k,card,fun x hx y hy hne ↦ avoid x (sub hx) y (sub hy) hne⟩
  obtain ⟨k,hk⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin r) (by simp; omega) j
  constructor
  · intro S hS
    exact cap S j fun _ hx _ hy hne he ↦ hS hx hy hne ⟨hne,he⟩
  · intro S hS
    apply cap S k
    intro x hx y hy hne he
    obtain ⟨_,hj⟩ := hS hx hy hne
    exact hk (he.symm.trans hj)

variable [Fintype V] [DecidableEq V] (T : Trace V r)

def live := Finset.univ.filter (fun v ↦ T.stop ≤ T.time v)

omit [Fintype V] [DecidableEq V] in
theorem cross_target :
    cross (targetGraph T.color T.target) T.row = T.crossGraph := by
  ext x y
  constructor
  · rintro ⟨hne,_,hc⟩
    exact ⟨hne,hc⟩
  · rintro ⟨hne,hc⟩
    exact ⟨hne,fun h ↦ hne (congrArg T.row h),hc⟩

def assigned (i : ℕ) : ℝ := ((T.firstSources.filter (fun v ↦ T.destination v = i)).card:ℝ)/r
def firstRate : ℝ := (T.firstSources.card:ℝ)/r
def secondRate : ℝ := (T.secondSources.card:ℝ)/r

omit [DecidableEq V] in
theorem assigned_total (dest : ∀ v ∈ T.firstSources, T.destination v < r) :
    ∑ i ∈ range r, assigned T i = firstRate T := by
  unfold assigned firstRate
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 2
  exact (card_eq_sum_card_fiberwise fun v hv ↦ mem_range.mpr (dest v hv)).symm

theorem deleted_rate : (((univ \ live T).card:ℝ)/r) = firstRate T+secondRate T := by
  have he : univ \ live T = T.firstSources ∪ T.secondSources := by
    ext v
    simp only [live,Trace.firstSources,Trace.secondSources,mem_sdiff,mem_univ,
      mem_filter,true_and,mem_union,not_le]
    have h := T.stages
    omega
  have hd : Disjoint T.firstSources T.secondSources := disjoint_left.mpr (by
    intro v hf hs
    exact (not_lt.mpr (mem_filter.mp hs).2.1) (mem_filter.mp hf).2)
  simp [he,card_union_of_disjoint hd, firstRate,secondRate,add_div]

/-- The color graph produces the lists and (2) after the sequential pruning
has reached its stated degree cap. -/
theorem witness_or_lists (qual : Finset ℕ) (hr : 2 ≤ r)
    (order : Fintype.card V = r^2+1) (rows : ∀ v, T.row v < r)
    (stop : ∀ v ∈ live T, (Transversal.neighbors T.crossGraph (live T) v).card ≤ degreeBound r) :
    Witness T.color ∨ ∃ E, ListBounds (targetGraph T.color T.target) T.row
      univ (live T) (range r) qual E r := by
  by_cases h : Witness T.color
  · exact Or.inl h
  obtain ⟨hi,hc⟩ := caps_of_no_witness T.color T.target hr h
  exact Or.inr (exists_list_bounds _ _ _ _ _ _ r hr (by simpa using order) (subset_univ _)
    (card_range r) (fun v _ ↦ mem_range.mpr (rows v)) hi hc
    (fun v hv ↦ by rw [cross_target]; exact stop v hv))

end
end Erdos617.ColoredLists
