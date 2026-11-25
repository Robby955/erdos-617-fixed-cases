import RowExtraction
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! The ordered raw partition obtained by iterating the maximum-degree pivot. -/

namespace Erdos617.RowExtraction

open Finset
open scoped Classical
noncomputable section

variable {V : Type*} (H : SimpleGraph V)

def fiber (A : Finset V) (row : V → ℕ) (i : ℕ) := A.filter fun x ↦ row x = i

def laterRows (A : Finset V) (row : V → ℕ) (i : ℕ) := A.filter fun x ↦ i < row x

/-- A nonempty part has a maximum-degree pivot in the residual graph. Only
its neighbors remain for later rows. The last two fields count target edges. -/
structure RowStep (P L : Finset V) : Prop where
  pivot : P.Nonempty → ∃ x ∈ P, (P ∪ L).filter (H.Adj x) = L ∧
    ∀ y ∈ P ∪ L, ((P ∪ L).filter (H.Adj y)).card ≤ L.card
  at_vertex : ∀ x ∈ P, (P.filter (H.Adj x)).card ≤ (L.filter (Hᶜ.Adj x)).card
  forward : 2*(H.induce (P:Set V)).edgeFinset.card ≤ ∑ x ∈ P, (L.filter (Hᶜ.Adj x)).card

private theorem empty_step : RowStep H ∅ ∅ where
  pivot := by simp
  at_vertex := by simp
  forward := by
    simp
    ext v w
    exact ((Finset.notMem_empty _) v.property).elim

/-- A clique cap of k supplies an actual ordered partition with at most k
nonempty parts. The row function includes empty terminal slots. -/
theorem exists_ordered_rows (k : ℕ) (A : Finset V)
    (cap : ∀ S ⊆ A, H.IsClique (S:Set V) → S.card ≤ k) :
    ∃ row : V → ℕ, (∀ v ∈ A, row v < k) ∧
      ∀ i < k, RowStep H (fiber A row i) (laterRows A row i) := by
  induction k generalizing A with
  | zero =>
    have hempty : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have h := cap {v} (singleton_subset_iff.mpr hv) (by simp)
      simp at h
    subst A
    exact ⟨fun _ ↦ 0, by simp, by simp⟩
  | succ k ih =>
    by_cases ne : A.Nonempty
    · obtain ⟨p,hp,hm⟩ := A.exists_max_image (fun x ↦ (A.filter (H.Adj x)).card) ne
      let L := A.filter (H.Adj p)
      let P := A \ L
      have hL : L ⊆ A := filter_subset ..
      have hpL : p ∉ L := by simp [L]
      have union : P ∪ L = A := sdiff_union_of_subset hL
      have nextCap (S : Finset V) (hs : S ⊆ L) (cl : H.IsClique (S:Set V)) : S.card ≤ k := by
        have fresh : p ∉ S := fun h ↦ hpL (hs h)
        have hcl : H.IsClique ((insert p S:Finset V):Set V) := by
          rw [coe_insert]
          exact cl.insert (fun x hx _ ↦ (mem_filter.mp (hs hx)).2)
        have bound := cap (insert p S) (insert_subset hp (hs.trans hL)) hcl
        simpa [card_insert_of_notMem fresh] using bound
      obtain ⟨tail, labels, steps⟩ := ih L nextCap
      let row := fun v ↦ if v ∈ L then tail v+1 else 0
      have zeroPart : fiber A row 0 = P := by
        ext v
        by_cases h : v ∈ L <;> simp [fiber,row,P,h]
      have zeroLater : laterRows A row 0 = L := by
        ext v
        by_cases h : v ∈ L
        · simp [laterRows,row,h,hL h]
        · simp [laterRows,row,h]
      have succPart (i : ℕ) : fiber A row (i+1) = fiber L tail i := by
        ext v
        by_cases h : v ∈ L
        · simp [fiber,row,h,hL h]
        · simp [fiber,row,h]
      have succLater (i : ℕ) : laterRows A row (i+1) = laterRows L tail i := by
        ext v
        by_cases h : v ∈ L
        · simp [laterRows,row,h,hL h]
        · simp [laterRows,row,h]
      refine ⟨row, ?_, ?_⟩
      · intro v _
        by_cases h : v ∈ L
        · simpa [row,h] using labels v h
        · simp [row,h]
      · intro i hi
        cases i with
        | zero =>
          rw [zeroPart,zeroLater]
          have fw := forward_edges_of_max_degree H A p hm
          refine ⟨fun _ ↦ ⟨p, mem_sdiff.mpr ⟨hp,hpL⟩, ?_, ?_⟩, fw.1, fw.2⟩
          · rw [union]
          · rw [union]; exact hm
        | succ i =>
          rw [succPart, succLater]
          exact steps i (by omega)
    · rw [not_nonempty_iff_eq_empty.mp ne]
      exact ⟨fun _ ↦ 0, by simp, fun i _ ↦ by simpa [fiber,laterRows] using empty_step H⟩

end
end Erdos617.RowExtraction
