import ThirdPruningHoles
import EdgeProductTransversal
import ColoringLists

/-! The two endpoints of a nontarget edge in a common row must block an
independent transversal of all the other surviving rows. -/
namespace Erdos617.ThirdPruning

open Finset PackingLists Transversal
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V]

/-- All degrees, lists and surviving cross edges in the conclusion are
computed on the same original graph. Neither endpoint has to belong to A. -/
theorem hole_blocks_other_rows (G : SimpleGraph V) (row : V → ℕ) (A : Finset V)
    {r : ℕ} {B : ℝ} (pos : 0 < B)
    (floor : ∀ i < r, B ≤ ((A.filter fun v ↦ row v = i).card : ℝ))
    (cap : ∀ R : Finset V, G.IsIndepSet (R : Set V) → R.card ≤ r)
    {x w : V} (ne : x ≠ w) (same : row w = row x) (idx : row x < r)
    (missing : ¬G.Adj x w) :
    B - (((cross G row).induce (A : Set V)).edgeFinset.card : ℝ) / B ≤
      ((A.filter ((cross G row).Adj x)).card : ℝ) + (A.filter ((cross G row).Adj w)).card := by
  classical
  by_contra! small
  let N := fun v ↦ A.filter ((cross G row).Adj v)
  let D := N x ∪ N w
  let L := (A \ D).filter fun v ↦ row v ≠ row x
  let P := (range r).erase (row x)
  let lost := fun i ↦ D.filter fun v ↦ row v = i
  let kept := fun i ↦ L.filter fun v ↦ row v = i
  let E := ((cross G row).induce (A : Set V)).edgeFinset.card
  have cost : (D.card : ℝ) < B - E / B := lt_of_le_of_lt
    (by exact_mod_cast card_union_le (N x) (N w)) small
  have budget : (D.card:ℝ) < B :=
    cost.trans_le (sub_le_self _ (div_nonneg (Nat.cast_nonneg _) pos.le))
  have lower (i) (hi : i ∈ P) : B - (lost i).card ≤ ((kept i).card : ℝ) := by
    have diff := (mem_erase.mp hi).1
    have cover : A.filter (fun v ↦ row v = i) ⊆ kept i ∪ lost i := by
      intro v hv
      obtain ⟨hA,eq⟩ := mem_filter.mp hv
      by_cases hD : v ∈ D
      · exact mem_union_right _ (mem_filter.mpr ⟨hD,eq⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_sdiff.mpr ⟨hA,hD⟩,eq ▸ diff⟩,eq⟩)
    have h : ((A.filter fun v ↦ row v = i).card : ℝ) ≤ (kept i).card + ((lost i).card:ℝ) := by
      exact_mod_cast (card_le_card cover).trans (card_union_le ..)
    linarith only [h,floor i (mem_range.mp (mem_erase.mp hi).2)]
  have subset : L ⊆ A := (filter_subset ..).trans sdiff_subset
  obtain ⟨R,sub,rep,im⟩ := exists_of_edge_products G A L row P subset (by
    intro i hi
    have h : ((lost i).card:ℝ) ≤ D.card := by exact_mod_cast card_le_card (filter_subset ..)
    have positive : (0:ℝ) < (kept i).card := by linarith only [h, budget, lower i hi]
    exact card_pos.mp (by exact_mod_cast positive)) (by
    intro i hi j hj nij
    have dis : Disjoint (lost i) (lost j) := disjoint_left.mpr fun _ h k ↦
      nij ((mem_filter.mp h).2.symm.trans (mem_filter.mp k).2)
    have both : (lost i).card + (lost j).card ≤ D.card := by
      rw [← card_union_of_disjoint dis]
      exact card_le_card (union_subset (filter_subset ..) (filter_subset ..))
    have bound := two_list_product pos (Nat.cast_nonneg E) (Nat.cast_nonneg (lost i).card)
      (Nat.cast_nonneg (lost j).card) ((show ((lost i).card:ℝ)+(lost j).card ≤ D.card by
        exact_mod_cast both).trans_lt cost) (lower i hi) (lower j hj)
    exact_mod_cast bound)
  have avoids {v} (hv : v ∈ R) : row v ≠ row x ∧ ¬G.Adj x v ∧ ¬G.Adj w v := by
    obtain ⟨h, diff⟩ := mem_filter.mp (sub hv)
    obtain ⟨hA,hD⟩ := mem_sdiff.mp h
    exact ⟨diff,fun bad ↦ hD (mem_union_left _ (mem_filter.mpr ⟨hA,diff.symm,bad⟩)),
      fun bad ↦ hD (mem_union_right _ (mem_filter.mpr ⟨hA,same ▸ diff.symm,bad⟩))⟩
  have add (v : V) (S : Finset V) (ind : G.IsIndepSet (S:Set V))
      (ok : ∀ u ∈ S, ¬G.Adj v u) : G.IsIndepSet (insert v S : Finset V) := by
    intro a ha b hb nab adj
    rcases mem_insert.mp ha with ax | ain
    · subst a
      rcases mem_insert.mp hb with bx | bin
      · exact nab bx.symm
      · exact ok _ bin adj
    · rcases mem_insert.mp hb with bx | bin
      · exact ok _ ain (bx ▸ G.adj_symm adj)
      · exact ind ain bin nab adj
  have rwInd := add w R rep.independent fun _ hv ↦ (avoids hv).2.2
  have allInd := add x (insert w R) rwInd (by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact missing
    · exact (avoids hv).2.1)
  have size := cap _ allInd
  have nx : x ∉ R := fun h ↦ (avoids h).1 rfl
  have nw : w ∉ R := fun h ↦ (avoids h).1 same
  rw [card_insert_of_notMem (show x ∉ insert w R by simpa [ne] using nx),
      card_insert_of_notMem nw, ← card_image_of_injOn rep.distinct, im] at size
  have erased : P.card = r-1 := by simp [P,card_erase_of_mem (mem_range.mpr idx)]
  omega

end
end Erdos617.ThirdPruning
