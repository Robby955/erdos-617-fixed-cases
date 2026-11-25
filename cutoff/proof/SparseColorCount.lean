import RawColorRows

/-! Count the original unordered edges by color to pay the sparsity budget in (1). -/

namespace Erdos617.ColoredLists

open Finset
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V]

/-- Each edge belongs to exactly one color class, including when a color is unused. -/
theorem edge_color_partition (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) :
    ∑ k, (targetGraph color k).edgeFinset.card = (Fintype.card V).choose 2 := by
  let F := fun k ↦ (targetGraph color k).edgeFinset
  have dis : ((univ:Finset (Fin r)):Set (Fin r)).PairwiseDisjoint F := by
    intro k _ l _ ne
    apply disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro hk hl
      obtain ⟨_,hk⟩ := SimpleGraph.mem_edgeFinset.mp hk
      obtain ⟨_,hl⟩ := SimpleGraph.mem_edgeFinset.mp hl
      exact ne (hk.symm.trans hl)
  have cover : univ.biUnion F = (⊤ : SimpleGraph V).edgeFinset := by
    apply Finset.ext
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [mem_biUnion, SimpleGraph.mem_edgeFinset]
      change (∃ k ∈ univ, s(x,y) ∈ F k) ↔ x ≠ y
      constructor
      · rintro ⟨k,_,hk⟩
        exact (SimpleGraph.mem_edgeFinset.mp hk).1
      · intro ne
        let k := color ⟨s(x,y),fun h ↦ ne (Sym2.mk_isDiag_iff.mp h)⟩
        exact ⟨k,mem_univ _,SimpleGraph.mem_edgeFinset.mpr ⟨ne,rfl⟩⟩
  calc _ = (univ.biUnion F).card := (card_biUnion dis).symm
       _ = _ := cover ▸ SimpleGraph.card_edgeFinset_top_eq_card_choose_two

/-- Twice the least color's edge count, summed over the r colors, cannot
exceed the number of ordered distinct vertex pairs in the original graph. -/
theorem sparse_edge_cap (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (least : Sparsest color j) :
    (r:ℝ)*2*((targetGraph color j).edgeFinset.card:ℝ) ≤
      (Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1) := by
  let n := Fintype.card V
  have bound : r*(targetGraph color j).edgeFinset.card ≤ n.choose 2 := by
    rw [← edge_color_partition color]
    simpa using Finset.sum_le_sum (s := (univ:Finset (Fin r))) (fun k _ ↦ least k)
  have count : n.choose 2 * 2 = n*(n-1) := by
    rw [Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have paid := Nat.mul_le_mul_right 2 bound
  rw [count] at paid
  change (r:ℝ)*2*(targetGraph color j).edgeFinset.card ≤ (n:ℝ)*((n:ℝ)-1)
  have pred (k : ℕ) : (k:ℝ)*(↑(k-1:ℕ):ℝ) = (k:ℝ)*((k:ℝ)-1) := by
    cases k <;> simp
  calc _ = (r:ℝ)*(targetGraph color j).edgeFinset.card*2 := by ring
       _ ≤ (n:ℝ)*(↑(n-1:ℕ):ℝ) := by exact_mod_cast paid
       _ = _ := pred n

end
end Erdos617.ColoredLists
