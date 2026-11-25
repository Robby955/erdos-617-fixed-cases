import ColoringLists

/-! The other colors force internal nontarget edges in every oversized raw row. -/

namespace Erdos617.ColoredLists

open Finset
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

/-- Choose one endpoint of each edge. Deleting the chosen vertices leaves
an independent set, so a graph with independence cap k needs |V|-k edges. -/
theorem edge_lower_of_independence [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (cap : ∀ S : Finset V, G.IsIndepSet (S:Set V) → S.card ≤ k) :
    Fintype.card V ≤ k+G.edgeFinset.card := by
  let C := G.edgeFinset.image (fun e ↦ e.out.1)
  have ind : G.IsIndepSet (((univ \ C):Finset V):Set V) := by
    intro x hx y hy _ edge
    have he : s(x,y) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr edge
    have inC : (s(x,y)).out.1 ∈ C := mem_image_of_mem _ he
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x,y)) with h | h
    · exact (mem_sdiff.mp hx).2 (h ▸ inC)
    · exact (mem_sdiff.mp hy).2 (h ▸ inC)
  have upper := cap _ ind
  have count := card_sdiff_add_card_eq_card (subset_univ C)
  have cheap : C.card ≤ G.edgeFinset.card := card_image_le
  calc Fintype.card V = (univ \ C).card+C.card := by simpa only [card_univ] using count.symm
       _ ≤ _ := Nat.add_le_add upper cheap

private theorem induced_cap (G : SimpleGraph V) (A : Finset V) (k : ℕ)
    (cap : ∀ S : Finset V, G.IsIndepSet (S:Set V) → S.card ≤ k)
    (S : Finset A) (hS : (G.induce (A:Set V)).IsIndepSet (S:Set A)) : S.card ≤ k := by
  let f : A ↪ V := Function.Embedding.subtype _
  have independent : G.IsIndepSet ((S.map f : Finset V):Set V) := by
    intro x hx y hy ne edge
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    exact hS hu hv (fun h ↦ ne (congrArg f h)) edge
  simpa using cap _ independent

/-- All nontarget edges in A are partitioned by their actual colors. -/
theorem sum_other_colors (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r) (A : Finset V) :
    ∑ k ∈ univ.erase j, ((targetGraph color k).induce (A:Set V)).edgeFinset.card =
      ((targetGraph color j)ᶜ.induce (A:Set V)).edgeFinset.card := by
  let F := fun k ↦ ((targetGraph color k).induce (A:Set V)).edgeFinset
  let other := ((targetGraph color j)ᶜ.induce (A:Set V)).edgeFinset
  have member (k : Fin r) (u v : A) : s(u,v) ∈ F k ↔ (targetGraph color k).Adj u v :=
    SimpleGraph.mem_edgeFinset
  have hm (u v : A) : s(u,v) ∈ other ↔ (targetGraph color j)ᶜ.Adj u v :=
    SimpleGraph.mem_edgeFinset
  have dis : ((univ.erase j:Finset (Fin r)):Set (Fin r)).PairwiseDisjoint F := by
    intro k _ l _ ne
    apply disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro hk hl
      obtain ⟨_,he⟩ := (member k u v).mp hk
      obtain ⟨_,he'⟩ := (member l u v).mp hl
      exact ne (he.symm.trans he')
  have cover : (univ.erase j).biUnion F = other := by
    apply Finset.ext
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [mem_biUnion, hm, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨k,hk,he⟩
        obtain ⟨ne,lab⟩ := (member k u v).mp he
        refine ⟨ne, ?_⟩
        rintro ⟨_,lab'⟩
        exact (mem_erase.mp hk).1 (lab.symm.trans lab')
      · rintro ⟨ne,hn⟩
        let k := color ⟨s((u:V),(v:V)),fun d ↦ ne (Sym2.mk_isDiag_iff.mp d)⟩
        have adj : (targetGraph color k).Adj u v := ⟨ne,rfl⟩
        have diff : k ≠ j := fun h ↦ hn (h ▸ adj)
        exact ⟨k,mem_erase.mpr ⟨diff,mem_univ _⟩,(member k u v).mpr adj⟩
  exact (card_biUnion dis).symm.trans (congrArg Finset.card cover)

/-- A row with s vertices needs at least (r-1)(s-r) nontarget edges, by
applying the independence cap separately to each of the other colors. -/
theorem other_color_floor (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (A : Finset V) (hr : 2 ≤ r) (no : ¬Witness color) :
    (r-1)*(A.card-r) ≤ ((targetGraph color j)ᶜ.induce (A:Set V)).edgeFinset.card := by
  have each (k : Fin r) :
      A.card-r ≤ ((targetGraph color k).induce (A:Set V)).edgeFinset.card := by
    have lower := edge_lower_of_independence ((targetGraph color k).induce (A:Set V)) r
      (induced_cap _ A r (caps_of_no_witness color k hr no).1)
    apply Nat.sub_le_iff_le_add'.mpr
    convert lower using 2
    · simp
    · congr 4
  calc _ = ∑ _k ∈ univ.erase j, (A.card-r) := by simp [Finset.card_erase_of_mem]
       _ ≤ _ := Finset.sum_le_sum fun k _ ↦ each k
       _ = _ := sum_other_colors color j A

end
end Erdos617.ColoredLists
