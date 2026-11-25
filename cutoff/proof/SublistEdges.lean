import CountingTransversal
import PackingLists
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Count a row's candidate conflicts among actual cross edges, with both
endpoints restricted to the available vertices. -/

namespace Erdos617.Transversal

open Finset PackingLists
open scoped Classical
noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq I]

private theorem restricted_edge_count (G : SimpleGraph V) (A : Finset V) (row : V → I)
    (i : I) (parts : Finset I) :
    (conflicts G A row i (parts.erase i)).card ≤
      ((cross G row).edgeFinset ∩ A.sym2).card := by
  have ends (p : V × V) (hp : p ∈ conflicts G A row i (parts.erase i)) :
      p.1 ∈ A ∧ p.2 ∈ A ∧ row p.1 = i ∧ row p.2 ≠ i ∧ G.Adj p.1 p.2 := by
    obtain ⟨inProd,edge⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp inProd
    obtain ⟨inA,r₁⟩ := mem_filter.mp hx
    obtain ⟨inB,r₂⟩ := mem_filter.mp hy
    exact ⟨inA,inB,r₁,(mem_erase.mp r₂).1,edge⟩
  apply card_le_card_of_injOn (fun p : V × V ↦ s(p.1,p.2))
  · intro p hp
    obtain ⟨hx,hy,r₁,r₂,adj⟩ := ends p hp
    exact mem_inter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr ⟨fun eq ↦ r₂ (eq.symm.trans r₁),adj⟩,
      mk_mem_sym2_iff.mpr ⟨hx,hy⟩⟩
  · intro p hp q hq eq
    rcases Sym2.mk_eq_mk_iff.mp eq with same | swap
    · exact same
    · have rowp := (ends p hp).2.2.1
      have rowq := (ends q hq).2.2.2.1
      exact (rowq ((congrArg (fun e : V × V ↦ row e.1) swap).symm.trans rowp)).elim

/-- Orient each conflict away from row i. Two such ordered conflicts can
never be opposite orientations of the same unordered edge. -/
theorem conflicts_le_cross_edges (G : SimpleGraph V) (A : Finset V) (row : V → I)
    (i : I) (parts : Finset I) :
    (conflicts G A row i (parts.erase i)).card ≤ (cross G row).edgeFinset.card :=
  (restricted_edge_count G A row i parts).trans (card_le_card inter_subset_left)

/-- Both endpoints of every list conflict belong to A. Thus even the edges
with an endpoint outside A can be removed from the upper bound. -/
theorem conflicts_le_induced_cross_edges (G : SimpleGraph V) (A : Finset V) (row : V → I)
    (i : I) (parts : Finset I) :
    (conflicts G A row i (parts.erase i)).card ≤
      ((cross G row).induce (A:Set V)).edgeFinset.card := by
  have eq := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := cross G row) (s := (A:Set V)))
  simp only [card_map,Finset.toFinset_coe] at eq
  apply (restricted_edge_count G A row i parts).trans
  convert eq.symm.le using 2
  congr 4
  exact Subsingleton.elim _ _

end
end Erdos617.Transversal
