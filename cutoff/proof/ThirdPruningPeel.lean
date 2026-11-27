import AuxiliaryPeeling
import RawEdgeIdentity

/-! A pruning pass on an arbitrary surviving set, keeping the part of each
deleted degree facing the final survivors in excess of its quota. -/
namespace Erdos617.ThirdPruning
open Finset
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def edges (A : Finset V) : ℝ := ((G.induce (A : Set V)).edgeFinset.card:ℝ)
def deg (A : Finset V) (x : V) : ℝ := ((A.filter (G.Adj x)).card:ℝ)

theorem deg_mono {A B : Finset V} (sub : A ⊆ B) (x : V) : deg G A x ≤ deg G B x := by
  unfold deg
  exact_mod_cast card_le_card (filter_subset_filter (G.Adj x) sub)

theorem sum_deg (A : Finset V) : ∑ x ∈ A, deg G A x = 2*edges G A := by
  rw [show edges G A = ((G.induce (A : Set V)).edgeFinset.card : ℝ) from rfl,
    ← Erdos617.ColoredLists.internal_end_sum G A]
  apply sum_congr rfl
  intro x hx
  simp [deg]

theorem erase_edges (A : Finset V) {x : V} (hx : x ∈ A) :
    edges G (A.erase x) + deg G A x ≤ edges G A := by
  let inside := fun (S : Finset V) ↦ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S
  have eq (S : Finset V) : ((inside S).card:ℝ) = edges G S := by
    unfold inside edges
    rw [G.card_filter_edgeFinset_toFinset_subset S]
  rw [← eq,← eq]
  let star := (A.filter (G.Adj x)).map (Sym2.mkEmbedding x)
  have ends {y : V} : s(x,y).toFinset ⊆ A ↔ x ∈ A ∧ y ∈ A := by simp [Sym2.toFinset_mk_eq,Finset.insert_subset_iff]
  have sub : inside (A.erase x) ∪ star ⊆ inside A := by
    intro e he
    rcases mem_union.mp he with hi | hs
    · obtain ⟨ed,sub⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨ed,sub.trans (erase_subset ..)⟩
    · obtain ⟨y,hy,rfl⟩ := mem_map.mp hs
      obtain ⟨ha,adj⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj,ends.mpr ⟨hx,ha⟩⟩
  have dis : Disjoint (inside (A.erase x)) star := by
    apply disjoint_left.mpr
    intro e hi hs
    obtain ⟨y,_,rfl⟩ := mem_map.mp hs
    exact notMem_erase x A ((mem_filter.mp hi).2 (show x ∈ s(x,y).toFinset by simp))
  have nat := card_le_card sub
  rw [card_union_of_disjoint dis,card_map] at nat
  unfold deg
  exact_mod_cast nat

/-- For a quota q the comparison cap a may be larger. The surplus is counted
against the degree into the final set, one term for each removed vertex. -/
theorem peel_from (start : Finset V) {q a : ℝ} (qa : q ≤ a) :
    ∃ A ⊆ start, (∀ x ∈ A, deg G A x ≤ q) ∧
      (∀ x ∈ start \ A, q ≤ deg G start x) ∧
      edges G A + ∑ x ∈ start \ A, (q + max (deg G A x - a) 0) ≤ edges G start := by
  induction start using Finset.strongInductionOn with
  | _ S ih =>
    by_cases high : ∃ x ∈ S, q < deg G S x
    · obtain ⟨x,hx,hdeg⟩ := high
      obtain ⟨A,sub,stop,removed,cost⟩ := ih (S.erase x) (erase_ssubset hx)
      have inside := sub.trans (erase_subset x S)
      have ex : x ∉ A := fun h ↦ notMem_erase x S (sub h)
      have rem : S \ A = insert x (S.erase x \ A) := by
        ext v
        by_cases h : v = x <;> simp [h,hx,ex]
      have one : q + max (deg G A x-a) 0 ≤ deg G S x := by
        rw [add_max]
        apply max_le <;> linarith only [hdeg,qa,deg_mono G inside x]
      refine ⟨A,inside,stop,?_,?_⟩
      · intro y hy
        by_cases eq : y = x
        · exact eq ▸ hdeg.le
        · exact (removed y (mem_sdiff.mpr ⟨mem_erase.mpr ⟨eq,(mem_sdiff.mp hy).1⟩,
            (mem_sdiff.mp hy).2⟩)).trans (deg_mono G (erase_subset x S) y)
      rw [rem,sum_insert (by simp)]
      linarith only [one,cost,erase_edges G S hx]
    · exact ⟨S,Subset.rfl,fun x hx ↦ le_of_not_gt (fun h ↦ high ⟨x,hx,h⟩),by simp,by simp⟩

end
end Erdos617.ThirdPruning
