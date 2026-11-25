import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Degree pruning on the auxiliary graph for Appendix A §4. -/

namespace Erdos617.AuxiliaryPeeling

open Finset
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-- Unordered original edges whose two endpoints are still present. -/
private def inside (A : Finset V) := H.edgeFinset.filter fun e ↦ e.toFinset ⊆ A

private theorem erase_cost (A : Finset V) {x : V} (hx : x ∈ A) :
    (inside H (A.erase x)).card+(A.filter (H.Adj x)).card ≤ (inside H A).card := by
  let star := (A.filter (H.Adj x)).map (Sym2.mkEmbedding x)
  have ends {y : V} : s(x,y).toFinset ⊆ A ↔ x ∈ A ∧ y ∈ A := by simp [Sym2.toFinset_mk_eq,Finset.insert_subset_iff]
  have sub : inside H (A.erase x) ∪ star ⊆ inside H A := by
    intro e he
    rcases mem_union.mp he with hold | hfresh
    · obtain ⟨edge,sub⟩ := mem_filter.mp hold
      exact mem_filter.mpr ⟨edge,sub.trans (erase_subset ..)⟩
    · obtain ⟨y,hy,rfl⟩ := mem_map.mp hfresh
      obtain ⟨hyA,adj⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj,ends.mpr ⟨hx,hyA⟩⟩
  have dis : Disjoint (inside H (A.erase x)) star := by
    apply disjoint_left.mpr
    intro e hkeep hstar
    obtain ⟨y,_,rfl⟩ := mem_map.mp hstar
    have mem : x ∈ s(x,y).toFinset := by simp
    exact notMem_erase x A ((mem_filter.mp hkeep).2 mem)
  have count := card_le_card sub
  simpa only [card_union_of_disjoint dis,star,card_map] using count

private theorem peel (q : ℝ) (start : Finset V) :
    ∃ A ⊆ start, (∀ x ∈ A, ((A.filter (H.Adj x)).card:ℝ) ≤ q) ∧
      ((inside H A).card:ℝ) + q*((start.card:ℝ)-A.card) ≤ (inside H start).card := by
  induction start using Finset.strongInductionOn with
  | _ A ih =>
    by_cases high : ∃ x ∈ A, q < ((A.filter (H.Adj x)).card:ℝ)
    · obtain ⟨x,hx,degree⟩ := high
      obtain ⟨B,sub,stop,paid⟩ := ih (A.erase x) (erase_ssubset hx)
      have fresh : ((inside H (A.erase x)).card:ℝ)+((A.filter (H.Adj x)).card:ℝ) ≤
          (inside H A).card := by exact_mod_cast erase_cost H A hx
      have oneLess : ((A.erase x).card:ℝ)+1 = (A.card:ℝ) := by
        exact_mod_cast card_erase_add_one hx
      refine ⟨B,sub.trans (erase_subset ..),stop,?_⟩
      nlinarith only [fresh,degree,paid,congrArg (fun n : ℝ ↦ q*n) oneLess]
    · exact ⟨A,Subset.rfl,fun x hx ↦ le_of_not_gt (fun h ↦ high ⟨x,hx,h⟩),by simp⟩

/-- Prune any vertex exceeding q current neighbors. Every removal pays
its quota with original edges still present at that step. -/
theorem exists_live (q : ℝ) :
    ∃ A : Finset V, (∀ x ∈ A, ((A.filter (H.Adj x)).card:ℝ) ≤ q) ∧
      ((H.induce (A:Set V)).edgeFinset.card:ℝ) + q*((Fintype.card V:ℝ)-(A.card:ℝ)) ≤
      (H.edgeFinset.card:ℝ) := by
  obtain ⟨A,_,stop,paid⟩ := peel H q univ
  refine ⟨A,stop,?_⟩
  unfold inside at paid
  rw [H.card_filter_edgeFinset_toFinset_subset A] at paid
  simpa using paid

end
end Erdos617.AuxiliaryPeeling
