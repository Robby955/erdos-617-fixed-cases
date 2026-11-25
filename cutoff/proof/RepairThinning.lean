import PairThinning
import ColoringSignedCut
import ColoringRepairCost

/-! The decision to add one unordered repair edge reads exactly its two
sender coordinates, once the auxiliary circle starts are fixed. -/

namespace Erdos617.ColoredLists

open Finset FiniteLaw MarkedSender PruningOverlap RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} {r : ℕ} [Fintype V]

omit [Fintype V] in
private theorem agree_endpoints {x y a b : V} {w v : V → State V}
    (hx : w x = v x) (hy : w y = v y) (eq : s(a,b) = s(x,y)) :
    w a = v a ∧ w b = v b := by
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

omit [Fintype V] in
private theorem same_row_transfer (G : SimpleGraph V) (C U O L : Finset V)
    {x y : V} {w v : V → State V} (hx : w x = v x) (hy : w y = v y)
    (h : s(x,y) ∈ SameRowConflicts.edges G C U O L w) :
    s(x,y) ∈ SameRowConflicts.edges G C U O L v := by
  rcases mem_union.mp h with both|hit
  · obtain ⟨⟨a,b⟩,hp,eq⟩ := mem_image.mp both
    obtain ⟨ha,hb,ne⟩ := mem_offDiag.mp hp
    obtain ⟨wa,wb⟩ := agree_endpoints hx hy eq
    exact mem_union_left _ (mem_image.mpr ⟨(a,b),mem_offDiag.mpr
      ⟨mem_filter.mpr ⟨(mem_filter.mp ha).1,wa ▸ (mem_filter.mp ha).2⟩,
       mem_filter.mpr ⟨(mem_filter.mp hb).1,wb ▸ (mem_filter.mp hb).2⟩,ne⟩,eq⟩)
  · obtain ⟨a,ha,edge⟩ := mem_biUnion.mp hit
    apply mem_union_right _
    apply mem_biUnion.mpr
    refine ⟨a,ha,?_⟩
    rcases mem_union.mp edge with fixed|marked
    · obtain ⟨b,hb,eq⟩ := mem_image.mp fixed
      obtain ⟨inL,z,hz,wz,adj⟩ := mem_filter.mp hb
      exact mem_union_left _ (mem_image.mpr ⟨b,mem_filter.mpr
        ⟨inL,z,hz,(agree_endpoints hx hy eq).1.symm.trans wz,adj⟩,eq⟩)
    · obtain ⟨b,hb,eq⟩ := mem_image.mp marked
      obtain ⟨inO,⟨z,hz,wz,adj⟩,mark⟩ := mem_filter.mp hb
      obtain ⟨wa,wb⟩ := agree_endpoints hx hy eq
      exact mem_union_right _ (mem_image.mpr ⟨b,mem_filter.mpr
        ⟨inO,⟨z,hz,wa.symm.trans wz,adj⟩,wb ▸ mark⟩,eq⟩)

omit [Fintype V] in
private theorem rep_transfer (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V)
    {x y : V} {w v : V → State V} (hx : w x = v x) (hy : w y = v y)
    (edge : s(x,y) ∈ edges G I C H U L w) : s(x,y) ∈ edges G I C H U L v := by
  rcases mem_union.mp edge with same|across
  · obtain ⟨i,hi,e⟩ := mem_biUnion.mp same
    exact mem_union_left _ (mem_biUnion.mpr ⟨i,hi,same_row_transfer _ _ _ _ _ hx hy e⟩)
  · obtain ⟨q,hq,e⟩ := mem_biUnion.mp across
    obtain ⟨⟨a,b⟩,hp,eq⟩ := mem_image.mp e
    obtain ⟨inRows,z,hz,t,ht,wz,wt,adj⟩ := mem_filter.mp hp
    obtain ⟨wa,wb⟩ := agree_endpoints hx hy eq
    exact mem_union_right _ (mem_biUnion.mpr ⟨q,hq,mem_image.mpr
      ⟨(a,b),mem_filter.mpr ⟨inRows,z,hz,t,ht,wa.symm.trans wz,wb.symm.trans wt,adj⟩,eq⟩⟩)

variable (T : Trace V r)

/-- This applies to the union itself, including repeated reasons to add the
same edge across different rows or repair mechanisms. -/
theorem sample_pair_local (E : Finset V) (I : Finset ℕ) (s : ℕ) [NeZero (30*s*r)]
    (z : I → V → ZMod (30*s*r)) (x y : V) (w v : V → State V)
    (hx : w x = v x) (hy : w y = v y) :
    s(x,y) ∈ samplePairs T E I s w z ↔ s(x,y) ∈ samplePairs T E I s v z := by
  unfold samplePairs
  rw [mem_union,mem_union,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeFinset]
  apply or_congr
  · exact ⟨rep_transfer _ _ _ _ _ _ hx hy,rep_transfer _ _ _ _ _ _ hx.symm hy.symm⟩
  · change (∃ i ∈ (univ : Finset I), x ≠ y ∧ _) ↔ (∃ i ∈ (univ : Finset I), x ≠ y ∧ _)
    simp only [hx,hy]

private theorem exchange {A B : Type*} [Fintype A] [Fintype B] (μ : Law A) (ν : Law B)
    (f : A → B → ℝ) : μ.expect (fun a ↦ ν.expect (f a)) = ν.expect (fun b ↦ μ.expect (fun a ↦ f a b)) := by
  unfold Law.expect
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-- Increasing the sender thinning rate from p to q≤kp multiplies the
expected number of actual distinct repairs by at most k². All circle starts
and all sender kinds are the same on both sides. -/
theorem oversample_repairs (E : Finset V) (I : Finset ℕ) (s : ℕ) [NeZero (30*s*r)]
    (p q k : ℝ) (rate : 100*((9/40:ℝ)/s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hk : 1 ≤ k) (inc : p ≤ q) (cap : q ≤ k*p) :
    let base := product (senderLaw T E I s p rate hp hp1)
    let enlarged := product (senderLaw T E I s q rate hq hq1)
    let ν := product fun _ : I ↦ ArcRepair.starts V (30*s*r)
    let cost := fun w z ↦ ((samplePairs T E I s w z).card:ℝ)
    enlarged.expect (fun w ↦ ν.expect (cost w)) ≤ k^2 * base.expect (fun w ↦ ν.expect (cost w)) := by
  intro base enlarged ν cost
  rw [exchange enlarged ν cost,exchange base ν cost,← Law.expect_const_mul]
  apply ν.expect_mono
  intro z
  apply expect_pair_set_card_le _ _ hk _ (fun w ↦ samplePairs T E I s w z) (sample_pair_local T E I s z)
  exact fun v o ↦ MarkedSender.oversample_weight _ v _ _ p q k (by positivity) rate hp hp1 hq hq1 hk inc cap o

end
end Erdos617.ColoredLists
