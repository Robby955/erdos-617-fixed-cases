import PackingLists
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Independent representatives when the product of every pair of list sizes
exceeds the number of surviving cross edges. -/

namespace Erdos617.Transversal

open Finset PackingLists
open scoped Classical
noncomputable section

private theorem two_fixed_choices {J V : Type*} [Fintype J] [DecidableEq J] [DecidableEq V]
    (lists : J → Finset V) (i j : J) (ne : i ≠ j) (x y : V)
    (B : Finset (J → V)) (pool : B ⊆ Fintype.piFinset lists)
    (fixed : ∀ f ∈ B, f i = x ∧ f j = y) :
    B.card * ((lists i).card * (lists j).card) ≤ (Fintype.piFinset lists).card := by
  let pinned (k : J) : Finset V := if k = i then {x} else if k = j then {y} else lists k
  have subset : B ⊆ Fintype.piFinset pinned := by
    intro f hf
    apply Fintype.mem_piFinset.mpr
    intro k
    by_cases hi : k = i
    · simpa [pinned,hi] using (fixed f hf).1
    by_cases hj : k = j
    · simpa [pinned,hi,hj,ne.symm] using (fixed f hf).2
    simpa [pinned,hi,hj] using Fintype.mem_piFinset.mp (pool hf) k
  apply (Nat.mul_le_mul_right _ (card_le_card subset)).trans
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  let others := (univ.erase i).erase j
  have jmem : j ∈ univ.erase i := mem_erase.mpr ⟨ne.symm,mem_univ j⟩
  have same : (∏ k ∈ others, (pinned k).card) = ∏ k ∈ others, (lists k).card := by
    apply prod_congr rfl
    intro k hk
    simp only [others,mem_erase] at hk
    simp [pinned,hk.1,hk.2.1]
  rw [← mul_prod_erase univ (fun k ↦ (pinned k).card) (mem_univ i),
    ← mul_prod_erase _ (fun k ↦ (pinned k).card) jmem,
    ← mul_prod_erase univ (fun k ↦ (lists k).card) (mem_univ i),
    ← mul_prod_erase _ (fun k ↦ (lists k).card) jmem]
  change (pinned i).card * ((pinned j).card * (∏ k ∈ others, (pinned k).card)) * _ ≤ _
  rw [same]
  simp only [pinned,ite_true,eq_self,ite_false,card_singleton,one_mul,ne.symm]
  exact le_of_eq (by ac_rfl)

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

/-- Pick one target-independent vertex per selected row. A cross edge forbids
at most the fraction reciprocal to its two list sizes. Counting once per
unordered edge allows use of the residual edge count on A. -/
theorem exists_of_edge_products (G : SimpleGraph V) (A L : Finset V) (row : V → I)
    (parts : Finset I) (sub : L ⊆ A)
    (nonempty : ∀ i ∈ parts, (L.filter (fun v ↦ row v = i)).Nonempty)
    (products : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j →
      ((cross G row).induce (A:Set V)).edgeFinset.card <
        (L.filter (fun v ↦ row v = i)).card * (L.filter (fun v ↦ row v = j)).card) :
    ∃ R ⊆ L, Partial G row R ∧ R.image row = parts := by
  let lists (i : parts) := L.filter fun v ↦ row v = i.1
  let pool := Fintype.piFinset lists
  let E := (cross G row).edgeFinset ∩ A.sym2
  have count : E.card = ((cross G row).induce (A:Set V)).edgeFinset.card := by
    have eq := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := cross G row) (s := (A:Set V)))
    simp only [card_map,Finset.toFinset_coe] at eq
    convert eq.symm using 2
    congr 4
    exact Subsingleton.elim _ _
  have positive : 0 < pool.card := card_pos.mpr
    (Fintype.piFinset_nonempty.mpr fun i ↦ nonempty i.1 i.2)
  let selected (f : parts → V) := univ.image f
  have tagged {f} (hf : f ∈ pool) (i : parts) : f i ∈ L ∧ row (f i) = i.1 :=
    mem_filter.mp (Fintype.mem_piFinset.mp hf i)
  let bad (e : Sym2 V) := pool.filter (fun f ↦ ∀ v ∈ e, v ∈ selected f)
  have cost (e) (he : e ∈ E) : (bad e).card * E.card < pool.card := by
    induction e using Sym2.inductionOn with | hf x y
    by_cases has : (bad s(x,y)).Nonempty
    · obtain ⟨f,hf⟩ := has
      obtain ⟨hf,hit⟩ := mem_filter.mp hf
      obtain ⟨i,_,hx⟩ := mem_image.mp (hit x (Sym2.mem_mk_left x y))
      obtain ⟨j,_,hy⟩ := mem_image.mp (hit y (Sym2.mem_mk_right x y))
      have xi : row x = i.1 := hx ▸ (tagged hf i).2
      have yj : row y = j.1 := hy ▸ (tagged hf j).2
      have different : row x ≠ row y := (SimpleGraph.mem_edgeFinset.mp (mem_inter.mp he).1).1
      have ne : i ≠ j := fun eq ↦ different (xi.trans ((congrArg Subtype.val eq).trans yj.symm))
      have unique {g} (hg : g ∈ pool) (k : parts) (v : V) (hv : v ∈ selected g)
          (hrow : row v = k.1) : g k = v := by
        obtain ⟨m,_,hm⟩ := mem_image.mp hv
        have same : m = k := Subtype.ext ((tagged hg m).2.symm.trans (hm ▸ hrow))
        exact same ▸ hm
      have bound := two_fixed_choices lists i j ne x y (bad s(x,y)) (filter_subset ..) (by
        intro g hg
        obtain ⟨hg,both⟩ := mem_filter.mp hg
        exact ⟨unique hg i x (both x (Sym2.mem_mk_left x y)) xi,
          unique hg j y (both y (Sym2.mem_mk_right x y)) yj⟩)
      have product : E.card < (lists i).card * (lists j).card := count ▸ products i.1 i.2 j.1 j.2 (fun h ↦ ne (Subtype.ext h))
      exact (Nat.mul_lt_mul_of_pos_left product (card_pos.mpr ⟨f,mem_filter.mpr ⟨hf,hit⟩⟩)).trans_le bound
    · simpa [Finset.not_nonempty_iff_eq_empty.mp has] using positive
  by_contra! none
  have cover : pool ⊆ E.biUnion bad := by
    intro f hf
    have included : selected f ⊆ L := by
      intro v hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact (tagged hf i).1
    have distinct : Set.InjOn row (selected f : Set V) := by
      intro x hx y hy eq
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      exact congrArg f (Subtype.ext ((tagged hf i).2.symm.trans (eq.trans (tagged hf j).2)))
    have full : (selected f).image row = parts := by
      ext i
      constructor
      · rintro hi
        obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
        obtain ⟨k,_,rfl⟩ := mem_image.mp hv
        exact (tagged hf k).2 ▸ k.2
      · intro hi
        let k : parts := ⟨i,hi⟩
        exact mem_image.mpr ⟨f k,mem_image_of_mem _ (mem_univ k),(tagged hf k).2⟩
    have failure : ¬G.IsIndepSet (selected f:Set V) := fun h ↦ none _ included ⟨h,distinct⟩ full
    change ¬(∀ ⦃x⦄, x ∈ selected f → ∀ ⦃y⦄, y ∈ selected f → x ≠ y → ¬G.Adj x y) at failure
    push Not at failure
    obtain ⟨x,hx,y,hy,hne,adj⟩ := failure
    apply mem_biUnion.mpr
    refine ⟨s(x,y),mem_inter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
      ⟨fun eq ↦ hne (distinct hx hy eq),adj⟩,mk_mem_sym2_iff.mpr ⟨sub (included hx),sub (included hy)⟩⟩,
      mem_filter.mpr ⟨hf,?_⟩⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy
  have total := (card_le_card cover).trans (card_biUnion_le (s := E) (t := bad))
  have present : E.Nonempty := by
    by_contra h
    have zero : pool.card ≤ 0 := by simpa only [not_nonempty_iff_eq_empty.mp h,sum_empty] using total
    exact (not_lt_of_ge zero) positive
  have strict := sum_lt_sum_of_nonempty present cost
  rw [← sum_mul] at strict
  simp only [sum_const,nsmul_eq_mul] at strict
  exact (not_lt_of_ge (Nat.mul_le_mul_right E.card total)) (by simpa [Nat.mul_comm] using strict)

end
end Erdos617.Transversal
