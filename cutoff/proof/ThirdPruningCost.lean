import ThirdPruningTrace

/-! The new pass spends the residual budget of the original colored edges.
Each edge between old deletions is charged to at most one earlier endpoint. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap ColoredLists
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private def fresh (x : V) : Finset V :=
  univ.filter fun y ↦ T.crossGraph.Adj x y ∧ T.time x < T.time y

private theorem old_quota (legal : T.Legal) {A : Finset V} (sub : A ⊆ live T) :
    edges T.crossGraph (live T) +
      (∑ x ∈ univ \ live T, (T.quota x + max (deg T.crossGraph A x-(199/400:ℝ)*r) 0)) ≤
        T.crossGraph.edgeFinset.card := by
  let D := univ \ live T
  let S := fun x ↦ (fresh T x).map (Sym2.mkEmbedding x)
  let I := T.crossGraph.edgeFinset.filter fun e ↦ e.toFinset ⊆ live T
  have source (x : V) (hx : x ∈ D) : T.time x < T.stop := by
    simpa [D,live] using hx
  have active (x : V) (hx : x ∈ D) :
      T.quota x + max (deg T.crossGraph A x-(199/400:ℝ)*r) 0 ≤ ((S x).card : ℝ) := by
    change _ ≤ (((fresh T x).map _).card : ℝ)
    rw [card_map,add_max]; apply max_le
    · have current : deg T.crossGraph A x ≤ ((fresh T x).card : ℝ) := by
        apply Nat.cast_le.mpr; apply card_le_card
        intro y hy
        obtain ⟨ha,adj⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨mem_univ _,adj,(source x hx).trans_le (mem_filter.mp (sub ha)).2⟩
      have rate : T.quota x ≤ (199/400:ℝ)*r := by
        unfold Trace.quota; split_ifs <;> linarith [Nat.cast_nonneg (α:=ℝ) r]
      linarith
    · have incl : T.star x ⊆ fresh T x := by
        intro y hy
        obtain ⟨_,adj,_,later,_⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨mem_univ _,adj,later⟩
      simpa using (legal.degree x (source x hx)).le.trans (Nat.cast_le.mpr (card_le_card incl))
  have unique : (D : Set V).PairwiseDisjoint S := by
    intro x hx y hy ne
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨u,hu,eu⟩ := mem_map.mp he
    obtain ⟨v,hv,ev⟩ := mem_map.mp hf
    have same : s(x,u) = s(y,v) := eu.trans ev.symm
    rcases Sym2.eq_iff.mp same with h | ⟨rfl,rfl⟩
    · exact ne h.1
    · exact asymm (mem_filter.mp hu).2.2 (mem_filter.mp hv).2.2
  have dis : Disjoint I (D.biUnion S) := by
    apply disjoint_left.mpr
    intro e hi he
    obtain ⟨x,hx,h⟩ := mem_biUnion.mp he
    obtain ⟨y,_,rfl⟩ := mem_map.mp h
    exact (mem_sdiff.mp hx).2 ((mem_filter.mp hi).2 (show x ∈ s(x,y).toFinset by simp))
  have cover : I ∪ D.biUnion S ⊆ T.crossGraph.edgeFinset := by
    intro e he
    rcases mem_union.mp he with h|h
    · exact (mem_filter.mp h).1
    · obtain ⟨x,_,hs⟩ := mem_biUnion.mp h
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hs
      exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hy).2.1
  have count := card_le_card cover
  rw [card_union_of_disjoint dis,card_biUnion unique] at count
  have inside : I.card = (T.crossGraph.induce (live T : Set V)).edgeFinset.card :=
    T.crossGraph.card_filter_edgeFinset_toFinset_subset _
  rw [inside] at count
  have paid := sum_le_sum active
  have total : edges T.crossGraph (live T) + (∑ x ∈ D, ((S x).card:ℝ)) ≤ T.crossGraph.edgeFinset.card := by unfold edges; exact_mod_cast count
  exact (add_le_add_right paid _).trans total

private theorem quota_sum : (∑ x ∈ univ \ live T, T.quota x) =
    (r:ℝ)/4*T.firstSources.card + ((199/400:ℝ)*r)*T.secondSources.card := by
  have reduced (x : V) : (if x ∈ univ \ live T then T.quota x else 0) =
      (if x ∈ T.firstSources then (r:ℝ)/4 else 0) +
      (if x ∈ T.secondSources then (199/400:ℝ)*r else 0) := by
    have stages := T.stages
    by_cases h : T.time x < T.firstEnd
    · simp [live,Trace.quota,Trace.firstSources,Trace.secondSources,h,h.trans_le stages,not_le.mpr h]
    · by_cases hs : T.time x < T.stop <;>
        simp [live,Trace.quota,Trace.firstSources,Trace.secondSources,h,hs,le_of_not_gt h]
  have indicator : (∑ x, if x ∈ univ \ live T then T.quota x else 0) = ∑ x ∈ univ \ live T, T.quota x := by
    rw [sum_ite_mem,univ_inter]
  rw [← indicator]
  have h := sum_congr (s₁:=univ) rfl (fun x _ ↦ reduced x)
  simpa [sum_add_distrib,mul_comm] using h

/-- One final set records its stopping rule, the cost of all three stages and
the entire surplus available to charge missing internal edges. -/
theorem three_pass_cost (legal : T.Legal) :
    ∃ A ⊆ live T, (∀ x ∈ A, deg T.crossGraph A x ≤ (9/25:ℝ)*r) ∧
      (∀ x ∈ live T \ A, (9/25:ℝ)*r ≤ deg T.crossGraph (live T) x) ∧
      edges T.crossGraph A + (r:ℝ)/4*T.firstSources.card +
      ((199/400:ℝ)*r)*T.secondSources.card + ((9/25:ℝ)*r)*(live T \ A).card +
      (∑ x ∈ univ \ A, max (deg T.crossGraph A x-(199/400:ℝ)*r) 0) ≤ T.crossGraph.edgeFinset.card := by
  obtain ⟨A,sub,stopped,removed,paid⟩ := peel_from T.crossGraph (live T)
    (show (9/25:ℝ)*r ≤ (199/400:ℝ)*r by linarith [Nat.cast_nonneg (α:=ℝ) r])
  refine ⟨A,sub,stopped,removed,?_⟩
  have split : univ \ A = (univ \ live T) ∪ (live T \ A) := by
    ext x
    by_cases h : x ∈ live T <;> simp [h] <;> grind
  have dis : Disjoint (univ \ live T) (live T \ A) := disjoint_left.mpr
    fun x hx hy ↦ (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  have old := old_quota T legal sub
  rw [split,sum_union dis]
  rw [sum_add_distrib,quota_sum] at old
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at paid
  linarith only [paid,old]

end
end Erdos617.ThirdPruning
