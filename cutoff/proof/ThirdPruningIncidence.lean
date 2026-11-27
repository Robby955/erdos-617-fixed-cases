import ThirdPruningCost

/-! Unrecorded incidences left on the actual surviving vertices. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap PruningOverlap.Trace ColoredLists PackingLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

theorem ordinary_total (K : Finset V) :
    countEnds (T.ordinary K) = ∑ x ∈ K, unrecordedDegree T x := by
  have per (x : V) : (∑ y, if T.ordinary K x y then (1:ℝ) else 0) =
      if x ∈ K then unrecordedDegree T x else 0 := by
    by_cases h : x ∈ K <;> simp [Trace.ordinary,h,unrecordedDegree]
  simp [countEnds,total,per]

theorem final_incidences (A K : Finset V) (sub : K ⊆ A) (legal : T.Legal) :
    (∑ x ∈ K, unrecordedDegree T x) + (r:ℝ)/4*T.firstSources.card ≤
      (T.crossGraph.edgeFinset.card:ℝ) + edges T.crossGraph A := by
  let o := fun x y ↦ if T.ordinary K x y then (1:ℝ) else 0
  let f := fun x y ↦ if x ∈ T.firstSources ∧ y ∈ T.star x then (1:ℝ) else 0
  let a := fun x y ↦ if T.crossGraph.Adj x y then (1:ℝ) else 0
  let b := fun x y ↦ if x ∈ A then (if y ∈ A then a x y else 0) else 0
  have entry (x y : V) : o x y + o y x + f x y + f y x ≤ a x y + b x y := by
    by_cases adj : T.crossGraph.Adj x y
    · have reverse := adj.symm
      have flip : T.recorded x y ↔ T.recorded y x := or_comm
      by_cases xy : x ∈ T.firstSources ∧ y ∈ T.star x
      · have yx : ¬(y ∈ T.firstSources ∧ x ∈ T.star y) := fun h ↦
          asymm (mem_filter.mp xy.2).2.2.2.1 (mem_filter.mp h.2).2.2.2.1
        have hit : T.recorded x y := Or.inl ⟨(mem_filter.mp xy.1).2,xy.2⟩
        simp [o,f,a,b,Trace.ordinary,xy,yx,adj,reverse,hit,flip.mp hit]; split_ifs <;> norm_num
      · by_cases yx : y ∈ T.firstSources ∧ x ∈ T.star y
        · have hit : T.recorded x y := Or.inr ⟨(mem_filter.mp yx.1).2,yx.2⟩
          simp [o,f,a,b,Trace.ordinary,xy,yx,adj,reverse,hit,flip.mp hit]; split_ifs <;> norm_num
        · by_cases kx : x ∈ K <;> by_cases ky : y ∈ K <;>
            simp_all [o,f,a,b,Trace.ordinary] <;> split_ifs <;> grind
    · have rev : ¬T.crossGraph.Adj y x := fun h ↦ adj h.symm
      have nx : y ∉ T.star x := fun h ↦ adj (mem_filter.mp h).2.1
      have ny : x ∉ T.star y := fun h ↦ rev (mem_filter.mp h).2.1
      simp [o,f,a,b,Trace.ordinary,adj,rev,nx,ny]
  have cost : (r:ℝ)/4*T.firstSources.card ≤ ∑ x, ∑ y, f x y := by
    have per (x : V) : (if x ∈ T.firstSources then (r:ℝ)/4 else 0) ≤ ∑ y, f x y := by
      by_cases h : x ∈ T.firstSources
      · have first := (mem_filter.mp h).2
        have q := (legal.degree x (first.trans_le T.stages)).le
        simpa [f,h,Trace.quota,first] using q
      · simp [f,h]
    simpa [mul_comm] using sum_le_sum (s:=univ) (fun x _ ↦ per x)
  have ao : (∑ x, ∑ y, o x y) = ∑ x ∈ K, unrecordedDegree T x := ordinary_total T K
  have ab : (∑ x, ∑ y, b x y) = 2*edges T.crossGraph A := by
    convert internal_end_sum T.crossGraph A using 1
    · simp [b,a,ite_sum_zero]
    · rfl
  have aa : (∑ x, ∑ y, a x y) = 2*(T.crossGraph.edgeFinset.card:ℝ) := by
    have per (x : V) : (∑ y, a x y) = T.crossGraph.degree x := by
      simp [a,← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp_rw [per]
    exact_mod_cast T.crossGraph.sum_degrees_eq_twice_card_edges
  have h := sum_le_sum (s:=univ) fun x _ ↦ sum_le_sum (s:=univ) fun y _ ↦ entry x y
  simp only [sum_add_distrib] at h
  rw [sum_comm (f:=fun x y ↦ o y x),sum_comm (f:=fun x y ↦ f y x),ao,aa,ab] at h
  linarith only [h,cost]

end
end Erdos617.ThirdPruning
