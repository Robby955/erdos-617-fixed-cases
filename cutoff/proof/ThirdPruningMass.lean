import ThirdPruningRowHoles

/-! Account for each nontarget edge internal to a raw row using its two
endpoints. An edge with two survivors is impossible in the clique case. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap ColoredLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

private def arcs (G : SimpleGraph V) (B C : Finset V) : ℝ :=
  ∑ x ∈ B, ∑ y ∈ C, if G.Adj x y then (1:ℝ) else 0

private theorem arcs_swap (G : SimpleGraph V) (B C : Finset V) :
    arcs G B C = arcs G C B := by
  unfold arcs
  rw [sum_comm]
  exact sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ by rw [G.adj_comm]

theorem missing_mass (A : Finset V) (rows : ∀ x, T.row x < r)
    (cliques : ∀ i < r, (targetGraph T.color T.target).IsClique
       ((A.filter fun v ↦ T.row v = i) : Set V)) :
    (∑ i ∈ range r, (internalMissing T i:ℝ)) ≤
      ((holes (targetGraph T.color T.target) T.row A).card:ℝ) +
       (∑ i ∈ range r, ((((univ \ A).filter fun v ↦ T.row v=i).card:ℝ)^2))/2 := by
  let G := targetGraph T.color T.target
  let R := fun i ↦ univ.filter fun v ↦ T.row v=i
  let C := fun i ↦ A.filter fun v ↦ T.row v=i
  let D := fun i ↦ (univ \ A).filter fun v ↦ T.row v=i
  let crossH := fun x ↦ ∑ y ∈ A, if T.row x=T.row y ∧ Gᶜ.Adj x y then (1:ℝ) else 0
  have mixed (i : ℕ) : arcs Gᶜ (D i) (C i) = ∑ x ∈ D i, crossH x := by
    apply sum_congr rfl
    intro x hx
    have lab := (mem_filter.mp hx).2
    simp only [C,sum_filter,crossH]
    apply sum_congr rfl; intro y _
    by_cases h : T.row y=i
    · simp [lab,h]
    · simp [lab,h,Ne.symm h]
  have global : (∑ i ∈ range r, arcs Gᶜ (D i) (C i)) = ((holes G T.row A).card:ℝ) := by
    simp_rw [mixed]
    rw [holes,natCast_card_filter,sum_product]
    exact sum_fiberwise_of_maps_to (fun x _ ↦ mem_range.mpr (rows x)) crossH
  have per (i : ℕ) (hi : i ∈ range r) :
      2*(internalMissing T i:ℝ) ≤ ((D i).card:ℝ)^2 + 2*arcs Gᶜ (D i) (C i) := by
    have partition : R i = D i ∪ C i := by ext x; by_cases h : x ∈ A <;> simp [R,D,C,h]
    have dis : Disjoint (D i) (C i) := disjoint_left.mpr fun x hd hc ↦
      (mem_sdiff.mp (mem_filter.mp hd).1).2 (mem_filter.mp hc).1
    have parts : arcs Gᶜ (R i) (R i) =
        arcs Gᶜ (D i) (D i) + arcs Gᶜ (C i) (C i) + 2*arcs Gᶜ (D i) (C i) := by
      rw [partition]
      have eq : arcs Gᶜ (D i ∪ C i) (D i ∪ C i) =
          arcs Gᶜ (D i) (D i)+arcs Gᶜ (D i) (C i)+
          (arcs Gᶜ (C i) (D i)+arcs Gᶜ (C i) (C i)) := by
        simp [arcs,sum_union dis,sum_add_distrib]
      rw [eq,arcs_swap Gᶜ (C i) (D i)]
      ring
    have zero : arcs Gᶜ (C i) (C i) = 0 := by
      apply sum_eq_zero
      intro x hx
      apply sum_eq_zero
      intro y hy
      have absent : ¬ Gᶜ.Adj x y := fun h ↦
        ((SimpleGraph.compl_adj ..).mp h).2 (cliques i (mem_range.mp hi) hx hy ((SimpleGraph.compl_adj ..).mp h).1)
      simp [absent]
    have upper : arcs Gᶜ (D i) (D i) ≤ ((D i).card:ℝ)^2 := calc
      _ ≤ ∑ _ ∈ D i, ∑ _ ∈ D i, (1:ℝ) :=
        sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ by split <;> norm_num
      _ = _ := by simp [sq]
    have ends : arcs Gᶜ (R i) (R i) = 2*(internalMissing T i:ℝ) := by
      convert internal_end_sum Gᶜ (R i) using 2
      · rfl
      · dsimp only [G,R,internalMissing]
        congr 4
        exact Subsingleton.elim _ _
    linarith only [parts,upper,zero,ends]
  have all := sum_le_sum per
  rw [sum_add_distrib,← mul_sum,← mul_sum,global] at all
  linarith only [all]

/-- Young's inequality in the exact form used by every rational cell. -/
theorem deleted_second_moment {ι : Type*} (I : Finset ι) (a b : ι → ℝ) {d s : ℝ}
    (a0 : ∀ i ∈ I, 0 ≤ a i) (cap : ∀ i ∈ I, a i ≤ d + b i)
    (variance : (∑ i ∈ I, (b i)^2) ≤ s) {u : ℝ} (hu : 0 < u) :
    (1-u)*(∑ i ∈ I, (a i)^2) ≤ d*(∑ i ∈ I, a i)+s/(4*u) := by
  have per (i) (hi : i ∈ I) : (1-u)*(a i)^2 ≤ d*a i + (b i)^2/(4*u) := by
    have h : a i * a i ≤ (d+b i)*a i := mul_le_mul_of_nonneg_right (cap i hi) (a0 i hi)
    have y : b i*a i ≤ u*(a i)^2 + (b i)^2/(4*u) := by
      apply (sub_le_iff_le_add').mp
      apply (le_div_iff₀ (by linarith : (0:ℝ)<4*u)).2
      nlinarith only [sq_nonneg (2*u*a i-b i)]
    nlinarith only [h,y]
  have h := sum_le_sum per
  rw [sum_add_distrib,← mul_sum,← mul_sum,← Finset.sum_div] at h
  exact h.trans (add_le_add_right (div_le_div_of_nonneg_right variance (by positivity)) _)

end
end Erdos617.ThirdPruning
