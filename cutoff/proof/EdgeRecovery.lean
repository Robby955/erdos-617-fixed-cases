import ColoringRepairCost

/-! Recover the foreign load from the same original edges as the pair repair budget. -/

namespace Erdos617.EdgeRecovery

open Finset RepresentativeRepairs RepresentativeCut FiniteLaw ColoredLists PruningOverlap
open scoped Classical
noncomputable section
variable {V : Type*}

/-- Swapping the endpoints gives a bijection of the two oriented target cuts. -/
theorem cut_card_comm (G : SimpleGraph V) (A B : Finset V) :
    (cut G A B).card = (cut G B A).card := by
  apply card_bij (fun p _ ↦ p.swap)
  · intro p hp
    obtain ⟨inRows,adj⟩ := mem_filter.mp hp
    obtain ⟨h₁,h₂⟩ := mem_product.mp inRows
    exact mem_filter.mpr ⟨mem_product.mpr ⟨h₂,h₁⟩,G.adj_symm adj⟩
  · intro p _ q _ eq
    exact Prod.swap_injective eq
  · intro q hq
    obtain ⟨inRows,adj⟩ := mem_filter.mp hq
    obtain ⟨h₁,h₂⟩ := mem_product.mp inRows
    exact ⟨q.swap,mem_filter.mpr ⟨mem_product.mpr ⟨h₂,h₁⟩,G.adj_symm adj⟩,rfl⟩

/-- Each ordered pair with unequal labels has one increasing orientation. -/
private theorem sum_both (I : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i ∈ I, ∑ k ∈ I.erase i, f i k) =
      ∑ p ∈ rowPairs I, (f p.1 p.2+f p.2 p.1) := by
  let u := fun i k ↦ if i<k then f i k else 0
  let v := fun i k ↦ if i<k then f k i else 0
  have both (i k) : (if k≠i then f i k else 0) = u i k+v k i := by
    rcases lt_trichotomy i k with lt|eq|gt
    · simp [u,v,lt,lt.ne',not_lt.mpr lt.le]
    · subst k; simp [u,v]
    · simp [u,v,gt,gt.ne,not_lt.mpr gt.le]
  have split (i) : (∑ k ∈ I.erase i, f i k) = (∑ k ∈ I, u i k)+(∑ k ∈ I, v k i) := by
    rw [← filter_ne',sum_filter]
    simp_rw [both,sum_add_distrib]
  simp_rw [split,sum_add_distrib]
  rw [sum_comm (f := fun i k ↦ v k i)]
  simp only [rowPairs,sum_filter,sum_product,u,v]

/-- The two mixed terms of each tested pair cover both directed foreign loads.
Its pure N term remains available in full to pay for representative collisions. -/
theorem pair_recovery (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V)
    (n N F : ℕ → ℝ) (a b j r : ℝ) (ha : 0 ≤ a) (hb : j ≤ b) (hr : 0 < r)
    (hn : ∀ i ∈ I, 0 ≤ n i) (hN : ∀ i ∈ I, 0 ≤ N i)
    (foreign : ∀ i ∈ I, F i ≤ (j/r)*∑ k ∈ I.erase i,
      N k*((cut G (C i) (C k)).card:ℝ)) :
    let π := fun i ↦ (a*n i+b*N i)/r
    (a/r)*(∑ i ∈ I, n i*F i) +
        (b/r)^2*(∑ p ∈ rowPairs I, N p.1*N p.2*((cut G (C p.1) (C p.2)).card:ℝ)) ≤
      ∑ p ∈ rowPairs I, π p.1*π p.2*((cut G (C p.1) (C p.2)).card:ℝ) := by
  intro π
  let e := fun i k ↦ ((cut G (C i) (C k)).card:ℝ)
  let f := fun i k ↦ (a/r)*n i*(j/r)*N k*e i k
  have charge (i) (hi : i ∈ I) : (a/r)*(n i*F i) ≤ ∑ k ∈ I.erase i, f i k := by
    calc _ = ((a/r)*n i)*F i := by ring
         _ ≤ ((a/r)*n i)*((j/r)*∑ k ∈ I.erase i, N k*e i k) :=
           mul_le_mul_of_nonneg_left (foreign i hi) (mul_nonneg (div_nonneg ha hr.le) (hn i hi))
         _ = _ := by
           rw [← mul_assoc,Finset.mul_sum]
           exact sum_congr rfl fun k _ ↦ by dsimp [f]; ring
  have mixed : (a/r)*(∑ i ∈ I, n i*F i) ≤
      ∑ p ∈ rowPairs I, (f p.1 p.2+f p.2 p.1) := by
    rw [Finset.mul_sum,← sum_both]
    exact sum_le_sum charge
  apply (add_le_add_left mixed _).trans
  rw [Finset.mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  obtain ⟨hi,hk⟩ := mem_product.mp (mem_filter.mp hp).1
  have sym : e p.2 p.1 = e p.1 p.2 := by
    unfold e
    exact_mod_cast cut_card_comm G (C p.2) (C p.1)
  have edge : 0 ≤ e p.1 p.2 := Nat.cast_nonneg _
  have A : 0 ≤ a/r := div_nonneg ha hr.le
  have B : j/r ≤ b/r := div_le_div_of_nonneg_right hb hr.le
  have pi (i) : π i = (a/r)*n i+(b/r)*N i := by dsimp [π]; ring
  dsimp only [f]
  change _ + _ + (b/r)^2*(N p.1*N p.2*e p.1 p.2) ≤ π p.1*π p.2*e p.1 p.2
  rw [sym,pi,pi]
  have m₁ := mul_nonneg (sub_nonneg.mpr B) (mul_nonneg A (mul_nonneg (hn _ hi) (hN _ hk)))
  have m₂ := mul_nonneg (sub_nonneg.mpr B) (mul_nonneg A (mul_nonneg (hn _ hk) (hN _ hi)))
  have pure := mul_nonneg (sq_nonneg (a/r)) (mul_nonneg (hn _ hi) (hn _ hk))
  nlinarith only [mul_nonneg m₁ edge,mul_nonneg m₂ edge,mul_nonneg pure edge]

variable {r : ℕ} [Fintype V]

/-- The pair recovery with the original coloring's sender counts and expected
foreign incidences. The cut used on both sides is its actual target cut. -/
theorem coloring_pair_recovery (T : Trace V r) {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : representativeFactor X ≤ b) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let I := S.retained
    let μ := senderLaw T E I S.s p rate hp hp1
    let n' := heavyLoadMean G C (lowExterior T E I S.s) S.s r μ
    let N := fun i ↦ ((uniqueGroup T E I S.s i).card:ℝ)
    let F := fun i ↦ ∑ y, (μ y).expect (foreignDegree G C i)
    let π := fun i ↦ (a*n' i+b*N i)/r
    (a/r)*(∑ i ∈ I, n' i*F i)+(b/r)^2*(∑ q ∈ rowPairs I,
      N q.1*N q.2*((cut G (C q.1) (C q.2)).card:ℝ)) ≤
        ∑ q ∈ rowPairs I, π q.1*π q.2*((cut G (C q.1) (C q.2)).card:ℝ) := by
  intro G C I μ n' N F π
  have n0 (i : ℕ) (_ : i ∈ I) : 0 ≤ n' i := by
    apply sum_nonneg
    intro y _
    apply sum_nonneg
    intro o _
    apply mul_nonneg ((μ y).nonneg o)
    dsimp only [ArcRepair.active]
    split <;> norm_num
  exact pair_recovery G I C n' N F a b (representativeFactor X) r ha
    hb (by exact_mod_cast hr) n0 (fun _ _ ↦ Nat.cast_nonneg _)
    (fun i _ ↦ foreign_load_le_interrow_cut T S hr X lo hi width p rate hp hp1 i)

end
end Erdos617.EdgeRecovery
