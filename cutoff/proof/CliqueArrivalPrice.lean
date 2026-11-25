import ExteriorRowEdges
import PrescribedListCounts

/-! Charging large arrivals at an enlarged ordinary or auxiliary clique in
Appendix A, §4. The intermediate arrival count is rounded down in the graph. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap RowExtraction PackingLists GraphPartitionCount
open scoped Classical
noncomputable section

/-- The joint square bound gives the individual auxiliary deficit needed by
the price estimate. Enlargement can only decrease this deficit. -/
theorem auxiliary_pricing_deficit {W : Type*} [Fintype W] (G : SimpleGraph W)
    (row : W → ℕ) {A : Finset W} {h r : ℕ} (hr : 0 < r)
    (survivors : AuxiliarySurvivors G row h r A)
    (budget : ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range h, (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20)
    (i : ℕ) (hi : i < h) :
    (r:ℝ)-(fiber A row i).card ≤ (317/2000:ℝ)*r := by
  let u := max (1-(size row i:ℝ)/r) 0
  let z := ((Fintype.card W:ℝ)-A.card)/r
  let x := ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2
  have pos : (0:ℝ)<r := by exact_mod_cast hr
  have single := single_le_sum (fun j _ ↦ sq_nonneg (max (1-(size row j:ℝ)/r) 0)) (mem_range.mpr hi)
  have square : x+u^2 ≤ (3/20:ℝ)^2+1/2^20 := (add_le_add_right single x).trans budget
  have paid : (43/200:ℝ)*z ≤ x := by
    apply (le_div_iff₀ (sq_pos_of_pos pos)).2
    have raw := (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) _)).trans survivors.residual
    convert raw using 1
    dsimp [z]
    field_simp
  have d := AuxiliaryMoments.deficit_plus_deletions square paid
  have cover := PrescribedLists.normalized_row_cover A ∅ ∅ row i r hr 0 (by simp [fiber])
  simp only [PrescribedLists.candidates,PrescribedLists.losses,union_empty,sdiff_empty,sub_zero] at cover
  have lo : (fiber (univ \ A) row i).card ≤ (univ \ A).card := card_le_card (filter_subset ..)
  have cost : (((fiber (univ \ A) row i).card:ℝ)/r) ≤ z := by
    apply div_le_div_of_nonneg_right _ pos.le
    have total := card_sdiff_add_card_eq_card (subset_univ A)
    rw [card_univ] at total
    apply le_sub_iff_add_le.mpr
    exact_mod_cast (show (fiber (univ \ A) row i).card+A.card ≤ Fintype.card W by omega)
  change 1-u-_/ (r:ℝ) ≤ ((fiber A row i).card:ℝ)/r at cover
  have norm : 1-317/2000 ≤ ((fiber A row i).card:ℝ)/r := by linarith only [d,cost,cover]
  have scaled := (le_div_iff₀ pos).mp norm
  linarith only [scaled]

variable {V : Type*} {r : ℕ}

/-- For any set of arrivals, use exactly the floor of twice the proposed
price plus the deficit as a trial count. Such a subset would exceed the
clique's actual edge capacity, so the total count must be smaller. -/
theorem clique_arrival_price_in_edges (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C Z : Finset V) (hr : 2^20 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C Z) (cl : (targetGraph color j).IsClique (C:Set V))
    (θ : ℝ) (large : ∀ v ∈ Z, θ*r ≤ ((C.filter ((targetGraph color j).Adj v)).card:ℝ))
    (rowType : (θ = 81/200 ∧ (r:ℝ)-C.card ≤ (317/2000:ℝ)*r) ∨
      (θ = 369/1000 ∧ (r:ℝ)-C.card ≤ (1/256:ℝ)*r)) :
    (Z.card:ℝ)+1 ≤ 2*((177/100:ℝ)*((r:ℝ)-C.card)+(r:ℝ)/10000) := by
  have hr' : 2 ≤ r := by omega
  have scale : (1048576:ℝ) ≤ r := by exact_mod_cast hr
  have rp : 0 < (r:ℝ) := by linarith only [scale]
  let g := (r:ℝ)-C.card
  have nonneg : 0 ≤ g := sub_nonneg.mpr (by exact_mod_cast (caps_of_no_witness color j hr' no).2 C cl)
  let t := 2*((177/100:ℝ)*g+(r:ℝ)/10000)
  let m := ⌊t⌋₊
  have floor_lo : t < (m:ℝ)+1 := Nat.lt_floor_add_one t
  have floor_hi : (m:ℝ) ≤ t := Nat.floor_le (by dsimp [t]; positivity)
  have size : Z.card < m := by
    by_contra! enough
    obtain ⟨Y,sub,card⟩ := exists_subset_card_eq enough
    have actual := clique_arrival_capacity color j C Y hr' no (dis.mono_right sub) cl
    change _+(Y.card:ℝ)*g ≤ ((r:ℝ)-1)*g+_ at actual
    have lower := sum_le_sum fun v (hv : v ∈ Y) ↦ large v (sub hv)
    simp only [sum_const,nsmul_eq_mul,card] at lower actual
    have capacity : (m:ℝ)*(θ*r+g-((m:ℝ)+1)/2) ≤ ((r:ℝ)-1)*g := by
      linarith only [actual,lower]
    have factor : (113/400:ℝ)*r ≤ θ*r+g-((m:ℝ)+1)/2 := by
      change (m:ℝ) ≤ 2*((177/100:ℝ)*g+(r:ℝ)/10000) at floor_hi
      rcases rowType with ⟨rfl,deficit⟩ | ⟨rfl,deficit⟩
      · change g ≤ _ at deficit
        linarith only [floor_hi,deficit,scale]
      · change g ≤ _ at deficit
        linarith only [floor_hi,deficit,scale]
    have low := mul_le_mul_of_nonneg_left factor (Nat.cast_nonneg (α := ℝ) m)
    have strict := mul_lt_mul_of_pos_right (show t-1 < (m:ℝ) by linarith only [floor_lo])
      (show 0 < (113/400:ℝ)*r by positivity)
    have surplus := mul_nonneg nonneg rp.le
    have margin := mul_pos (show 0 < (r:ℝ)/5000-1 by linarith only [scale]) rp
    dsimp only [t] at strict
    nlinarith only [capacity,low,strict,surplus,nonneg,margin]
  exact (show (Z.card:ℝ)+1 ≤ m by exact_mod_cast size).trans floor_hi

/-- The normalized price of a large arrival in the one-clique capacity. -/
theorem clique_arrival_price (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C Z : Finset V) (hr : 2^20 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C Z) (cl : (targetGraph color j).IsClique (C:Set V))
    (θ : ℝ) (large : ∀ v ∈ Z, θ*r ≤ ((C.filter ((targetGraph color j).Adj v)).card:ℝ))
    (rowType : (θ = 81/200 ∧ (r:ℝ)-C.card ≤ (317/2000:ℝ)*r) ∨
      (θ = 369/1000 ∧ (r:ℝ)-C.card ≤ (1/256:ℝ)*r)) :
    let d := ((r:ℝ)-C.card)/r
    ((Z.card:ℝ)+1)/(2*r)-d ≤ (77/100:ℝ)*d+1/10000 := by
  have raw := clique_arrival_price_in_edges color j C Z hr no dis cl θ large rowType
  have pos : (0:ℝ)<r := by exact_mod_cast (show 0 < r by omega)
  dsimp only
  field_simp
  linarith only [raw]

end
end Erdos617.ColoredLists
