import PrescribedListCounts
import PrescribedProducts
import EdgeProductTransversal

/-! Independent representatives on the actual auxiliary survivors after prescribed exclusions. -/

namespace Erdos617.PrescribedLists

open Finset RowExtraction GraphPartitionCount PackingLists Transversal ColoredLists
open scoped Classical
noncomputable section

/-- Exterior neighbors cost a per-row allowance. Neighbors of the at most two
prescribed representatives cost one shared allowance across all unfilled rows. -/
theorem auxiliary_representatives {W : Type*} [Fintype W] (G : SimpleGraph W)
    (row : W → ℕ) {h r : ℕ} (hr : 0 < r) {A : Finset W}
    (live : AuxiliarySurvivors G row h r A) (parts : Finset ℕ) (indices : parts ⊆ range h)
    (budget : ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range h, (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20)
    (F D : Finset W) (a d : ℝ)
    (mode : (a = 81/100 ∧ d = 0) ∨ (a = 81/200 ∧ d = 43/100))
    (exterior : ∀ i ∈ parts, ((fiber (A ∩ F) row i).card:ℝ) ≤ a*r)
    (shared : (D.card:ℝ) ≤ d*r) :
    ∃ R ⊆ candidates A F D, Partial G row R ∧ R.image row = parts := by
  let H := cross G row
  let L := candidates A F D
  let x := (H.edgeFinset.card:ℝ)/(r:ℝ)^2
  let z := ((Fintype.card W:ℝ)-A.card)/r
  let u := fun i ↦ max (1-(size row i:ℝ)/r) 0
  let p := fun i ↦ ((fiber (losses A D) row i).card:ℝ)/r
  let m := fun i ↦ ((fiber L row i).card:ℝ)/r
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr (by exact_mod_cast card_le_univ A)) pos.le
  have total : x+∑ i ∈ range h, (u i)^2 ≤ (3/20:ℝ)^2+1/2^20 := budget
  have one (i) (hi : i ∈ parts) : x+(u i)^2 ≤ (3/20:ℝ)^2+1/2^20 := by
    apply le_trans _ total
    exact add_le_add_right (single_le_sum (fun k _ ↦ sq_nonneg (u k)) (indices hi)) x
  have two (i j) (hi : i ∈ parts) (hj : j ∈ parts) (ne : i ≠ j) :
      x+(u i)^2+(u j)^2 ≤ (3/20:ℝ)^2+1/2^20 := by
    have sub : ({i,j} : Finset ℕ) ⊆ range h  := by
      intro k hk
      rcases mem_insert.mp hk with rfl|hk
      · exact indices hi
      · simpa only [mem_singleton.mp hk] using indices hj
    have small := sum_le_sum_of_subset_of_nonneg sub (fun k _ _ ↦ sq_nonneg (u k))
    rw [sum_pair ne] at small
    linarith only [small,total]
  have residual : ((H.induce (A:Set W)).edgeFinset.card:ℝ)/(r:ℝ)^2 ≤ x-(43/200)*z := by
    have eq : ((43/200:ℝ)*r*((Fintype.card W:ℝ)-A.card))/(r:ℝ)^2 = (43/200)*z := by
      dsimp [z]; field_simp
    have q := div_le_div_of_nonneg_right live.residual (sq_nonneg (r:ℝ))
    change (_ + (43/200:ℝ)*r*((Fintype.card W:ℝ)-A.card))/(r:ℝ)^2 ≤ x at q
    rw [add_div,eq] at q
    linarith only [q]
  have paid : (43/200)*z ≤ x := by
    linarith only [residual,show (0:ℝ) ≤ ((H.induce (A:Set W)).edgeFinset.card:ℝ)/(r:ℝ)^2 by positivity]
  have allowance : ((losses A D).card:ℝ)/r ≤ z+d := by
    have sum := div_le_div_of_nonneg_right (loss_count A D) pos.le
    rw [add_div] at sum
    exact sum.trans (add_le_add_right ((div_le_iff₀ pos).2 shared) z)
  have p₁ (i) : p i ≤ z+d :=
    (div_le_div_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset (fun v ↦ row v=i) (losses A D))) pos.le).trans allowance
  have p₂ (i j) (ne : i ≠ j) : p i+p j ≤ z+d := by
    have c : ((fiber (losses A D) row i).card:ℝ)+(fiber (losses A D) row j).card ≤
        (losses A D).card := by exact_mod_cast distinct_losses A D row ne
    exact (show p i+p j ≤ ((losses A D).card:ℝ)/r by
      simpa only [p,← add_div] using div_le_div_of_nonneg_right c pos.le).trans allowance
  have hs (i) (hi : i ∈ parts) : 1-a-u i-p i ≤ m i :=
    normalized_row_cover A F D row i r hr a (exterior i hi)
  have np (i) : 0 ≤ p i := div_nonneg (Nat.cast_nonneg _) pos.le
  apply exists_of_edge_products G A L row parts sdiff_subset
  · intro i hi
    have bound := hs i hi
    have lost := p₁ i
    have ok : 0 < m i := by
      rcases mode with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact PrescribedProducts.two_exterior_positive (p := p i) (one i hi) paid (by linarith only [lost]) (by linarith only [bound])
      · exact PrescribedProducts.one_exterior_positive (p := p i) (one i hi) paid lost (by linarith only [bound])
    have card : 0 < ((fiber L row i).card:ℝ) := (div_pos_iff_of_pos_right pos).mp ok
    exact card_pos.mp (by exact_mod_cast card)
  · intro i hi j hj ne
    have li := hs i hi
    have lj := hs j hj
    have lost := p₂ i j ne
    have prod : x-(43/200)*z < m i*m j := by
      rcases mode with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact PrescribedProducts.two_exterior_product (le_max_right _ _) (le_max_right _ _)
          (np i) (np j) (two i j hi hj ne) paid (by linarith only [lost]) (by linarith only [li]) (by linarith only [lj])
      · exact PrescribedProducts.one_exterior_product (np i) (np j) (two i j hi hj ne) paid hz lost
          (by linarith only [li]) (by linarith only [lj])
    have bound := residual.trans_lt prod
    dsimp only [m] at bound
    rw [div_mul_div_comm,← sq] at bound
    have raw := (div_lt_div_iff_of_pos_right (sq_pos_of_pos pos)).mp bound
    exact_mod_cast raw

end
end Erdos617.PrescribedLists
