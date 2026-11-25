import AuxiliaryCliques

/-! Accounting for eligible vertices in a pair of distinct auxiliary rows. -/

namespace Erdos617.PrescribedLists

open Finset RowExtraction GraphPartitionCount
open scoped Classical
noncomputable section

variable {W : Type*} [Fintype W]

/-- Vertices unavailable through peeling or through one of the prescribed representatives. -/
def losses (A D : Finset W) : Finset W := (univ \ A) ∪ D

/-- Candidates after removing neighbors of the exterior points and the prescribed representatives. -/
def candidates (A F D : Finset W) : Finset W := A \ (F ∪ D)

theorem loss_count (A D : Finset W) :
    ((losses A D).card:ℝ) ≤ ((Fintype.card W:ℝ)-A.card)+D.card := by
  have eq := card_sdiff_add_card_eq_card (subset_univ A)
  rw [card_univ] at eq
  have add : (((univ \ A).card:ℝ) + A.card) = Fintype.card W := by exact_mod_cast eq
  have sub : ((losses A D).card:ℝ) ≤ (univ \ A).card + (D.card:ℝ) := by
    exact_mod_cast card_union_le (univ \ A) D
  linarith only [add,sub]

theorem distinct_losses (A D : Finset W) (row : W → ℕ) {i j : ℕ} (ne : i ≠ j) :
    (fiber (losses A D) row i).card + (fiber (losses A D) row j).card ≤
      (losses A D).card := by
  have dis : Disjoint (fiber (losses A D) row i) (fiber (losses A D) row j) :=
    disjoint_left.mpr fun _ h k ↦ ne ((mem_filter.mp h).2.symm.trans (mem_filter.mp k).2)
  rw [← card_union_of_disjoint dis]
  exact card_le_card (union_subset (filter_subset ..) (filter_subset ..))

/-- Count raw vertices in a row before its two kinds of exclusions.
Overlapping losses can only increase the right hand side. -/
theorem row_cover (A F D : Finset W) (row : W → ℕ) (i : ℕ) :
    size row i ≤ (fiber (candidates A F D) row i).card +
      (fiber (A ∩ F) row i).card + (fiber (losses A D) row i).card := by
  let L := fiber (candidates A F D) row i
  let N := fiber (A ∩ F) row i
  let B := fiber (losses A D) row i
  have sub : fiber univ row i ⊆ (L ∪ N) ∪ B := by
    intro v hv
    have eq := (mem_filter.mp hv).2
    by_cases a : v ∈ A
    · by_cases f : v ∈ F
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_inter.mpr ⟨a,f⟩,eq⟩))
      by_cases d : v ∈ D
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_union_right _ d,eq⟩)
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨a,by simpa only [mem_union,not_or] using And.intro f d⟩,eq⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _,a⟩),eq⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans
    (Nat.add_le_add_right (card_union_le L N) _))

/-- Local raw deficit, actual row losses and exterior attachments together pay
for every vertex missing from its candidate list. -/
theorem normalized_row_cover (A F D : Finset W) (row : W → ℕ) (i r : ℕ) (hr : 0 < r)
    (rate : ℝ) (attach : ((fiber (A ∩ F) row i).card:ℝ) ≤ rate*r) :
    1-rate-max (1-(size row i:ℝ)/r) 0-((fiber (losses A D) row i).card:ℝ)/r ≤
      ((fiber (candidates A F D) row i).card:ℝ)/r := by
  have pos : (0:ℝ)<r := by exact_mod_cast hr
  have count : (size row i:ℝ) ≤ (fiber (candidates A F D) row i).card+
      ((fiber (A ∩ F) row i).card:ℝ)+(fiber (losses A D) row i).card := by
    exact_mod_cast row_cover A F D row i
  have base := le_max_left (1-(size row i:ℝ)/r) (0:ℝ)
  have sum : (size row i:ℝ)/r ≤ ((fiber (candidates A F D) row i).card:ℝ)/r+
      ((fiber (A ∩ F) row i).card:ℝ)/r+((fiber (losses A D) row i).card:ℝ)/r := by
    simpa only [add_div] using div_le_div_of_nonneg_right count pos.le
  linarith only [base,sum,(div_le_iff₀ pos).2 attach]

end
end Erdos617.PrescribedLists
