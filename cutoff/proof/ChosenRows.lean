import ListDeficit

/-! Chosen-row surplus, omitted slots and the bound on the short and chosen lists. -/

namespace Erdos617.PackingLists

open Finset
open scoped Classical
noncomputable section
variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def verticesIn (A : Finset V) (row : V → I) (indices : Finset I) :=
  A.filter fun v ↦ row v ∈ indices

def rowCard (A : Finset V) (row : V → I) (i : I) := (A.filter fun v ↦ row v = i).card

def surplus (all : Finset V) (row : V → I) (r : ℕ) (i : I) : ℝ :=
  max ((rowCard all row i:ℝ)/r-1) 0

def oversizedRows (all : Finset V) (row : V → I) (C : Finset I) (r : ℕ) :=
  C.filter fun i ↦ 257*r < 256*rowCard all row i

def oversizedExcess (all : Finset V) (row : V → I) (C : Finset I) (r : ℕ) : ℝ :=
  ∑ i ∈ oversizedRows all row C r, ((rowCard all row i:ℝ)/r-1)

omit [DecidableEq V] in
theorem card_verticesIn (A : Finset V) (row : V → I) (C : Finset I) :
    (verticesIn A row C).card = ∑ i ∈ C, rowCard A row i := by
  have cov : ((verticesIn A row C : Finset V):Set V).MapsTo row C := fun _ h ↦ (mem_filter.mp h).2
  rw [card_eq_sum_card_fiberwise cov]
  apply sum_congr rfl
  intro i hi
  unfold rowCard
  congr 1
  ext v
  simp only [verticesIn, mem_filter]
  constructor
  · exact fun h ↦ ⟨h.1.1,h.2⟩
  · exact fun h ↦ ⟨⟨h.1,h.2 ▸ hi⟩,h.2⟩

omit [DecidableEq V] in
private theorem chosen_eq_sum (live : Finset V) (row : V → I) (E : Finset V) (r : ℕ) :
    chosenExcess live row E r = ∑ i ∈ E.image row, ((rowCard live row i:ℝ)/r-1) := by
  unfold chosenExcess
  change ((verticesIn live row (E.image row)).card:ℝ)/r - _ = _
  rw [card_verticesIn]
  simp [sum_sub_distrib,Finset.sum_div]

omit [DecidableEq V] in
theorem chosen_le_surplus (all live : Finset V) (row : V → I) (parts E : Finset I)
    (r : ℕ) (inside : live ⊆ all) (sub : E ⊆ parts) :
    (∑ i ∈ E, ((rowCard live row i:ℝ)/r-1)) ≤ ∑ i ∈ parts, surplus all row r i := by
  apply le_trans (Finset.sum_le_sum (s := E) (g := surplus all row r) ?_)
  · exact sum_le_sum_of_subset_of_nonneg sub fun i _ _ ↦ le_max_right _ _
  · intro i _
    have h : rowCard live row i ≤ rowCard all row i := card_le_card (filter_subset_filter _ inside)
    apply le_trans _ (le_max_left ..)
    exact sub_le_sub_right (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg r)) _

/-- Charge only the deleted vertices in oversized chosen rows. Each other
chosen row's surviving surplus is at most 1/256. -/
theorem chosen_oversize_bound (all live : Finset V) (row : V → I) (E : Finset V)
    (r : ℕ) (hr : 0 < (r:ℝ)) (inside : live ⊆ all) :
    let C := E.image row
    let B := oversizedRows all row C r
    chosenExcess live row E r ≤ oversizedExcess all row C r -
      ((verticesIn (all \ live) row B).card:ℝ)/r + ((C \ B).card:ℝ)/256 := by
  let C := E.image row
  let B := oversizedRows all row C r
  have sub : B ⊆ C := filter_subset ..
  have split (i) : (rowCard (all \ live) row i:ℝ)+rowCard live row i = rowCard all row i := by
    have h := card_sdiff_add_card_eq_card (filter_subset_filter (fun v ↦ row v = i) inside)
    unfold rowCard
    have he : (all \ live).filter (fun v ↦ row v = i) =
        (all.filter fun v ↦ row v = i) \ (live.filter fun v ↦ row v = i) := by
      ext v
      simp only [mem_filter, mem_sdiff]
      tauto
    rw [he]
    exact_mod_cast h
  have large : (∑ i ∈ B, ((rowCard live row i:ℝ)/r-1)) =
      oversizedExcess all row C r - ((verticesIn (all \ live) row B).card:ℝ)/r := by
    rw [card_verticesIn, Nat.cast_sum, Finset.sum_div]
    change _ = (∑ i ∈ B, _) - ∑ i ∈ B, _
    rw [← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← split i]
    ring
  have small : (∑ i ∈ C \ B, ((rowCard live row i:ℝ)/r-1)) ≤ ((C \ B).card:ℝ)/256 := by
    calc _ ≤ ∑ _i ∈ C \ B, (1/256:ℝ) := by
           apply sum_le_sum
           intro i hi
           obtain ⟨hc,hn⟩ := mem_sdiff.mp hi
           have hraw : 256*rowCard all row i ≤ 257*r := le_of_not_gt (fun h ↦ hn (mem_filter.mpr ⟨hc,h⟩))
           have hl : rowCard live row i ≤ rowCard all row i := card_le_card (filter_subset_filter _ inside)
           have h : (256:ℝ)*rowCard live row i ≤ 257*r := by exact_mod_cast (Nat.mul_le_mul_left 256 hl).trans hraw
           apply sub_le_iff_le_add.mpr
           apply (div_le_iff₀ hr).2
           linarith only [h]
         _ = _ := by simp; ring
  rw [chosen_eq_sum]
  change (∑ i ∈ C, _) ≤ _
  rw [← Finset.sum_sdiff sub (f := fun i ↦ (rowCard live row i:ℝ)/r-1), large]
  linarith only [small]

/-- The number of chosen and short rows is at most 1411. -/
theorem ListBounds.count_le {G : SimpleGraph V} {row : V → I} {all live : Finset V}
    {parts qual : Finset I} {E : Finset V} {r : ℕ} (data : ListBounds G row all live parts qual E r)
    {p t : ℝ} (hr : 0 < (r:ℝ)) (inside : live ⊆ all) (covers : ∀ v ∈ live, row v ∈ parts)
    (cliqueCap : ∀ S : Finset V, G.IsClique (S:Set V) → S.card ≤ r)
    (sizes : (∑ i ∈ parts, surplus all row r i) ≤ 1/2)
    (deleted : ((all \ live).card:ℝ)/r = p+t)
    (hp : p ≤ 125/61) (hpt : p/4+(199/400)*t ≤ 1) :
    (shortRows (parts \ E.image row) (fun i ↦ (available G live row E i).card) (blockSize r)).card +
      (E.image row).card ≤ 1411 := by
  let U := parts \ E.image row
  let m := fun i ↦ (available G live row E i).card
  let O := ordinaryRows U qual m (blockSize r)
  let F := shortRows U m (blockSize r)
  have nonneg : 0 ≤ deficit O m r := by
    apply Finset.sum_nonneg
    intro i hi
    have hU : i ∈ U := (mem_sdiff.mp (mem_inter.mp hi).1).1
    have hc := cliqueCap _ (data.clique i (mem_sdiff.mp hU).2)
    exact sub_nonneg.mpr ((div_le_iff₀ hr).2 (by rw [one_mul]; exact_mod_cast hc))
  have hc : chosenExcess live row E r ≤ 1/2 := by
    rw [chosen_eq_sum]
    apply le_trans (chosen_le_surplus all live row parts (E.image row) r inside ?_) sizes
    intro i hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    exact covers _ (data.selected hv)
  have cost := data.budget
  change deficit O m r+((F.card:ℝ)+(E.image row).card)/400 ≤ _ at cost
  rw [deleted] at cost
  have bound : (F.card:ℝ)+(E.image row).card < 1412 := by
    linarith only [nonneg,cost,hc,hp,hpt,div_nonneg zero_le_one hr.le]
  have hn : F.card+(E.image row).card < 1412 := by exact_mod_cast bound
  exact Nat.le_of_lt_succ hn

omit [DecidableEq V] in
/-- Every initially omitted ordinary-row slot is unqualified, chosen or short. -/
theorem omitted_ordinary (parts bad : Finset I) (row : V → I) (E : Finset V)
    (m : I → ℕ) (b : ℕ) :
    let U := parts \ E.image row
    let O := ordinaryRows U (parts \ bad) m b
    (parts \ O).card ≤ bad.card + ((shortRows U m b).card+(E.image row).card) := by
  let U := parts \ E.image row
  let F := shortRows U m b
  let C := E.image row
  have sub : parts \ ordinaryRows U (parts \ bad) m b ⊆ bad ∪ (F ∪ C) := by
    intro i hi
    simp only [ordinaryRows,mem_sdiff,mem_inter,mem_union] at hi ⊢
    by_cases hb : i ∈ bad
    · exact Or.inl hb
    by_cases hc : i ∈ C
    · exact Or.inr (Or.inr hc)
    by_cases hf : i ∈ F
    · exact Or.inr (Or.inl hf)
    exact (hi.2 ⟨⟨mem_sdiff.mpr ⟨hi.1,hc⟩,hf⟩,⟨hi.1,hb⟩⟩).elim
  exact (card_le_card sub).trans ((card_union_le ..).trans
    (Nat.add_le_add_left (card_union_le ..) _))

end
end Erdos617.PackingLists
