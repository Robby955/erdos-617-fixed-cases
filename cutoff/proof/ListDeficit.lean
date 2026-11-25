import PackingLists
import WeightedWidth

/-! Real vertex counts for Appendix A, inequality (2). -/

namespace Erdos617.PackingLists

open Finset
open scoped Classical
noncomputable section

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def chosenVertices (live : Finset V) (row : V → I) (E : Finset V) : Finset V :=
  live.filter fun v ↦ row v ∈ E.image row

def deficit (indices : Finset I) (m : I → ℕ) (r : ℕ) : ℝ :=
  ∑ i ∈ indices, (1-(m i:ℝ)/r)

def shortRows (U : Finset I) (m : I → ℕ) (b : ℕ) := U.filter fun i ↦ m i < b

def ordinaryRows (U qual : Finset I) (m : I → ℕ) (b : ℕ) :=
  (U \ shortRows U m b) ∩ qual

def blockSize (r : ℕ) := 399*r/400
def degreeBound (r : ℕ) := 199*r/400

/-- Rows selected in (2) contribute their actual surviving size in excess of
one full row per selected pair. -/
def chosenExcess (live : Finset V) (row : V → I) (E : Finset V) (r : ℕ) : ℝ :=
  ((chosenVertices live row E).card:ℝ)/r - (E.image row).card

/-- All surviving vertices belong to a chosen row, belong to an available
list, or are removed from a different row by a chosen endpoint. -/
theorem count_survivors (G : SimpleGraph V) (row : V → I) (live E : Finset V)
    (parts : Finset I) (Δ : ℕ) (sub : E ⊆ live) (covers : ∀ v ∈ live, row v ∈ parts)
    (degree : ∀ v ∈ live, (Transversal.neighbors (cross G row) live v).card ≤ Δ) :
    live.card ≤ (chosenVertices live row E).card +
      (∑ i ∈ parts \ E.image row, (available G live row E i).card) + E.card*Δ := by
  let U := parts \ E.image row
  let L := available G live row E
  let N := Transversal.neighbors (cross G row) live
  have count : (U.biUnion L).card = ∑ i ∈ U, (L i).card := by
    apply card_biUnion
    intro i _ j _ ne
    exact disjoint_left.mpr fun _ hi hj ↦ ne (((mem_filter.mp hi).2.1).symm.trans (mem_filter.mp hj).2.1)
  have cov : live ⊆ (chosenVertices live row E ∪ U.biUnion L) ∪ E.biUnion N := by
    intro x hx
    by_cases chosen : row x ∈ E.image row
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,chosen⟩))
    have hu : row x ∈ U := mem_sdiff.mpr ⟨covers _ hx,chosen⟩
    by_cases ok : ∀ z ∈ E, ¬G.Adj z x
    · exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
        ⟨_,hu,mem_filter.mpr ⟨hx,rfl,ok⟩⟩))
    push Not at ok
    obtain ⟨z,hz,adj⟩ := ok
    have diff : row z ≠ row x := fun he ↦ chosen (he ▸ mem_image_of_mem row hz)
    exact mem_union_right _ (mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨hx,diff,adj⟩⟩)
  have bound := card_biUnion_le_card_mul E N Δ fun v hv ↦ degree v (sub hv)
  calc live.card ≤ _ := card_le_card cov
       _ ≤ _ := card_union_le ..
       _ ≤ _ := Nat.add_le_add (card_union_le ..) bound
       _ = _ := by rw [count]

omit [DecidableEq I] in
private theorem sum_deficit (U : Finset I) (m : I → ℕ) (r : ℕ) :
    deficit U m r = (U.card:ℝ)-((∑ i ∈ U, m i : ℕ):ℝ)/r := by
  simp [deficit,sum_sub_distrib,Nat.cast_sum,Finset.sum_div]

omit [DecidableEq I] in
/-- Short lists pay their full lost fraction at the rounded block size b. -/
private theorem short_charge (U : Finset I) (m : I → ℕ) (r b : ℕ)
    (hr : 0 < (r:ℝ)) (hb : 0 < (b:ℝ)) (scale : (b:ℝ) ≤ (399/400)*r) :
    (1-399/400:ℝ)*(shortRows U m b).card + (399/400)*shortfall U m b ≤
      deficit (shortRows U m b) m r := by
  have rate : 1/(r:ℝ) ≤ (399/400)/(b:ℝ) := by
    apply (div_le_div_iff₀ hr hb).2
    linarith only [scale]
  rw [shortfall, deficit, Finset.mul_sum]
  let F := shortRows U m b
  change (1-399/400:ℝ)*(F.card:ℝ) + (∑ i ∈ F, (399/400:ℝ)*(1-(m i:ℝ)/b)) ≤ ∑ i ∈ F, (1-(m i:ℝ)/r)
  rw [show (1-399/400:ℝ)*(F.card:ℝ) = ∑ _i ∈ F, (1-399/400:ℝ) by simp; ring,
    ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro i _
  have he := mul_le_mul_of_nonneg_left rate (Nat.cast_nonneg (α := ℝ) (m i))
  simp only [div_eq_mul_inv] at he ⊢
  linarith only [he]

omit [DecidableEq I] in
theorem shortfall_le_shortRows (U : Finset I) (m : I → ℕ) (b : ℕ) :
    shortfall U m b ≤ (shortRows U m b).card := by
  calc shortfall U m b ≤ ∑ _i ∈ shortRows U m b, (1:ℝ) := by
         apply sum_le_sum
         intro i _
         exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
       _ = _ := by simp

/-- The packing, the clique lists, the missing-representative bound and the
deficit of the ordinary rows all refer to the same original graph. -/
structure ListBounds (G : SimpleGraph V) (row : V → I) (all live : Finset V)
    (parts qual : Finset I) (E : Finset V) (r : ℕ) : Prop where
  selected : E ⊆ live
  packing : Packing G row E
  clique : ∀ i ∉ E.image row, G.IsClique (available G live row E i:Set V)
  missing : ((E.image row).card:ℝ) ≤ shortfall (parts \ E.image row)
    (fun i ↦ (available G live row E i).card) (blockSize r)
  pairs_le_short : (E.image row).card ≤ (shortRows (parts \ E.image row)
    (fun i ↦ (available G live row E i).card) (blockSize r)).card
  budget :
    let U := parts \ E.image row
    let m := fun i ↦ (available G live row E i).card
    deficit (ordinaryRows U qual m (blockSize r)) m r +
        ((shortRows U m (blockSize r)).card + ((E.image row).card:ℝ))/400 ≤
      ((all \ live).card:ℝ)/r + chosenExcess live row E r - 1/r

/-- Equation (2) with the favorable 1/r retained. The construction starts
with a surviving subgraph and its inter-row degree cap. -/
theorem exists_list_bounds (G : SimpleGraph V) (row : V → I) (all live : Finset V)
    (parts qual : Finset I) (r : ℕ) (hr₂ : 2 ≤ r)
    (order : all.card = r^2+1) (inside : live ⊆ all) (hparts : parts.card = r)
    (covers : ∀ v ∈ live, row v ∈ parts)
    (indCap : ∀ S : Finset V, G.IsIndepSet (S:Set V) → S.card ≤ r)
    (cliqueCap : ∀ S : Finset V, G.IsClique (S:Set V) → S.card ≤ r)
    (degree : ∀ v ∈ live, (Transversal.neighbors (cross G row) live v).card ≤ degreeBound r) :
    ∃ E, ListBounds G row all live parts qual E r := by
  obtain ⟨E,hE,pack,cliques⟩ := exists_packing G live row
  let U := parts \ E.image row
  let m := fun i ↦ (available G live row E i).card
  let q := (E.image row).card
  let b := blockSize r
  let F := shortRows U m b
  let O := ordinaryRows U qual m b
  have hr : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hb : 0 < b := by dsimp [b,blockSize]; omega
  have hb' : 2*degreeBound r ≤ b := by dsimp [degreeBound,b,blockSize]; omega
  have into : E.image row ⊆ parts := by
    intro i hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    exact covers v (hE hv)
  have hqw := pairs_le_shortfall G row live E parts r b (degreeBound r) hparts into pack indCap degree hb' hb
  change (q:ℝ) ≤ shortfall U m b at hqw
  have hqf := hqw.trans (shortfall_le_shortRows U m b)
  refine ⟨E, hE, pack, cliques, hqw, by exact_mod_cast hqf, ?_⟩
  change deficit O m r + ((F.card:ℝ)+q)/400 ≤ _
  have sumb := count_survivors G row live E parts (degreeBound r) hE covers degree
  rw [pack.card] at sumb
  change live.card ≤ (chosenVertices live row E).card + ∑ i ∈ U, m i + (2*q)*degreeBound r at sumb
  have sizes : (U.card:ℝ)+q = r := by exact_mod_cast (card_sdiff_add_card_eq_card into).trans hparts
  have totalCard : ((all \ live).card:ℝ)+live.card = (r:ℝ)^2+1 := by
    exact_mod_cast (card_sdiff_add_card_eq_card inside).trans order
  have Δrate : (degreeBound r:ℝ) ≤ (199/400)*r := by
    have h : 400*degreeBound r ≤ 199*r := by dsimp [degreeBound]; omega
    have hh : (400:ℝ)*degreeBound r ≤ 199*r := by exact_mod_cast h
    linarith only [hh]
  have total : deficit U m r ≤ ((all \ live).card:ℝ)/r + chosenExcess live row E r -
      1/r + (398/400)*q := by
    rw [sum_deficit,chosenExcess]
    rw [← (show q = (E.image row).card from rfl)]
    apply le_of_mul_le_mul_right _ hr
    field_simp
    have h : (live.card:ℝ) ≤ (chosenVertices live row E).card + ((∑ i ∈ U, m i : ℕ):ℝ)
        + (2*q:ℝ)*degreeBound r := by exact_mod_cast sumb
    nlinarith only [h, totalCard, congrArg (fun z : ℝ ↦ z*r) sizes,
      mul_le_mul_of_nonneg_left Δrate (show 0 ≤ 2*(q:ℝ) by positivity)]
  have nonnegative (i) (hi : i ∈ U) : 0 ≤ 1-(m i:ℝ)/r := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hr).2
    rw [one_mul]
    exact_mod_cast cliqueCap _ (cliques i (mem_sdiff.mp hi).2)
  have separate : Disjoint O F := sdiff_disjoint.mono_left inter_subset_left
  have united : O ∪ F ⊆ U :=
    union_subset (inter_subset_left.trans sdiff_subset) (filter_subset ..)
  have subtotal : deficit O m r + deficit F m r ≤ deficit U m r := by
    unfold deficit
    rw [← sum_union separate]
    exact sum_le_sum_of_subset_of_nonneg united (fun i hi _ ↦ nonnegative i hi)
  have bscale : (b:ℝ) ≤ (399/400)*r := by
    have hh : 400*b ≤ 399*r := by dsimp [b,blockSize]; omega
    have hc : (400:ℝ)*b ≤ 399*r := by exact_mod_cast hh
    linarith only [hc]
  have charge := short_charge U m r b hr (by exact_mod_cast hb) bscale
  have hfinal := WeightedWidth.short_lists (T := 398/400) (q := (q:ℝ)) (F := (F.card:ℝ))
    (subtotal.trans total) (by convert! charge using 1; norm_num [F]) (by norm_num) hqw
  linarith only [hfinal]

end
end Erdos617.PackingLists
