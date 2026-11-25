import ArrivalSummation
import MultipleArrivalPrice
import TaggedDeficitCaps

/-! Every exterior vertex left after enlargement pays for itself from its
actual target neighbors in its original large rows. -/

namespace Erdos617.ColoredLists

open Finset UniqueAttachment PruningOverlap AuxiliaryMoments
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [DecidableEq V]

/-- Two large rows force a complete rectangle between the sender's
nonneighbors. Three already exceed the required payment at the attachment
thresholds. All further large rows contribute nonnegatively. -/
theorem priced_arena_impossible (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (arena : Finset V) (parts : Finset (ℕ ⊕ ℕ)) (row : ℕ ⊕ ℕ → Finset V)
    (large : V → ℕ ⊕ ℕ → Prop) (hr : 2^20 ≤ r) (no : ¬Witness color)
    (bounds : ArenaBounds (targetGraph color j) arena parts row r)
    (extensions : CanExtend (targetGraph color j) arena parts row large)
    (enlargement : EnlargedRows (targetGraph color j) arena parts row large r)
    (joint : ∀ J ⊆ parts, J.card ≤ 3 →
      (∑ i ∈ J, max ((r:ℝ)-(row i).card) 0) ≤
        (r:ℝ)*(peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256))
    (large_iff : ∀ v i, large v i ↔
      (i.elim (fun _ ↦ (81/200:ℝ)) (fun _ ↦ (369/1000:ℝ)))*r <
        (((row i).filter ((targetGraph color j).Adj v)).card:ℝ)) : False := by
  let θ := fun i : ℕ ⊕ ℕ ↦ i.elim (fun _ ↦ (81/200:ℝ)) (fun _ ↦ (369/1000:ℝ))
  let g := fun i ↦ (r:ℝ)-(row i).card
  let G := targetGraph color j
  have pos : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have types (i) (hi : i ∈ parts) : (θ i = 81/200 ∧ g i ≤ (317/2000:ℝ)*r) ∨
      (θ i = 369/1000 ∧ g i ≤ (1/256:ℝ)*r) := by
    have b := individual_of_tagged_deficit_cap (size := fun k ↦ (row k).card) joint hi
    cases i with
    | inl i => exact Or.inl ⟨rfl,b⟩
    | inr i => exact Or.inr ⟨rfl,b⟩
  have typeN (l) (hl : l ∈ parts) : ArrivalRow (θ l) (g l/r) := by
    rcases types l hl with ⟨t,cap⟩|⟨t,cap⟩
    · exact Or.inl ⟨t,(div_le_iff₀ pos).mpr cap⟩
    · exact Or.inr ⟨t,(div_le_iff₀ pos).mpr cap⟩
  apply arrival_sum_contradiction color j arena parts row large θ hr no enlargement types
    (fun v _ i _ h ↦ ((large_iff v i).mp h).le)
  intro x xP
  let N := parts.filter (large x)
  let deg := fun i ↦ (((row i).filter (G.Adj x)).card:ℝ)
  let net := fun i ↦ deg i-((77/100:ℝ)*g i+(r:ℝ)/10000)
  change (r:ℝ) ≤ ∑ i ∈ N, net i
  have sum_g (J : Finset (ℕ ⊕ ℕ)) (sub : J ⊆ parts) (small : J.card ≤ 3) :
      ∑ i ∈ J, g i ≤ (r:ℝ)*(peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256) :=
    (sum_le_sum fun i _ ↦ le_max_left (g i) 0).trans (joint J sub small)
  have hit (i) (hi : i ∈ N) : θ i*r < deg i := (large_iff x i).mp (mem_filter.mp hi).2
  obtain ⟨i,hi,k,hk,ne,li,lk⟩ := enlargement.remaining x xP
  let pair : Finset (ℕ ⊕ ℕ) := {i,k}
  have sub : pair ⊆ N := insert_subset (mem_filter.mpr ⟨hi,li⟩)
    (singleton_subset_iff.mpr (mem_filter.mpr ⟨hk,lk⟩))
  have pairSize : pair.card = 2 := by simp [pair,ne]
  by_cases few : N.card ≤ 2
  · have eq : N = pair := (eq_of_subset_of_card_le sub (pairSize ▸ few)).symm
    have onlyTwo (l) (hl : l ∈ parts) (big : large x l) : l=i ∨ l=k := by
      have inn : l ∈ N := mem_filter.mpr ⟨hl,big⟩
      simpa [eq,pair] using inn
    have old : x ∈ exterior arena parts row := by
      obtain ⟨inArena,out⟩ := mem_sdiff.mp xP
      refine mem_sdiff.mpr ⟨inArena,?_⟩
      intro mem
      obtain ⟨c,hc,xc⟩ := mem_biUnion.mp mem
      exact out (mem_biUnion.mpr ⟨c,hc,mem_union_left _ xc⟩)
    have rect := two_large_row_price color j (row i) (row k) x hr no (bounds.disjoint i hi k hk ne)
      (bounds.cliques i hi) (bounds.cliques k hk) (θ i) (θ k) (typeN i hi) (typeN k hk)
      ((large_iff x i).mp li) ((large_iff x k).mp lk) (fun _ ha xa _ hb xb ↦
        two_row_rectangle bounds.inside bounds.disjoint bounds.independent extensions old hi hk ne
          onlyTwo ha hb xa xb)
    have gc := (sum_g pair (sub.trans (filter_subset ..)) (by omega)).trans
      (mul_le_mul_of_nonneg_left (two_tagged_price_cap pair pairSize) pos.le)
    rw [show (∑ l ∈ pair, g l) = g i+g k from sum_pair ne] at gc
    change (1+(77/100:ℝ)*(213/1000)+2/10000)*r < deg i+deg k at rect
    rw [eq,show (∑ l ∈ pair, net l) = net i+net k from sum_pair ne]
    dsimp only [net]
    linarith only [rect,gc]
  · obtain ⟨J,Jsub,hJ⟩ := exists_subset_card_eq (show 3 ≤ N.card by omega)
    have part := Jsub.trans (filter_subset ..)
    have enough := three_large_rows_price J hJ r pos deg g (fun l hl ↦ (hit l (Jsub hl)).le)
      (sum_g J part (by omega))
    have per : (1/10000:ℝ)*r = (r:ℝ)/10000 := by ring
    rw [per] at enough
    apply enough.le.trans (sum_le_sum_of_subset_of_nonneg Jsub ?_)
    intro l hl _
    have add := additional_large_price pos (typeN l (mem_filter.mp hl).1) (hit l hl).le
    rw [per] at add
    exact add.le

end
end Erdos617.ColoredLists
