import AttachmentArena
import CliqueArrivalPrice

/-! Close the exterior capacity count of Appendix A, §4 by summing the
same large-attachment incidences first over vertices and then over rows. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap UniqueAttachment
open scoped Classical
noncomputable section

variable {V I : Type*} {r : ℕ}

/-- After paying the price on every arrival, the row contributes at most
r−1 times its deficit in vertices. Both estimates count the same arrivals. -/
theorem clique_net_capacity (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C Z : Finset V) (hr : 2^20 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C Z) (cl : (targetGraph color j).IsClique (C:Set V))
    (θ : ℝ) (large : ∀ v ∈ Z, θ*r ≤ ((C.filter ((targetGraph color j).Adj v)).card:ℝ))
    (rowType : (θ = 81/200 ∧ (r:ℝ)-C.card ≤ (317/2000:ℝ)*r) ∨
      (θ = 369/1000 ∧ (r:ℝ)-C.card ≤ (1/256:ℝ)*r)) :
    let g := (r:ℝ)-C.card
    (∑ v ∈ Z, (((C.filter ((targetGraph color j).Adj v)).card:ℝ) -
      ((77/100:ℝ)*g+(r:ℝ)/10000))) ≤ ((r:ℝ)-1)*g := by
  dsimp only
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
  have capacity := clique_arrival_capacity color j C Z (by omega) no dis cl
  have price := clique_arrival_price_in_edges color j C Z hr no dis cl θ large rowType
  have paid := mul_le_mul_of_nonneg_left price (Nat.cast_nonneg (α := ℝ) Z.card)
  dsimp only at capacity
  linarith only [capacity,paid]

variable [DecidableEq V]

/-- If every remaining exterior vertex contributes r after prices, then
the enlarged clique rows would require more target edges than their capacity.
The sender hypothesis uses only the original rows. -/
theorem arrival_sum_contradiction (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (arena : Finset V) (parts : Finset I) (row : I → Finset V)
    (large : V → I → Prop) (threshold : I → ℝ)
    (hr : 2^20 ≤ r) (no : ¬Witness color)
    (enlargement : EnlargedRows (targetGraph color j) arena parts row large r)
    (types : ∀ i ∈ parts, (threshold i = 81/200 ∧ (r:ℝ)-(row i).card ≤ (317/2000:ℝ)*r) ∨
      (threshold i = 369/1000 ∧ (r:ℝ)-(row i).card ≤ (1/256:ℝ)*r))
    (detects : ∀ v ∈ exterior arena parts (enlarged arena parts row large), ∀ i ∈ parts,
      large v i → threshold i*r ≤ (((row i).filter ((targetGraph color j).Adj v)).card:ℝ))
    (pay : ∀ v ∈ exterior arena parts (enlarged arena parts row large),
      (r:ℝ) ≤ ∑ i ∈ parts.filter (large v),
        ((((row i).filter ((targetGraph color j).Adj v)).card:ℝ) -
          ((77/100:ℝ)*((r:ℝ)-(row i).card)+(r:ℝ)/10000))) : False := by
  let G := targetGraph color j
  let C := enlarged arena parts row large
  let P := exterior arena parts C
  let arrivals := fun i ↦ P.filter (fun v ↦ large v i)
  let g := fun i ↦ (r:ℝ)-(C i).card
  let net := fun (v : V) i ↦ (((row i).filter (G.Adj v)).card:ℝ) -
    ((77/100:ℝ)*((r:ℝ)-(row i).card)+(r:ℝ)/10000)
  have original (i) : row i ⊆ C i := subset_union_left
  have card (i) : ((row i).card:ℝ) ≤ (C i).card := by exact_mod_cast card_le_card (original i)
  have count (v i) : ((((row i).filter (G.Adj v)).card):ℝ) ≤ ((C i).filter (G.Adj v)).card :=
    Nat.cast_le.mpr (card_le_card (filter_subset_filter _ (original i)))
  have rowCap (i) (hi : i ∈ parts) : ∑ v ∈ arrivals i, net v i ≤ ((r:ℝ)-1)*g i := by
    have sep : Disjoint (C i) (arrivals i) := disjoint_left.mpr fun v hv hv' ↦
      (mem_sdiff.mp (mem_filter.mp hv').1).2 (mem_biUnion.mpr ⟨i,hi,hv⟩)
    have c := clique_net_capacity color j (C i) (arrivals i) hr no sep (enlargement.cliques i hi)
      (threshold i) (by
        intro v hv
        obtain ⟨p,attached⟩ := mem_filter.mp hv
        exact (detects v p i hi attached).trans (count v i)) (by
        rcases types i hi with ⟨t,d⟩|⟨t,d⟩
        · exact Or.inl ⟨t,by linarith only [d,card i]⟩
        · exact Or.inr ⟨t,by linarith only [d,card i]⟩)
    apply le_trans (sum_le_sum (s := arrivals i) (g := fun v ↦
        (((C i).filter (G.Adj v)).card:ℝ)-((77/100:ℝ)*g i+(r:ℝ)/10000)) _) c
    intro v _
    dsimp only [net,g]
    linarith only [count v i,card i]
  have lower := sum_le_sum pay
  change (∑ _v ∈ P, (r:ℝ)) ≤ ∑ v ∈ P, ∑ i ∈ parts.filter (large v), net v i at lower
  have transpose : (∑ v ∈ P, ∑ i ∈ parts.filter (large v), net v i) =
      ∑ i ∈ parts, ∑ v ∈ arrivals i, net v i := by
    simp only [arrivals,sum_filter]
    rw [sum_comm]
  have upper := lower.trans (transpose ▸ sum_le_sum rowCap)
  rw [sum_const,nsmul_eq_mul,← mul_sum] at upper
  have exactDeficit : (∑ i ∈ parts, g i)+1 = (P.card:ℝ) := by
    have id : ((∑ i ∈ parts, (r-(C i).card) : ℕ):ℝ)+1 = P.card := by
      exact_mod_cast enlargement.deficit_sum
    rw [Nat.cast_sum] at id
    refine Eq.trans ?_ id
    congr 1
    apply sum_congr rfl
    intro i hi
    exact (Nat.cast_sub (R := ℝ) (enlargement.size_cap i hi)).symm
  have positive : (0:ℝ)<r := by exact_mod_cast (show 0 < r by omega)
  have nonnegative : 0 ≤ ∑ i ∈ parts, g i :=
    sum_nonneg (fun i hi ↦ sub_nonneg.mpr (Nat.cast_le.mpr (enlargement.size_cap i hi)))
  rw [← exactDeficit] at upper
  nlinarith only [upper,nonnegative,positive]

end
end Erdos617.ColoredLists
