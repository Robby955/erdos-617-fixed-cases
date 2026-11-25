import RawEdgeIdentity

/-! The cost of adjoining exterior vertices to a raw destination row. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

private def ends (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then 1 else 0

private theorem ends_symm (G : SimpleGraph V) (A B : Finset V) :
    ends G A B = ends G B A := by
  unfold ends
  rw [Finset.sum_comm]
  exact sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ by rw [G.adj_comm]

private theorem off_row (G : SimpleGraph V) (A Z : Finset V) (dis : Disjoint A Z) :
    ends Gᶜ Z A + ends G Z A = (Z.card:ℝ)*A.card := by
  unfold ends
  rw [← sum_add_distrib]
  calc _ = ∑ _x ∈ Z, ∑ _y ∈ A, (1:ℝ) := by
         apply sum_congr rfl
         intro x hx
         rw [← sum_add_distrib]
         apply sum_congr rfl
         intro y hy
         have ne : x ≠ y := fun h ↦ disjoint_left.mp dis hy (h ▸ hx)
         by_cases adj : G.Adj x y <;> simp [SimpleGraph.compl_adj,ne,adj]
       _ = _ := by simp

private theorem ends_le_distinct (G : SimpleGraph V) (Z : Finset V) :
    ends G Z Z ≤ (Z.card:ℝ)*((Z.card:ℝ)-1) := by
  have per (x : V) (hx : x ∈ Z) : (∑ y ∈ Z, if G.Adj x y then (1:ℝ) else 0) + 1 ≤ Z.card := by
    have entry (y : V) (_hy : y ∈ Z) :
        (if G.Adj x y then (1:ℝ) else 0)+(if y=x then 1 else 0) ≤ 1 := by
      by_cases he : y=x
      · subst y; simp
      · simp [he]; split <;> norm_num
    simpa only [sum_add_distrib,sum_ite_eq',ite_eq_left hx,sum_const,nsmul_eq_mul,mul_one]
      using sum_le_sum (s := Z) entry
  have h := sum_le_sum (s := Z) per
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at h
  unfold ends
  linarith only [h]

private theorem signed_floor (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (A : Finset V) (hr : 2 ≤ r) (no : ¬Witness color) :
    ((r:ℝ)-1)*((A.card:ℝ)-r) ≤ ((targetGraph color j)ᶜ.induce (A:Set V)).edgeFinset.card := by
  by_cases h : r ≤ A.card
  · have floor := other_color_floor color j A hr no
    have real_floor : (((r-1)*(A.card-r):ℕ):ℝ) ≤
        (((targetGraph color j)ᶜ.induce (A:Set V)).edgeFinset.card:ℝ) := by exact_mod_cast floor
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ r by omega),Nat.cast_sub h,Nat.cast_one] using real_floor
  · have small : (A.card:ℝ) ≤ r := by exact_mod_cast le_of_not_ge h
    exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ r by omega)) : (0:ℝ) ≤ r-1)
      (sub_nonpos.mpr small)).trans (Nat.cast_nonneg _)

/-- Target edges from Z into A spend the unused nontarget allowance of A.
All vertices of Z are outside A. The argument also applies to an empty Z
or a row smaller than r. -/
private theorem adjoining_bound_counted (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (A Z : Finset V) (hr : 2 ≤ r) (no : ¬Witness color) (dis : Disjoint A Z) :
    ends (targetGraph color j) Z A ≤ ends (targetGraph color j)ᶜ A A / 2 -
      ((r:ℝ)-1)*((A.card:ℝ)-r)+(1+(A.card:ℝ)-r)*(Z.card:ℝ)+ends (targetGraph color j)ᶜ Z Z/2 := by
  let G := targetGraph color j
  have lower := signed_floor color j (A ∪ Z) hr no
  rw [card_union_of_disjoint dis, Nat.cast_add] at lower
  have count : ends Gᶜ (A ∪ Z) (A ∪ Z) =
      2*((Gᶜ.induce ((A ∪ Z : Finset V):Set V)).edgeFinset.card:ℝ) := by
    convert internal_end_sum Gᶜ (A ∪ Z) using 2 <;> congr 7; apply Subsingleton.elim
  have split : ends Gᶜ (A ∪ Z) (A ∪ Z) =
      ends Gᶜ A A + 2*ends Gᶜ Z A + ends Gᶜ Z Z := by
    calc _ = ends Gᶜ A A + ends Gᶜ A Z + (ends Gᶜ Z A + ends Gᶜ Z Z) := by
           simp only [ends, Finset.sum_union dis,sum_add_distrib]
         _ = _ := by rw [ends_symm Gᶜ A Z]; ring
  have cross := off_row G A Z dis
  change ((r:ℝ)-1)*((A.card:ℝ)+Z.card-r) ≤ (Gᶜ.induce ((A ∪ Z:Finset V):Set V)).edgeFinset.card at lower
  change ends G Z A ≤ ends Gᶜ A A / 2 - _ + _ + _
  linarith only [lower,count,split,cross]

private theorem adjoining_bound (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (A Z : Finset V) (hr : 2 ≤ r) (no : ¬Witness color) (dis : Disjoint A Z) :
    ends (targetGraph color j) Z A ≤ ends (targetGraph color j)ᶜ A A / 2 -
      ((r:ℝ)-1)*((A.card:ℝ)-r)+(1+(A.card:ℝ)-r)*(Z.card:ℝ)+(Z.card:ℝ)*((Z.card:ℝ)-1)/2 := by
  linarith only [adjoining_bound_counted color j A Z hr no dis,
    ends_le_distinct (targetGraph color j)ᶜ Z]

private theorem clique_missing_zero (G : SimpleGraph V) (A : Finset V)
    (cl : G.IsClique (A:Set V)) : ends Gᶜ A A = 0 := by
  apply sum_eq_zero
  intro x hx
  apply sum_eq_zero
  intro y hy
  apply ite_eq_right
  rintro ⟨ne,non⟩
  exact non (cl hx hy ne)

/-- One-clique capacity for any set of exterior arrivals, including an
empty set. The deficit is counted once for every arrival. -/
theorem clique_arrival_capacity (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C Z : Finset V) (hr : 2 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C Z) (cl : (targetGraph color j).IsClique (C:Set V)) :
    let d := (r:ℝ)-C.card
    (∑ x ∈ Z, ((C.filter ((targetGraph color j).Adj x)).card:ℝ)) + (Z.card:ℝ)*d ≤
      ((r:ℝ)-1)*d + (Z.card:ℝ)*((Z.card:ℝ)+1)/2 := by
  dsimp only
  have bound := adjoining_bound color j C Z hr no dis
  rw [clique_missing_zero _ _ cl] at bound
  have degree : ends (targetGraph color j) Z C =
      ∑ x ∈ Z, ((C.filter ((targetGraph color j).Adj x)).card:ℝ) := by simp [ends]
  rw [degree] at bound
  linarith only [bound]

/-- Two disjoint target cliques with vertex deficits d and e have at most
r−d−e+de target edges between them. Each actual edge is counted once. -/
theorem clique_pair_capacity (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C D : Finset V) (hr : 2 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C D) (cl : (targetGraph color j).IsClique (C:Set V))
    (cl' : (targetGraph color j).IsClique (D:Set V)) :
    let d := (r:ℝ)-C.card
    let e := (r:ℝ)-D.card
    (∑ x ∈ D, ((C.filter ((targetGraph color j).Adj x)).card:ℝ)) ≤ (r:ℝ)-d-e+d*e := by
  dsimp only
  have bound := adjoining_bound_counted color j C D hr no dis
  rw [clique_missing_zero _ _ cl,clique_missing_zero _ _ cl'] at bound
  have degree : ends (targetGraph color j) D C =
      ∑ x ∈ D, ((C.filter ((targetGraph color j).Adj x)).card:ℝ) := by simp [ends]
  rw [degree] at bound
  linarith only [bound]

/-- The ordered-star count in the original coloring of a destination row
and an arbitrary set of exterior vertices. -/
theorem exterior_row_edges [Fintype V] (T : Trace V r) (hr : 2 ≤ r) (no : ¬Witness T.color)
    (i : ℕ) (Z : Finset V) (exterior : ∀ x ∈ Z, T.row x ≠ i) :
    (∑ x ∈ Z, ((((univ.filter fun y ↦ T.row y=i).filter
        ((targetGraph T.color T.target).Adj x)).card:ℝ))) ≤
      (internalMissing T i:ℝ)-((r:ℝ)-1)*((T.rowSize i:ℝ)-r)+
      (1+(T.rowSize i:ℝ)-r)*(Z.card:ℝ)+(Z.card:ℝ)*((Z.card:ℝ)-1)/2 := by
  let G := targetGraph T.color T.target
  let A := univ.filter fun y ↦ T.row y = i
  have dis : Disjoint A Z := disjoint_left.mpr fun x ha hz ↦ exterior x hz (mem_filter.mp ha).2
  have count : ends Gᶜ A A = 2*(internalMissing T i:ℝ) := by
    convert internal_end_sum Gᶜ A using 2 <;> dsimp only [G,A,internalMissing] <;> congr 7; apply Subsingleton.elim
  have h := adjoining_bound T.color T.target A Z hr no dis
  rw [show (targetGraph T.color T.target) = G from rfl, count] at h
  have size : A.card = T.rowSize i := rfl
  rw [size] at h
  have cross : ends G Z A = ∑ x ∈ Z, ((A.filter (G.Adj x)).card:ℝ) := by simp [ends]
  rw [cross] at h
  linarith only [h]

end
end Erdos617.ColoredLists
