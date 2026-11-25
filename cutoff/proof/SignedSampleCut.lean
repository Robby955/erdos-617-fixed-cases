import AuxiliaryMoments
import AuxiliaryColoring
import DistinctRowConflicts

/-! The signed cut inequality for a realized sample and tested rows, Appendix A §5. -/

namespace Erdos617.SignedSampleCut

open Finset ColoredLists AuxiliaryMoments
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

/-- Twice the number of unordered pairs on a finite set, also at orders zero and one. -/
private theorem two_choose (n : ℕ) : 2*(n.choose 2:ℝ) = (n:ℝ)*(n-1) := by
  have raw : n.choose 2*2 = n*(n-1) := by
    rw [Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have pred (k : ℕ) : (k:ℝ)*(↑(k-1:ℕ):ℝ) = (k:ℝ)*((k:ℝ)-1) := by cases k <;> simp
  calc 2*(n.choose 2:ℝ) = (n.choose 2:ℝ)*2 := by ring
       _ = (n:ℝ)*(↑(n-1:ℕ):ℝ) := by exact_mod_cast raw
       _ = _ := pred n

/-- Summing each of the two Turán tangents over the actual nontarget colors
on U gives two upper bounds for its target edge count. -/
private theorem two_color_budgets (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (U : Finset V) (H : ℕ) (q : ℝ)
    (hr : 2 ≤ r) (no : ¬Witness color) (order : (U.card:ℝ) = H*r-q) :
    let e := (((targetGraph color j).induce (U:Set V)).edgeFinset.card:ℝ)
    let n := (H:ℝ)*r-q
    ((r:ℝ)-1)*(r*H*((H:ℝ)-1)-2*((H:ℝ)-1)*q)+2*e ≤ n*(n-1) ∧
    ((r:ℝ)-1)*(r*H*((H:ℝ)-1)-2*H*q)+2*e ≤ n*(n-1) := by
  let c := inducedColor color U
  let e := fun k ↦ ((targetGraph c k).edgeFinset.card:ℝ)
  have order' : (Fintype.card U:ℝ) = H*r+(-q) := by simpa [sub_eq_add_neg] using order
  have minus : (((univ.erase j).card:ℕ):ℝ) = (r:ℝ)-1 := by
    rw [card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin,Nat.cast_sub (by omega),Nat.cast_one]
  have colsum : (∑ k ∈ univ.erase j, 2*e k)+2*e j = ((H:ℝ)*r-q)*((H:ℝ)*r-q-1) := by
    rw [sum_erase_add _ _ (mem_univ j),← Finset.mul_sum]
    unfold e
    rw [← Nat.cast_sum,edge_color_partition,two_choose,order']
    ring
  have summed (B : ℝ) (floor : ∀ k ≠ j, B ≤ 2*e k) :
      ((r:ℝ)-1)*B+2*e j ≤ ((H:ℝ)*r-q)*((H:ℝ)*r-q-1) := by
    rw [← colsum]
    apply add_le_add_left
    have S := Finset.sum_le_sum (s := univ.erase j) (fun k hk ↦ floor k (mem_erase.mp hk).1)
    simpa only [sum_const,nsmul_eq_mul,minus] using S
  have tangents (k : Fin r) := tangent_floor (targetGraph c k) r H (-q) order'
    (induced_color_cap color no U hr k)
  have upper₀ := summed _ (fun k _ ↦ (tangents k).1)
  have upper₁ := summed _ (fun k _ ↦ (tangents k).2)
  dsimp [e,c] at upper₀ upper₁
  have eqEdges : (targetGraph (inducedColor color U) j).edgeFinset =
      ((targetGraph color j).induce (U:Set V)).edgeFinset := by
    apply Finset.ext
    intro p
    induction p using Sym2.inductionOn with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeFinset]
      change (targetGraph (inducedColor color U) j).Adj x y ↔ (targetGraph color j).Adj x.val y.val
      rw [induced_target_graph]
      rfl
  rw [eqEdges] at upper₀ upper₁
  dsimp
  constructor
  · simpa only [mul_neg, ← sub_eq_add_neg] using upper₀
  · simpa only [mul_neg, ← sub_eq_add_neg] using upper₁

/-- Edge budget on the union of W and the tested disjoint rows. The target-edge
difference counts the cut and all interrow target edges when the rows are cliques. -/
theorem signed_cut (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (W : Finset V) (I : Finset ℕ) (C : ℕ → Finset V) (h : ℕ)
    (repaired : SimpleGraph W) (P : ℝ)
    (hr : 2 ≤ r) (no : ¬Witness color)
    (rows : (I:Set ℕ).PairwiseDisjoint C) (outside : Disjoint W (I.biUnion C))
    (slots : h+I.card ≤ r)
    (cap : ∀ S : Finset W, repaired.IsIndepSet (S:Set W) → S.card ≤ h)
    (repairCost : (repaired.edgeFinset.card:ℝ) ≤
      (((targetGraph color j).induce (W:Set V)).edgeFinset.card:ℝ)+P) :
    let U := W ∪ I.biUnion C
    let H := h+I.card
    let v := (h:ℝ)*r-W.card
    let d := fun i ↦ (r:ℝ)-(C i).card
    let D := ∑ i ∈ I, d i
    let e := fun A : Finset V ↦ (((targetGraph color j).induce (A:Set V)).edgeFinset.card:ℝ)
    2*(e U-e W-∑ i ∈ I, ((C i).card.choose 2:ℝ)) ≤
      2*P+r*H*((H:ℝ)-1)+D^2-(∑ i ∈ I, (d i)^2)+2*v*D+v*(v-1) := by
  intro U H v d D e
  have orderW : (Fintype.card W:ℝ) = r*h+(-v) := by simp [v]; ring
  have orderU : (U.card:ℝ) = H*r-(D+v) := by
    dsimp [U,H,D,d,v]
    rw [card_union_of_disjoint outside,card_biUnion rows,Nat.cast_add,Nat.cast_sum,Finset.sum_sub_distrib]
    simp
    ring
  have orderRows : 2*(∑ i ∈ I, ((C i).card.choose 2:ℝ)) =
      (I.card:ℝ)*r*((r:ℝ)-1)-(2*(r:ℝ)-1)*D+∑ i ∈ I, (d i)^2 := by
    rw [Finset.mul_sum]
    have each (i : ℕ) : 2*((C i).card.choose 2:ℝ) =
        (r:ℝ)*((r:ℝ)-1)-(2*(r:ℝ)-1)*d i+(d i)^2 := by
      rw [two_choose]; dsimp [d]; ring
    simp_rw [each,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp [D]
    ring
  have Wfloor := (tangent_floor repaired h r (-v) orderW cap).1
  have Wpaid : (h:ℝ)*r*((r:ℝ)-1)-2*((r:ℝ)-1)*v ≤ 2*(e W)+2*P := by
    dsimp [e]; linarith only [Wfloor,repairCost]
  have floors := two_color_budgets color j U H (D+v) hr no orderU
  change _ + 2*e U ≤ _ ∧ _ + 2*e U ≤ _ at floors
  have size : (H:ℝ) = h+(I.card:ℝ) := by simp [H]
  have bound : (H:ℝ) ≤ r := by exact_mod_cast slots
  by_cases sign : D+v ≤ 0
  · have rebate := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr bound) sign
    nlinarith only [floors.2,Wpaid,orderRows,rebate,
      congrArg (fun t : ℝ ↦ t*r*((r:ℝ)-1)) size]
  · have Hpos : 1 ≤ H := by
      by_contra! zero
      have Hz : H = 0 := by omega
      rw [Hz] at orderU
      simp at orderU
      linarith [Nat.cast_nonneg (α := ℝ) U.card]
    have Hpos' : (1:ℝ) ≤ H := by exact_mod_cast Hpos
    have rebate := mul_nonneg (sub_nonneg.mpr Hpos') (le_of_not_ge sign)
    nlinarith only [floors.1,Wpaid,orderRows,rebate,
      congrArg (fun t : ℝ ↦ t*r*((r:ℝ)-1)) size]

/-- Count directed target incidences in a rectangle. -/
private def arcs (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then (1:ℝ) else 0

private theorem arcs_comm (G : SimpleGraph V) (A B : Finset V) : arcs G A B = arcs G B A := by
  unfold arcs
  rw [Finset.sum_comm]
  exact sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ by rw [G.adj_comm x y]

private theorem arcs_internal (G : SimpleGraph V) (A : Finset V) :
    arcs G A A = 2*((G.induce (A:Set V)).edgeFinset.card:ℝ) := by
  let K := G.induce (A:Set V)
  have degree (x : A) : (∑ y : A, if K.Adj x y then (1:ℝ) else 0) = K.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_eq_filter]
    exact sum_boole _ _
  have inside : arcs G A A = ∑ x : A, ∑ y : A, if K.Adj x y then (1:ℝ) else 0 := by
    unfold arcs
    rw [← sum_coe_sort A (fun x ↦ ∑ y ∈ A, if G.Adj x y then (1:ℝ) else 0)]
    apply sum_congr rfl
    intro x hx
    exact (sum_coe_sort A (fun y ↦ if G.Adj x.val y then (1:ℝ) else 0)).symm
  rw [inside]
  simp_rw [degree]
  exact_mod_cast K.sum_degrees_eq_twice_card_edges

private theorem arcs_union (G : SimpleGraph V) (A B D : Finset V) (sep : Disjoint A B) :
    arcs G (A∪B) D = arcs G A D+arcs G B D := by simp [arcs,sum_union sep]

private theorem arcs_rows (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V) (A : Finset V)
    (rows : (I:Set ℕ).PairwiseDisjoint C) :
    arcs G (I.biUnion C) A = ∑ i ∈ I, arcs G (C i) A := by
  unfold arcs
  exact sum_biUnion rows

private theorem arcs_card (G : SimpleGraph V) (A B : Finset V) :
    arcs G A B = ∑ x ∈ A, ((B.filter (G.Adj x)).card:ℝ) :=
  sum_congr rfl fun x _ ↦ sum_boole (G.Adj x) B

private theorem arcs_eq_cut (G : SimpleGraph V) (A B : Finset V) :
    arcs G A B = ((RepresentativeCut.cut G A B).card:ℝ) := by
  rw [RepresentativeCut.cut,natCast_card_filter,sum_product]
  rfl

private theorem arcs_rows_exact (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V)
    (rows : (I:Set ℕ).PairwiseDisjoint C) :
    arcs G (I.biUnion C) (I.biUnion C) =
      (∑ i ∈ I, arcs G (C i) (C i)) +
      2*(∑ p ∈ (I ×ˢ I).filter (fun p ↦ p.1<p.2), ((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ)) := by
  let a := fun i k ↦ arcs G (C i) (C k)
  let u := fun i k ↦ if i<k then a i k else 0
  have sym (i k) : a i k = a k i := arcs_comm G _ _
  have expand : arcs G (I.biUnion C) (I.biUnion C) = ∑ i ∈ I, ∑ k ∈ I, a i k := by
    rw [arcs_rows G I C _ rows]
    apply sum_congr rfl
    intro i _
    rw [arcs_comm,arcs_rows G I C _ rows]
    exact sum_congr rfl fun k _ ↦ sym k i
  have both (i k) : a i k = (if k=i then a i i else 0)+u i k+u k i := by
    rcases lt_trichotomy i k with lt|eq|gt
    · simp [u,lt,lt.ne',not_lt.mpr lt.le]
    · subst k; simp [u]
    · simp [u,gt,gt.ne,not_lt.mpr gt.le,sym k i]
  have diag : (∑ i ∈ I, ∑ k ∈ I, if k=i then a i i else 0) = ∑ i ∈ I, a i i := by simp
  have upper : (∑ i ∈ I, ∑ k ∈ I, u i k) =
      ∑ p ∈ (I ×ˢ I).filter (fun p ↦ p.1<p.2), ((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ) := by
    rw [sum_filter,sum_product]
    simp only [u,a,arcs_eq_cut]
  have split := sum_congr (s₁ := I) rfl fun i _ ↦
    sum_congr (s₁ := I) rfl fun k _ ↦ both i k
  simp_rw [sum_add_distrib] at split
  rw [diag,Finset.sum_comm (f := fun i k ↦ u k i)] at split
  rw [expand,split,upper]
  dsimp [a]
  ring

/-- Exact unordered-edge decomposition. Each exterior-to-row target edge occurs
once in X, and each target edge between two tested rows occurs once for i<k. -/
theorem exterior_interrow_identity (G : SimpleGraph V) (W : Finset V) (I : Finset ℕ)
    (C : ℕ → Finset V) (rows : (I:Set ℕ).PairwiseDisjoint C)
    (outside : Disjoint W (I.biUnion C)) (cliques : ∀ i ∈ I, G.IsClique (C i:Set V)) :
    let e := fun A : Finset V ↦ ((G.induce (A:Set V)).edgeFinset.card:ℝ)
    (∑ i ∈ I, ∑ x ∈ W, (((C i).filter (G.Adj x)).card:ℝ)) +
      (∑ p ∈ (I ×ˢ I).filter (fun p ↦ p.1<p.2), ((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ)) =
      e (W∪I.biUnion C)-e W-∑ i ∈ I, ((C i).card.choose 2:ℝ) := by
  intro e
  let B := I.biUnion C
  have area : arcs G (W∪B) (W∪B) = arcs G W W+2*arcs G W B+arcs G B B := by
    rw [arcs_union _ _ _ _ outside,arcs_comm _ W,arcs_comm _ B (W∪B),
      arcs_union _ _ _ _ outside,arcs_union _ _ _ _ outside,arcs_comm _ B W]
    ring
  have cross : arcs G W B = ∑ i ∈ I, ∑ x ∈ W, (((C i).filter (G.Adj x)).card:ℝ) := by
    rw [arcs_comm,arcs_rows _ _ _ _ rows]
    apply sum_congr rfl
    intro i _
    rw [arcs_comm,arcs_card]
  have complete (i) (hi : i ∈ I) : arcs G (C i) (C i) = 2*((C i).card.choose 2:ℝ) := by
    rw [arcs_internal]
    have top := SimpleGraph.induce_eq_top.mpr (cliques i hi)
    have eqEdges : (G.induce (C i:Set V)).edgeFinset = (⊤ : SimpleGraph (C i)).edgeFinset := by
      apply Finset.ext
      intro p
      induction p using Sym2.inductionOn with
      | _ x y =>
        rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeFinset]
        change (G.induce (C i:Set V)).Adj x y ↔ (⊤ : SimpleGraph (C i)).Adj x y
        rw [top]
    rw [eqEdges,SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_coe]
  rw [arcs_internal,arcs_internal,cross,arcs_rows_exact _ _ _ rows,sum_congr rfl complete,← Finset.mul_sum] at area
  dsimp [e]
  linarith only [area]

/-- The actual exterior-to-row target incidences are covered by the target edge
difference, because W and the row cliques are pairwise disjoint. -/
theorem exterior_incidence_le (G : SimpleGraph V) (W : Finset V) (I : Finset ℕ)
    (C : ℕ → Finset V) (rows : (I:Set ℕ).PairwiseDisjoint C)
    (outside : Disjoint W (I.biUnion C)) (cliques : ∀ i ∈ I, G.IsClique (C i:Set V)) :
    let e := fun A : Finset V ↦ ((G.induce (A:Set V)).edgeFinset.card:ℝ)
    (∑ i ∈ I, ∑ x ∈ W, (((C i).filter (G.Adj x)).card:ℝ)) ≤
      e (W∪I.biUnion C)-e W-∑ i ∈ I, ((C i).card.choose 2:ℝ) := by
  intro e
  have paid := exterior_interrow_identity G W I C rows outside cliques
  have other : 0 ≤ ∑ p ∈ (I ×ˢ I).filter (fun p ↦ p.1<p.2),
      ((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ) :=
    sum_nonneg fun p _ ↦ Nat.cast_nonneg _
  exact (le_add_of_nonneg_right other).trans_eq paid

/-- The signed bound in the form used for averaging tested-row incidences. -/
theorem incidence_cut (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (W : Finset V) (I : Finset ℕ) (C : ℕ → Finset V) (h : ℕ)
    (repaired : SimpleGraph W) (P : ℝ)
    (hr : 2 ≤ r) (no : ¬Witness color)
    (rows : (I:Set ℕ).PairwiseDisjoint C) (outside : Disjoint W (I.biUnion C))
    (cliques : ∀ i ∈ I, (targetGraph color j).IsClique (C i:Set V))
    (slots : h+I.card ≤ r)
    (cap : ∀ S : Finset W, repaired.IsIndepSet (S:Set W) → S.card ≤ h)
    (repairCost : (repaired.edgeFinset.card:ℝ) ≤
      (((targetGraph color j).induce (W:Set V)).edgeFinset.card:ℝ)+P) :
    let H := h+I.card
    let v := (h:ℝ)*r-W.card
    let d := fun i ↦ (r:ℝ)-(C i).card
    let D := ∑ i ∈ I, d i
    2*(∑ i ∈ I, ∑ x ∈ W, (((C i).filter ((targetGraph color j).Adj x)).card:ℝ)) ≤
      2*P+r*H*((H:ℝ)-1)+D^2-(∑ i ∈ I, (d i)^2)+2*v*D+v*(v-1) :=
  (mul_le_mul_of_nonneg_left (exterior_incidence_le (targetGraph color j) W I C rows outside cliques)
    (by norm_num : (0:ℝ) ≤ 2)).trans
    (signed_cut color j W I C h repaired P hr no rows outside slots cap repairCost)

/-- The signed cut budget retaining both the exterior incidences and every
target edge between a pair of tested rows. -/
theorem full_incidence_cut (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (W : Finset V) (I : Finset ℕ) (C : ℕ → Finset V) (h : ℕ)
    (repaired : SimpleGraph W) (P : ℝ)
    (hr : 2 ≤ r) (no : ¬Witness color)
    (rows : (I:Set ℕ).PairwiseDisjoint C) (outside : Disjoint W (I.biUnion C))
    (cliques : ∀ i ∈ I, (targetGraph color j).IsClique (C i:Set V))
    (slots : h+I.card ≤ r)
    (cap : ∀ S : Finset W, repaired.IsIndepSet (S:Set W) → S.card ≤ h)
    (repairCost : (repaired.edgeFinset.card:ℝ) ≤
      (((targetGraph color j).induce (W:Set V)).edgeFinset.card:ℝ)+P) :
    let G := targetGraph color j
    let H := h+I.card
    let v := (h:ℝ)*r-W.card
    let d := fun i ↦ (r:ℝ)-(C i).card
    let D := ∑ i ∈ I, d i
    2*((∑ i ∈ I, ∑ x ∈ W, (((C i).filter (G.Adj x)).card:ℝ))+
        ∑ p ∈ (I ×ˢ I).filter (fun p ↦ p.1<p.2), ((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ)) ≤
      2*P+r*H*((H:ℝ)-1)+D^2-(∑ i ∈ I, (d i)^2)+2*v*D+v*(v-1) := by
  intro G H v d D
  rw [exterior_interrow_identity G W I C rows outside cliques]
  exact signed_cut color j W I C h repaired P hr no rows outside slots cap repairCost

end
end Erdos617.SignedSampleCut
