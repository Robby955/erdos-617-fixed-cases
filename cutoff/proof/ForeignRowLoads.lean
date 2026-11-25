import RepairedIndependence
import SenderSupport

/-! The load paid by a foreign representative is counted on the very same
target cut that supplies the inter-row repair term. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V]

/-- Target incidences into row i of the representative, when it belongs to
a different row. Repeated choices of a point are charged to their senders. -/
def foreignDegree (G : SimpleGraph V) (C : ℕ → Finset V) (i : ℕ) (o : State V) : ℝ :=
  match o with
  | some (some a) => if a ∈ C i then 0 else SameRowConflicts.degree G (C i) a
  | _ => 0

private theorem support_mono {Ω : Type*} [Fintype Ω] (ν : Law Ω) {f g : Ω → ℝ}
    (h : ∀ o, 0 < ν.weight o → f o ≤ g o) : ν.expect f ≤ ν.expect g := by
  apply sum_le_sum
  intro o _
  by_cases zero : ν.weight o = 0
  · simp [zero]
  · exact mul_le_mul_of_nonneg_left (h o (lt_of_le_of_ne (ν.nonneg o) (Ne.symm zero))) (ν.nonneg o)

private theorem chosen_mark (T : Trace V r) {E I s p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E I s p rate hp hp1)).weight w)
    {y : V} (selected : (w y).isSome) : y ∈ senderSet T E I s := by
  cases value : w y with
  | none => simp [value] at selected
  | some out =>
    cases out with
    | none => exact (moderate_support T positive value).1
    | some a =>
      obtain ⟨_,_,member,_,_⟩ := represented_support T positive value
      exact (mem_filter.mp member).1

/-- E_i is the true degree sum from the sampled exterior into C_i. F_i is
the sum of actual foreign-representative degrees, with multiplicity. -/
theorem expected_load_le_cut_add_foreign (T : Trace V r) (E : Finset V) (I : Finset ℕ)
    (s : ℕ) (p : ℝ) (rate : 100*((9/40:ℝ)/s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let μ := senderLaw T E I s p rate hp hp1
    (∑ y, (μ y).expect (fun a ↦ (repairLoad G C L i y a : ℝ))) ≤
      (product μ).expect (fun w ↦ ∑ y ∈ RepresentativeRepairs.exterior H L w, SameRowConflicts.degree G (C i) y) +
      ∑ y, (μ y).expect (foreignDegree G C i) := by
  intro G C H L μ
  let W := RepresentativeRepairs.exterior H L
  let own := fun w y ↦ if y ∈ W w then SameRowConflicts.degree G (C i) y else 0
  have ownSum (w : V → State V) : ∑ y, own w y = ∑ y ∈ W w, SameRowConflicts.degree G (C i) y := by
    simp [own]
  have point (w : V → State V) (positive : 0 < (product μ).weight w) (y : V) :
      (repairLoad G C L i y (w y):ℝ) ≤ own w y + foreignDegree G C i (w y) := by
    by_cases fixed : y ∈ L
    · have inside : y ∈ W w := mem_union_left _ fixed
      cases h : w y with
      | none => simp [repairLoad,fixed,own,inside,foreignDegree,SameRowConflicts.degree]
      | some out =>
        cases out with
        | none => simp [repairLoad,fixed,own,inside,foreignDegree,SameRowConflicts.degree]
        | some a => by_cases ha : a ∈ C i <;> simp [repairLoad,fixed,own,inside,foreignDegree,ha,SameRowConflicts.degree]
    · cases value : w y with
      | none => by_cases inside : y ∈ W w <;> simp [repairLoad,fixed,own,inside,foreignDegree,SameRowConflicts.degree]
      | some out =>
        have mark : (w y).isSome := by simp [value]
        have inside : y ∈ W w := mem_union_right _ (mem_filter.mpr ⟨chosen_mark T positive mark,mark⟩)
        cases out with
        | none => simp [repairLoad,fixed,own,inside,foreignDegree,SameRowConflicts.degree]
        | some a => by_cases ha : a ∈ C i <;> simp [repairLoad,fixed,own,inside,foreignDegree,ha,SameRowConflicts.degree]
  have upper := support_mono (product μ) fun w pos ↦ sum_le_sum (s:=univ) fun y _ ↦ point w pos y
  simp_rw [sum_add_distrib,ownSum] at upper
  rw [Law.expect_add,Law.expect_sum,Law.expect_sum] at upper
  have marginal (y : V) := expect_coord μ y (fun a ↦ (repairLoad G C L i y a:ℝ))
  simpa only [marginal,expect_coord] using upper

/-- One incidence charge per original ordered target edge; the second point of
the edge is the representative in the source row. -/
private def fromRow (G : SimpleGraph V) (D C : Finset V) (o : State V) : ℝ :=
  ∑ e ∈ RepresentativeCut.cut G D C, RepresentativeCut.atom e.2 o

omit [Fintype V] in
private theorem fromRow_nonneg (G : SimpleGraph V) (D C : Finset V) (o : State V) :
    0 ≤ fromRow G D C o := sum_nonneg fun e _ ↦ by unfold RepresentativeCut.atom; split <;> norm_num

omit [Fintype V] in
private theorem fromRow_chosen (G : SimpleGraph V) (D C : Finset V) {z : V} (hz : z ∈ C) :
    fromRow G D C (some (some z)) = SameRowConflicts.degree G D z := by
  unfold fromRow RepresentativeCut.cut SameRowConflicts.degree
  rw [sum_filter,sum_product,card_filter,Nat.cast_sum]
  apply sum_congr rfl
  intro y _
  by_cases edge : G.Adj z y
  · have single (v : V) : (if G.Adj y v then RepresentativeCut.atom v (some (some z)) else 0) =
        if v=z then (1:ℝ) else 0 := by
      by_cases same : v=z
      · subst v; simp [G.adj_symm edge,RepresentativeCut.atom]
      · simp [RepresentativeCut.atom,same,Ne.symm same]
    simp [edge,single,hz]
  · have zero (v : V) : (if G.Adj y v then RepresentativeCut.atom v (some (some z)) else 0) = 0 := by
      by_cases same : v=z
      · subst v
        exact ite_eq_right (show ¬ G.Adj y z from fun h ↦ edge (G.adj_symm h))
      · simp [RepresentativeCut.atom,Ne.symm same]
    simp [edge,zero]

private theorem fromRow_mean (G : SimpleGraph V) (D C : Finset V) (ν : Law (State V)) {c : ℝ}
    (cap : ∀ z ∈ C, ν.weight (some (some z)) ≤ c) :
    ν.expect (fromRow G D C) ≤ c*((RepresentativeCut.cut G D C).card:ℝ) := by
  unfold fromRow
  rw [Law.expect_sum]
  calc
    _ ≤ ∑ _e ∈ RepresentativeCut.cut G D C, c := by
      apply sum_le_sum
      intro e he
      have atom : ν.expect (RepresentativeCut.atom e.2) = ν.weight (some (some e.2)) := by
        convert ν.expect_atom (some (some e.2)) using 2
        funext o
        by_cases hit : o = some (some e.2) <;> simp [RepresentativeCut.atom,hit]
      exact atom.le.trans (cap e.2 (mem_product.mp (mem_filter.mp he).1).2)
    _ = _ := by simp [mul_comm]

/-- The F_i appearing in the load estimate satisfies the same-edge bound
F_i ≤ (j/r) ∑_{k ≠ i} N_k e_ik under the original coloring's own sender law. -/
theorem foreign_load_le_interrow_cut (T : Trace V r) {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let I := S.retained
    let U := uniqueGroup T E I S.s
    let μ := senderLaw T E I S.s p rate hp hp1
    (∑ y, (μ y).expect (foreignDegree G C i)) ≤
      (representativeFactor X/r) * ∑ k ∈ I.erase i, ((U k).card:ℝ)*((RepresentativeCut.cut G (C i) (C k)).card:ℝ) := by
  intro G C I U μ
  let charge := fun k (y : V) o ↦ if y ∈ U k then fromRow G (C i) (C k) o else 0
  have nonneg (k) (y : V) (o : State V) : 0 ≤ charge k y o := by
    dsimp only [charge]
    split
    · exact fromRow_nonneg ..
    · exact le_rfl
  have point (w : V → State V) (positive : 0 < (product μ).weight w) (y : V) :
      foreignDegree G C i (w y) ≤ ∑ k ∈ I.erase i, charge k y (w y) := by
    have pos := sum_nonneg (s:=I.erase i) fun k _ ↦ nonneg k y (w y)
    cases val : w y with
    | none => simpa only [val,foreignDegree] using pos
    | some a =>
      cases a with
      | none => simpa only [val,foreignDegree] using pos
      | some z =>
        by_cases own : z ∈ C i
        · simpa only [val,foreignDegree,ite_eq_left own] using pos
        · obtain ⟨k,hk,hy,hz,_⟩ := represented_support T positive val
          have ne : k ≠ i := fun eq ↦ own (eq ▸ hz)
          have le := single_le_sum (s:=I.erase i) (f:=fun k ↦ charge k y (some (some z)))
            (fun k _ ↦ nonneg k y _) (mem_erase.mpr ⟨ne,hk⟩)
          have member : y ∈ U k := hy
          simpa only [foreignDegree,ite_eq_right own,charge,ite_eq_left member,fromRow_chosen G (C i) (C k) hz] using le
  have upper := support_mono (product μ) fun w pos ↦ sum_le_sum (s:=univ) fun y _ ↦ point w pos y
  rw [Law.expect_sum] at upper
  simp only [expect_coord] at upper
  apply upper.trans
  have order (w : V → State V) : (∑ y, ∑ k ∈ I.erase i, charge k y (w y)) =
      ∑ k ∈ I.erase i, ∑ y ∈ U k, fromRow G (C i) (C k) (w y) := by
    rw [sum_comm]
    simp [charge]
  simp_rw [order,Law.expect_sum,expect_coord]
  rw [mul_sum]
  apply sum_le_sum
  intro k _
  let a := representativeFactor X/r
  let edges := ((RepresentativeCut.cut G (C i) (C k)).card:ℝ)
  calc
    _ ≤ ∑ _y ∈ U k, a*edges := by
      apply sum_le_sum
      intro y hy
      apply fromRow_mean
      exact fun z _ ↦ sender_atom_bound T S hr X lo hi width p rate hp hp1 hy z
    _ = _ := by simp [a,edges]; ring

end
end Erdos617.ColoredLists
