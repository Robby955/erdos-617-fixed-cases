import GraphPartitionCount
import SparseColorCount

/-! Direct square-mass bounds on the exterior auxiliary graph, Appendix A §4. -/

namespace Erdos617.AuxiliaryMoments

open Finset RowExtraction GraphPartitionCount ColoredLists PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V]

/-- Adjacent integer tangents to s(s-1). Both hold even for empty rows. -/
private theorem integer_tangents (s h : ℕ) :
    (h:ℝ)*(h-1)+2*((h:ℝ)-1)*((s:ℝ)-h) ≤ (s:ℝ)*(s-1) ∧
    (h:ℝ)*(h-1)+2*h*((s:ℝ)-h) ≤ (s:ℝ)*(s-1) := by
  by_cases eq : s = h
  · subst s; simp
  · by_cases lt : s < h
    · have le : (s:ℝ)+1 ≤ h := by exact_mod_cast (show s+1 ≤ h by omega)
      constructor <;> nlinarith only [mul_nonneg (show (0:ℝ) ≤ h-s by linarith)
        (show (0:ℝ) ≤ h-s-1 by linarith),le]
    · have le : (h:ℝ)+1 ≤ s := by exact_mod_cast (show h+1 ≤ s by omega)
      constructor <;> nlinarith only [mul_nonneg (show (0:ℝ) ≤ s-h by linarith)
        (show (0:ℝ) ≤ s-h-1 by linarith),le]

/-- A color with independence at most r meets both integer edge floors near
order hr. The pivot rows give the floor for any possible row sizes. -/
theorem tangent_floor (G : SimpleGraph V) (r h : ℕ) (b : ℝ)
    (order : (Fintype.card V:ℝ) = h*r+b)
    (cap : ∀ S : Finset V, G.IsIndepSet (S:Set V) → S.card ≤ r) :
    (r:ℝ)*h*(h-1)+2*((h:ℝ)-1)*b ≤ 2*(G.edgeFinset.card:ℝ) ∧
    (r:ℝ)*h*(h-1)+2*h*b ≤ 2*(G.edgeFinset.card:ℝ) := by
  obtain ⟨row,inRange,pivots⟩ := exists_ordered_rows Gᶜ r univ
    (fun S _ cl ↦ cap S (by simpa using cl))
  have cover (x : V) := inRange x (mem_univ _)
  have paid := pivot_edge_budget G row r cover pivots
  have parts : (∑ i ∈ range r, (size row i:ℝ)) = Fintype.card V := by exact_mod_cast sum_sizes row r cover
  have dev : (∑ i ∈ range r, ((size row i:ℝ)-h)) = b := by
    rw [Finset.sum_sub_distrib,parts,order]
    simp
    ring
  have summed (a : ℝ) (each : ∀ i ∈ range r, (h:ℝ)*(h-1)+a*((size row i:ℝ)-h) ≤
      (size row i:ℝ)*((size row i:ℝ)-1)) :
      (r:ℝ)*h*(h-1)+a*b ≤ 2*(G.edgeFinset.card:ℝ) := by
    have sum := Finset.sum_le_sum each
    rw [Finset.sum_add_distrib,← Finset.mul_sum (a := a),dev] at sum
    simp only [sum_const,card_range,nsmul_eq_mul] at sum
    linarith only [sum,paid,Nat.cast_nonneg (α := ℝ) (cross G row).edgeFinset.card]
  exact ⟨summed _ (fun i _ ↦ (integer_tangents (size row i) h).1),
    summed _ (fun i _ ↦ (integer_tangents (size row i) h).2)⟩

/-- On hr+b auxiliary vertices the cross edges and the squared deviations of
all h target rows share one budget. The two tangents give separate signed rebates. -/
theorem auxiliary_square_budget (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (h : ℕ) (b : ℝ) (order : (Fintype.card V:ℝ) = h*r+b)
    (other : ∀ k ≠ j, ∀ S : Finset V, (targetGraph color k).IsIndepSet (S:Set V) → S.card ≤ r)
    (row : V → ℕ) (labels : ∀ x, row x < h)
    (pivots : ∀ i < h, RowStep (targetGraph color j)ᶜ (fiber univ row i) (laterRows univ row i)) :
    ((cross (targetGraph color j) row).edgeFinset.card:ℝ) +
      (∑ i ∈ range h, ((size row i:ℝ)-r)^2) ≤
      (r:ℝ)*h*(h-1)+b^2+min (2*((h:ℝ)-1)*b) (2*((h:ℝ)-r)*b) := by
  let e := fun k ↦ ((targetGraph color k).edgeFinset.card:ℝ)
  let n := Fintype.card V
  have hsum : 2*(∑ k, e k) = (n:ℝ)*((n:ℝ)-1) := by
    unfold e
    rw [← Nat.cast_sum,edge_color_partition]
    change 2*(n.choose 2:ℝ) = _
    have exactN : 2*n.choose 2 = n*(n-1) := by
      rw [Nat.mul_comm, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
    have pred (k : ℕ) : (k:ℝ)*(↑(k-1:ℕ):ℝ) = (k:ℝ)*((k:ℝ)-1) := by cases k <;> simp
    calc 2*(n.choose 2:ℝ) = (n:ℝ)*(↑(n-1:ℕ):ℝ) := by exact_mod_cast exactN
         _ = _ := pred n
  have parts : (∑ i ∈ range h, (size row i:ℝ)) = Fintype.card V := by exact_mod_cast sum_sizes row h labels
  have dev : (∑ i ∈ range h, ((size row i:ℝ)-r)) = b := by
    rw [Finset.sum_sub_distrib,parts,order]
    simp
  have expand : (∑ i ∈ range h, (size row i:ℝ)*((size row i:ℝ)-1)) =
      (∑ i ∈ range h, ((size row i:ℝ)-r)^2)+(2*(r:ℝ)-1)*b+h*r*((r:ℝ)-1) := by
    have each (i) : (size row i:ℝ)*((size row i:ℝ)-1) =
        ((size row i:ℝ)-r)^2+(2*(r:ℝ)-1)*((size row i:ℝ)-r)+(r:ℝ)*(r-1) := by ring
    simp_rw [each,Finset.sum_add_distrib,← Finset.mul_sum,dev]
    simp
    ring
  have budget := pivot_edge_budget (targetGraph color j) row h labels pivots
  rw [expand] at budget
  have hr : 0 < r := Nat.zero_lt_of_lt j.isLt
  have minus : (((univ.erase j).card:ℕ):ℝ) = (r:ℝ)-1 := by
    rw [card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin,Nat.cast_sub (by omega),Nat.cast_one]
  have colsum : (∑ k ∈ univ.erase j, 2*e k)+2*e j = (h*(r:ℝ)+b)*(h*r+b-1) := by
    rw [sum_erase_add _ _ (mem_univ j),← Finset.mul_sum,hsum]
    rw [show (n:ℝ) = h*r+b from order]
  have upper (a : ℝ) (floor : ∀ k ≠ j, (r:ℝ)*h*(h-1)+a*b ≤ 2*e k) :
      ((r:ℝ)-1)*((r:ℝ)*h*(h-1)+a*b)+2*e j ≤ (h*(r:ℝ)+b)*(h*r+b-1) := by
    rw [← colsum]
    apply add_le_add_left
    have sum := Finset.sum_le_sum (s := univ.erase j) (fun k hk ↦ floor k (mem_erase.mp hk).1)
    simpa only [sum_const,nsmul_eq_mul,minus] using sum
  have floors (k) (ne : k ≠ j) := tangent_floor (targetGraph color k) r h b order (other k ne)
  have lo := upper _ fun k ne ↦ (floors k ne).1
  have hi := upper _ fun k ne ↦ (floors k ne).2
  dsimp [e] at lo hi
  rw [add_min]
  apply le_min <;> nlinarith only [budget,lo,hi]

/-- For the selected scale, h²/r is below the allowance 2⁻²⁰. -/
theorem scale_facts {r s : ℕ} {Y exp α β : ℝ} (band : RetainedWidth.Band Y exp α β)
    (slo : 1120 ≤ s) (scale : (2:ℝ)^exp*(s:ℝ)^4 < r) :
    7 ≤ r ∧ 1 ≤ s-1 ∧ s-1 ≤ r ∧ (2:ℝ)^20*((s-1:ℕ):ℝ)^2 < r := by
  have hs : (1120:ℝ) ≤ s := by exact_mod_cast slo
  have base : (16384:ℝ) ≤ (2:ℝ)^exp := by cases band <;> norm_num
  have big := lt_of_le_of_lt (mul_le_mul_of_nonneg_right base (by positivity)) scale
  have pow : (64:ℝ) ≤ (s:ℝ)^2 := by nlinarith only [sq_nonneg ((s:ℝ)-8),hs]
  have mult := mul_le_mul_of_nonneg_right pow (sq_nonneg (s:ℝ))
  have sh : ((s-1:ℕ):ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
  have sh2 := sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) (s-1)] : -(s:ℝ) ≤ ((s-1:ℕ):ℝ)) sh
  have large : (1048576:ℝ)*(s:ℝ)^2 < r := by linarith only [mult,big]
  have sr : (s:ℝ) ≤ r := by nlinarith only [large,pow,hs,sq_nonneg ((s:ℝ)-1)]
  exact ⟨by exact_mod_cast (show (7:ℝ) ≤ r by linarith),by omega,
    by exact_mod_cast (le_trans sh sr),by norm_num; linarith only [large,sh2]⟩

/-- The combined normalized auxiliary budget. Every initial row below r is
charged its squared deficit and every cross edge is charged once. -/
theorem auxiliary_normalized {W : Type*} [Fintype W] {r s : ℕ} {b Y exp α β : ℝ}
    (G : SimpleGraph W) (row : W → ℕ) (band : RetainedWidth.Band Y exp α β)
    (slo : 1120 ≤ s) (scale : (2:ℝ)^exp*(s:ℝ)^4 < r)
    (lo : -(3/20:ℝ)*r ≤ b) (hi : b ≤ 1)
    (budget : ((cross G row).edgeFinset.card:ℝ) + (∑ i ∈ range (s-1), ((size row i:ℝ)-r)^2) ≤
      (r:ℝ)*((s-1:ℕ):ℝ)*(((s-1:ℕ):ℝ)-1)+b^2+
      min (2*(((s-1:ℕ):ℝ)-1)*b) (2*(((s-1:ℕ):ℝ)-r)*b)) :
    ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range (s-1), (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20 := by
  obtain ⟨r7,hl,hr,hsmall⟩ := scale_facts band slo scale
  let h : ℝ := (s-1:ℕ)
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have r7' : (7:ℝ)≤r := by exact_mod_cast r7
  have h1 : 1 ≤ h := by dsimp [h]; exact_mod_cast hl
  have hr' : h ≤ r := by dsimp [h]; exact_mod_cast hr
  have rebate : min (2*(h-1)*b) (2*(h-r)*b) ≤ 0 := by
    by_cases sign : b ≤ 0
    · exact (min_le_left ..).trans (mul_nonpos_of_nonneg_of_nonpos (by linarith) sign)
    · exact (min_le_right ..).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_not_ge sign))
  have b2 : b^2 ≤ ((3/20:ℝ)*r)^2 := sq_le_sq' (by linarith) (by linarith)
  have rowBound (i : ℕ) : (max (1-(size row i:ℝ)/r) 0)^2*(r:ℝ)^2 ≤ ((size row i:ℝ)-r)^2 := by
    by_cases low : 0 ≤ 1-(size row i:ℝ)/r
    · rw [max_eq_left low, ← mul_pow]
      have clear : (1-(size row i:ℝ)/r)*r = (r:ℝ)-size row i := by field_simp
      rw [clear,sub_sq_comm]
    · rw [max_eq_right (le_of_not_ge low)]
      simpa using sq_nonneg ((size row i:ℝ)-r)
  have sum := sum_le_sum (s := range (s-1)) fun i _ ↦ rowBound i
  rw [← Finset.sum_mul] at sum
  have small : (2:ℝ)^20*h^2 < r := hsmall
  have small' := mul_le_mul_of_nonneg_right small.le rp.le
  change _ ≤ (r:ℝ)*h*(h-1)+b^2+min (2*(h-1)*b) (2*(h-r)*b) at budget
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos rp)
  rw [add_mul,div_mul_cancel₀ _ (by positivity)]
  nlinarith only [sum,budget,b2,rebate,small',mul_nonneg rp.le (show 0 ≤ h by linarith)]

end
end Erdos617.AuxiliaryMoments
