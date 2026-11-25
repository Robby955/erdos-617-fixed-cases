import CertifiedWidthCell

/-! End-to-end large-order theorem for the Erdős–Gyárfás balanced-coloring conjecture. -/

namespace Erdos617
open Finset PruningOverlap PackingLists ColoredLists CutoffCells
open scoped Classical
noncomputable section

/-- An arbitrary coloring on r²+1 vertices has r+1 vertices missing a color
whenever r is at least the improved cutoff. -/
theorem missing_color_of_large_order {V : Type*} [Fintype V] {r : ℕ}
    (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 255*2^136 ≤ r) (order : Fintype.card V = r^2+1) : Witness color := by
  by_contra no
  obtain ⟨T,eq,prep,E,lists,ex,α,β,band,S,_,scale,short⟩ :=
    (witness_or_exterior_shortage color hr order).resolve_left no
  have sub : ordinaryLists T E ⊆ range r := fun _ hi ↦
    (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card sub
  rw [card_range] at slots
  obtain ⟨i,exp_eq,alpha_eq,beta_eq,hi⟩ := band_index band
  obtain ⟨j,wl,wr⟩ := locate_width S.width_pos.le S.width_lt.le
  let d := bandData i
  let A := (incidence d j:ℝ)
  let X := (deficit d j:ℝ)
  let κ := (kappa d j:ℝ)
  let Y := (d.y:ℝ)
  obtain ⟨α0,β0,a0,a1,x0,x1,k0,k1,y0,y1⟩ := cell_ranges i j
  obtain ⟨inc,defi,squares⟩ := width_envelopes d j α0 β0 wl wr
  rw [← alpha_eq] at inc
  rw [← beta_eq] at defi squares
  have ra0 : 0 ≤ A := by simpa only [Rat.cast_zero, Rat.cast_ofNat] using (Rat.cast_mono (K:=ℝ) a0)
  have ra1 : A ≤ 656/4000 := by simpa using (Rat.cast_mono (K:=ℝ) a1)
  have rx0 : 0 ≤ X := by simpa only [Rat.cast_zero, Rat.cast_ofNat] using (Rat.cast_mono (K:=ℝ) x0)
  have rx1 : X ≤ 1/2 := by simpa using (Rat.cast_mono (K:=ℝ) x1)
  have rk0 : 0 ≤ κ := by simpa only [Rat.cast_zero, Rat.cast_ofNat] using (Rat.cast_mono (K:=ℝ) k0)
  have rk1 : κ ≤ 1/4 := by simpa using (Rat.cast_mono (K:=ℝ) k1)
  have ry0 : 0 ≤ Y := by simpa only [Rat.cast_zero, Rat.cast_ofNat] using (Rat.cast_mono (K:=ℝ) y0)
  have ry1 : Y ≤ 2 := by simpa only [Rat.cast_zero, Rat.cast_ofNat] using (Rat.cast_mono (K:=ℝ) y1)
  obtain ⟨l,l0,l1,required⟩ := coloring_signed_cut T prep (by omega) (eq ▸ no) order lists S
    band slots scale A X ra0 ra1 rx0 rx1 inc defi κ Y rk0 rk1 ry0 ry1 squares hi short
  have ends := real_endpoints i j
  change (signedEpsilon A X Y κ d.exponent 0 < 1 ∧ 0 < signedMargin A X Y κ d.exponent 0) ∧
    (signedEpsilon A X Y κ d.exponent ((501/1000)*κ) < 1 ∧
      0 < signedMargin A X Y κ d.exponent ((501/1000)*κ)) at ends
  rw [← exp_eq] at ends
  obtain ⟨eps,pos⟩ := signed_interval ra0 ra1 rx0 rx1 rk0 rk1 l0 l1 ends.1 ends.2
  exact (not_lt_of_ge (required eps)) pos

/-- The large-r case in the encoding used by Formal Conjectures for problem 617.
Diagonal values are arbitrary because the witness compares distinct vertices. -/
theorem erdos_617_of_ge_cutoff {r : ℕ} (hr : 255*2^136 ≤ r) {V : Type*} [Fintype V]
    (order : Fintype.card V = r^2+1) (coloring : Sym2 V → Fin r) :
    ∃ (vertices : Finset V) (missing : Fin r), vertices.card = r+1 ∧
      ∀ x ∈ vertices, ∀ y ∈ vertices, x ≠ y → coloring s(x,y) ≠ missing :=
  missing_color_of_large_order (fun edge ↦ coloring edge.val) hr order

/-- The strengthened cutoff, in the balanced-coloring statement on Fin (r²+1). -/
theorem balancedColoringAt_of_ge_reduced_cutoff (r : ℕ) (hr : 255*2^136 ≤ r) :
    BalancedColoringAt r :=
  (balanced_iff r).mpr fun color ↦ missing_color_of_large_order color hr (Fintype.card_fin _)

/-- Only finitely many color counts can violate the conjecture. -/
theorem finite_counterexample_orders : {r : ℕ | 3 ≤ r ∧ ¬BalancedColoringAt r}.Finite := by
  apply (Finset.range (255*2^136)).finite_toSet.subset
  intro r h
  exact Finset.mem_range.mpr (lt_of_not_ge fun hr ↦ h.2 (balancedColoringAt_of_ge_reduced_cutoff r hr))

/-- The power-of-two theorem as stated in the November manuscript. -/
theorem paper_cutoff : CutoffStatement := fun r hr ↦
  balancedColoringAt_of_ge_reduced_cutoff r ((by decide : 255*2^136 ≤ (2:ℕ)^144).trans hr)

end
end Erdos617
