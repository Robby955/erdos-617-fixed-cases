import CertifiedWidthCell

/-! End-to-end large-order theorem for the Erdős–Gyárfás balanced-coloring conjecture. -/

namespace Erdos617
open Finset PruningOverlap PackingLists ColoredLists CutoffCells
open scoped Classical
noncomputable section

/-- Finishing the signed cut only requires a width selection on the cliques
from the same trace. Its scale may come from any pruning argument. -/
theorem contradiction_of_selected_rows {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)
    {Y ex α β M : ℝ} (prep : CutInputs T Y) (hr : 2^20 ≤ r)
    (no : ¬ Witness T.color) (order : Fintype.card V = r^2+1) {E : Finset V}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      (range r \ ordinaryLists T E).card (omittedCount T E) α β M)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r) : False := by
  have sub : ordinaryLists T E ⊆ range r := fun _ hi ↦
    (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card sub
  rw [card_range] at slots
  have short : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) := by
    by_contra! failed
    exact excludes_enlarged_rows T prep hr no S band scale
      (enlarged_of_failed_shortage T prep (by omega) no order S band scale slots lists failed)
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
  obtain ⟨l,l0,l1,required⟩ := coloring_signed_cut T prep (by omega) no order lists S
    band slots scale A X ra0 ra1 rx0 rx1 inc defi κ Y rk0 rk1 ry0 ry1 squares hi short
  have ends := real_endpoints i j
  change (signedEpsilon A X Y κ d.exponent 0 < 1 ∧ 0 < signedMargin A X Y κ d.exponent 0) ∧
    (signedEpsilon A X Y κ d.exponent ((501/1000)*κ) < 1 ∧
      0 < signedMargin A X Y κ d.exponent ((501/1000)*κ)) at ends
  rw [← exp_eq] at ends
  obtain ⟨eps,pos⟩ := signed_interval ra0 ra1 rx0 rx1 rk0 rk1 l0 l1 ends.1 ends.2
  exact (not_lt_of_ge (required eps)) pos

/-- An arbitrary coloring on r²+1 vertices has r+1 vertices missing a color
whenever r is at least the improved cutoff. -/
theorem missing_color_of_large_order {V : Type*} [Fintype V] {r : ℕ}
    (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1) : Witness color := by
  by_contra no
  obtain ⟨T,eq,prep⟩ := (witness_or_prepared color hr order).resolve_left no
  obtain ⟨E,lists,ex,α,β,band,S,_,scale⟩ := prep.width
  exact contradiction_of_selected_rows T prep.cutInputs (by omega) (eq ▸ no) order lists band S scale

/-- The large-r case in the encoding used by Formal Conjectures for problem 617.
Diagonal values are arbitrary because the witness compares distinct vertices. -/
theorem erdos_617_of_ge_cutoff {r : ℕ} (hr : 15*2^140 ≤ r) {V : Type*} [Fintype V]
    (order : Fintype.card V = r^2+1) (coloring : Sym2 V → Fin r) :
    ∃ (vertices : Finset V) (missing : Fin r), vertices.card = r+1 ∧
      ∀ x ∈ vertices, ∀ y ∈ vertices, x ≠ y → coloring s(x,y) ≠ missing :=
  missing_color_of_large_order (fun edge ↦ coloring edge.val) hr order

/-- The strengthened cutoff, in the balanced-coloring statement on Fin (r²+1). -/
theorem balancedColoringAt_of_ge_reduced_cutoff (r : ℕ) (hr : 15*2^140 ≤ r) :
    BalancedColoringAt r :=
  (balanced_iff r).mpr fun color ↦ missing_color_of_large_order color hr (Fintype.card_fin _)

/-- Only finitely many color counts can violate the conjecture. -/
theorem finite_counterexample_orders : {r : ℕ | 3 ≤ r ∧ ¬BalancedColoringAt r}.Finite := by
  apply (Finset.range (15*2^140)).finite_toSet.subset
  intro r h
  exact Finset.mem_range.mpr (lt_of_not_ge fun hr ↦ h.2 (balancedColoringAt_of_ge_reduced_cutoff r hr))

/-- The power-of-two theorem as stated in the November manuscript. -/
theorem paper_cutoff : CutoffStatement := fun r hr ↦
  balancedColoringAt_of_ge_reduced_cutoff r ((by decide : 15*2^140 ≤ (2:ℕ)^144).trans hr)

end
end Erdos617
