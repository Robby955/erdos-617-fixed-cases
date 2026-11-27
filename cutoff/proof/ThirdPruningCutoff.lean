import ThirdPruningPaired
import ThirdPruningFloor

/-! The third-pass cutoff, starting from an arbitrary edge coloring. -/
namespace Erdos617
open Finset ColoredLists PackingLists PruningOverlap ThirdPruning
open scoped Classical
noncomputable section

theorem missing_color_at_143 {V : Type*} [Fintype V] {r : ℕ}
    (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 2^143 ≤ r) (order : Fintype.card V=r^2+1) : Witness color := by
  by_contra none
  obtain ⟨T,eq,pr⟩ := (witness_or_pruned color (by omega)).resolve_left none
  have no : ¬ Witness T.color := eq ▸ none
  have rp : 0<r := by omega
  have rp' : (0:ℝ)<r := by exact_mod_cast rp
  obtain ⟨v0,vc,pc,rates⟩ := raw_fractions T pr no (by omega) order
  have p0 : 0 ≤ firstRate T := div_nonneg (Nat.cast_nonneg _) rp'.le
  have t0 : 0 ≤ secondRate T := div_nonneg (Nat.cast_nonneg _) rp'.le
  obtain ⟨b,α,β,band,_⟩ := RetainedWidth.width_for_every_pruning_pair p0 pc t0 rates
  have oldZero : thirdRate T (live T)=0 := by simp [thirdRate]
  have oldStage : Stage T (live T) (degreeBound r) (199/400) := by
    have edges : 400*degreeBound r ≤ 199*r := by unfold degreeBound; omega
    have cast : (400:ℝ)*degreeBound r ≤ 199*r := by exact_mod_cast edges
    refine ⟨Subset.rfl,by simp,pr.stopped,le_rfl,by linarith only [cast],le_rfl,?_,?_⟩ <;>
      dsimp only [mass] <;> rw [oldZero] <;> linarith only [pc,rates]
  obtain ⟨oldE,oldList⟩ := Stage.lists T oldStage pr (by omega) order no
  have failed := stage_failure T oldStage pr hr order no oldList band
  rw [oldZero] at failed
  have old : margin (firstRate T) (secondRate T) b α β+2*spentFraction T/α ≤ 0 := by
    norm_num at failed
    exact failed
  obtain ⟨A,pass⟩ := exists_pass T pr.legal
  obtain ⟨slack,_⟩ := normalized_cost T pass rp
  have spent : spentFraction T+survivingFraction T A+(9/25)*thirdRate T A ≤ remaining T := by
    linarith only [slack]
  obtain ⟨paired,size⟩ := paired_margin p0 pc t0 (z:=remaining T) (by rfl) (v0.trans vc)
    (show 0 ≤ survivingFraction T A from div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) spent band old
  let Δ := 9*r/25
  have stage : Stage T A Δ (9/25) := by
    have dnat : 25*Δ ≤ 9*r := by dsimp only [Δ]; omega
    have dreal : (25:ℝ)*Δ ≤ 9*r := by exact_mod_cast dnat
    refine ⟨pass.sub,pass.removed,?_,by dsimp only [Δ,degreeBound]; omega,
      by linarith only [dreal],by norm_num,?_,?_⟩
    · intro x hx
      have s : (deg T.crossGraph A x)*25 ≤ 9*r := by linarith only [pass.stop x hx]
      change ((Transversal.neighbors T.crossGraph A x).card:ℝ)*25 ≤ 9*r at s
      have n : (Transversal.neighbors T.crossGraph A x).card*25 ≤ 9*r := by exact_mod_cast s
      dsimp [Δ]; omega
    · unfold mass; linarith only [size]
    · unfold mass; linarith only [size]
  obtain ⟨E,data⟩ := Stage.lists T stage pr (by omega) order no
  by_cases empty : E = ∅
  · subst E
    exact clique_case_impossible T pass pr no (by omega) order (empty_cliques T pass.sub data)
      band old (zero_width_deficit T stage pr hr order no data band)
  · have q : (1:ℝ) ≤ (E.image T.row).card := by
      exact_mod_cast card_pos.mpr ((nonempty_iff_ne_empty.mpr empty).image T.row)
    have fails := stage_failure T stage pr hr order no data band
    cases band <;> linarith only [fails,paired,q]

/-- The statement on unordered pairs allows arbitrary values on diagonal pairs. -/
theorem erdos_617_of_ge_two_pow_143 {r : ℕ} (hr : 2^143 ≤ r) {V : Type*} [Fintype V]
    (order : Fintype.card V=r^2+1) (coloring : Sym2 V → Fin r) :
    ∃ (vertices : Finset V) (missing : Fin r), vertices.card=r+1 ∧
      ∀ x ∈ vertices, ∀ y ∈ vertices, x ≠ y → coloring s(x,y) ≠ missing :=
  missing_color_at_143 (fun edge ↦ coloring edge.val) hr order

theorem balancedColoringAt_of_ge_two_pow_143 (r : ℕ) (hr : 2^143 ≤ r) : BalancedColoringAt r :=
  (balanced_iff r).mpr fun color ↦ missing_color_at_143 color hr (Fintype.card_fin _)

end
end Erdos617
