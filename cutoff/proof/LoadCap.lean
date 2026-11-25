import SenderSupport
import RepairedIndependence

/-! The pruning threshold and the exact support of the sender law bound
each sender's own and represented load on every outcome of positive mass. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem list_member {E : Finset V} {i : ℕ} {x : V} (hx : x ∈ rowList T E i) :
    x ∈ live T ∧ T.row x = i := by
  simp only [rowList,PackingLists.available,mem_filter] at hx
  exact ⟨hx.1,hx.2.1⟩

/-- An actual representative has at most r/4 target neighbors in each
other retained row. This uses the first stopping rule before further pruning. -/
theorem foreign_representative_degree (prep : Prepared T) {E : Finset V} {i k : ℕ}
    (hi : i ∈ qualifying T) (diff : k ≠ i) {a : V} (ha : a ∈ rowList T E k) :
    4*((rowList T E i).filter ((targetGraph T.color T.target).Adj a)).card ≤ r := by
  apply le_trans _ (prep.first_stopped.live_bound (list_member T ha).1 hi)
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro y hy
  obtain ⟨inC,adj⟩ := mem_filter.mp hy
  obtain ⟨surv,label⟩ := list_member T inC
  refine mem_filter.mpr ⟨surv,?_,label⟩
  rw [← cross_target]
  exact ⟨by simpa only [(list_member T ha).2,label] using diff,adj⟩

/-- Every load on a positive-weight outcome fits the circle of circumference
3r/4. The three bounds used here are actual degrees of exterior vertices,
their output vertices, and low exterior vertices. -/
theorem sender_load_fits (prep : Prepared T) {E : Finset V} {I : Finset ℕ} {s : ℕ}
    (qual : I ⊆ qualifying T) (hs : 1 ≤ s) {p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E I s p rate hp hp1)).weight w)
    {i : ℕ} (hi : i ∈ I) (x : V) :
    4*repairLoad (targetGraph T.color T.target) (rowList T E) (lowExterior T E I s) i x (w x) ≤ 3*r := by
  let degree := fun y ↦ ((rowList T E i).filter ((targetGraph T.color T.target).Adj y)).card
  have half (h : i ∉ strongRows T E I x) : 2*degree x ≤ r := by
    have cap : (degree x:ℝ) ≤ (r:ℝ)/2 := le_of_not_gt fun hbad ↦ h (mem_filter.mpr ⟨hi,hbad⟩)
    exact_mod_cast (show 2*(degree x:ℝ) ≤ r by linarith only [cap])
  by_cases low : x ∈ lowExterior T E I s
  · have cap := (mem_filter.mp low).2.2 i hi
    have one : (1:ℝ) ≤ s := by exact_mod_cast hs
    have small : (9/40:ℝ)/s ≤ 1/2 := (div_le_iff₀ (by linarith : (0:ℝ)<s)).mpr (by linarith)
    have raw : (degree x:ℝ) ≤ (1/2:ℝ)*r := cap.trans (mul_le_mul_of_nonneg_right small (Nat.cast_nonneg _))
    have m : 2*degree x ≤ r := by exact_mod_cast (show 2*(degree x:ℝ) ≤ r by linarith only [raw])
    simpa only [repairLoad,ite_eq_left low] using (show 4*degree x ≤ 3*r by omega)
  · cases eq : w x with
    | none => simp [repairLoad,low]
    | some o =>
      cases o with
      | none =>
        obtain ⟨_,empty⟩ := moderate_support T positive eq
        have m := half (by simp [empty])
        simpa only [repairLoad,ite_eq_right low] using (show 4*degree x ≤ 3*r by omega)
      | some a =>
        obtain ⟨k,_,group,ha,_⟩ := represented_support T positive eq
        by_cases same : a ∈ rowList T E i
        · simp [repairLoad,low,same]
        · have diff : k ≠ i := fun h ↦ same (h ▸ ha)
          have weak := half (by simp [(mem_filter.mp group).2,diff.symm])
          have foreign : 4*degree a ≤ r := foreign_representative_degree T prep (qual hi) diff ha
          simpa only [repairLoad,ite_eq_right low,ite_eq_right same] using
            (show 4*(degree x+degree a) ≤ 3*r by omega)

end
end Erdos617.ColoredLists
