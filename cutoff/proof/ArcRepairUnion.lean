import ExcessArcRepairs

/-! One common finite start space for all retained rows. Repeated repair edges
in different rows enter the union graph only once. -/

namespace Erdos617.ArcRepair

open Finset FiniteLaw ExcessCircle
open scoped Classical
noncomputable section
variable {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω]

def graphUnion (rows : Finset J) (g : J → SimpleGraph I) : SimpleGraph I where
  Adj x y := ∃ j ∈ rows, (g j).Adj x y
  symm := ⟨by rintro _ _ ⟨j,hj,adj⟩; exact ⟨j,hj,(g j).adj_symm adj⟩⟩
  loopless := ⟨by rintro i ⟨j,_,adj⟩; exact (g j).loopless.irrefl i adj⟩

omit [Fintype J] in
theorem graphUnion_count (rows : Finset J) (g : J → SimpleGraph I) :
    (graphUnion rows g).edgeFinset.card ≤ ∑ j ∈ rows, (g j).edgeFinset.card := by
  have sub : (graphUnion rows g).edgeFinset ⊆ rows.biUnion (fun j ↦ (g j).edgeFinset) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro h
      obtain ⟨j,hj,a⟩ := SimpleGraph.mem_edgeFinset.mp h
      exact mem_biUnion.mpr ⟨j,hj,SimpleGraph.mem_edgeFinset.mpr a⟩
  exact (card_le_card sub).trans (card_biUnion_le ..)

def expectedUnion (μ : I → Law Ω) (N : ℕ) [NeZero N] (rows : Finset J)
    (len : J → I → Ω → ℕ) : ℝ :=
  (product μ).expect fun w ↦
    (product fun _ : J ↦ starts I N).expect fun z ↦
      ((graphUnion rows fun j ↦ graph (z j) (fun i ↦ len j i (w i))).edgeFinset.card:ℝ)

theorem expected_union_le (μ : I → Law Ω) (N : ℕ) [NeZero N] (rows : Finset J)
    (len : J → I → Ω → ℕ) :
    expectedUnion μ N rows len ≤ ∑ j ∈ rows, expectedEdges μ N (len j) := by
  let stat (j : J) (w : I → Ω) (z : I → ZMod N) :=
    ((graph z (fun i ↦ len j i (w i))).edgeFinset.card:ℝ)
  let ν := product fun _ : J ↦ starts I N
  have localBound (w : I → Ω) : ν.expect (fun z ↦ ((graphUnion rows
      fun j ↦ graph (z j) (fun i ↦ len j i (w i))).edgeFinset.card:ℝ)) ≤
      ∑ j ∈ rows, (starts I N).expect (stat j w) := by
    have per (z : J → I → ZMod N) : ((graphUnion rows
        fun j ↦ graph (z j) (fun i ↦ len j i (w i))).edgeFinset.card:ℝ) ≤
        ∑ j ∈ rows, stat j w (z j) := by
      dsimp only [stat]
      exact_mod_cast graphUnion_count rows (fun j ↦ graph (z j) (fun i ↦ len j i (w i)))
    have upper := ν.expect_mono per
    rw [Law.expect_sum] at upper
    simpa only [ν,expect_coord] using upper
  have upper := (product μ).expect_mono localBound
  rw [Law.expect_sum] at upper
  exact upper

/-- The arc term 4(Q−H)/3, with Q and H evaluated on the actual local
loads of each row. The expectation counts distinct edges on a single sample,
irrespective of how many rows create each collision. -/
theorem expected_excess_union (μ : I → Law Ω) (s r : ℕ) (hs : 0<s) (hr : 0<r)
    (rows : Finset J) (load : J → I → Ω → ℕ) :
    letI : NeZero (30*s*r) := ⟨by positivity⟩
    let n := fun j ↦ ∑ i, (μ i).expect (fun a ↦ active (excess s r (load j i a)))
    let L := fun j ↦ ∑ i, (μ i).expect (fun a ↦ (load j i a:ℝ))
    expectedUnion μ (30*s*r) rows (fun j i a ↦ excess s r (load j i a)) ≤
      (4/3:ℝ)*((∑ j ∈ rows, n j*L j/r)-(9/40:ℝ)/s*(∑ j ∈ rows, (n j)^2)) := by
  let _ : NeZero (30*s*r) := ⟨by positivity⟩
  let n := fun j ↦ ∑ i, (μ i).expect (fun a ↦ active (excess s r (load j i a)))
  let L := fun j ↦ ∑ i, (μ i).expect (fun a ↦ (load j i a:ℝ))
  have upper := sum_le_sum (s:=rows) fun j _ ↦ expected_excess_edges μ s r hs hr (load j)
  apply (expected_union_le μ (30*s*r) rows _).trans (upper.trans_eq ?_)
  change (∑ j ∈ rows, (4/3:ℝ)/r*n j*(L j-9/40/s*r*n j)) = _
  rw [mul_sum,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro j _
  have rp : (0:ℝ)<r := by exact_mod_cast hr
  field_simp
  ring

end
end Erdos617.ArcRepair
