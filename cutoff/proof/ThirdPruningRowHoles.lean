import ThirdPruningExtension
import ThirdPruningPeel
import GlobalRowBudgets

/-! Bounds for the missing edges of the original rows after a pruning pass. -/
namespace Erdos617.ThirdPruning
open Finset PackingLists PruningOverlap ColoredLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

/-- The orientation is from a deleted vertex to a surviving vertex, in the same raw row. -/
def holes (G : SimpleGraph V) (row : V → ℕ) (A : Finset V) :=
  (((univ \ A) ×ˢ A) : Finset (V × V)).filter fun uv ↦ row uv.1 = row uv.2 ∧ Gᶜ.Adj uv.1 uv.2

private theorem hole_mem {G : SimpleGraph V} {row : V → ℕ} {A : Finset V} {uv : V × V}
    (mem : uv ∈ holes G row A) :
    uv.1 ∈ univ \ A ∧ uv.2 ∈ A ∧ row uv.1 = row uv.2 ∧ uv.1 ≠ uv.2 ∧ ¬G.Adj uv.1 uv.2 := by
  obtain ⟨hp,eq,adj⟩ := mem_filter.mp mem
  exact ⟨(mem_product.mp hp).1,(mem_product.mp hp).2,eq,(SimpleGraph.compl_adj ..).mp adj⟩

/-- Both versions of (8) before division by r². The supplied budget is just
the sum of the positive excesses of the deleted degrees into A. -/
theorem charge_actual_holes (G : SimpleGraph V) (row : V → ℕ) (A : Finset V) {r : ℕ}
    (rows : ∀ x, row x < r) (cap : ∀ R : Finset V, G.IsIndepSet (R : Set V) → R.card ≤ r)
    {L M N τ c σ : ℝ} (pos : 0 < L)
    (floor : ∀ i < r, L ≤ ((A.filter fun v ↦ row v = i).card : ℝ))
    (live_cap : ∀ i < r, ((A.filter fun v ↦ row v = i).card : ℝ) ≤ M)
    (removed_cap : ∀ i < r, (((univ \ A).filter fun v ↦ row v = i).card : ℝ) ≤ N)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (stopped : ∀ w ∈ A, deg (cross G row) A w ≤ c)
    (excess : (∑ x ∈ univ \ A, max (deg (cross G row) A x-τ) 0) ≤ σ) :
    let E := edges (cross G row) A
    let H : ℝ := (holes G row A).card
    (L-E/L-τ)*H ≤ M*σ+N*(2*E) ∧ (L-E/L-τ-c)*H ≤ M*σ := by
  classical
  let Z := holes G row A
  let D := deg (cross G row) A
  let X := fun x ↦ max (D x-τ) 0
  let E := edges (cross G row) A
  have src (uv) (h : uv ∈ Z) := (hole_mem h).1
  have dst (uv) (h : uv ∈ Z) := (hole_mem h).2.1
  have srcCap (x : V) (_hx : x ∈ univ \ A) : ((Z.filter fun uv ↦ uv.1=x).card : ℝ) ≤ M := by
    apply le_trans _ (live_cap _ (rows x))
    exact_mod_cast (card_le_card_of_injOn Prod.snd (s:=Z.filter fun uv ↦ uv.1=x)
      (t:=A.filter fun v ↦ row v=row x) (by
        intro uv h
        obtain ⟨hm,eq⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨dst _ hm,eq ▸ (hole_mem hm).2.2.1.symm⟩)
      (by intro v hv w hw eq; exact Prod.ext ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm) eq))
  have dstCap (w : V) (_hw : w ∈ A) : ((Z.filter fun uv ↦ uv.2=w).card : ℝ) ≤ N := by
    apply le_trans _ (removed_cap _ (rows w))
    exact_mod_cast (card_le_card_of_injOn Prod.fst (s:=Z.filter fun uv ↦ uv.2=w)
      (t:=(univ \ A).filter fun v ↦ row v=row w) (by
        intro uv h
        obtain ⟨hm,eq⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨src _ hm,eq ▸ (hole_mem hm).2.2.1⟩)
      (by intro v hv w hw eq; exact Prod.ext eq ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)))
  have per (uv) (hm : uv ∈ Z) : L-E/L-τ ≤ X uv.1+D uv.2 := by
    obtain ⟨_,_,eq,ne,miss⟩ := hole_mem hm
    have h := hole_blocks_other_rows G row A pos floor cap ne eq.symm (rows uv.1) miss
    have mx := le_max_left (D uv.1-τ) (0:ℝ)
    change L-E/L ≤ D uv.1+D uv.2 at h
    dsimp only [X]
    linarith only [h,mx]
  have nonneg (w : V) (_ : w ∈ A) : 0 ≤ D w := Nat.cast_nonneg _
  have one := hole_charge Z (univ \ A) A Prod.fst Prod.snd X D _ M N src dst
    (fun _ _ ↦ le_max_right ..) nonneg srcCap dstCap per
  have two := hole_charge Z (univ \ A) A Prod.fst Prod.snd X (fun _ ↦ 0) (L-E/L-τ-c) M N
    src dst (fun _ _ ↦ le_max_right ..) (fun _ _ ↦ le_rfl) srcCap dstCap (by
      intro uv h
      have bound : D uv.2 ≤ c := stopped _ (dst _ h)
      linarith only [per uv h,bound])
  have pos := mul_le_mul_of_nonneg_left excess hM
  change M*(∑ x ∈ univ \ A, X x) ≤ M*σ at pos
  have tot : ∑ w ∈ A, D w = 2*E := sum_deg ..
  rw [tot] at one
  simp only [sum_const_zero,mul_zero,add_zero] at two
  dsimp only
  constructor <;> linarith only [one,two,pos]

end
end Erdos617.ThirdPruning
