import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Partial independent transversals for the zero-one weight test in Appendix A, §2.
The exchange argument uses neighborhood minimization as in King's proof of a
lopsided independent transversal theorem (J. Graph Theory 67, 2011). -/

namespace Erdos617.Transversal

open Finset
open scoped Classical
noncomputable section

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- The chosen vertices are independent and lie in distinct rows. -/
structure Partial (G : SimpleGraph V) (row : V → I) (R : Finset V) : Prop where
  independent : G.IsIndepSet (R : Set V)
  distinct : Set.InjOn row (R : Set V)

variable (G : SimpleGraph V)

def neighbors (A : Finset V) (x : V) := A.filter (G.Adj x)

private def witnesses (X R : Finset V) := X.biUnion (neighbors G R)

private theorem witnesses_sub (X R : Finset V) : witnesses G X R ⊆ R := by
  intro v hv
  obtain ⟨_, _, h⟩ := mem_biUnion.mp hv
  exact (mem_filter.mp h).1

/-- A competing transversal cannot shrink any of the indicated neighborhoods
while keeping all of them inside their present sets. -/
private def Optimal (family : Finset (Finset V)) (X R : Finset V) : Prop :=
  ∀ T ∈ family, (∀ z ∈ X, neighbors G T z ⊆ neighbors G R z) →
    ∀ z ∈ X, neighbors G T z = neighbors G R z

private theorem refine_optimal (family : Finset (Finset V)) (X R : Finset V) (x : V)
    (mem : R ∈ family) (old : Optimal G family X R) :
    ∃ S ∈ family, (∀ z ∈ X, neighbors G S z = neighbors G R z) ∧
      Optimal G family (insert x X) S := by
  let choices := family.filter fun S ↦ ∀ z ∈ X, neighbors G S z = neighbors G R z
  have hr : R ∈ choices := mem_filter.mpr ⟨mem, fun _ _ ↦ rfl⟩
  obtain ⟨S,hS,hmin⟩ := choices.exists_min_image (fun T ↦ (neighbors G T x).card) ⟨R,hr⟩
  obtain ⟨hs, same⟩ := mem_filter.mp hS
  refine ⟨S,hs,same,?_⟩
  intro T hT sub z hz
  have prior := old T hT (fun v hv ↦ (sub v (mem_insert_of_mem hv)).trans (same v hv).subset)
  rcases mem_insert.mp hz with rfl | hz
  · exact Finset.eq_of_subset_of_card_le (sub _ (mem_insert_self ..))
      (hmin T (mem_filter.mpr ⟨hT,prior⟩))
  · exact (prior _ hz).trans (same _ hz).symm

omit [DecidableEq V] [DecidableEq I] in
private theorem Partial.subset {row : V → I} {R S : Finset V}
    (h : Partial G row R) (hs : S ⊆ R) : Partial G row S :=
  ⟨by intro x ha y hb hne; exact h.independent (hs ha) (hs hb) hne, h.distinct.mono hs⟩

private theorem Partial.add {row : V → I} {R : Finset V} {x : V} (h : Partial G row R)
    (isolated : ∀ y ∈ R, ¬G.Adj x y) (fresh : row x ∉ R.image row) :
    Partial G row (insert x R) := by
  constructor
  · intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | haR <;> rcases mem_insert.mp hb with rfl | hbR
    · exact (hab rfl).elim
    · exact isolated b hbR
    · exact fun e ↦ isolated a haR (G.adj_symm e)
    · exact h.independent haR hbR hab
  · intro a ha b hb he
    rcases mem_insert.mp ha with rfl | haR <;> rcases mem_insert.mp hb with rfl | hbR
    · rfl
    · exact (fresh (he.symm ▸ mem_image_of_mem row hbR)).elim
    · exact (fresh (he ▸ mem_image_of_mem row haR)).elim
    · exact h.distinct haR hbR he

private theorem covered_state (A : Finset V) (row : V → I) :
    ∃ R ⊆ A, Partial G row R ∧ ∃ X ⊆ A, ∃ Y ⊆ R, X.card ≤ Y.card ∧
      A ⊆ ((R \ Y).biUnion fun v ↦ A.filter (fun u ↦ row u = row v)) ∪
        ((X ∪ Y).biUnion (neighbors G A)) := by
  classical
  let reps := A.powerset.filter (Partial G row)
  have hnone : ∅ ∈ reps := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    ⟨by intro x hx; simp at hx, by intro x hx; simp at hx⟩⟩
  obtain ⟨M,hM,hmax⟩ := reps.exists_max_image Finset.card ⟨∅,hnone⟩
  let family := reps.filter fun R ↦ R.image row = M.image row
  have hMf : M ∈ family := mem_filter.mpr ⟨hM,rfl⟩
  have facts {R : Finset V} (hR : R ∈ family) :
      R ⊆ A ∧ Partial G row R ∧ R.image row = M.image row ∧ R.card = M.card := by
    obtain ⟨hr, hi⟩ := mem_filter.mp hR
    obtain ⟨sub, part⟩ := mem_filter.mp hr
    refine ⟨mem_powerset.mp sub, part, hi, ?_⟩
    rw [← card_image_of_injOn part.distinct, hi,
      card_image_of_injOn (mem_filter.mp hM).2.distinct]
  let states := A.powerset.filter fun X ↦ ∃ R ∈ family,
    Optimal G family X R ∧ X.card ≤ (witnesses G X R).card
  have initial : ∅ ∈ states := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    M, hMf, (by intro T hT sub z hz; simp at hz), by simp⟩
  obtain ⟨X,hX,hmaxX⟩ := states.exists_max_image Finset.card ⟨∅,initial⟩
  obtain ⟨hXA,R,hRf,optimal,hsize⟩ := mem_filter.mp hX
  have hXA' := mem_powerset.mp hXA
  obtain ⟨hRA, hR, hRI, _⟩ := facts hRf
  let Y := witnesses G X R
  have hYR : Y ⊆ R := witnesses_sub G X R
  refine ⟨R,hRA,hR,X,hXA',Y,hYR,hsize,?_⟩
  intro x hx
  by_contra outside
  have avoid (v) (hv : v ∈ X ∪ Y) : ¬G.Adj v x := fun e ↦ outside
    (mem_union_right _ (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hx,e⟩⟩))
  have blocked (y) (hy : y ∈ R) (hr : row x = row y) : y ∈ Y := by
    by_contra hy'
    exact outside (mem_union_left _ (mem_biUnion.mpr
      ⟨y,mem_sdiff.mpr ⟨hy,hy'⟩,mem_filter.mpr ⟨hx,hr⟩⟩))
  obtain ⟨S,hSf,same,opt'⟩ := refine_optimal G family X R x hRf optimal
  obtain ⟨hSA,hS,hSI,hSc⟩ := facts hSf
  have sameY : witnesses G X S = Y := Finset.biUnion_congr rfl same
  have hYS : Y ⊆ S := sameY ▸ witnesses_sub G X S
  have hasNeighbor : (neighbors G S x).Nonempty := by
    by_contra none
    have iso (y) (hy : y ∈ S) : ¬G.Adj x y := fun e ↦ none ⟨y,mem_filter.mpr ⟨hy,e⟩⟩
    by_cases present : row x ∈ S.image row
    · have inR : row x ∈ R.image row := by rw [hRI, ← hSI]; exact present
      obtain ⟨y,hyR,hrow⟩ := mem_image.mp inR
      have hy := blocked y hyR hrow.symm
      have hyS := hYS hy
      obtain ⟨z,hz,hyz⟩ := mem_biUnion.mp hy
      have hedge := (mem_filter.mp hyz).2
      have hxy : x ≠ y := fun eq ↦ avoid z (mem_union_left _ hz) (eq ▸ hedge)
      let T := insert x (S.erase y)
      have fresh : row x ∉ (S.erase y).image row := by
        rintro h
        obtain ⟨v,hv,he⟩ := mem_image.mp h
        exact (mem_erase.mp hv).1 (hS.distinct (mem_erase.mp hv).2 hyS (he.trans hrow.symm))
      have hTpart := (hS.subset G (erase_subset y S)).add G (fun v hv ↦ iso v (mem_erase.mp hv).2) fresh
      have hTI : T.image row = S.image row := by
        dsimp [T]
        rw [image_insert, ← hrow, ← image_insert, insert_erase hyS]
      have hTf : T ∈ family := mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_powerset.mpr (insert_subset hx ((erase_subset ..).trans hSA)),hTpart⟩,hTI.trans hSI⟩
      have shrink (v) (hv : v ∈ X) : neighbors G T v ⊆ neighbors G R v := by
        rw [← same v hv]
        intro a ha
        obtain ⟨hat,he⟩ := mem_filter.mp ha
        rcases mem_insert.mp hat with rfl | hm
        · exact (avoid v (mem_union_left _ hv) he).elim
        · exact mem_filter.mpr ⟨(mem_erase.mp hm).2,he⟩
      have hold := optimal T hTf shrink z hz
      have hyT := (mem_filter.mp (hold ▸ hyz)).1
      rcases mem_insert.mp hyT with he | he
      · exact hxy he.symm
      · exact (mem_erase.mp he).1 rfl
    · have hplus : insert x S ∈ reps := mem_filter.mpr
        ⟨mem_powerset.mpr (insert_subset hx hSA),hS.add G iso present⟩
      have hxS : x ∉ S := fun h ↦ present (mem_image_of_mem row h)
      have hbad := hmax _ hplus
      rw [card_insert_of_notMem hxS, hSc] at hbad
      omega
  obtain ⟨y, hy⟩ := hasNeighbor
  have edge := (mem_filter.mp hy).2
  have hyY : y ∉ Y := fun h ↦ avoid y (mem_union_right _ h) (G.adj_symm edge)
  have hxX : x ∉ X := fun h ↦ hyY (sameY ▸ mem_biUnion.mpr ⟨x,h,hy⟩)
  have larger : insert y Y ⊆ witnesses G (insert x X) S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_biUnion.mpr ⟨x,mem_insert_self ..,hy⟩
    · obtain ⟨z,hz,hv⟩ := mem_biUnion.mp (sameY.symm ▸ h)
      exact mem_biUnion.mpr ⟨z,mem_insert_of_mem hz,hv⟩
  have hsize' := card_le_card larger
  rw [card_insert_of_notMem hyY] at hsize'
  have more : insert x X ∈ states := mem_filter.mpr
    ⟨mem_powerset.mpr (insert_subset hx hXA'),S,hSf,opt',
      by rw [card_insert_of_notMem hxX]; exact (Nat.add_le_add_right hsize 1).trans hsize'⟩
  have impossible := hmaxX _ more
  rw [card_insert_of_notMem hxX] at impossible
  omega

/-- If each row contains at most b available vertices and the graph of
conflicts has degree at most Δ with 2Δ ≤ b, an independent partial transversal
represents at least |A|/b rows. Empty rows and zero degree are allowed. -/
theorem exists_partial (A : Finset V) (row : V → I) (b Δ : ℕ)
    (size : ∀ v ∈ A, (A.filter (fun u ↦ row u = row v)).card ≤ b)
    (degree : ∀ v ∈ A, (neighbors G A v).card ≤ Δ) (hb : 2*Δ ≤ b) :
    ∃ R ⊆ A, Partial G row R ∧ A.card ≤ b*R.card := by
  obtain ⟨R,hRA,hR,X,hXA,Y,hYR,hXY,cover⟩ := covered_state G A row
  refine ⟨R,hRA,hR,?_⟩
  have left : ((R \ Y).biUnion fun v ↦ A.filter (fun u ↦ row u = row v)).card ≤
      (R \ Y).card*b := (card_biUnion_le).trans
        (by simpa using Finset.sum_le_sum (s := R \ Y) (fun v hv ↦ size v (hRA (mem_sdiff.mp hv).1)))
  have right : ((X ∪ Y).biUnion (neighbors G A)).card ≤ (X ∪ Y).card*Δ :=
    card_biUnion_le.trans (by
      apply le_trans (Finset.sum_le_sum (s := X ∪ Y)
        (fun v hv ↦ degree v ((Finset.union_subset hXA (hYR.trans hRA)) hv)))
      simp)
  have hn : (X ∪ Y).card*Δ ≤ Y.card*b := by
    calc _ ≤ (X.card+Y.card)*Δ := Nat.mul_le_mul_right _ (card_union_le ..)
         _ ≤ (Y.card+Y.card)*Δ := Nat.mul_le_mul_right _ (Nat.add_le_add_right hXY _)
         _ = Y.card*(2*Δ) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ hb
  calc A.card ≤ _ := card_le_card cover
       _ ≤ _ := card_union_le ..
       _ ≤ _ := Nat.add_le_add left (right.trans hn)
       _ = b*R.card := by rw [← Nat.add_mul, Finset.card_sdiff_add_card_eq_card hYR, Nat.mul_comm]

end
end Erdos617.Transversal
