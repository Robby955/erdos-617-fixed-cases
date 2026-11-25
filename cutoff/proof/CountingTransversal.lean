import PartialTransversal

/-! A counting bound for independent representatives when each row meets few
conflicting pairs in total. This form allows an arbitrary real list-size bound. -/

namespace Erdos617.Transversal

open Finset
open scoped Classical
noncomputable section

variable {V I : Type*} [DecidableEq V] [DecidableEq I] (G : SimpleGraph V)
  (A : Finset V) (row : V → I)

private def choices (U : Finset I) := A.powerset.filter fun R ↦ Partial G row R ∧ R.image row = U

def conflicts (i : I) (U : Finset I) :=
  ((A.filter fun x ↦ row x = i) ×ˢ (A.filter fun y ↦ row y ∈ U)).filter
    fun e ↦ G.Adj e.1 e.2

omit [DecidableEq V] in
private theorem mem_choices {U : Finset I} {R : Finset V} :
    R ∈ choices G A row U ↔ R ⊆ A ∧ Partial G row R ∧ R.image row = U := by
  simp [choices]

private theorem remove_at {U : Finset I} {y : V} :
    ((choices G A row U).filter fun R ↦ y ∈ R).card ≤ (choices G A row (U.erase (row y))).card := by
  apply Finset.card_le_card_of_injOn (fun R ↦ R.erase y)
  · intro R h
    obtain ⟨hR,hy⟩ := mem_filter.mp h
    obtain ⟨sub,part,im⟩ := (mem_choices G A row).mp hR
    refine (mem_choices G A row).mpr ⟨(erase_subset ..).trans sub,
      ⟨part.independent.mono (by exact_mod_cast erase_subset y R),part.distinct.mono (by exact_mod_cast erase_subset y R)⟩,?_⟩
    ext j
    rw [← im]
    constructor
    · rintro hj
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hj
      obtain ⟨ne,hin⟩ := mem_erase.mp hz
      exact mem_erase.mpr ⟨fun eq ↦ ne (part.distinct hin hy eq),mem_image_of_mem row hin⟩
    · rintro hj
      obtain ⟨ne,hin⟩ := mem_erase.mp hj
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hin
      exact mem_image_of_mem row (mem_erase.mpr ⟨fun eq ↦ ne (congrArg row eq),hz⟩)
  · intro R h S h' eq
    change R.erase y = S.erase y at eq
    rw [← insert_erase (mem_filter.mp h).2,← insert_erase (mem_filter.mp h').2,eq]

private theorem extension_count (U : Finset I) (i : I) (fresh : i ∉ U) :
    (A.filter (fun x ↦ row x = i)).card*(choices G A row U).card ≤
      (choices G A row (insert i U)).card +
      ∑ e ∈ conflicts G A row i U, (choices G A row (U.erase (row e.2))).card := by
  let L := A.filter fun x ↦ row x = i
  let F := choices G A row U
  let pool := L ×ˢ F
  let good := pool.filter (fun p ↦ ∀ y ∈ p.2, ¬G.Adj p.1 y)
  have extension (p : V × Finset V) (hp : p ∈ good) :
      insert p.1 p.2 ∈ choices G A row (insert i U) := by
    obtain ⟨inPool,avoid⟩ := mem_filter.mp hp
    obtain ⟨hx,hR⟩ := mem_product.mp inPool
    obtain ⟨xA,xi⟩ := mem_filter.mp hx
    obtain ⟨sub,part,im⟩ := (mem_choices G A row).mp hR
    have nu (y) (hy : y ∈ p.2) : row p.1 ≠ row y := fun eq ↦
      fresh (xi ▸ (eq ▸ im ▸ mem_image_of_mem row hy))
    refine (mem_choices G A row).mpr ⟨insert_subset xA sub,⟨?_,?_⟩, by rw [image_insert,im,xi]⟩
    · intro v hv w hw ne
      rcases mem_insert.mp hv with rfl | hv <;> rcases mem_insert.mp hw with rfl | hw
      · exact (ne rfl).elim
      · exact avoid w hw
      · exact fun e ↦ avoid v hv (G.adj_symm e)
      · exact part.independent hv hw ne
    · intro v hv w hw eq
      rcases mem_insert.mp hv with rfl | hv <;> rcases mem_insert.mp hw with rfl | hw
      · rfl
      · exact (nu w hw eq).elim
      · exact (nu v hv eq.symm).elim
      · exact part.distinct hv hw eq
  have inject : Set.InjOn (fun p : V × Finset V ↦ insert p.1 p.2) (good:Set (V × Finset V)) := by
    rintro ⟨x,R⟩ hx ⟨y,S⟩ hy eq
    obtain ⟨hxl,hR⟩ := mem_product.mp (mem_filter.mp hx).1
    obtain ⟨hyl,hS⟩ := mem_product.mp (mem_filter.mp hy).1
    have outside (P : Finset V) (hP : P ∈ F) (v : V) (hv : v ∈ L) : v ∉ P := by
      intro h
      have image := ((mem_choices G A row).mp hP).2.2
      exact fresh ((mem_filter.mp hv).2 ▸ image ▸ mem_image_of_mem row h)
    change insert x R = insert y S at eq
    have same : x = y := (mem_insert.mp (eq ▸ mem_insert_self x R)).resolve_right (outside S hS x hxl)
    subst y
    have rest := congrArg (fun P : Finset V ↦ P.erase x) eq
    simp [outside R hR x hxl,outside S hS x hxl] at rest
    exact Prod.ext rfl rest
  let bad := fun (e : V × V) ↦ ({e.1}:Finset V) ×ˢ (F.filter (fun P ↦ e.2 ∈ P))
  have cover : pool ⊆ good ∪ (conflicts G A row i U).biUnion bad := by
    rintro ⟨x,P⟩ hp
    obtain ⟨hx,hP⟩ := mem_product.mp hp
    by_cases h : ∀ y ∈ P, ¬G.Adj x y
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,h⟩)
    push Not at h
    obtain ⟨y,hy,edge⟩ := h
    obtain ⟨sub,_,image⟩ := (mem_choices G A row).mp hP
    have he : (x,y) ∈ conflicts G A row i U := mem_filter.mpr
      ⟨mem_product.mpr ⟨hx,mem_filter.mpr ⟨sub hy,image ▸ mem_image_of_mem row hy⟩⟩,edge⟩
    exact mem_union_right _ (mem_biUnion.mpr ⟨(x,y),he,
      mem_product.mpr ⟨mem_singleton_self _,mem_filter.mpr ⟨hP,hy⟩⟩⟩)
  have bound := (card_le_card cover).trans (card_union_le ..)
  rw [show pool.card = L.card*F.card by exact card_product ..] at bound
  apply bound.trans (Nat.add_le_add (Finset.card_le_card_of_injOn _ extension inject) _)
  apply card_biUnion_le.trans (sum_le_sum fun e _ ↦ ?_)
  simpa [bad,F] using remove_at G A row (U := U) (y := e.2)

/-- At least one independent representative per row exists if every row
has at least L vertices and meets at most L²/4 conflicting pairs with other rows. -/
theorem exists_of_row_conflicts (parts : Finset I) (L : ℝ) (pos : 0 < L)
    (size : ∀ i ∈ parts, L ≤ (A.filter (fun x ↦ row x = i)).card)
    (cap : ∀ i ∈ parts, 4*((conflicts G A row i (parts.erase i)).card:ℝ) ≤ L^2) :
    ∃ R ⊆ A, Partial G row R ∧ R.image row = parts := by
  let Z := fun U ↦ ((choices G A row U).card:ℝ)
  have growth (U : Finset I) : ∀ i ∈ parts, U ⊆ parts → i ∉ U → L/2*Z U ≤ Z (insert i U) := by
    induction U using Finset.strongInduction with
    | H U ih =>
      intro i hi sub fresh
      let E := conflicts G A row i U
      have subE : E ⊆ conflicts G A row i (parts.erase i) := by
        intro e he
        obtain ⟨hp,adj⟩ := mem_filter.mp he
        obtain ⟨hx,hy⟩ := mem_product.mp hp
        obtain ⟨hA,hU⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hx,mem_filter.mpr ⟨hA,mem_erase.mpr
          ⟨fun heq ↦ fresh (heq ▸ hU),sub hU⟩⟩⟩,adj⟩
      have hind (e : V × V) (he : e ∈ E) : L/2*Z (U.erase (row e.2)) ≤ Z U := by
        have mem : row e.2 ∈ U := (mem_filter.mp (mem_product.mp (mem_filter.mp he).1).2).2
        have smaller := ih _ (erase_ssubset mem) _ (sub mem) ((erase_subset ..).trans sub)
          (by simp)
        rwa [insert_erase mem] at smaller
      have sumBound := sum_le_sum (s := E) hind
      rw [← Finset.mul_sum] at sumBound
      simp only [sum_const, nsmul_eq_mul] at sumBound
      have count : ((A.filter (fun x ↦ row x = i)).card:ℝ)*Z U ≤
          Z (insert i U) + ∑ e ∈ E, Z (U.erase (row e.2)) := by
        dsimp [Z,E]
        exact_mod_cast extension_count G A row U i fresh
      have zpos : 0 ≤ Z U := Nat.cast_nonneg _
      have ecap : 4*(E.card:ℝ) ≤ L^2 := le_trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card subE)) (by norm_num)) (cap i hi)
      apply le_of_mul_le_mul_left _ (show 0 < L/2 by linarith)
      nlinarith only [sumBound, mul_le_mul_of_nonneg_right ecap zpos,
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right (size i hi) zpos) count)
          (show 0 ≤ L/2 by linarith)]
  have nonzero (U : Finset I) (sub : U ⊆ parts) : 0 < Z U := by
    induction U using Finset.induction_on with
    | empty =>
      have he : (∅ : Finset V) ∈ choices G A row ∅ := (mem_choices G A row).mpr
        ⟨empty_subset _,⟨by simp [SimpleGraph.IsIndepSet],by simp⟩,by simp⟩
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨_,he⟩)
    | insert i U fresh ih =>
      have sU := (insert_subset_iff.mp sub).2
      exact lt_of_lt_of_le (mul_pos (by linarith : 0<L/2) (ih sU))
        (growth U i (sub (mem_insert_self ..)) sU fresh)
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (Nat.cast_pos.mp (nonzero parts Subset.rfl))
  exact ⟨R,(mem_choices G A row).mp hR⟩

end
end Erdos617.Transversal
