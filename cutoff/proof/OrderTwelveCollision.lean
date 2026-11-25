import Mathlib.Tactic

/-! The colored row collision in Section 4 of the twelve-color manuscript. -/

namespace Erdos617.OrderTwelve

/-- With at most four misses in each of two stars into a monochromatic row,
the row and the two vertices together omit a nontarget color. If the row has
eleven points and the two points are new and distinct, this is the desired
thirteen-vertex witness. -/
theorem two_stars_miss_color {V : Type*} [DecidableEq V]
    (color : V → V → Fin 12) (symm : ∀ u v, color u v = color v u)
    (target : Fin 12) (row : Finset V) (x y : V)
    (clique : ∀ u ∈ row, ∀ v ∈ row, u ≠ v → color u v = target)
    (hx : (row.filter (fun v => color x v ≠ target)).card ≤ 4)
    (hy : (row.filter (fun v => color y v ≠ target)).card ≤ 4) :
    ∃ c : Fin 12, c ≠ target ∧
      ∀ u ∈ insert x (insert y row), ∀ v ∈ insert x (insert y row), u ≠ v → color u v ≠ c := by
  classical
  let px := (row.filter (fun v => color x v ≠ target)).image (color x)
  let py := (row.filter (fun v => color y v ≠ target)).image (color y)
  let palette := insert target (insert (color x y) (px ∪ py))
  have hpx : px.card ≤ 4 := Finset.card_image_le.trans hx
  have hpy : py.card ≤ 4 := Finset.card_image_le.trans hy
  have hsize : palette.card ≤ 10 := by
    have h₁ := Finset.card_insert_le target (insert (color x y) (px ∪ py))
    have h₂ := Finset.card_insert_le (color x y) (px ∪ py)
    have h₃ := Finset.card_union_le px py
    dsimp only [palette]
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin 12, c ∉ palette := by
    by_contra! hall
    have heq := Finset.eq_univ_of_forall hall
    rw [heq] at hsize
    norm_num at hsize
  have ht : target ∈ palette := by simp [palette]
  have hxy : color x y ∈ palette := by simp [palette]
  have starX (v) (hv : v ∈ row) : color x v ∈ palette := by
    by_cases h : color x v = target
    · simpa only [h] using ht
    · have hp : color x v ∈ px :=
        Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩, rfl⟩
      simp [palette, hp]
  have starY (v) (hv : v ∈ row) : color y v ∈ palette := by
    by_cases h : color y v = target
    · simpa only [h] using ht
    · have hp : color y v ∈ py :=
        Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩, rfl⟩
      simp [palette, hp]
  refine ⟨c, fun h => hc (h ▸ ht), ?_⟩
  intro u hu v hv hne hcolor
  apply hc
  rw [← hcolor]
  simp only [Finset.mem_insert] at hu hv
  rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv
  · exact (hne rfl).elim
  · exact hxy
  · exact starX _ hv
  · rw [symm]; exact hxy
  · exact (hne rfl).elim
  · exact starY _ hv
  · rw [symm]; exact starX _ hu
  · rw [symm]; exact starY _ hu
  · rw [clique _ hu _ hv hne]; exact ht

/-- For an eleven-point row and two distinct exterior points the omitted
color occurs on no edge of an actual thirteen-point set. -/
theorem thirteen_vertex_witness {V : Type*} [DecidableEq V]
    (color : V → V → Fin 12) (symm : ∀ u v, color u v = color v u)
    (target : Fin 12) (row : Finset V) (x y : V)
    (size : row.card = 11) (newX : x ∉ row) (newY : y ∉ row) (distinct : x ≠ y)
    (clique : ∀ u ∈ row, ∀ v ∈ row, u ≠ v → color u v = target)
    (hx : (row.filter (fun v => color x v ≠ target)).card ≤ 4)
    (hy : (row.filter (fun v => color y v ≠ target)).card ≤ 4) :
    ∃ (w : Finset V) (c : Fin 12), w.card = 13 ∧ c ≠ target ∧
      ∀ u ∈ w, ∀ v ∈ w, u ≠ v → color u v ≠ c := by
  obtain ⟨c, hc, h⟩ := two_stars_miss_color color symm target row x y clique hx hy
  exact ⟨insert x (insert y row), c, by simp [distinct, newX, newY, size], hc, h⟩

end Erdos617.OrderTwelve
