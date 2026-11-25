import PartialTransversal

/-! Pairs, surviving vertex lists and the missing representatives in Appendix A, §2. -/

namespace Erdos617.PackingLists

open Finset
open scoped Classical
noncomputable section

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- The target graph restricted to edges between different raw rows. -/
def cross (G : SimpleGraph V) (row : V → I) : SimpleGraph V where
  Adj x y := row x ≠ row y ∧ G.Adj x y
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, G.adj_symm h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

def available (G : SimpleGraph V) (live : Finset V) (row : V → I)
    (E : Finset V) (i : I) : Finset V :=
  live.filter fun v ↦ row v = i ∧ ∀ z ∈ E, ¬G.Adj z v

/-- E contains exactly two independent endpoints in each chosen row. -/
structure Packing (G : SimpleGraph V) (row : V → I) (E : Finset V) : Prop where
  independent : G.IsIndepSet (E : Set V)
  two : ∀ i ∈ E.image row, (E.filter fun v ↦ row v = i).card = 2

omit [DecidableEq V] in
theorem Packing.card {G : SimpleGraph V} {row : V → I} {E : Finset V} (h : Packing G row E) :
    E.card = 2*(E.image row).card := by
  calc E.card = ∑ i ∈ E.image row, (E.filter fun v ↦ row v = i).card :=
         card_eq_sum_card_fiberwise fun v hv ↦ mem_image_of_mem row hv
       _ = _ := by rw [sum_congr rfl h.two]; simp [Nat.mul_comm]

private theorem independent_union (G : SimpleGraph V) (S T : Finset V)
    (hS : G.IsIndepSet (S:Set V)) (hT : G.IsIndepSet (T:Set V))
    (across : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y) : G.IsIndepSet ((S ∪ T : Finset V):Set V) := by
  intro x hx y hy ne
  rcases mem_union.mp hx with hxS | hxT <;> rcases mem_union.mp hy with hyS | hyT
  · exact hS hxS hyS ne
  · exact across _ hxS _ hyT
  · exact fun edge ↦ across _ hyS _ hxT (G.adj_symm edge)
  · exact hT hxT hyT ne

/-- Choose the pairs from the actual surviving vertices. No pair can be added
in an unchosen row, so the available list there is a clique. -/
theorem exists_packing (G : SimpleGraph V) (live : Finset V) (row : V → I) :
    ∃ E ⊆ live, Packing G row E ∧
      ∀ i ∉ E.image row, G.IsClique (available G live row E i : Set V) := by
  let candidates := live.powerset.filter (Packing G row)
  have start : ∅ ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    ⟨by intro v hv; simp at hv, by simp⟩⟩
  obtain ⟨E,hE,hmax⟩ := candidates.exists_max_image Finset.card ⟨∅,start⟩
  obtain ⟨sub,pack⟩ := mem_filter.mp hE
  have sub' := mem_powerset.mp sub
  refine ⟨E,sub',pack,?_⟩
  intro i new x hx y hy xy
  by_contra nonedge
  obtain ⟨hxl,hxi,hxE⟩ := mem_filter.mp hx
  obtain ⟨hyl,hyi,hyE⟩ := mem_filter.mp hy
  have hxf : x ∉ E := fun h ↦ new (hxi ▸ mem_image_of_mem row h)
  have hyf : y ∉ E := fun h ↦ new (hyi ▸ mem_image_of_mem row h)
  have pair : G.IsIndepSet (({x,y} : Finset V):Set V) := by
    intro u hu v hv hne
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (hne rfl).elim
    · exact nonedge
    · exact fun e ↦ nonedge (G.adj_symm e)
    · exact (hne rfl).elim
  have ind := independent_union G E {x,y} pack.independent pair (by
    intro z hz v hv
    rcases mem_insert.mp hv with rfl | h
    · exact hxE _ hz
    · exact mem_singleton.mp h ▸ hyE _ hz)
  let T := insert x (insert y E)
  have ind' : G.IsIndepSet (T:Set V) := by simpa [T, union_comm E] using ind
  have pt : Packing G row T := by
    refine ⟨ind', ?_⟩
    intro j hj
    by_cases hij : i = j
    · subst j
      have empty : E.filter (fun v ↦ row v = i) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro v hv he
        exact new (he ▸ mem_image_of_mem row hv)
      simp [T,filter_insert,hxi,hyi,empty,xy]
    · have old : j ∈ E.image row := by simpa [T,hxi,hyi,Ne.symm hij] using hj
      simpa [T,filter_insert,hxi,hyi,hij] using pack.two j old
  have hT := hmax T (mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hxl (insert_subset hyl sub')),pt⟩)
  have hxf' : x ∉ insert y E := by simp [xy,hxf]
  simp only [T, card_insert_of_notMem hxf', card_insert_of_notMem hyf] at hT
  omega

/-- Number of missing representatives measured in units of a full block. -/
def shortfall (U : Finset I) (m : I → ℕ) (b : ℕ) : ℝ :=
  ∑ i ∈ U.filter (fun i ↦ m i < b), (1 - (m i:ℝ)/b)

/-- The real vertices can supply at least the total truncated list size divided
by b independent representatives, all compatible with every chosen endpoint. -/
theorem real_representatives (G : SimpleGraph V) (row : V → I) (live E : Finset V)
    (U : Finset I) (b Δ : ℕ) (unused : Disjoint U (E.image row))
    (ind : G.IsIndepSet (E:Set V))
    (degree : ∀ v ∈ live, (Transversal.neighbors (cross G row) live v).card ≤ Δ)
    (hb : 2*Δ ≤ b) :
    ∃ R ⊆ live, Disjoint E R ∧ G.IsIndepSet ((E ∪ R : Finset V):Set V) ∧
      Set.InjOn row (R:Set V) ∧
      (∑ i ∈ U, min b (available G live row E i).card) ≤ b*R.card := by
  let L := available G live row E
  have trim (i : I) : ∃ A ⊆ L i, A.card = min b (L i).card :=
    exists_subset_card_eq (min_le_right ..)
  choose slice slice_sub slice_size using trim
  let A := U.biUnion slice
  have fiber {i v} (h : v ∈ slice i) : row v = i :=
    (mem_filter.mp (slice_sub i h)).2.1
  have row_info {v} (h : v ∈ A) : v ∈ live ∧ row v ∈ U ∧ ∀ z ∈ E, ¬G.Adj z v := by
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp h
    obtain ⟨hl,he,hz⟩ := mem_filter.mp (slice_sub i hv)
    exact ⟨hl,he ▸ hi,hz⟩
  have sub : A ⊆ live := fun _ h ↦ (row_info h).1
  have bound (v) (_hv : v ∈ A) : (A.filter (fun u ↦ row u = row v)).card ≤ b := by
    apply le_trans (Finset.card_le_card (t := slice (row v)) ?_)
    · rw [slice_size]; exact min_le_left ..
    · intro u hu
      obtain ⟨hua,huv⟩ := mem_filter.mp hu
      obtain ⟨i,_,hui⟩ := mem_biUnion.mp hua
      exact ((fiber hui).symm.trans huv) ▸ hui
  have count : A.card = ∑ i ∈ U, min b (L i).card := by
    apply (Finset.card_biUnion ?_).trans (sum_congr rfl fun i _ ↦ slice_size i)
    intro i _ j _ ne
    exact Finset.disjoint_left.mpr (fun _ hi hj ↦ ne ((fiber hi).symm.trans (fiber hj)))
  obtain ⟨R,hRA,hR,weight⟩ := Transversal.exists_partial (cross G row) A row b Δ bound
    (fun v hv ↦ (card_le_card (filter_subset_filter _ sub)).trans (degree _ (sub hv))) hb
  have disj : Disjoint E R := disjoint_left.mpr fun v he hr ↦
    disjoint_left.mp unused (row_info (hRA hr)).2.1 (mem_image_of_mem row he)
  have realInd : G.IsIndepSet (R:Set V) := by
    intro x hx y hy hxy edge
    exact hR.independent hx hy hxy ⟨fun e ↦ hxy (hR.distinct hx hy e),edge⟩
  rw [count] at weight
  exact ⟨R,hRA.trans sub,disj,
    independent_union G E R ind realInd (fun z hz v hv ↦ (row_info (hRA hv)).2.2 z hz),
    hR.distinct,weight⟩

/-- In the original graph the endpoints and real representatives together
have size at most r. This forces the claimed q ≤ W on the actual lists. -/
theorem pairs_le_shortfall (G : SimpleGraph V) (row : V → I) (live E : Finset V)
    (parts : Finset I) (r b Δ : ℕ) (hparts : parts.card = r)
    (inParts : E.image row ⊆ parts) (pack : Packing G row E)
    (cap : ∀ S : Finset V, G.IsIndepSet (S:Set V) → S.card ≤ r)
    (degree : ∀ v ∈ live, (Transversal.neighbors (cross G row) live v).card ≤ Δ)
    (hb : 2*Δ ≤ b) (bpos : 0 < b) :
    ((E.image row).card:ℝ) ≤ shortfall (parts \ E.image row) (fun i ↦ (available G live row E i).card) b := by
  let U := parts \ E.image row
  let m := fun i ↦ (available G live row E i).card
  obtain ⟨R,_,disj,ind,_,weight⟩ := real_representatives G row live E U b Δ sdiff_disjoint
    pack.independent degree hb
  have quota := cap (E ∪ R) ind
  rw [card_union_of_disjoint disj, pack.card] at quota
  have slots : U.card+(E.image row).card = r := (card_sdiff_add_card_eq_card inParts).trans hparts
  have hsum : (∑ i ∈ U, min b (m i)) + ∑ i ∈ U, (b-m i) = U.card*b := by
    rw [← sum_add_distrib]
    calc (∑ i ∈ U, (min b (m i) + (b-m i))) = ∑ _i ∈ U, b := by
          exact sum_congr rfl fun i _ ↦ by omega
         _ = _ := by simp
  change (∑ i ∈ U, min b (m i)) ≤ b*R.card at weight
  have hn : b*(E.image row).card ≤ ∑ i ∈ U, (b-m i) := by
    have h := Nat.mul_le_mul_left b quota
    rw [← slots] at h
    nlinarith only [h, hsum, weight]
  have hreal : ((∑ i ∈ U, (b-m i)):ℕ) = (b:ℝ)*shortfall U m b := by
    rw [Nat.cast_sum, shortfall, Finset.mul_sum, Finset.sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [Nat.cast_sub hi.le]
      field_simp [show (b:ℝ) ≠ 0 by exact_mod_cast bpos.ne']
    · simp [Nat.sub_eq_zero_of_le (le_of_not_gt hi)]
  have hcast : (b:ℝ)*((E.image row).card:ℝ) ≤ ((∑ i ∈ U, (b-m i)):ℕ) := by exact_mod_cast hn
  rw [hreal] at hcast
  exact le_of_mul_le_mul_left hcast (by exact_mod_cast bpos)

end
end Erdos617.PackingLists
