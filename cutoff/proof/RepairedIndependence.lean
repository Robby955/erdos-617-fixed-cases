import OrdinaryRepresentatives
import RepresentativeRepairs
import CircleStartLaw

/-! Filling the ordinary rows after deleting the neighbors of a repaired
independent exterior set and of its prescribed representatives. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap Transversal
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {rows : Finset ℕ} {e n : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection rows (rowDeficit T E) (rowIncidence T E) e n α β M)

private theorem row_label {i : ℕ} {x : V} (hx : x ∈ rowList T E i) : T.row x = i := by
  simp only [rowList,available,mem_filter] at hx
  exact hx.2.1

/-- The untrimmed retained clique is large enough to pay for both the
39r/40 neighbor budget and the r/41 needed for the final transversal. -/
theorem retained_repair_floor (hr : 0 < r) (band : RetainedWidth.Band Y b α β)
    {i : ℕ} (hi : i ∈ S.retained) :
    (39/40:ℝ)*r + (r:ℝ)/41 ≤ (rowList T E i).card := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  have lo : 0 ≤ β := by cases band <;> norm_num
  have upper : β ≤ 924/4000 := by cases band <;> norm_num
  have scale : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have deficit : rowDeficit T E i ≤ 1/2000 := by
    by_cases h : 0 ≤ rowDeficit T E i
    · linarith only [mul_le_mul_of_nonneg_right scale h,S.deficit i hi,
        mul_le_mul_of_nonneg_left S.width_lt.le (show 0 ≤ 2*β by linarith only [lo]),upper]
    · linarith only [le_of_not_ge h]
  change 1-((rowList T E i).card:ℝ)/r ≤ 1/2000 at deficit
  have ratio : (1999/2000:ℝ) ≤ ((rowList T E i).card:ℝ)/r := by linarith
  linarith only [(le_div_iff₀ pos).mp ratio,pos]

omit [Fintype V] in
/-- Disjoint integer excess arcs plus the baseline of exactly s exterior
vertices bound their true total load into an unrepresented row. -/
theorem row_load_of_disjoint_arcs {s r : ℕ} [NeZero (30*s*r)] (hs : 0 < s)
    (Z : Finset V) (size : Z.card = s) (start : V → ZMod (30*s*r)) (t : V → ℕ)
    (fits : ∀ v ∈ Z, 4*t v ≤ 3*r)
    (dis : (Z:Set V).PairwiseDisjoint fun v ↦ ExcessCircle.arc (start v) (ExcessCircle.excess s r (t v))) :
    (∑ v ∈ Z, (t v:ℝ)) ≤ (39/40:ℝ)*r := by
  have packed := ExcessCircle.packing Z start (fun v ↦ ExcessCircle.excess s r (t v))
    (fun v hv ↦ ExcessCircle.excess_fits (fits v hv)) dis
  have charge (v : V) : 40*s*t v ≤ ExcessCircle.excess s r (t v)+9*r := by
    unfold ExcessCircle.excess
    omega
  have total := sum_le_sum (s := Z) (fun v _ ↦ charge v)
  rw [← mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,size] at total
  have cost : 40*s*(∑ v ∈ Z, t v) ≤ 30*s*r+s*(9*r) := total.trans (Nat.add_le_add_right packed _)
  have reduced : 40*(∑ v ∈ Z, t v) ≤ 39*r := by
    apply Nat.le_of_mul_le_mul_left _ hs
    nlinarith only [cost]
  have realCost : (40:ℝ)*(∑ v ∈ Z, (t v:ℝ)) ≤ 39*r := by exact_mod_cast reduced
  linarith

/-- If s outside vertices and their prescribed representatives are mutually
compatible, some unrepresented row must lose more than 39r/40 vertices.
All row lists and graph edges here come from the same coloring. -/
theorem prescribed_exterior_load_contradiction (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+rows.card = r)
    (Z F : Finset V) (size : Z.card = S.s)
    (outside : Disjoint Z (S.retained.biUnion (rowList T E)))
    (inside : F ⊆ S.retained.biUnion (rowList T E))
    (independent : (targetGraph T.color T.target).IsIndepSet ((Z ∪ F : Finset V):Set V))
    (budget : ∀ i ∈ S.retained \ F.image T.row,
      (((Z ∪ F).biUnion fun v ↦ (rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ) ≤
        (39/40:ℝ)*r) : False := by
  let G := targetGraph T.color T.target
  let C := rowList T E
  let parts := S.retained \ F.image T.row
  let A := (parts.biUnion C).filter fun x ↦ ∀ v ∈ Z ∪ F, ¬G.Adj v x
  have imageRows : F.image T.row ⊆ S.retained := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    obtain ⟨k,hk,hxk⟩ := mem_biUnion.mp (inside hx)
    rwa [row_label T hxk]
  have sizeA (i) (hi : i ∈ parts) : (r:ℝ)/41 ≤ (A.filter fun x ↦ T.row x=i).card := by
    let lost := (Z ∪ F).biUnion fun v ↦ (C i).filter (G.Adj v)
    have cover : C i ⊆ (A.filter fun x ↦ T.row x=i) ∪ lost := by
      intro x hx
      by_cases clean : ∀ v ∈ Z ∪ F, ¬G.Adj v x
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,hi,hx⟩,clean⟩,
            row_label T hx⟩)
      · push Not at clean
        obtain ⟨v,hv,edge⟩ := clean
        exact mem_union_right _ (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hx,edge⟩⟩)
    have cnt : ((C i).card:ℝ) ≤ (A.filter fun x ↦ T.row x=i).card + (lost.card:ℝ) := by
      exact_mod_cast (card_le_card cover).trans (card_union_le ..)
    have floor := retained_repair_floor T S (by omega) band (mem_sdiff.mp hi).1
    have lim := budget i hi
    change (lost.card:ℝ) ≤ _ at lim
    change _ ≤ ((C i).card:ℝ) at floor
    linarith only [cnt,floor,lim]
  have Arow {x} (hx : x ∈ A) : ∃ i ∈ parts, x ∈ C i := mem_biUnion.mp (mem_filter.mp hx).1
  obtain ⟨R,sub,rep,im⟩ := retained_representatives T S (by omega) band parts
    sdiff_subset A (fun x hx ↦ by obtain ⟨i,_,hxi⟩ := Arow hx; rwa [row_label T hxi]) sizeA
  have disZF : Disjoint Z F := outside.mono_right inside
  have dis : Disjoint (Z ∪ F) R := by
    apply disjoint_left.mpr
    intro x hx hrx
    obtain ⟨i,hi,hxi⟩ := Arow (sub hrx)
    rcases mem_union.mp hx with hz|hf
    · exact disjoint_left.mp outside hz (mem_biUnion.mpr ⟨i,(mem_sdiff.mp hi).1,hxi⟩)
    · exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨x,hf,row_label T hxi⟩)
  have across {x y} (hx : x ∈ Z ∪ F) (hy : y ∈ R) : ¬G.Adj x y := (mem_filter.mp (sub hy)).2 _ hx
  have completed : G.IsIndepSet (((Z ∪ F) ∪ R : Finset V):Set V) := by
    intro x hx y hy ne
    rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
    · exact independent hx hy ne
    · exact across hx hy
    · exact fun edge ↦ across hy hx (G.adj_symm edge)
    · exact rep.independent hx hy ne
  have cap := (caps_of_no_witness T.color T.target hr no).1 _ completed
  rw [card_union_of_disjoint dis,card_union_of_disjoint disZF,size,← card_image_of_injOn rep.distinct,im] at cap
  have subRows : S.retained ⊆ rows := by rw [S.retained_eq]; exact (filter_subset ..).trans sdiff_subset
  have total := card_sdiff_add_card_eq_card subRows
  have avail := card_sdiff_add_card_eq_card imageRows
  have occ : (F.image T.row).card ≤ F.card := card_image_le
  have num := S.omitted
  change S.s+F.card+(S.retained \ F.image T.row).card ≤ r at cap
  omega

def repairLoad (G : SimpleGraph V) (C : ℕ → Finset V) (L : Finset V) (i : ℕ) (y : V)
    (o : Option (Option V)) : ℕ :=
  let degree := fun v ↦ ((C i).filter (G.Adj v)).card
  if y ∈ L then degree y else
    match o with
    | none => 0
    | some none => degree y
    | some (some a) => if a ∈ C i then 0 else degree y+degree a

/-- All represented points named by the sampled senders in Z. -/
def realizedReps (Z : Finset V) (w : V → Option (Option V)) :=
  Z.biUnion fun y ↦ (univ.filter fun v ↦ w y = some (some v))

private theorem mem_realizedReps {Z : Finset V} {w : V → Option (Option V)} {v : V} :
    v ∈ realizedReps Z w ↔ ∃ y ∈ Z, w y = some (some v) := by
  simp [realizedReps]

omit [Fintype V] in
private theorem marked_pair_repair {G : SimpleGraph V} {C : ℕ → Finset V} {parts : Finset ℕ}
    {U : ℕ → Finset V} {H L : Finset V} {w : V → Option (Option V)} {i : ℕ} (hi : i ∈ parts)
    {x y : V} (ne : x ≠ y) (hx : x ∈ U i) (hy : y ∈ U i) (wx : (w x).isSome) (wy : (w y).isSome) :
    s(x,y) ∈ RepresentativeRepairs.edges G parts C H U L w := by
  apply mem_union_left
  apply mem_biUnion.mpr
  refine ⟨i,hi,mem_union_left _ ?_⟩
  apply mem_image.mpr
  exact ⟨(x,y),mem_offDiag.mpr ⟨mem_filter.mpr ⟨hx,wx⟩,mem_filter.mpr ⟨hy,wy⟩,ne⟩,rfl⟩

omit [Fintype V] in

private theorem sender_rep_repair {G : SimpleGraph V} {C : ℕ → Finset V} {parts : Finset ℕ}
    {U : ℕ → Finset V} {H L : Finset V} {w : V → Option (Option V)} {i : ℕ} (hi : i ∈ parts)
    {x y v : V} (ne : x ≠ y) (hx : x ∈ U i) (wx : w x = some (some v)) (hv : v ∈ C i)
    (hy : y ∈ RepresentativeRepairs.exterior H L w) (adj : G.Adj y v)
    (fixed : Disjoint L H) (group : U i ⊆ H) :
    s(x,y) ∈ RepresentativeRepairs.edges G parts C H U L w := by
  by_cases uy : y ∈ U i
  · have wy : (w y).isSome := by
      rcases mem_union.mp hy with yl|ym
      · exact False.elim (disjoint_left.mp fixed yl (group uy))
      · exact (mem_filter.mp ym).2
    exact marked_pair_repair hi ne hx uy (by simp [wx]) wy
  apply mem_union_left
  apply mem_biUnion.mpr
  refine ⟨i,hi,mem_union_right _ (mem_biUnion.mpr ⟨x,hx,?_⟩)⟩
  rcases mem_union.mp hy with yl|ym
  · exact mem_union_left _ (mem_image.mpr ⟨y,mem_filter.mpr ⟨yl,v,hv,wx,adj⟩,rfl⟩)
  · have h := mem_filter.mp ym
    exact mem_union_right _ (mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_sdiff.mpr ⟨h.1,uy⟩,⟨v,hv,wx,adj⟩,h.2⟩,rfl⟩)

omit [Fintype V] in
private theorem cross_rep_repair {G : SimpleGraph V} {C : ℕ → Finset V} {parts : Finset ℕ}
    {U : ℕ → Finset V} {H L : Finset V} {w : V → Option (Option V)} {i k : ℕ}
    (hi : i ∈ parts) (hk : k ∈ parts) (lt : i < k)
    {x y a b : V} (hx : x ∈ U i) (hy : y ∈ U k)
    (wx : w x = some (some a)) (wy : w y = some (some b)) (ha : a ∈ C i) (hb : b ∈ C k)
    (adj : G.Adj a b) : s(x,y) ∈ RepresentativeRepairs.edges G parts C H U L w := by
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨(i,k),mem_filter.mpr ⟨mem_product.mpr ⟨hi,hk⟩,lt⟩,?_⟩
  exact mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,a,ha,b,hb,wx,wy,adj⟩,rfl⟩

/-- Avoiding the unordered repair edges makes the exterior vertices and all
their chosen representatives independent in the original target graph. -/
theorem realized_reps_independent (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L Z : Finset V) (w : V → Option (Option V))
    (group : ∀ i ∈ parts, U i ⊆ H) (fixed : Disjoint L H)
    (sample : Z ⊆ RepresentativeRepairs.exterior H L w)
    (legal : ∀ x ∈ Z, ∀ a, w x = some (some a) → ∃ i ∈ parts, x ∈ U i ∧ a ∈ C i ∧ ¬G.Adj x a)
    (ind : G.IsIndepSet (Z:Set V))
    (clean : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → s(x,y) ∉ RepresentativeRepairs.edges G parts C H U L w) :
    G.IsIndepSet ((Z ∪ realizedReps Z w : Finset V):Set V) := by
  have compat {a y : V} (ha : a ∈ realizedReps Z w) (hy : y ∈ Z) : ¬G.Adj y a := by
    obtain ⟨x,hx,wx⟩ := mem_realizedReps.mp ha
    obtain ⟨i,hi,hxi,hai,non⟩ := legal x hx a wx
    by_cases eq : x=y
    · exact eq ▸ non
    · exact fun adj ↦ clean x hx y hy eq (sender_rep_repair hi eq hxi wx hai (sample hy) adj fixed (group i hi))
  intro a ha b hb ne
  rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
  · exact ind ha hb ne
  · exact compat hb ha
  · exact fun adj ↦ compat ha hb adj.symm
  obtain ⟨x,hx,wx⟩ := mem_realizedReps.mp ha
  obtain ⟨y,hy,wy⟩ := mem_realizedReps.mp hb
  have distinct : x ≠ y := by rintro rfl; exact ne (Option.some.inj (Option.some.inj (wx.symm.trans wy)))
  obtain ⟨i,hi,hxi,hai,_⟩ := legal x hx a wx
  obtain ⟨k,hk,hyk,hbk,_⟩ := legal y hy b wy
  intro adj
  rcases lt_trichotomy i k with lt|rfl|lt
  · exact clean x hx y hy distinct (cross_rep_repair hi hk lt hxi hyk wx wy hai hbk adj)
  · exact clean x hx y hy distinct (marked_pair_repair hi distinct hxi hyk (by simp [wx]) (by simp [wy]))
  · exact clean y hy x hx distinct.symm (cross_rep_repair hk hi lt hyk hxi wy wx hbk hai adj.symm)

/-- On a row without a prescribed representative, each deleted point is
charged to the load of a sender or to the load of its actual representative. -/
theorem realized_neighbors_le_load (G : SimpleGraph V) (C : ℕ → Finset V) (H L Z : Finset V)
    (w : V → Option (Option V)) (i : ℕ) (sample : Z ⊆ RepresentativeRepairs.exterior H L w)
    (low : ∀ x ∈ L, ∀ a, w x ≠ some (some a))
    (free : ∀ a ∈ realizedReps Z w, a ∉ C i) :
    (((Z ∪ realizedReps Z w).biUnion fun v ↦ (C i).filter (G.Adj v)).card:ℝ) ≤
      ∑ y ∈ Z, (repairLoad G C L i y (w y):ℝ) := by
  let N := fun v ↦ (C i).filter (G.Adj v)
  let K := fun y ↦ N y ∪ (match w y with | some (some a) => N a | _ => ∅)
  have cover : ((Z ∪ realizedReps Z w).biUnion N) ⊆ Z.biUnion K := by
    intro v hv
    obtain ⟨x,hx,hv⟩ := mem_biUnion.mp hv
    rcases mem_union.mp hx with hz|hf
    · exact mem_biUnion.mpr ⟨x,hz,mem_union_left _ hv⟩
    · obtain ⟨y,hy,wy⟩ := mem_realizedReps.mp hf
      apply mem_biUnion.mpr
      refine ⟨y,hy,mem_union_right _ ?_⟩
      simpa only [wy] using hv
  have cost (y) (hy : y ∈ Z) : (K y).card ≤ repairLoad G C L i y (w y) := by
    rcases wy : w y with _|o
    · have yl : y ∈ L := by
        rcases mem_union.mp (sample hy) with hl|hs
        · exact hl
        · simpa [wy] using (mem_filter.mp hs).2
      simp [K,wy,repairLoad,yl,N]
    · cases o with
      | none => by_cases yl : y ∈ L <;> simp [K,wy,repairLoad,yl,N]
      | some a =>
        have yl : y ∉ L := fun hl ↦ low y hl a wy
        have ai : a ∉ C i := free a (mem_realizedReps.mpr ⟨y,hy,wy⟩)
        simpa [K,wy,repairLoad,yl,ai,N] using card_union_le (N y) (N a)
  exact_mod_cast ((card_le_card cover).trans (card_biUnion_le ..)).trans (sum_le_sum cost)

/-- Independence number cap for the actual union of original target edges,
unordered representative conflicts, and the excess-arc repair on each retained
row. The two support conditions and the per-sender load ceiling can be checked
coordinatewise before sampling the arc starts. -/
theorem realized_repaired_independence_cap (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+rows.card = r)
    (H L : Finset V) (U : ℕ → Finset V) (w : V → Option (Option V))
    [NeZero (30*S.s*r)] (start : ℕ → V → ZMod (30*S.s*r))
    (outside : Disjoint (RepresentativeRepairs.exterior H L w) (S.retained.biUnion (rowList T E)))
    (group : ∀ i ∈ S.retained, U i ⊆ H) (fixed : Disjoint L H)
    (legal : ∀ x ∈ RepresentativeRepairs.exterior H L w, ∀ a, w x = some (some a) →
      ∃ i ∈ S.retained, x ∈ U i ∧ a ∈ rowList T E i ∧ ¬(targetGraph T.color T.target).Adj x a)
    (fits : ∀ i ∈ S.retained, ∀ y ∈ RepresentativeRepairs.exterior H L w,
      4*repairLoad (targetGraph T.color T.target) (rowList T E) L i y (w y) ≤ 3*r)
    (A : Finset V) (sample : A ⊆ RepresentativeRepairs.exterior H L w)
    (ind : (targetGraph T.color T.target).IsIndepSet (A:Set V))
    (clean : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      s(x,y) ∉ RepresentativeRepairs.edges (targetGraph T.color T.target) S.retained (rowList T E) H U L w)
    (arcs : ∀ i ∈ S.retained, (A:Set V).PairwiseDisjoint fun y ↦ ExcessCircle.arc (start i y)
      (ExcessCircle.excess S.s r (repairLoad (targetGraph T.color T.target) (rowList T E) L i y (w y)))) :
    A.card ≤ S.s-1 := by
  by_contra! many
  have sp : 0 < S.s := by have := S.scale_lo; omega
  obtain ⟨Z,sub,size⟩ := exists_subset_card_eq (show S.s ≤ A.card by omega)
  have sel := sub.trans sample
  have occ : realizedReps Z w ⊆ S.retained.biUnion (rowList T E) := by
    intro x hx
    obtain ⟨y,hy,wy⟩ := mem_realizedReps.mp hx
    obtain ⟨i,hi,_,hxi,_⟩ := legal y (sel hy) x wy
    exact mem_biUnion.mpr ⟨i,hi,hxi⟩
  have independent := realized_reps_independent (targetGraph T.color T.target) S.retained (rowList T E) H U L Z w
    group fixed sel (fun y hy ↦ legal y (sel hy))
    (fun _ hx _ hy ↦ ind (sub hx) (sub hy)) (fun x hx y hy ↦ clean x (sub hx) y (sub hy))
  apply prescribed_exterior_load_contradiction T S hr no band slots Z (realizedReps Z w) size
    (outside.mono_left sel) occ independent
  intro i hi
  have free : ∀ a ∈ realizedReps Z w, a ∉ rowList T E i := by
    intro a ha hai
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨a,ha,row_label T hai⟩)
  have low : ∀ x ∈ L, ∀ a, w x ≠ some (some a) := by
    intro x hx a wx
    obtain ⟨j,hj,hin,_,_⟩ := legal x (mem_union_left _ hx) a wx
    exact disjoint_left.mp fixed hx (group j hj hin)
  exact (realized_neighbors_le_load _ _ H L Z w i sel low free).trans
    (row_load_of_disjoint_arcs sp Z size (start i) _ (fun v hv ↦ fits i (mem_sdiff.mp hi).1 v (sel hv))
      (fun _ hx _ hy ↦ arcs i (mem_sdiff.mp hi).1 (sub hx) (sub hy)))

end
end Erdos617.ColoredLists
