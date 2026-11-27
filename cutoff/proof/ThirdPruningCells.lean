import ThirdPruningBounds

/-! Lean replay of the generated linear certificates. Each split is exhaustive
over real inputs. Regenerate with generate_third_pruning_cells.py. -/
namespace Erdos617.ThirdPruning
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
private theorem zero_cell_0 {p t z s e k d h m w : ℝ}
    (B : ZeroBounds p t z s e k d h m w (41/250) (37/160))
    (yl : 0 ≤ 2-p/2-(199/400)*t)
    (yr : 2-p/2-(199/400)*t ≤ (501/1000))
    (wl : (3066578951/200000000)-(2-p/2-(199/400)*t)/(41/250)-(p+t)/(37/160)+(349+114*p)/1000 ≤ w) : False := by
  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]
  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]
  rcases le_total d ((1/2):ℝ) with cut0 | cut0
  · rcases le_total e ((1/2):ℝ) with cut1 | cut1
    · rcases le_total s ((1/2):ℝ) with cut2 | cut2
      · rcases le_total d ((1/4):ℝ) with cut3 | cut3
        · rcases le_total e ((1/4):ℝ) with cut4 | cut4
          · rcases le_total s ((1/4):ℝ) with cut5 | cut5
            · rcases le_total d ((1/8):ℝ) with cut6 | cut6
              · have ch := B.linear_charge (D := (1/8)) (E := (1/4)) (U := (500001/1000000)) cut6 (by norm_num) cut4 (le_trans cut5 (by norm_num)) (by norm_num)
                norm_num1 at ch
                have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                norm_num1 at young_M0
                linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.holes, yr, young_M0, ch.1]
              · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.deficit, yr, wl, cut6]
            · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, cut5, yr]
          · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, yr, cut4]
        · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.deficit, yr, wl, cut3]
      · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, yr, cut2]
    · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, cut1, yr]
  · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.deficit, yr, wl, cut0]

private theorem zero_cell_1 {p t z s e k d h m w : ℝ}
    (B : ZeroBounds p t z s e k d h m w (41/250) (923/4000))
    (yl : (501/1000) ≤ 2-p/2-(199/400)*t)
    (yr : 2-p/2-(199/400)*t ≤ (11/20))
    (wl : (3066578951/200000000)-(2-p/2-(199/400)*t)/(41/250)-(p+t)/(923/4000)+(349+114*p)/1000 ≤ w) : False := by
  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]
  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]
  rcases le_total d ((1/2):ℝ) with cut0 | cut0
  · rcases le_total e ((1/2):ℝ) with cut1 | cut1
    · rcases le_total s ((1/2):ℝ) with cut2 | cut2
      · rcases le_total d ((1/4):ℝ) with cut3 | cut3
        · rcases le_total e ((1/4):ℝ) with cut4 | cut4
          · rcases le_total s ((1/4):ℝ) with cut5 | cut5
            · rcases le_total d ((1/8):ℝ) with cut6 | cut6
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · have ch := B.linear_charge (D := (1/8)) (E := (1/8)) (U := (176777/500000)) cut6 (by norm_num) cut7 (le_trans cut8 (by norm_num)) (by norm_num)
                    norm_num1 at ch
                    have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                    norm_num1 at young_M0
                    linarith only [B.p1, B.edge_eq, B.k0, B.old, B.d0, B.holes, B.deficit, yr, wl, young_M0, ch.1]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, yr, cut8]
                · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, cut7, yr]
              · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut6]
            · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut5]
          · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut4]
        · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut3]
      · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut2]
    · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut1]
  · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut0]

private theorem zero_cell_2 {p t z s e k d h m w : ℝ}
    (B : ZeroBounds p t z s e k d h m w (653/4000) (459/2000))
    (yl : (11/20) ≤ 2-p/2-(199/400)*t)
    (yr : 2-p/2-(199/400)*t ≤ (13/20))
    (wl : (3066578951/200000000)-(2-p/2-(199/400)*t)/(653/4000)-(p+t)/(459/2000)+(349+114*p)/1000 ≤ w) : False := by
  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]
  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]
  rcases le_total d ((1/2):ℝ) with cut0 | cut0
  · rcases le_total e ((1/2):ℝ) with cut1 | cut1
    · rcases le_total s ((1/2):ℝ) with cut2 | cut2
      · rcases le_total d ((1/4):ℝ) with cut3 | cut3
        · rcases le_total e ((1/4):ℝ) with cut4 | cut4
          · rcases le_total s ((1/4):ℝ) with cut5 | cut5
            · rcases le_total d ((1/8):ℝ) with cut6 | cut6
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((1/16):ℝ) with cut9 | cut9
                    · have ch := B.linear_charge (D := (1/16)) (E := (1/8)) (U := (176777/500000)) cut9 (by norm_num) cut7 (le_trans cut8 (by norm_num)) (by norm_num)
                      norm_num1 at ch
                      have young_M1 := (B.linear_young (D := (1/16)) (u := (1/16)) cut9 (by norm_num) (by norm_num))
                      norm_num1 at young_M1
                      linarith only [B.p1, B.edge_eq, cut7, B.s0, B.old, B.d0, B.holes, B.deficit, ch.1, wl, young_M1]
                    · have ch := B.linear_charge (D := (1/8)) (E := (1/8)) (U := (176777/500000)) cut6 (by norm_num) cut7 (le_trans cut8 (by norm_num)) (by norm_num)
                      norm_num1 at ch
                      have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                      norm_num1 at young_M0
                      linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, ch.1, wl, cut9, young_M0]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut8]
                · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut7]
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((3/16):ℝ) with cut9 | cut9
                    · have ch := B.linear_charge (D := (3/16)) (E := (1/8)) (U := (176777/500000)) cut9 (by norm_num) cut7 (le_trans cut8 (by norm_num)) (by norm_num)
                      norm_num1 at ch
                      have young_M0 := (B.linear_young (D := (3/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                      norm_num1 at young_M0
                      linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, cut6, ch.1, young_M0]
                    · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut9]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut8]
                · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, cut7, wl]
            · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut5]
          · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut4]
        · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut3]
      · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut2]
    · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut1]
  · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut0]

private theorem zero_cell_3 {p t z s e k d h m w : ℝ}
    (B : ZeroBounds p t z s e k d h m w (163/1000) (229/1000))
    (yl : (13/20) ≤ 2-p/2-(199/400)*t)
    (yr : 2-p/2-(199/400)*t ≤ 1)
    (wl : (378990199/25000000)-(2-p/2-(199/400)*t)/(163/1000)-(p+t)/(229/1000)+(349+114*p)/1000 ≤ w) : False := by
  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]
  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]
  rcases le_total d ((1/2):ℝ) with cut0 | cut0
  · rcases le_total e ((1/2):ℝ) with cut1 | cut1
    · rcases le_total s ((1/2):ℝ) with cut2 | cut2
      · rcases le_total d ((1/4):ℝ) with cut3 | cut3
        · rcases le_total e ((1/4):ℝ) with cut4 | cut4
          · rcases le_total s ((1/4):ℝ) with cut5 | cut5
            · rcases le_total d ((1/8):ℝ) with cut6 | cut6
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((1/16):ℝ) with cut9 | cut9
                    · rcases le_total e ((1/16):ℝ) with cut10 | cut10
                      · have ch := B.linear_charge (D := (1/16)) (E := (1/16)) (U := (176777/500000)) cut9 (by norm_num) cut10 (le_trans cut8 (by norm_num)) (by norm_num)
                        norm_num1 at ch
                        have young_M0 := (B.linear_young (D := (1/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                        norm_num1 at young_M0
                        linarith only [B.p1, B.edge_eq, B.s0, B.old, B.d0, B.holes, B.deficit, wl, ch.1, young_M0, cut10]
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · have ch := B.linear_charge (D := (1/16)) (E := (1/8)) (U := (250001/1000000)) cut9 (by norm_num) cut7 (le_trans cut11 (by norm_num)) (by norm_num)
                          norm_num1 at ch
                          have young_M0 := (B.linear_young (D := (1/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                          norm_num1 at young_M0
                          linarith only [B.p1, B.edge_eq, B.s0, B.old, B.d0, B.holes, B.deficit, wl, ch.1, young_M0, cut7]
                        · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, wl, cut11, cut10]
                    · rcases le_total e ((1/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · have ch := B.linear_charge (D := (1/8)) (E := (1/16)) (U := (250001/1000000)) cut6 (by norm_num) cut10 (le_trans cut11 (by norm_num)) (by norm_num)
                          norm_num1 at ch
                          have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                          norm_num1 at young_M0
                          linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, wl, cut9, cut10, young_M0, ch.1]
                        · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, cut11, wl]
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((3/32):ℝ) with cut12 | cut12
                          · have ch := B.linear_charge (D := (3/32)) (E := (1/8)) (U := (250001/1000000)) cut12 (by norm_num) cut7 (le_trans cut11 (by norm_num)) (by norm_num)
                            norm_num1 at ch
                            have young_M0 := (B.linear_young (D := (3/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                            norm_num1 at young_M0
                            linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, wl, cut9, ch.1, young_M0, cut7]
                          · rcases le_total e ((3/32):ℝ) with cut13 | cut13
                            · have ch := B.linear_charge (D := (1/8)) (E := (3/32)) (U := (250001/1000000)) cut6 (by norm_num) cut13 (le_trans cut11 (by norm_num)) (by norm_num)
                              norm_num1 at ch
                              have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                              norm_num1 at young_M0
                              linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, wl, cut12, ch.1, young_M0, cut13]
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (1/8)) (E := (1/8)) (U := (176777/1000000)) cut6 (by norm_num) cut7 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (1/8)) (u := (1/32)) cut6 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, wl, cut12, ch.1, young_M0, cut7]
                              · linarith only [B.p1, B.edge_eq, B.spent, B.old, cut14, cut13, B.deficit, wl, cut12]
                        · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, cut11, cut10, wl]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, cut8, wl]
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((1/16):ℝ) with cut9 | cut9
                    · rcases le_total e ((3/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((1/32):ℝ) with cut12 | cut12
                          · have ch := B.linear_charge (D := (1/32)) (E := (3/16)) (U := (250001/1000000)) cut12 (by norm_num) cut10 (le_trans cut11 (by norm_num)) (by norm_num)
                            norm_num1 at ch
                            have young_M2 := (B.linear_young (D := (1/32)) (u := (1/8)) cut12 (by norm_num) (by norm_num))
                            norm_num1 at young_M2
                            linarith only [B.p1, B.edge_eq, B.s0, B.old, B.d0, B.holes, B.deficit, cut10, wl, young_M2, ch.1]
                          · rcases le_total e ((5/32):ℝ) with cut13 | cut13
                            · have ch := B.linear_charge (D := (1/16)) (E := (5/32)) (U := (250001/1000000)) cut9 (by norm_num) cut13 (le_trans cut11 (by norm_num)) (by norm_num)
                              norm_num1 at ch
                              have young_M0 := (B.linear_young (D := (1/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                              norm_num1 at young_M0
                              linarith only [cut12, B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, cut13, wl, young_M0, ch.1]
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (1/16)) (E := (3/16)) (U := (176777/1000000)) cut9 (by norm_num) cut10 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (1/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [cut13, cut12, B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, wl, young_M0, ch.1]
                              · linarith only [cut13, B.p1, B.edge_eq, B.k0, B.spent, B.old, wl, cut14]
                        · linarith only [cut7, B.p1, B.edge_eq, B.k0, B.spent, B.old, wl, cut11]
                      · linarith only [cut10, B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl]
                    · rcases le_total e ((3/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((3/32):ℝ) with cut12 | cut12
                          · rcases le_total e ((5/32):ℝ) with cut13 | cut13
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (3/32)) (E := (5/32)) (U := (176777/1000000)) cut12 (by norm_num) cut13 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (3/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, cut9, ch.1, young_M0]
                              · linarith only [cut14, B.p1, B.edge_eq, B.spent, B.old, B.deficit, wl, cut7, cut9]
                            · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, wl, cut13, cut9]
                          · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, wl, cut7, cut12]
                        · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, wl, cut7, cut11]
                      · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut10]
                  · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, cut8, wl, cut7]
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((3/16):ℝ) with cut9 | cut9
                    · rcases le_total e ((1/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((5/32):ℝ) with cut12 | cut12
                          · have ch := B.linear_charge (D := (5/32)) (E := (1/16)) (U := (250001/1000000)) cut12 (by norm_num) cut10 (le_trans cut11 (by norm_num)) (by norm_num)
                            norm_num1 at ch
                            have young_M0 := (B.linear_young (D := (5/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                            norm_num1 at young_M0
                            linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, cut10, wl, ch.1, young_M0, cut6]
                          · rcases le_total e ((1/32):ℝ) with cut13 | cut13
                            · have ch := B.linear_charge (D := (3/16)) (E := (1/32)) (U := (250001/1000000)) cut9 (by norm_num) cut13 (le_trans cut11 (by norm_num)) (by norm_num)
                              norm_num1 at ch
                              have young_M0 := (B.linear_young (D := (3/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                              norm_num1 at young_M0
                              linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, cut13, wl, ch.1, young_M0, cut12]
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (3/16)) (E := (1/16)) (U := (176777/1000000)) cut9 (by norm_num) cut10 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (3/16)) (u := (1/32)) cut9 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [B.p1, B.edge_eq, B.s0, B.old, B.holes, B.deficit, cut10, wl, ch.1, young_M0, cut12]
                              · linarith only [B.p1, B.edge_eq, B.spent, B.old, B.deficit, cut13, wl, cut14, cut12]
                        · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut11]
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((5/32):ℝ) with cut12 | cut12
                          · rcases le_total e ((3/32):ℝ) with cut13 | cut13
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (5/32)) (E := (3/32)) (U := (176777/1000000)) cut12 (by norm_num) cut13 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (5/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, ch.1, young_M0, cut6]
                              · linarith only [B.p1, B.edge_eq, cut14, B.spent, B.old, B.deficit, wl, cut10, cut6]
                            · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, wl, cut13, cut6]
                          · rcases le_total e ((3/32):ℝ) with cut13 | cut13
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · rcases le_total d ((11/64):ℝ) with cut15 | cut15
                                · have ch := B.linear_charge (D := (11/64)) (E := (3/32)) (U := (176777/1000000)) cut15 (by norm_num) cut13 (le_trans cut14 (by norm_num)) (by norm_num)
                                  norm_num1 at ch
                                  have young_M0 := (B.linear_young (D := (11/64)) (u := (1/32)) cut15 (by norm_num) (by norm_num))
                                  norm_num1 at young_M0
                                  linarith only [B.p1, B.edge_eq, young_M0, B.s0, B.spent, B.old, B.holes, B.deficit, wl, ch.1, cut12]
                                · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, cut10, wl, cut15]
                              · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, cut14, cut10, wl]
                            · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, cut13, wl, cut12]
                        · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, cut10, cut11, wl]
                    · rcases le_total e ((1/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((7/32):ℝ) with cut12 | cut12
                          · rcases le_total e ((1/32):ℝ) with cut13 | cut13
                            · have ch := B.linear_charge (D := (7/32)) (E := (1/32)) (U := (250001/1000000)) cut12 (by norm_num) cut13 (le_trans cut11 (by norm_num)) (by norm_num)
                              norm_num1 at ch
                              have young_M0 := (B.linear_young (D := (7/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                              norm_num1 at young_M0
                              linarith only [B.p1, B.edge_eq, B.s0, B.old, cut13, B.holes, B.deficit, wl, ch.1, young_M0, cut9]
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · rcases le_total d ((13/64):ℝ) with cut15 | cut15
                                · have ch := B.linear_charge (D := (13/64)) (E := (1/16)) (U := (176777/1000000)) cut15 (by norm_num) cut10 (le_trans cut14 (by norm_num)) (by norm_num)
                                  norm_num1 at ch
                                  have young_M0 := (B.linear_young (D := (13/64)) (u := (1/32)) cut15 (by norm_num) (by norm_num))
                                  norm_num1 at young_M0
                                  linarith only [B.p1, B.edge_eq, B.s0, B.old, cut10, B.holes, B.deficit, wl, ch.1, young_M0, cut9]
                                · have ch := B.linear_charge (D := (7/32)) (E := (1/16)) (U := (176777/1000000)) cut12 (by norm_num) cut10 (le_trans cut14 (by norm_num)) (by norm_num)
                                  norm_num1 at ch
                                  have young_M0 := (B.linear_young (D := (7/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                                  norm_num1 at young_M0
                                  linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, ch.1, young_M0, cut15]
                              · linarith only [B.p1, B.edge_eq, B.k0, B.spent, B.old, cut14, wl, cut13]
                          · rcases le_total e ((1/32):ℝ) with cut13 | cut13
                            · rcases le_total s ((1/32):ℝ) with cut14 | cut14
                              · have ch := B.linear_charge (D := (1/4)) (E := (1/32)) (U := (176777/1000000)) cut3 (by norm_num) cut13 (le_trans cut14 (by norm_num)) (by norm_num)
                                norm_num1 at ch
                                have young_M0 := (B.linear_young (D := (1/4)) (u := (1/32)) cut3 (by norm_num) (by norm_num))
                                norm_num1 at young_M0
                                linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, cut12, young_M0, ch.1]
                              · linarith only [B.p1, B.edge_eq, B.e0, B.spent, B.old, B.deficit, cut14, wl, cut12]
                            · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, cut13, wl, cut12]
                        · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut11]
                      · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, cut9, wl, cut10]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut8]
                · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, wl, cut7, cut6]
            · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut5]
          · linarith only [cut4, B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl]
        · rcases le_total e ((1/4):ℝ) with cut4 | cut4
          · rcases le_total s ((1/4):ℝ) with cut5 | cut5
            · rcases le_total d ((3/8):ℝ) with cut6 | cut6
              · rcases le_total e ((1/8):ℝ) with cut7 | cut7
                · rcases le_total s ((1/8):ℝ) with cut8 | cut8
                  · rcases le_total d ((5/16):ℝ) with cut9 | cut9
                    · rcases le_total e ((1/16):ℝ) with cut10 | cut10
                      · rcases le_total s ((1/16):ℝ) with cut11 | cut11
                        · rcases le_total d ((9/32):ℝ) with cut12 | cut12
                          · have ch := B.linear_charge (D := (9/32)) (E := (1/16)) (U := (250001/1000000)) cut12 (by norm_num) cut10 (le_trans cut11 (by norm_num)) (by norm_num)
                            norm_num1 at ch
                            have young_M0 := (B.linear_young (D := (9/32)) (u := (1/32)) cut12 (by norm_num) (by norm_num))
                            norm_num1 at young_M0
                            linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.holes, B.deficit, wl, ch.1, young_M0, cut3]
                          · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut12]
                        · linarith only [cut11, B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl]
                      · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, B.deficit, wl, cut10, cut3]
                    · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut9]
                  · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut8]
                · linarith only [B.p1, B.edge_eq, B.s0, B.spent, B.old, cut7, B.deficit, wl, cut3]
              · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut6]
            · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, cut5, wl]
          · linarith only [cut4, B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl]
      · linarith only [B.p1, B.edge_eq, B.e0, B.k0, B.spent, B.old, wl, cut2]
    · linarith only [B.p1, B.edge_eq, B.s0, B.k0, B.spent, B.old, wl, cut1]
  · linarith only [B.p1, B.edge_eq, B.s0, B.e0, B.spent, B.old, B.deficit, wl, cut0]

private theorem zero_cell_4 {p t z s e k d h m w : ℝ}
    (B : ZeroBounds p t z s e k d h m w (327/2000) (459/2000))
    (yl : 1 ≤ 2-p/2-(199/400)*t)
    (yr : 2-p/2-(199/400)*t ≤ 2)
    (wl : (1481303437/100000000)-(2-p/2-(199/400)*t)/(327/2000)-(p+t)/(459/2000)+(349+114*p)/1000 ≤ w) : False := by
  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]
  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]
  linarith only [B.edge_eq, B.s0, B.e0, B.k0, B.spent, B.old, yl, wl]
/-- No zero-pair configuration can fail both width tests at exponent 143. -/
theorem zero_branch_impossible {p t z s e k d h m w α β b : ℝ}
    (band : RetainedWidth.Band (2-p/2-(199/400)*t) b α β)
    (bounds : ZeroBounds p t z s e k d h m w α β)
    (width : ((143-b)/4-10)*(69314718/100000000)-8963/100000-
      (2-p/2-(199/400)*t)/α-(p+t)/β+(349+114*p)/1000 ≤ w) : False := by
  cases band with
  | first yl yr => exact zero_cell_0 (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)
  | second yl yr => exact zero_cell_1 (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)
  | third yl yr => exact zero_cell_2 (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)
  | fourth yl yr => exact zero_cell_3 (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)
  | fifth yl yr => exact zero_cell_4 (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)

end
end Erdos617.ThirdPruning
