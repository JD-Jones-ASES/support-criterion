module

public import SupportCriterion.Certificate
public import SupportCriterion.SharpGapRow0
public import SupportCriterion.SharpGapRow1
public import SupportCriterion.SharpGapRow2
public import SupportCriterion.SharpGapRow3
public import SupportCriterion.SharpGapRow4
public import SupportCriterion.SharpGapRow5
public import SupportCriterion.SharpGapRow6
public import SupportCriterion.SharpGapRow7

@[expose] public section

namespace SupportCriterion

lemma sharp_gap_any_cell (i j : Fin 8) (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ sharpCompactPolynomial (9*((i:ℝ)+x)/160) (((j:ℝ)+y)/8) := by
  fin_cases i <;> fin_cases j
  · simpa using sharp_gap_cell_0_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_0_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_1_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_2_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_3_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_4_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_5_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_6_7 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_0 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_1 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_2 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_3 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_4 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_5 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_6 x y hx0 hx1 hy0 hy1
  · simpa using sharp_gap_cell_7_7 x y hx0 hx1 hy0 hy1

lemma sharpCompactPolynomial_nonneg (w r : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 9/20)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ sharpCompactPolynomial w r := by
  obtain ⟨i, hi0, hi1⟩ := cover_eight (w*160/9) (by positivity) (by linarith)
  obtain ⟨j, hj0, hj1⟩ := cover_eight (r*8) (by positivity) (by linarith)
  have h := sharp_gap_any_cell i j (w*160/9-i) (r*8-j)
    (by linarith) (by linarith) (by linarith) (by linarith)
  convert h using 1 <;> congr 1 <;> ring

lemma sharpGapPolynomial_lower (v z : ℝ) (hv0 : 11/20 ≤ v) (hv1 : v ≤ 1)
    (hz : 0 ≤ z) : z^2/1575 ≤ sharpGapPolynomial v z := by
  by_cases he : v = 1
  · subst v
    unfold sharpGapPolynomial gapPolynomial
    nlinarith [sq_nonneg z, pow_nonneg hz 3, pow_nonneg hz 4]
  have hw : 0 < 1-v := sub_pos.mpr (lt_of_le_of_ne hv1 he)
  have hd : 0 < z+15/2*(1-v) := by positivity
  have hr0 : 0 ≤ z/(z+15/2*(1-v)) := div_nonneg hz hd.le
  have hr1 : z/(z+15/2*(1-v)) ≤ 1 := (div_le_one hd).2 (by linarith)
  have hc := sharpCompactPolynomial_nonneg (1-v) (z/(z+15/2*(1-v)))
    hw.le (by linarith) hr0 hr1
  have hi : sharpCompactPolynomial (1-v) (z/(z+15/2*(1-v))) *
      (z+15/2*(1-v))^4 =
      (15/2)^4*(1-v)^2*(sharpGapPolynomial v z-z^2/1575) := by
    unfold sharpCompactPolynomial sharpGapPolynomial gapPolynomial
    field_simp
    <;> ring
  have hm := mul_nonneg hc (pow_nonneg hd.le 4)
  rw [hi] at hm
  have := (mul_nonneg_iff_of_pos_left
    (show 0 < (15/2:ℝ)^4*(1-v)^2 by positivity)).1 hm
  linarith

end SupportCriterion
