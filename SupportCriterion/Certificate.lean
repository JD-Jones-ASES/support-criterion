module

public import SupportCriterion.CertificateRow0
public import SupportCriterion.CertificateRow1
public import SupportCriterion.CertificateRow2
public import SupportCriterion.CertificateRow3
public import SupportCriterion.CertificateRow4
public import SupportCriterion.CertificateRow5
public import SupportCriterion.CertificateRow6
public import SupportCriterion.CertificateRow7

@[expose] public section

/-! Complete closed-cell coverage and inversion of the rational compactification. -/
namespace SupportCriterion

lemma cover_eight (x : ℝ) (h0 : 0 ≤ x) (h8 : x ≤ 8) :
    ∃ i : Fin 8, (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
  by_cases h1 : x ≤ 1
  · exact ⟨0, by norm_num; exact ⟨h0, h1⟩⟩
  by_cases h2 : x ≤ 2
  · exact ⟨1, by norm_num; constructor <;> linarith⟩
  by_cases h3 : x ≤ 3
  · exact ⟨2, by norm_num; constructor <;> linarith⟩
  by_cases h4 : x ≤ 4
  · exact ⟨3, by norm_num; constructor <;> linarith⟩
  by_cases h5 : x ≤ 5
  · exact ⟨4, by norm_num; constructor <;> linarith⟩
  by_cases h6 : x ≤ 6
  · exact ⟨5, by norm_num; constructor <;> linarith⟩
  by_cases h7 : x ≤ 7
  · exact ⟨6, by norm_num; constructor <;> linarith⟩
  exact ⟨7, by norm_num; constructor <;> linarith⟩

lemma shifted_any_cell (i j : Fin 8) (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ shiftedPolynomial (9*((i:ℝ)+x)/160) (((j:ℝ)+y)/8) := by
  fin_cases i <;> fin_cases j
  · simpa using shifted_cell_0_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_0_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_1_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_2_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_3_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_4_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_5_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_6_7 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_0 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_1 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_2 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_3 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_4 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_5 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_6 x y hx0 hx1 hy0 hy1
  · simpa using shifted_cell_7_7 x y hx0 hx1 hy0 hy1

lemma shiftedPolynomial_nonneg (w r : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 9/20)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ shiftedPolynomial w r := by
  obtain ⟨i, hi0, hi1⟩ := cover_eight (w*160/9) (by positivity) (by linarith)
  obtain ⟨j, hj0, hj1⟩ := cover_eight (r*8) (by positivity) (by linarith)
  have h := shifted_any_cell i j (w*160/9-i) (r*8-j)
    (by linarith) (by linarith) (by linarith) (by linarith)
  convert h using 1 <;> congr 1 <;> ring

lemma gapPolynomial_lower (v z : ℝ) (hv0 : 11/20 ≤ v) (hv1 : v ≤ 1)
    (hz : 0 ≤ z) : ((v-1)^2 + z^2)/4000 ≤ gapPolynomial v z := by
  by_cases he : v = 1
  · subst v
    unfold gapPolynomial
    nlinarith [sq_nonneg z, pow_nonneg hz 3]
  have hw : 0 < 1-v := sub_pos.mpr (lt_of_le_of_ne hv1 he)
  have hd : 0 < z+7*(1-v) := by positivity
  have hr0 : 0 ≤ z/(z+7*(1-v)) := div_nonneg hz hd.le
  have hr1 : z/(z+7*(1-v)) ≤ 1 := (div_le_one hd).2 (by linarith)
  have hc := shiftedPolynomial_nonneg (1-v) (z/(z+7*(1-v)))
    hw.le (by linarith) hr0 hr1
  have hi : shiftedPolynomial (1-v) (z/(z+7*(1-v))) * (z+7*(1-v))^3 =
      343*(1-v)*(gapPolynomial v z - ((v-1)^2+z^2)/4000) := by
    unfold shiftedPolynomial compactPolynomial gapPolynomial
    field_simp
    <;> ring
  have hm := mul_nonneg hc (pow_nonneg hd.le 3)
  rw [hi] at hm
  have := (mul_nonneg_iff_of_pos_left (show 0 < 343*(1-v) by positivity)).1 hm
  linarith

end SupportCriterion
