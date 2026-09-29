import ExactValue.ComplexityLower

open scoped ENNReal

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem dimensionScale_sq {d : ℕ} (hd : 1 ≤ d) :
    dimensionScale d ^ 2 = ((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (2 / 3 : ℝ) := by
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  have hbase : 0 ≤ (d : ℝ) / (1 + Real.log (d : ℝ)) := by positivity
  have h := Real.rpow_mul_natCast hbase (1 / 3 : ℝ) 2
  norm_num at h
  exact h.symm

theorem dimensionScale_reciprocal {d : ℕ} (hd : 1 ≤ d) :
    (((1 + Real.log (d : ℝ)) / d) ^ (2 / 3 : ℝ)) * dimensionScale d ^ 2 = 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  have hbase : 0 < (d : ℝ) / (1 + Real.log (d : ℝ)) := by positivity
  rw [dimensionScale_sq hd, show (1 + Real.log (d : ℝ)) / d =
    ((d : ℝ) / (1 + Real.log (d : ℝ)))⁻¹ by simp]
  rw [Real.inv_rpow hbase.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hbase _).ne']

theorem dimensionScale_product {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * dimensionScale d = (d : ℝ) ^ (4 / 3 : ℝ) / (1 + Real.log (d : ℝ)) ^ (1 / 3 : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  rw [dimensionScale, Real.div_rpow hdpos.le (by positivity),
    show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hdpos, Real.rpow_one]
  ring

theorem low_accuracy_regime {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2)
    (hregime : β * R ^ 2 / ε ≤ ((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (2 / 3 : ℝ)) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (β * R ^ 2 / ε)) ≤ valueComplexity d R β ε := by
  have hd1 : 1 ≤ d := by omega
  have hbranch : Real.sqrt (β * R ^ 2 / ε) ≤ dimensionScale d := by
    apply (Real.sqrt_le_left (dimensionScale_pos hd1).le).mpr
    rwa [dimensionScale_sq hd1]
  have hmain := dimension_accuracy_lower hd hβ hR hε hεsmall
  simpa only [lowerScale, min_eq_left hbranch] using hmain

theorem high_accuracy_regime {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2)
    (hregime : ((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (2 / 3 : ℝ) ≤ β * R ^ 2 / ε) :
    ENNReal.ofReal ((1 / 8192 : ℝ) *
      ((d : ℝ) ^ (4 / 3 : ℝ) / (1 + Real.log (d : ℝ)) ^ (1 / 3 : ℝ))) ≤ valueComplexity d R β ε := by
  have hd1 : 1 ≤ d := by omega
  have hbranch : dimensionScale d ≤ Real.sqrt (β * R ^ 2 / ε) := by
    apply (Real.le_sqrt (dimensionScale_pos hd1).le (by positivity)).mpr
    rwa [dimensionScale_sq hd1]
  have hmain := dimension_accuracy_lower hd hβ hR hε hεsmall
  rw [lowerScale, min_eq_right hbranch, mul_assoc, dimensionScale_product hd1] at hmain
  exact hmain

theorem matching_complexity {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (hεlower : β * R ^ 2 * (((1 + Real.log (d : ℝ)) / d) ^ (2 / 3 : ℝ)) ≤ ε)
    (hεupper : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * Real.sqrt (β * R ^ 2 / ε)) ≤ valueComplexity d R β ε ∧
      valueComplexity d R β ε ≤ ENNReal.ofReal (6 * d * Real.sqrt (β * R ^ 2 / ε)) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd1)
  have hrpos : 0 < ((1 + Real.log (d : ℝ)) / d) ^ (2 / 3 : ℝ) := by positivity
  have hε : 0 < ε := (mul_pos (mul_pos hβ (sq_pos_of_pos hR)) hrpos).trans_le hεlower
  have hmul := mul_le_mul_of_nonneg_right hεlower (sq_nonneg (dimensionScale d))
  have hrec := congrArg (fun v : ℝ => (β * R ^ 2) * v) (dimensionScale_reciprocal hd1)
  have hregime : β * R ^ 2 / ε ≤ ((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (2 / 3 : ℝ) := by
    rw [← dimensionScale_sq hd1]
    apply (div_le_iff₀ hε).mpr
    nlinarith
  have hεmax : ε ≤ β * R ^ 2 := by nlinarith [mul_pos hβ (sq_pos_of_pos hR)]
  exact ⟨low_accuracy_regime hd hβ hR hε hεupper hregime,
    valueComplexity_upper (by omega) hβ hR hε hεmax⟩

/-- Matching minimax complexity throughout the moderate-accuracy interval in the manuscript. -/
theorem matching_rate :
    ∃ c C cε : ℝ, ∃ d₀ : ℕ, 0 < c ∧ 0 < C ∧ 0 < cε ∧
      ∀ (d : ℕ), d₀ ≤ d → ∀ β R ε : ℝ, 0 < β → 0 < R →
        β * R ^ 2 * (((1 + Real.log (d : ℝ)) / d) ^ (2 / 3 : ℝ)) ≤ ε → ε ≤ cε * β * R ^ 2 →
        ENNReal.ofReal (c * d * Real.sqrt (β * R ^ 2 / ε)) ≤ valueComplexity d R β ε ∧
          valueComplexity d R β ε ≤ ENNReal.ofReal (C * d * Real.sqrt (β * R ^ 2 / ε)) := by
  refine ⟨1 / 8192, 6, 1 / 1048576, 18446744073709551616, by norm_num, by norm_num, by norm_num, ?_⟩
  intro d hd β R ε hβ hR hlo hhi
  exact matching_complexity hd hβ hR hlo hhi

end

end ExactValue
