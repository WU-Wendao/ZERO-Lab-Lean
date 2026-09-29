import ExactValue.DimensionScale

open scoped ENNReal

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem valueComplexity_lower_of_failure {d : ℕ} {R β ε c : ℝ}
    (hfail : ∀ T : ℕ, (T : ℝ) < c → ∀ A : ValueAlgorithm d R T, ¬ A.Guarantees (β := β) (ε := ε)) :
    ENNReal.ofReal c ≤ valueComplexity d R β ε := by
  apply le_iInf
  intro T
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  have hreal : c ≤ (T : ℝ) := by
    by_contra hc
    exact hfail T (lt_of_not_ge hc) A hA
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal

theorem integer_budget_failure {d m T : ℕ} (hd : 8 ≤ d) (hm : 0 < m)
    (hmd : 4 * m ≤ d) (hT : 8 * T < d * m) {β R ε : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hscale : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d)
    (hgap : ε < 11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2))
    (A : ValueAlgorithm d R T) : ¬ A.Guarantees (β := β) (ε := ε) := by
  intro hA
  obtain ⟨f, hf, xstar, hmin, hbad⟩ := algorithm_integer_lower_bound hd hm hmd hT hβ hR hscale A
  obtain ⟨zstar, hzmin, hgood⟩ := hA f hf
  have hx := hmin zstar
  have hz := hzmin xstar
  linarith

theorem dimension_accuracy_lower {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * lowerScale d β R ε) ≤ valueComplexity d R β ε := by
  let M := lowerScale d β R ε
  let m := ⌊M / 512⌋₊
  obtain ⟨hm, hmd, hround, _, hscale, hgap⟩ := lowerScale_floor hd hβ hR hε hεsmall
  apply valueComplexity_lower_of_failure
  intro T hT A
  have hbudget : 8 * T < d * m := by
    have hmul := mul_le_mul_of_nonneg_left hround (show (0 : ℝ) ≤ d by positivity)
    have hreal : (8 : ℝ) * T < (d : ℝ) * m := by
      change (T : ℝ) < (1 / 8192 : ℝ) * d * M at hT
      change (d : ℝ) * (M / 1024) ≤ (d : ℝ) * m at hmul
      nlinarith
    exact_mod_cast hreal
  exact integer_budget_failure (by omega) hm hmd hbudget hβ hR hscale hgap A

/-- The manuscript's dimension-accuracy theorem, with explicit universal witnesses. -/
theorem main_lower_rate :
    ∃ c cε : ℝ, ∃ d₀ : ℕ, 0 < c ∧ 0 < cε ∧
      ∀ (d : ℕ), d₀ ≤ d → ∀ β R ε : ℝ, 0 < β → 0 < R → 0 < ε → ε ≤ cε * β * R ^ 2 →
        ENNReal.ofReal (c * d * min (Real.sqrt (β * R ^ 2 / ε))
          (((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (1 / 3 : ℝ))) ≤ valueComplexity d R β ε := by
  refine ⟨1 / 8192, 1 / 1048576, 18446744073709551616, by norm_num, by norm_num, ?_⟩
  intro d hd β R ε hβ hR hε hεsmall
  exact dimension_accuracy_lower hd hβ hR hε hεsmall

end

end ExactValue
