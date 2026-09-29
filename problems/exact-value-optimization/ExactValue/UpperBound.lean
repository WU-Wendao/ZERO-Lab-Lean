import ExactValue.BatchAlgorithm

open scoped ENNReal

set_option autoImplicit false

namespace ExactValue

noncomputable section

def acceleratedValueAlgorithm {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    ValueAlgorithm d R ((d + 1) * upperIterationCount β R ε) :=
  batchValueAlgorithm hR.le (show 0 < 2 * β by positivity)
    (upper_parameter_bounds hd hβ hR hε hεmax).2.2.1.le
    (upper_parameter_bounds hd hβ hR hε hεmax).2.2.2.1 (upperIterationCount β R ε)

theorem acceleratedValueAlgorithm_guarantees {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    (acceleratedValueAlgorithm hd hβ hR hε hεmax).Guarantees (β := β) (ε := ε) := by
  intro f hf
  obtain ⟨xstar, hmin, herr⟩ := upper_iterate_accuracy hd hf hβ hR hε hεmax
  refine ⟨xstar, hmin, ?_⟩
  unfold acceleratedValueAlgorithm
  rw [batch_algorithm_result]
  exact herr.le

theorem valueComplexity_upper_calls {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    valueComplexity d R β ε ≤ ((d + 1) * upperIterationCount β R ε : ℕ) :=
  valueComplexity_le (acceleratedValueAlgorithm hd hβ hR hε hεmax)
    (acceleratedValueAlgorithm_guarantees hd hβ hR hε hεmax)

theorem valueComplexity_upper {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    valueComplexity d R β ε ≤ ENNReal.ofReal (6 * d * Real.sqrt (β * R ^ 2 / ε)) := by
  have hcount := (upper_parameter_bounds hd hβ hR hε hεmax).2.2.2.2.2
  have hreal : (((d + 1) * upperIterationCount β R ε : ℕ) : ℝ) ≤
      6 * d * Real.sqrt (β * R ^ 2 / ε) := by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcount
  apply (valueComplexity_upper_calls hd hβ hR hε hεmax).trans
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hreal

theorem acceleratedValueAlgorithm_output_inner {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2)
    (hist : QueryHistory d R ((d + 1) * upperIterationCount β R ε)) :
    ‖((acceleratedValueAlgorithm hd hβ hR hε hεmax).output hist : Euclid d)‖ ≤ R / 2 := by
  have hz : (0 : Euclid d) ∈ (ballDomain (R / 2) (by positivity)).carrier := by
    simpa [ballDomain] using (show 0 ≤ R / 2 by positivity)
  have hm := batchRun_mem (ballDomain (d := d) (R / 2) (by positivity)) hz
    (show 0 < 2 * β by positivity) (upperDifferenceStep d β R ε (upperIterationCount β R ε))
    (historyValues hist) (upperIterationCount β R ε)
  simpa [acceleratedValueAlgorithm, batchValueAlgorithm, ballDomain] using hm

end

end ExactValue
