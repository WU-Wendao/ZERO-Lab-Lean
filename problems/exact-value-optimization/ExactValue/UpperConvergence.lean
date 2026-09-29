import ExactValue.FiniteDifferenceUpper

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem upper_initial_error {β R ε : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hε : 0 < ε) {N : ℕ} (hN : 0 < N)
    (hNbound : 2 * Real.sqrt (β * R ^ 2 / ε) ≤ N) :
    (R / 2) ^ 2 / (2 * accelerationWeight (2 * β) N) ≤ ε / 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha := accelerationWeight_lower (show 0 < 2 * β by positivity) N
  have ha' : (N : ℝ) ^ 2 ≤ 8 * β * accelerationWeight (2 * β) N := by
    have h := (div_le_iff₀ (show 0 < 4 * (2 * β) by positivity)).mp ha
    nlinarith
  have hstep : (R / 2) ^ 2 / (2 * accelerationWeight (2 * β) N) ≤ β * R ^ 2 / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (accelerationWeight_pos (by positivity) hN))
      (sq_pos_of_pos hn)).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha' (sq_nonneg R)]
  have hQpos : 0 ≤ β * R ^ 2 / ε := by positivity
  have hs := Real.sq_sqrt hQpos
  have hsN := pow_le_pow_left₀ (show 0 ≤ 2 * Real.sqrt (β * R ^ 2 / ε) by positivity) hNbound 2
  have hprod := mul_le_mul_of_nonneg_left hsN hε.le
  have hcancel : (β * R ^ 2 / ε) * ε = β * R ^ 2 := div_mul_cancel₀ _ hε.ne'
  apply hstep.trans
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith [congrArg (fun v : ℝ => v * ε) hs]

theorem upper_error_terms {β R ε : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) (N : ℕ) :
    (N + 1) * (R * upperGradientAccuracy R ε N) = ε / 8 ∧
      (N : ℝ) * (upperGradientAccuracy R ε N ^ 2 / (2 * β)) ≤ ε / 128 := by
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  constructor
  · unfold upperGradientAccuracy
    field_simp
    ring
  · have hratio : (N : ℝ) / ((N : ℝ) + 1) ^ 2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos hNp)).mpr
      have := Nat.cast_nonneg (α := ℝ) N
      nlinarith
    have herr : ε ^ 2 / (128 * β * R ^ 2) ≤ ε / 128 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hεmax hε.le]
    calc
      _ = ((N : ℝ) / ((N : ℝ) + 1) ^ 2) * (ε ^ 2 / (128 * β * R ^ 2)) := by
        unfold upperGradientAccuracy
        field_simp
        ring_nf
        simp
      _ ≤ 1 * (ε / 128) := mul_le_mul hratio herr (by positivity) (by norm_num)
      _ = _ := one_mul _

theorem upper_iterate_accuracy {d : ℕ} (hd : 0 < d) {f : Euclid d → ℝ} {β R ε : ℝ}
    (hf : AdmissibleObjective d β R f) (hβ : 0 < β) (hR : 0 < R)
    (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    let N := upperIterationCount β R ε
    let h := upperDifferenceStep d β R ε N
    let K := ballDomain (d := d) (R / 2) (by positivity)
    ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧
      f (accelRun K f (finiteGradient f h) (2 * β) N).x - f xstar < ε := by
  dsimp only
  obtain ⟨hN, _, hh, _, hδeq, _⟩ := upper_parameter_bounds hd hβ hR hε hεmax
  obtain ⟨xstar, hmin, herr⟩ := finiteDifference_run_error hf hβ hR hh hδeq.le (show
    0 < upperIterationCount β R ε by omega)
  have hfirst := upper_initial_error hβ hR hε (show 0 < upperIterationCount β R ε by omega)
    (Nat.le_ceil _)
  obtain ⟨hl, hu⟩ := upper_error_terms hβ hR hε hεmax (upperIterationCount β R ε)
  exact ⟨xstar, hmin, upper_error_budget hε (by linarith)⟩

end

end ExactValue
