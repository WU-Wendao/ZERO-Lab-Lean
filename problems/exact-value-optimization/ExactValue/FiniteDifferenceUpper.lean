import ExactValue.Acceleration
import ExactValue.SmoothModel

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem finiteDifference_model {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    {β R h δ : ℝ} (hβ : 0 < β) (hR : 0 ≤ R) (hh : 0 < h)
    (hconv : ConvexOn ℝ Set.univ f) (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖)
    (hδ : β * h * Real.sqrt d / 2 ≤ δ) :
    InexactModel (ballDomain (R / 2) (by positivity)) f (finiteGradient f h)
      (2 * β) (R * δ) (δ ^ 2 / (2 * β)) := by
  have herr (y : Euclid d) : ‖finiteGradient f h y - G y‖ ≤ δ :=
    (finiteGradient_error hβ.le hh hder hLip y).trans hδ
  constructor
  · intro x hx y hy
    have hx' : ‖x‖ ≤ R / 2 := by simpa [ballDomain] using hx
    have hy' : ‖y‖ ≤ R / 2 := by simpa [ballDomain] using hy
    exact inexact_oracle_lower (convex_supporting hconv hder x y) (herr y) (ball_diameter hx' hy')
  · intro x _ y _
    have hr := smooth_remainder hder hLip y (x - y)
    rw [add_sub_cancel] at hr
    have hup : f x ≤ f y + ⟪G y, x - y⟫_ℝ + β / 2 * ‖x - y‖ ^ 2 := by
      have ht := (le_abs_self _).trans hr
      linarith
    exact inexact_oracle_upper hβ hup (herr y)

theorem finiteDifference_run_error {d : ℕ} {f : Euclid d → ℝ} {β R h δ : ℝ}
    (hf : AdmissibleObjective d β R f) (hβ : 0 < β) (hR : 0 < R) (hh : 0 < h)
    (hδ : β * h * Real.sqrt d / 2 ≤ δ) {N : ℕ} (hN : 0 < N) :
    ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧
      f (accelRun (ballDomain (R / 2) (by positivity)) f (finiteGradient f h) (2 * β) N).x - f xstar ≤
        (R / 2) ^ 2 / (2 * accelerationWeight (2 * β) N) +
          (N + 1) * (R * δ) + N * (δ ^ 2 / (2 * β)) := by
  obtain ⟨G, hder, hLip⟩ := hf.gradient_lipschitz
  obtain ⟨xstar, hxstar, hmin, _⟩ := hf.minimizer
  let K := ballDomain (d := d) (R / 2) (by positivity)
  have hzero : (0 : Euclid d) ∈ K.carrier := by simp [K, ballDomain]; positivity
  have hx : xstar ∈ K.carrier := by simpa [K, ballDomain] using hxstar
  have hδ0 : 0 ≤ δ := (show 0 ≤ β * h * Real.sqrt d / 2 by positivity).trans hδ
  have hmodel := finiteDifference_model hβ hR.le hh hf.convex hder hLip hδ
  have herr := accelRun_error K hzero f (finiteGradient f h) (by positivity : 0 < 2 * β)
    (show 0 ≤ R * δ by positivity) (show 0 ≤ δ ^ 2 / (2 * β) by positivity) hmodel xstar hx hN
  have hnorm : ‖xstar‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxstar 2
  have hden : 0 < 2 * accelerationWeight (2 * β) N :=
    mul_pos (by norm_num) (accelerationWeight_pos (by positivity) hN)
  have hfirst := div_le_div_of_nonneg_right hnorm hden.le
  exact ⟨xstar, hmin, by dsimp [K] at herr; linarith⟩

def upperIterationCount (β R ε : ℝ) : ℕ := ⌈2 * Real.sqrt (β * R ^ 2 / ε)⌉₊

def upperGradientAccuracy (R ε : ℝ) (N : ℕ) : ℝ := ε / (8 * R * (N + 1))

def upperDifferenceStep (d : ℕ) (β R ε : ℝ) (N : ℕ) : ℝ :=
  2 * upperGradientAccuracy R ε N / (β * Real.sqrt d)

theorem upper_parameter_bounds {d : ℕ} (hd : 0 < d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    let N := upperIterationCount β R ε
    let δ := upperGradientAccuracy R ε N
    let h := upperDifferenceStep d β R ε N
    2 ≤ N ∧ 0 < δ ∧ 0 < h ∧ h ≤ R / 2 ∧ β * h * Real.sqrt d / 2 = δ ∧
      ((d + 1) * N : ℝ) ≤ 6 * d * Real.sqrt (β * R ^ 2 / ε) := by
  dsimp only
  let N := upperIterationCount β R ε
  let δ := upperGradientAccuracy R ε N
  have hQ : 1 ≤ β * R ^ 2 / ε := (one_le_div hε).mpr hεmax
  have hsQ : 1 ≤ Real.sqrt (β * R ^ 2 / ε) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hQ)
  have hNreal : (2 : ℝ) ≤ N := (show 2 ≤ 2 * Real.sqrt (β * R ^ 2 / ε) by linarith).trans
    (Nat.le_ceil _)
  have hN : 2 ≤ N := by exact_mod_cast hNreal
  have hδpos : 0 < δ := by dsimp [δ, upperGradientAccuracy]; positivity
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsd : 1 ≤ Real.sqrt (d : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr
    (by simpa using hdreal)
  have hδle : δ ≤ β * R / 8 := by
    change ε / (8 * R * (N + 1)) ≤ β * R / 8
    apply (div_le_iff₀ (by positivity)).mpr
    have hx : β * R ^ 2 ≤ β * R ^ 2 * (N + 1) := by
      exact le_mul_of_one_le_right (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    nlinarith
  have hhpos : 0 < upperDifferenceStep d β R ε N := by
    unfold upperDifferenceStep
    change 0 < 2 * δ / (β * Real.sqrt d)
    positivity
  have hhlen : upperDifferenceStep d β R ε N ≤ R / 2 := by
    change 2 * δ / (β * Real.sqrt d) ≤ R / 2
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hsd (show 0 ≤ β * R by positivity)
    nlinarith
  have herror : β * upperDifferenceStep d β R ε N * Real.sqrt d / 2 = δ := by
    unfold upperDifferenceStep
    change β * (2 * δ / (β * Real.sqrt d)) * Real.sqrt d / 2 = δ
    field_simp
    ring
  refine ⟨hN, hδpos, hhpos, hhlen, herror, ?_⟩
  apply upper_call_count (by omega) hQ
  exact (Nat.ceil_lt_add_one (by positivity)).le

end

end ExactValue
