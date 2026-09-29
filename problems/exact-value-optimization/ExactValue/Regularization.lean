import ExactValue.BallPenalty
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def regularized {d : ℕ} (H : Euclid d → ℝ) (β η r : ℝ) (x : Euclid d) : ℝ :=
  H x + β / 8 * (max (‖x‖ - r) 0) ^ 2 + η / 2 * ‖x‖ ^ 2

theorem regularized_eq_distance {d : ℕ} (H : Euclid d → ℝ) (β η r : ℝ)
    (hr : 0 ≤ r) (x : Euclid d) :
    regularized H β η r x = H x + β / 4 * (ballDomain r hr).halfSquaredDistance x +
      η / 2 * ‖x‖ ^ 2 := by
  rw [regularized, ball_halfSquaredDistance]
  ring

theorem regularized_strongConvex {d : ℕ} {H : Euclid d → ℝ} {β η r : ℝ}
    (hH : ConvexOn ℝ Set.univ H) (hβ : 0 ≤ β) (hr : 0 ≤ r) :
    StrongConvexOn Set.univ η (regularized H β η r) := by
  rw [strongConvexOn_iff_convex]
  have hconv := hH.add ((ballDomain (d := d) r hr).halfSquaredDistance_convex.smul
    (show 0 ≤ β / 4 by positivity))
  convert hconv using 1
  ext x
  rw [regularized_eq_distance H β η r hr x]
  simp [smul_eq_mul]

theorem regularized_contDiff {d : ℕ} {H : Euclid d → ℝ} {β η r : ℝ}
    (hH : ContDiff ℝ 1 H) (hr : 0 ≤ r) : ContDiff ℝ 1 (regularized H β η r) := by
  have hd := (ballDomain (d := d) r hr).halfSquaredDistance_contDiff
  have hc := (hH.add ((contDiff_const (c := β / 4)).mul hd)).add
    ((contDiff_const (c := η / 2)).mul (contDiff_norm_sq ℝ))
  convert hc using 1
  ext x
  exact regularized_eq_distance H β η r hr x

def regularizedGradient {d : ℕ} (G : Euclid d → Euclid d) (β η r : ℝ)
    (hr : 0 ≤ r) (x : Euclid d) : Euclid d :=
  G x + (β / 4) • (ballDomain r hr).residual x + η • x

theorem regularized_hasFDerivAt {d : ℕ} {H : Euclid d → ℝ} {G : Euclid d → Euclid d}
    {β η r : ℝ} (hr : 0 ≤ r) (x : Euclid d)
    (hH : HasFDerivAt H (innerSL ℝ (G x)) x) :
    HasFDerivAt (regularized H β η r) (innerSL ℝ (regularizedGradient G β η r hr x)) x := by
  have hd := (ballDomain (d := d) r hr).halfSquaredDistance_hasFDerivAt x
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hc := (hH.add (hd.const_mul (β / 4))).add (hn.const_mul (η / 2))
  convert hc using 1
  · ext y
    exact regularized_eq_distance H β η r hr y
  · ext y
    simp [regularizedGradient, innerSL_apply, inner_add_left, real_inner_smul_left]
    ring

theorem regularizedGradient_bound {d : ℕ} {G : Euclid d → Euclid d} {β η r L : ℝ}
    (hr : 0 ≤ r) (hβ : 0 ≤ β) (hη : 0 ≤ η)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : Euclid d) :
    ‖regularizedGradient G β η r hr x - regularizedGradient G β η r hr y‖ ≤
      (L + β / 4 + η) * ‖x - y‖ := by
  have hd := (ballDomain (d := d) r hr).residual_lipschitz.norm_sub_le x y
  simp only [NNReal.coe_one, one_mul] at hd
  have hg := hG x y
  have heq : regularizedGradient G β η r hr x - regularizedGradient G β η r hr y =
      ((G x - G y) + (β / 4) • ((ballDomain r hr).residual x - (ballDomain r hr).residual y)) +
        η • (x - y) := by unfold regularizedGradient; simp only [smul_sub]; abel
  rw [heq]
  have hnorm := (norm_add_le ((G x - G y) + (β / 4) •
    ((ballDomain r hr).residual x - (ballDomain r hr).residual y)) (η • (x - y))).trans
      (add_le_add_right (norm_add_le _ _) _)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη,
    abs_of_nonneg (show 0 ≤ β / 4 by positivity)] at hnorm
  nlinarith

/-- Points beyond this radius are strictly improved by scaling to the r-ball. -/
theorem regularized_outside_comparison {d : ℕ} {H : Euclid d → ℝ} {β η r A : ℝ}
    (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hH : ∀ x y, H x - H y ≤ A * ‖x - y‖)
    (x : Euclid d) (hout : r + 8 * A / β < ‖x‖) :
    regularized H β η r ((r / ‖x‖) • x) < regularized H β η r x := by
  have hxr : r < ‖x‖ := by
    have : 0 ≤ 8 * A / β := by positivity
    linarith
  have hn := scaled_norm hr x (lt_of_le_of_lt hr hxr)
  have hd := scaled_distance hr x hxr
  have hcore := hH ((r / ‖x‖) • x) x
  rw [← dist_eq_norm, dist_comm, hd] at hcore
  have hnum : 8 * A < (‖x‖ - r) * β :=
    (div_lt_iff₀ hβ).mp (by linarith : 8 * A / β < ‖x‖ - r)
  have hpositive : 0 < (‖x‖ - r) * (β / 8 * (‖x‖ - r) - A) := by
    apply mul_pos (by linarith)
    nlinarith
  have hquad : η / 2 * r ^ 2 ≤ η / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hxr.le 2) (by positivity)
  simp only [regularized, hn, sub_self, max_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, max_eq_left (show 0 ≤ ‖x‖ - r by linarith)]
  nlinarith

theorem regularized_exists_min {d : ℕ} {H : Euclid d → ℝ} {β η r A : ℝ}
    (hcontinuous : Continuous H) (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hH : ∀ x y, H x - H y ≤ A * ‖x - y‖) :
    ∃ x : Euclid d, (∀ y, regularized H β η r x ≤ regularized H β η r y) ∧
      ‖x‖ ≤ r + 8 * A / β := by
  classical
  let B := r + 8 * A / β + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBr : r ≤ B := by
    dsimp [B]
    have : 0 ≤ 8 * A / β := by positivity
    linarith
  have hc : Continuous (regularized H β η r) := by unfold regularized; fun_prop
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : Euclid d) B).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hB⟩ hc.continuousOn
  have hglobal : ∀ y, regularized H β η r x ≤ regularized H β η r y := by
    intro y
    by_cases hy : ‖y‖ ≤ B
    · exact hmin (by simpa using hy)
    · have hout : r + 8 * A / β < ‖y‖ := by dsimp [B] at hy; linarith
      have hyr : r < ‖y‖ := by
        have : 0 ≤ 8 * A / β := by positivity
        linarith
      have hz := scaled_norm hr y (lt_of_le_of_lt hr hyr)
      have hzmem : (r / ‖y‖) • y ∈ Metric.closedBall (0 : Euclid d) B := by
        simpa [hz] using hBr
      exact (hmin hzmem).trans (regularized_outside_comparison hβ hη hr hA hH y hout).le
  refine ⟨x, hglobal, ?_⟩
  by_contra hxout
  have hstrict := regularized_outside_comparison hβ hη hr hA hH x (lt_of_not_ge hxout)
  exact (not_lt_of_ge (hglobal _)) hstrict

theorem regularized_exists_unique_min {d : ℕ} {H : Euclid d → ℝ} {β η r A : ℝ}
    (hcontinuous : Continuous H) (hconvex : ConvexOn ℝ Set.univ H)
    (hβ : 0 < β) (hη : 0 < η) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hH : ∀ x y, H x - H y ≤ A * ‖x - y‖) :
    ∃ x : Euclid d, (∀ y, regularized H β η r x ≤ regularized H β η r y) ∧
      ‖x‖ ≤ r + 8 * A / β ∧
      ∀ z, (∀ y, regularized H β η r z ≤ regularized H β η r y) → z = x := by
  obtain ⟨x, hmin, hnorm⟩ := regularized_exists_min hcontinuous hβ hη.le hr hA hH
  refine ⟨x, hmin, hnorm, ?_⟩
  intro z hz
  exact (regularized_strongConvex hconvex hβ.le hr).strictConvexOn hη |>.eq_of_isMinOn
    (fun _ _ => hz _) (fun _ _ => hmin _) (Set.mem_univ z) (Set.mem_univ x)

end

end ExactValue
