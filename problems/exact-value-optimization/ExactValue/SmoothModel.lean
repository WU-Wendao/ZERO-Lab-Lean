import ExactValue.HardParameters
import Mathlib.Analysis.Convex.Deriv

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem scalar_comparison {f g : ℝ → ℝ} {f' g' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) 1, f' t ≤ g' t) : f 1 - f 0 ≤ g 1 - g 0 := by
  have hd (t : ℝ) := (hg t).sub (hf t)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (show ContinuousOn (fun t => g t - f t) (Set.Icc 0 1) from
      (show Continuous (fun t => g t - f t) from continuous_iff_continuousAt.mpr
        (fun t => (hd t).continuousAt)).continuousOn)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => sub_nonneg.mpr (hle t (interior_subset ht)))
  have h := hm (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
    (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp only at h
  linarith

theorem line_hasDerivAt {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (y h : Euclid d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (y + t • h)) ⟪G (y + t • h), h⟫_ℝ t := by
  simpa only [id_eq, one_smul] using
    (hder _).comp_hasDerivAt t (((hasDerivAt_id t).smul_const h).const_add y)

theorem smooth_remainder {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d} {β : ℝ}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (y h : Euclid d) :
    |f (y + h) - f y - ⟪G y, h⟫_ℝ| ≤ β / 2 * ‖h‖ ^ 2 := by
  let φ := fun t : ℝ => f (y + t • h) - f y - t * ⟪G y, h⟫_ℝ
  let q := fun t : ℝ => β / 2 * t ^ 2 * ‖h‖ ^ 2
  have hφ (t : ℝ) : HasDerivAt φ ⟪G (y + t • h) - G y, h⟫_ℝ t := by
    convert ((line_hasDerivAt hder y h t).sub_const (f y)).sub
      ((hasDerivAt_id t).mul_const ⟪G y, h⟫_ℝ) using 1
    simp only [inner_sub_left, one_mul]
  have hq (t : ℝ) : HasDerivAt q (β * t * ‖h‖ ^ 2) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (β / 2)).mul_const (‖h‖ ^ 2) using 1
    dsimp only [id_eq]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      |⟪G (y + t • h) - G y, h⟫_ℝ| ≤ β * t * ‖h‖ ^ 2 := by
    have hi := abs_real_inner_le_norm (G (y + t • h) - G y) h
    have hl := hLip (y + t • h) y
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hl
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg h)
    nlinarith
  have hup := scalar_comparison hφ hq (fun t ht => (le_abs_self _).trans (hbound t ht))
  have hlo := scalar_comparison (fun t => (hφ t).neg) hq
    (fun t ht => (neg_le_abs _).trans (hbound t ht))
  simp only [φ, q, one_smul, zero_smul, add_zero, zero_mul, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_one, one_mul, mul_zero, sub_self, sub_zero, neg_zero] at hup hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

theorem convex_supporting {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    (hconv : ConvexOn ℝ Set.univ f)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (x y : Euclid d) :
    f y + ⟪G y, x - y⟫_ℝ ≤ f x := by
  let φ := fun t : ℝ => f (y + t • (x - y))
  have hc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ u v hu hv huv
    have hh := hconv.2 (Set.mem_univ (y + a • (x - y)))
      (Set.mem_univ (y + b • (x - y))) hu hv huv
    have heq : u • (y + a • (x - y)) + v • (y + b • (x - y)) =
        y + (u * a + v * b) • (x - y) := by
      simp only [smul_add, smul_smul, add_smul]
      rw [show u • y + (u * a) • (x - y) + (v • y + (v * b) • (x - y)) =
        (u + v) • y + ((u * a) • (x - y) + (v * b) • (x - y)) by rw [add_smul]; abel, huv, one_smul]
    simpa only [heq, smul_eq_mul] using hh
  have hd := line_hasDerivAt hder y (x - y) 0
  simp only [zero_smul, add_zero] at hd
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hd
  simp [φ, slope] at hs
  change ⟪G y, x - y⟫_ℝ ≤ f x - f y at hs
  linarith

def finiteGradient {d : ℕ} (f : Euclid d → ℝ) (h : ℝ) (y : Euclid d) : Euclid d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm
    (fun i => (f (y + h • EuclideanSpace.single i 1) - f y) / h)

theorem finiteGradient_error {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d} {β h : ℝ}
    (hβ : 0 ≤ β) (hh : 0 < h) (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (y : Euclid d) :
    ‖finiteGradient f h y - G y‖ ≤ β * h * Real.sqrt d / 2 := by
  apply forward_difference_norm_bound hβ hh
  intro i
  have hr := smooth_remainder hder hLip y (h • EuclideanSpace.single i 1)
  simpa [inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs, mul_comm, mul_left_comm,
    mul_assoc, div_eq_mul_inv] using hr

theorem ball_diameter {d : ℕ} {R : ℝ} {x y : Euclid d} (hx : ‖x‖ ≤ R / 2)
    (hy : ‖y‖ ≤ R / 2) : ‖x - y‖ ≤ R := by
  have := norm_sub_le x y
  linarith

end

end ExactValue
