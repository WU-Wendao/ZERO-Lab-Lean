import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
Analytic inequalities and numerical bookkeeping from the manuscript.
The oracle inequalities below explicitly assume the supporting-hyperplane
and smoothness inequalities; they do not assert the full optimization theorem.
-/

set_option autoImplicit false

namespace ExactValue

open scoped InnerProductSpace

theorem young_error {β δ r : ℝ} (hβ : 0 < β) :
    δ * r ≤ β / 2 * r ^ 2 + δ ^ 2 / (2 * β) := by
  have h := sq_nonneg (β * r - δ)
  have heq : δ ^ 2 / (2 * β) * (2 * β) = δ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem displaced_query_in_ball {R h : ℝ} {y e : E}
    (hy : ‖y‖ ≤ R / 2) (hh : 0 ≤ h) (hhR : h ≤ R / 2) (he : ‖e‖ = 1) :
    ‖y + h • e‖ ≤ R := by
  calc
    ‖y + h • e‖ ≤ ‖y‖ + ‖h • e‖ := norm_add_le _ _
    _ = ‖y‖ + h := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, he]
    _ ≤ R := by linarith

theorem inexact_oracle_lower {f : E → ℝ} {x y g grad : E} {R δ : ℝ}
    (hconvex : f y + ⟪grad, x - y⟫_ℝ ≤ f x)
    (herr : ‖g - grad‖ ≤ δ) (hdiam : ‖x - y‖ ≤ R) :
    f y + ⟪g, x - y⟫_ℝ - R * δ ≤ f x := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans herr
  have hinner := real_inner_le_norm (g - grad) (x - y)
  have hmul : ‖g - grad‖ * ‖x - y‖ ≤ δ * R := by
    exact mul_le_mul herr hdiam (norm_nonneg _) hδ
  rw [inner_sub_left] at hinner
  nlinarith

theorem inexact_oracle_upper {f : E → ℝ} {x y g grad : E} {β δ : ℝ}
    (hβ : 0 < β)
    (hsmooth : f x ≤ f y + ⟪grad, x - y⟫_ℝ + β / 2 * ‖x - y‖ ^ 2)
    (herr : ‖g - grad‖ ≤ δ) :
    f x ≤ f y + ⟪g, x - y⟫_ℝ + (2 * β) / 2 * ‖x - y‖ ^ 2 +
      δ ^ 2 / (2 * β) := by
  have he : ‖grad - g‖ ≤ δ := by simpa [norm_sub_rev] using herr
  have hi := real_inner_le_norm (grad - g) (x - y)
  have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (x - y))
  have hy := young_error (δ := δ) (r := ‖x - y‖) hβ
  rw [inner_sub_left] at hi
  nlinarith

end InnerProduct

/-- The scalar coordinate step in the finite-difference estimate. -/
theorem forward_difference_error {fx fy deriv β h : ℝ} (hh : 0 < h)
    (hrem : |fx - fy - h * deriv| ≤ β * h ^ 2 / 2) :
    |(fx - fy) / h - deriv| ≤ β * h / 2 := by
  have hid : (fx - fy) / h - deriv = (fx - fy - h * deriv) / h := by
    field_simp
  rw [hid, abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).2
  nlinarith [hrem]

theorem euclidean_norm_bound_of_coordinate_bounds {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoord : ∀ i, |v i| ≤ δ) : ‖v‖ ≤ δ * Real.sqrt d := by
  have hsum : (∑ i, (v i) ^ 2) ≤ (d : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have := pow_le_pow_left₀ (abs_nonneg (v i)) (hcoord i) 2
        simpa only [sq_abs] using this
      _ = _ := by simp
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  apply (Real.sqrt_le_left (by positivity)).2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  nlinarith

/-- The Euclidean norm estimate in the forward-difference lemma, given its
one-dimensional Taylor remainder bounds. -/
theorem forward_difference_norm_bound {d : ℕ} {β h fy : ℝ}
    (hβ : 0 ≤ β) (hh : 0 < h) (values : Fin d → ℝ)
    (grad : EuclideanSpace ℝ (Fin d))
    (hrem : ∀ i, |values i - fy - h * grad i| ≤ β * h ^ 2 / 2) :
    ‖((WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (values i - fy) / h) : EuclideanSpace ℝ (Fin d)) - grad‖ ≤
      β * h * Real.sqrt d / 2 := by
  have hb := euclidean_norm_bound_of_coordinate_bounds
    (((WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (values i - fy) / h) : EuclideanSpace ℝ (Fin d)) - grad)
    (δ := β * h / 2) (by positivity)
    (fun i => forward_difference_error hh (hrem i))
  convert hb using 1
  ring

/-- A_N growth after the square-root substitution used in the paper. -/
theorem accelerated_weight_growth (s : ℕ → ℝ) (hs0 : s 0 = 0)
    (hs : ∀ n, 0 < s (n + 1))
    (hrec : ∀ n, s (n + 1) ^ 2 - s n ^ 2 = s (n + 1)) :
    ∀ n : ℕ, (n : ℝ) / 2 ≤ s n := by
  intro n
  induction n with
  | zero => simp [hs0]
  | succ n ih =>
    have hn : 0 ≤ s n := le_trans (by positivity) ih
    have hn1 := hs n
    have hr := hrec n
    have hmono : s n ≤ s (n + 1) := by nlinarith
    have hstep : s n + 1 / 2 ≤ s (n + 1) := by
      by_contra h
      have hd : s (n + 1) - s n < 1 / 2 := by linarith
      have hp := mul_lt_mul_of_pos_right hd (show 0 < s (n + 1) + s n by linarith)
      nlinarith
    push_cast
    linarith

def accumulatedError (A : ℕ → ℝ) (δl δu : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (A k * δl + A (k + 1) * δu)

theorem accumulatedError_bound {A : ℕ → ℝ} {δl δu : ℝ} (N : ℕ)
    (hA : Monotone A) (hl : 0 ≤ δl) (hu : 0 ≤ δu) :
    accumulatedError A δl δu N ≤ (N : ℝ) * A N * (δl + δu) := by
  calc
    accumulatedError A δl δu N ≤ ∑ _k ∈ Finset.range N, A N * (δl + δu) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      have h1 := mul_le_mul_of_nonneg_right (hA hkN.le) hl
      have h2 := mul_le_mul_of_nonneg_right (hA (Nat.succ_le_of_lt hkN)) hu
      nlinarith
    _ = (N : ℝ) * A N * (δl + δu) := by simp; ring

/-- Combining the two estimate-sequence bounds and accumulated errors. -/
theorem accelerated_error_bound {A ψ fx fstar distanceSq E δl δu : ℝ} {N : ℕ}
    (hA : 0 < A)
    (hlower : A * fx - E ≤ ψ)
    (hupper : ψ ≤ distanceSq / 2 + A * fstar + A * δl)
    (hE : E ≤ (N : ℝ) * A * (δl + δu)) :
    fx - fstar ≤ distanceSq / (2 * A) + (N + 1) * δl + N * δu := by
  have heq : distanceSq / (2 * A) * (2 * A) = distanceSq :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- The strict final accuracy margin in the upper-bound proof. -/
theorem upper_error_budget {ε err : ℝ} (hε : 0 < ε)
    (herr : err ≤ ε / 4 + ε / 8 + ε / 128) : err < ε := by linarith

theorem upper_call_count {d N : ℕ} {Q : ℝ} (hd : 1 ≤ d) (hQ : 1 ≤ Q)
    (hN : (N : ℝ) ≤ 2 * Real.sqrt Q + 1) :
    ((d + 1) * N : ℝ) ≤ 6 * d * Real.sqrt Q := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt Q := (Real.le_sqrt (by norm_num) (by linarith)).2
    (by simpa using hQ)
  nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity)
    (show 0 ≤ 2 * Real.sqrt Q + 1 - N by linarith)]

/-- m is represented by s², so s is its positive square root. -/
theorem output_gap_constant {β R m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hsq : s ^ 2 = m) :
    (β * (R / (256 * m * s)) / 8) * (3 * (R / 4) / (4 * s)) -
      (β / (4096 * m ^ 2)) / 2 * (R / 4) ^ 2 =
        11 / 131072 * (β * R ^ 2 / m ^ 2) := by
  have hfirst :
      (β * (R / (256 * m * s)) / 8) * (3 * (R / 4) / (4 * s)) =
        3 * β * R ^ 2 / (32768 * m * s ^ 2) := by
    field_simp
    ring
  rw [hfirst, hsq]
  field_simp
  ring

theorem block_size_bound (d : ℕ) (hd : 8 ≤ d) : d ≤ 8 * (d / 4) := by omega

theorem budget_implies_incomplete_chain (d m T : ℕ) (hd : 8 ≤ d)
    (hT : 8 * T < d * m) : T < (d / 4) * m := by
  have hb := Nat.mul_le_mul_right m (block_size_bound d hd)
  rw [Nat.mul_assoc] at hb
  omega

theorem complete_blocks_lt_chain (b m T : ℕ) (hb : 0 < b) (hT : T < b * m) :
    T / b < m := by
  apply (Nat.div_lt_iff_lt_mul hb).2
  simpa [Nat.mul_comm] using hT

end ExactValue
