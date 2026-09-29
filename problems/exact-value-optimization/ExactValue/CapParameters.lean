import ExactValue.CapAvoidance

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem cap_log_count_bound {d M : ℝ} (hd : 8 ≤ d) (hM : 0 ≤ M)
    (hcount : M ≤ d ^ 2 / 16 + 1) :
    Real.log (4 * (M + 1)) ≤ 2 * (1 + Real.log d) := by
  have harg : 0 < 4 * (M + 1) := by positivity
  have hargle : 4 * (M + 1) ≤ d ^ 2 := by nlinarith
  have hlog := Real.log_le_log harg hargle
  rw [Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- The paper's universal choice c₀ = 2⁻²⁴ suffices for every cap selection. -/
theorem cap_parameter_condition {d m M p R ρ s : ℝ} (hd : 8 ≤ d) (hm : 0 < m)
    (hM : 0 ≤ M) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = m)
    (hcount : M ≤ d ^ 2 / 16 + 1) (hp : d / 2 ≤ p)
    (hρ : ρ = R / (256 * m * s))
    (hscale : m ^ 3 * (1 + Real.log d) ≤ (1 / 16777216 : ℝ) * d) :
    64 * R ^ 2 * Real.log (4 * (M + 1)) ≤ p * ρ ^ 2 := by
  have hlog := cap_log_count_bound hd hM hcount
  have hid : 65536 * m ^ 3 * ρ ^ 2 = R ^ 2 := by
    rw [hρ, ← hsq]
    field_simp
    ring
  have hmult : 0 < 65536 * m ^ 3 := by positivity
  apply (mul_le_mul_left hmult).mp
  calc
    _ ≤ (65536 * m ^ 3) * (64 * R ^ 2 * (2 * (1 + Real.log d))) := by
      gcongr
    _ = (8388608 * R ^ 2) * (m ^ 3 * (1 + Real.log d)) := by ring
    _ ≤ (8388608 * R ^ 2) * ((1 / 16777216 : ℝ) * d) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (d / 2) * R ^ 2 := by ring
    _ ≤ p * R ^ 2 := mul_le_mul_of_nonneg_right hp (sq_nonneg R)
    _ = (65536 * m ^ 3) * (p * ρ ^ 2) := by rw [← hid]; ring

end

end ExactValue
