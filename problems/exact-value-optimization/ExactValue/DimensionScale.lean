import ExactValue.UpperBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace ExactValue

noncomputable section

def dimensionScale (d : ℕ) : ℝ := ((d : ℝ) / (1 + Real.log (d : ℝ))) ^ (1 / 3 : ℝ)

def lowerScale (d : ℕ) (β R ε : ℝ) : ℝ := min (Real.sqrt (β * R ^ 2 / ε)) (dimensionScale d)

theorem dimensionScale_pos {d : ℕ} (hd : 1 ≤ d) : 0 < dimensionScale d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := Real.log_nonneg hd'
  unfold dimensionScale
  positivity

theorem dimensionScale_cube {d : ℕ} (hd : 1 ≤ d) :
    dimensionScale d ^ 3 = (d : ℝ) / (1 + Real.log (d : ℝ)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := Real.log_nonneg hd'
  simpa only [dimensionScale, one_div] using
    (Real.rpow_inv_natCast_pow (x := (d : ℝ) / (1 + Real.log (d : ℝ))) (n := 3)
      (by positivity) (by norm_num))

theorem dimensionScale_cube_mul {d : ℕ} (hd : 1 ≤ d) :
    dimensionScale d ^ 3 * (1 + Real.log (d : ℝ)) = d := by
  rw [dimensionScale_cube hd]
  apply div_mul_cancel₀
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have := Real.log_nonneg hd'
  positivity

theorem dimensionScale_le_dimension {d : ℕ} (hd : 1 ≤ d) : dimensionScale d ≤ d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdn : (0 : ℝ) ≤ d := by positivity
  have hl := Real.log_nonneg hd'
  apply le_of_pow_le_pow_left₀ (show (3 : ℕ) ≠ 0 by decide) hdn
  rw [dimensionScale_cube hd]
  have hquot : (d : ℝ) / (1 + Real.log (d : ℝ)) ≤ d :=
    div_le_self hdn (by linarith)
  have hc : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    nlinarith [mul_nonneg hdn (show 0 ≤ (d : ℝ) ^ 2 - 1 by nlinarith)]
  exact hquot.trans hc

/-- A deliberately conservative explicit dimension threshold for the universal theorem. -/
theorem dimensionScale_large {d : ℕ} (hd : 18446744073709551616 ≤ d) : 1024 ≤ dimensionScale d := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (18446744073709551616 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hspos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hslarge : (2147483648 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    (Real.le_sqrt (by norm_num) hdpos.le).mpr (by nlinarith)
  have hlog := Real.log_le_sub_one_of_pos hspos
  rw [Real.log_sqrt hdpos.le] at hlog
  have hlogs : 1 + Real.log (d : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hslarge hspos.le
  rw [← sq, Real.sq_sqrt hdpos.le] at hmul
  have hlpos : 0 < 1 + Real.log (d : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd1)
    linarith
  apply le_of_pow_le_pow_left₀ (show (3 : ℕ) ≠ 0 by decide) (dimensionScale_pos hd1).le
  rw [dimensionScale_cube hd1]
  apply (le_div_iff₀ hlpos).mpr
  nlinarith

theorem lowerScale_large {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2) :
    1024 ≤ lowerScale d β R ε := by
  apply le_min
  · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ hε).mpr
    nlinarith
  · exact dimensionScale_large hd

theorem lowerScale_floor {d : ℕ} (hd : 18446744073709551616 ≤ d) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 1048576 : ℝ) * β * R ^ 2) :
    let M := lowerScale d β R ε
    let m := ⌊M / 512⌋₊
    0 < m ∧ 4 * m ≤ d ∧ M / 1024 ≤ (m : ℝ) ∧ (m : ℝ) ≤ M / 512 ∧
      (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d ∧
      ε < 11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) := by
  dsimp only
  let M := lowerScale d β R ε
  let m := ⌊M / 512⌋₊
  have hM : 1024 ≤ M := lowerScale_large hd hβ hR hε hεsmall
  have hm : 0 < m := Nat.floor_pos.mpr (by linarith)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmf : (m : ℝ) ≤ M / 512 := Nat.floor_le (by linarith)
  have hround : M / 1024 ≤ (m : ℝ) := by
    have hlt := Nat.lt_floor_add_one (M / 512)
    change M / 512 < (m : ℝ) + 1 at hlt
    linarith
  have hMD : M ≤ dimensionScale d := min_le_right _ _
  have hMq : M ≤ Real.sqrt (β * R ^ 2 / ε) := min_le_left _ _
  have hd1 : 1 ≤ d := by omega
  have hDd := dimensionScale_le_dimension hd1
  have hmd : 4 * m ≤ d := by
    have hh : (4 : ℝ) * m ≤ d := by linarith
    exact_mod_cast hh
  have hlog : 0 < 1 + Real.log (d : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd1)
    linarith
  have hcubic : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d := by
    have hp : (m : ℝ) ^ 3 ≤ (dimensionScale d / 512) ^ 3 :=
      pow_le_pow_left₀ hmpos.le (by linarith) 3
    have hh := mul_le_mul_of_nonneg_right hp hlog.le
    have heq := dimensionScale_cube_mul hd1
    have hdn : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have hgap : ε < 11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) := by
    have hs := Real.sq_sqrt (show 0 ≤ β * R ^ 2 / ε by positivity)
    have hm2 : (m : ℝ) ^ 2 ≤ (Real.sqrt (β * R ^ 2 / ε) / 512) ^ 2 :=
      pow_le_pow_left₀ hmpos.le (by linarith) 2
    have hmε := mul_le_mul_of_nonneg_left hm2 hε.le
    have hcancel : (β * R ^ 2 / ε) * ε = β * R ^ 2 := div_mul_cancel₀ _ hε.ne'
    have hsε := congrArg (fun v : ℝ => v * ε) hs
    have ht : ε * (m : ℝ) ^ 2 < (11 / 131072 : ℝ) * (β * R ^ 2) := by
      nlinarith [mul_pos hβ (sq_pos_of_pos hR)]
    rw [show (11 / 131072 : ℝ) * (β * R ^ 2 / (m : ℝ) ^ 2) =
      ((11 / 131072 : ℝ) * (β * R ^ 2)) / (m : ℝ) ^ 2 by ring]
    exact (lt_div_iff₀ (sq_pos_of_pos hmpos)).mpr ht
  exact ⟨hm, hmd, hround, hmf, hcubic, hgap⟩

end

end ExactValue
