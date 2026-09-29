import ExactValue.UpperBound

set_option autoImplicit false

namespace ExactValue

noncomputable section

def zeroQueryAlgorithm {d : ℕ} {R : ℝ} (hR : 0 ≤ R) : ValueAlgorithm d R 0 where
  query _ _ := ⟨0, by simpa using hR⟩
  output _ := ⟨0, by simpa using hR⟩
  query_borel _ := by exact continuous_const.borel_measurable
  output_borel := by exact continuous_const.borel_measurable

theorem valueComplexity_zero_dimension {β R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    valueComplexity 0 R β ε = 0 := by
  apply le_antisymm _ (zero_le _)
  have hA : (zeroQueryAlgorithm (d := 0) hR).Guarantees (β := β) (ε := ε) := by
    intro f _
    refine ⟨0, ?_, ?_⟩
    · intro y
      have hy : y = 0 := Subsingleton.elim _ _
      rw [hy]
    · change f 0 - f 0 ≤ ε
      simpa only [sub_self] using hε
  simpa only [Nat.cast_zero] using valueComplexity_le _ hA

theorem valueComplexity_upper_all_dimensions (d : ℕ) {β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    valueComplexity d R β ε ≤ ENNReal.ofReal (6 * d * Real.sqrt (β * R ^ 2 / ε)) := by
  cases d with
  | zero => rw [valueComplexity_zero_dimension hR.le hε.le]; positivity
  | succ d => exact valueComplexity_upper (Nat.succ_pos d) hβ hR hε hεmax

end

end ExactValue
