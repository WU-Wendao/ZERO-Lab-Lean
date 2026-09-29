import ExactValue.Smoothness

/-! Output-gap calculation for the actual embedded objective. The hypotheses
describe the output and comparison point that the delayed-frame construction
must supply; this file does not assume or assert that construction exists. -/

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def frameCoordinates {d m : ℕ} (U : Fin m → Euclid d) (x : Euclid d) : Vec m :=
  fun i => ⟪U i, x⟫_ℝ

/-- max(norm x - R0, 0) is the Euclidean distance to the closed R0-ball
when R0 is nonnegative. -/
def embeddedObjective {d m : ℕ} (β ρ η R0 : ℝ) (U : Fin m → Euclid d)
    (x : Euclid d) : ℝ :=
  (β * ρ / 8) * moreauValue ρ (frameCoordinates U x) +
    β / 8 * (max (‖x‖ - R0) 0) ^ 2 + η / 2 * ‖x‖ ^ 2

theorem embedded_output_gap {d m : ℕ} (hm : 0 < m)
    {β R ρ η s fstar : ℝ} (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s)
    (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s))
    (hη : η = β / (4096 * (m : ℝ) ^ 2))
    (U : Fin m → Euclid d) (xout xcirc : Euclid d)
    (hlast : |frameCoordinates U xout ⟨m - 1, by omega⟩| ≤ ρ)
    (hcirc : frameCoordinates U xcirc = fun _ => -((R / 4) / s))
    (hcircnorm : ‖xcirc‖ = R / 4)
    (hmin : fstar ≤ embeddedObjective β ρ η (R / 4) U xcirc) :
    11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤
      embeddedObjective β ρ η (R / 4) U xout - fstar := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hηpos : 0 < η := by rw [hη]; positivity
  have hρ0 : ρ = (R / 4) / (64 * (m : ℝ) * s) := by rw [hρ]; ring
  have hgap := moreau_progress_gap hm (show 0 < R / 4 by positivity) hs hρ0
    (frameCoordinates U xout) hlast
  have hscaled := mul_le_mul_of_nonneg_left hgap (show 0 ≤ β * ρ / 8 by positivity)
  have hradial : 0 ≤ β / 8 * (max (‖xout‖ - R / 4) 0) ^ 2 := by positivity
  have hquad : 0 ≤ η / 2 * ‖xout‖ ^ 2 := by positivity
  have hcomp : embeddedObjective β ρ η (R / 4) U xcirc =
      (β * ρ / 8) * moreauValue ρ (fun _ : Fin m => -((R / 4) / s)) +
        η / 2 * (R / 4) ^ 2 := by
    simp [embeddedObjective, hcirc, hcircnorm]
  rw [hcomp] at hmin
  have hc := output_gap_constant (β := β) (R := R) hm' hs hsq
  rw [← hρ, ← hη] at hc
  unfold embeddedObjective
  nlinarith

end

end ExactValue
