import ExactValue.Projection

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def ballDomain {d : ℕ} (r : ℝ) (hr : 0 ≤ r) : ClosedConvexDomain d where
  carrier := Metric.closedBall 0 r
  nonempty := ⟨0, Metric.mem_closedBall_self hr⟩
  closed := Metric.isClosed_closedBall
  convex := convex_closedBall 0 r

theorem scaled_norm {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Euclid d)
    (hx : 0 < ‖x‖) : ‖(r / ‖x‖) • x‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_cancel₀ _ hx.ne']

theorem scaled_distance {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Euclid d)
    (hx : r < ‖x‖) : dist x ((r / ‖x‖) • x) = ‖x‖ - r := by
  have hn : 0 < ‖x‖ := lt_of_le_of_lt hr hx
  have hc : 0 ≤ 1 - r / ‖x‖ := by
    have := (div_le_one hn).mpr hx.le
    linarith
  rw [dist_eq_norm, show x - (r / ‖x‖) • x = (1 - r / ‖x‖) • x by
    rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hn.ne']

theorem infDist_closedBall {d : ℕ} (x : Euclid d) {r : ℝ} (hr : 0 ≤ r) :
    Metric.infDist x (Metric.closedBall (0 : Euclid d) r) = max (‖x‖ - r) 0 := by
  by_cases hx : ‖x‖ ≤ r
  · have hmem : x ∈ Metric.closedBall (0 : Euclid d) r := by simpa using hx
    rw [Metric.infDist_zero_of_mem hmem, max_eq_right (by linarith)]
  · have hxr : r < ‖x‖ := lt_of_not_ge hx
    rw [max_eq_left (by linarith)]
    apply le_antisymm
    · have hnorm := scaled_norm hr x (lt_of_le_of_lt hr hxr)
      have hmem : (r / ‖x‖) • x ∈ Metric.closedBall (0 : Euclid d) r := by
        simpa using hnorm.le
      have hi := Metric.infDist_le_dist_of_mem hmem (x := x)
      rwa [scaled_distance hr x hxr] at hi
    · apply (Metric.le_infDist ⟨0, Metric.mem_closedBall_self hr⟩).2
      intro y hy
      have hy' : ‖y‖ ≤ r := by simpa using hy
      have hn := norm_sub_norm_le x y
      rw [dist_eq_norm]
      linarith

theorem ball_halfSquaredDistance {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Euclid d) :
    (ballDomain r hr).halfSquaredDistance x = (max (‖x‖ - r) 0) ^ 2 / 2 := by
  rw [ClosedConvexDomain.halfSquaredDistance_eq]
  change (Metric.infDist x (Metric.closedBall 0 r)) ^ 2 / 2 = _
  rw [infDist_closedBall x hr]

theorem ballPenalty_convex {d : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ConvexOn ℝ Set.univ (fun x : Euclid d => (max (‖x‖ - r) 0) ^ 2 / 2) := by
  rw [← funext (ball_halfSquaredDistance (d := d) hr)]
  exact (ballDomain r hr).halfSquaredDistance_convex

theorem ballPenalty_contDiff {d : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ContDiff ℝ 1 (fun x : Euclid d => (max (‖x‖ - r) 0) ^ 2 / 2) := by
  rw [← funext (ball_halfSquaredDistance (d := d) hr)]
  exact (ballDomain r hr).halfSquaredDistance_contDiff

end

end ExactValue
