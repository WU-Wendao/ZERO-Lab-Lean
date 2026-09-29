import ExactValue.AccelerationGeometry

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

structure AccelState (d : ℕ) where
  x : Euclid d
  w : Euclid d
  c : ℝ

def accelY {d : ℕ} (K : ClosedConvexDomain d) (L : ℝ) (n : ℕ) (s : AccelState d) : Euclid d :=
  coupledPoint (accelerationWeight L n) (accelerationStep L n) s.x (K.project (-s.w))

def accelNext {d : ℕ} (K : ClosedConvexDomain d) (f : Euclid d → ℝ)
    (g : Euclid d → Euclid d) (L : ℝ) (n : ℕ) (s : AccelState d) : AccelState d :=
  let y := accelY K L n s
  let α := accelerationStep L n
  let w := s.w + α • g y
  { x := coupledPoint (accelerationWeight L n) α s.x (K.project (-w))
    w := w
    c := s.c + α * (f y - ⟪g y, y⟫_ℝ) }

def accelRun {d : ℕ} (K : ClosedConvexDomain d) (f : Euclid d → ℝ)
    (g : Euclid d → Euclid d) (L : ℝ) : ℕ → AccelState d
  | 0 => ⟨0, 0, 0⟩
  | n + 1 => accelNext K f g L n (accelRun K f g L n)

theorem accelRun_mem {d : ℕ} (K : ClosedConvexDomain d) (hzero : (0 : Euclid d) ∈ K.carrier)
    (f : Euclid d → ℝ) (g : Euclid d → Euclid d) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (accelRun K f g L n).x ∈ K.carrier := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact coupledPoint_mem K (accelerationWeight_nonneg hL n) (accelerationStep_pos hL n)
      ih (K.project_mem _)

theorem accelY_mem {d : ℕ} (K : ClosedConvexDomain d) (hzero : (0 : Euclid d) ∈ K.carrier)
    (f : Euclid d → ℝ) (g : Euclid d → Euclid d) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    accelY K L n (accelRun K f g L n) ∈ K.carrier :=
  coupledPoint_mem K (accelerationWeight_nonneg hL n) (accelerationStep_pos hL n)
    (accelRun_mem K hzero f g hL n) (K.project_mem _)

theorem accumulatedError_succ (A : ℕ → ℝ) (δl δu : ℝ) (n : ℕ) :
    accumulatedError A δl δu (n + 1) = accumulatedError A δl δu n + A n * δl + A (n + 1) * δu := by
  simp only [accumulatedError, Finset.sum_range_succ]
  ring

structure InexactModel {d : ℕ} (K : ClosedConvexDomain d) (f : Euclid d → ℝ)
    (g : Euclid d → Euclid d) (L δl δu : ℝ) : Prop where
  lower : ∀ x ∈ K.carrier, ∀ y ∈ K.carrier, f y + ⟪g y, x - y⟫_ℝ - δl ≤ f x
  upper : ∀ x ∈ K.carrier, ∀ y ∈ K.carrier,
    f x ≤ f y + ⟪g y, x - y⟫_ℝ + L / 2 * ‖x - y‖ ^ 2 + δu

theorem accelRun_invariant {d : ℕ} (K : ClosedConvexDomain d)
    (hzero : (0 : Euclid d) ∈ K.carrier) (f : Euclid d → ℝ) (g : Euclid d → Euclid d)
    {L δl δu : ℝ} (hL : 0 < L) (hmodel : InexactModel K f g L δl δu) (n : ℕ) :
    accelerationWeight L n * f (accelRun K f g L n).x -
        accumulatedError (accelerationWeight L) δl δu n ≤
      quadraticPotential (accelRun K f g L n).w (accelRun K f g L n).c
        (K.project (-(accelRun K f g L n).w)) := by
  induction n with
  | zero => simp [accelRun, accelerationWeight_zero, accumulatedError, quadraticPotential,
      K.project_eq_self hzero]
  | succ n ih =>
    let st := accelRun K f g L n
    let y := accelY K L n st
    let z' := K.project (-(st.w + accelerationStep L n • g y))
    have hrec : accelerationWeight L n + accelerationStep L n = L * accelerationStep L n ^ 2 := by
      rw [accelerationWeight_add_step hL, accelerationWeight_step_sq hL]
    have hstep := accelerated_estimate_step K (accelerationWeight_nonneg hL n)
      (accelerationStep_pos hL n) hrec st.x st.w (g y) z' (K.project_mem _) ih
      (hmodel.lower st.x (accelRun_mem K hzero f g hL n) y (accelY_mem K hzero f g hL n))
      (hmodel.upper (accelNext K f g L n st).x (accelRun_mem K hzero f g hL (n + 1))
        y (accelY_mem K hzero f g hL n))
    simpa only [st, y, z', accelRun, accelNext, accelY, accumulatedError_succ,
      accelerationWeight_add_step hL] using hstep

theorem accelRun_potential_upper {d : ℕ} (K : ClosedConvexDomain d)
    (hzero : (0 : Euclid d) ∈ K.carrier) (f : Euclid d → ℝ) (g : Euclid d → Euclid d)
    {L δl δu : ℝ} (hL : 0 < L) (hmodel : InexactModel K f g L δl δu)
    (x : Euclid d) (hx : x ∈ K.carrier) (n : ℕ) :
    quadraticPotential (accelRun K f g L n).w (accelRun K f g L n).c x ≤
      ‖x‖ ^ 2 / 2 + accelerationWeight L n * (f x + δl) := by
  induction n with
  | zero => simp [accelRun, accelerationWeight_zero, quadraticPotential]
  | succ n ih =>
    let st := accelRun K f g L n
    let y := accelY K L n st
    have hlo := hmodel.lower x hx y (accelY_mem K hzero f g hL n)
    have hscaled := mul_le_mul_of_nonneg_left hlo (accelerationStep_pos hL n).le
    change quadraticPotential (st.w + accelerationStep L n • g y)
      (st.c + accelerationStep L n * (f y - ⟪g y, y⟫_ℝ)) x ≤ _
    rw [quadraticPotential_update, ← accelerationWeight_add_step hL]
    nlinarith

theorem accelRun_error {d : ℕ} (K : ClosedConvexDomain d)
    (hzero : (0 : Euclid d) ∈ K.carrier) (f : Euclid d → ℝ) (g : Euclid d → Euclid d)
    {L δl δu : ℝ} (hL : 0 < L) (hδl : 0 ≤ δl) (hδu : 0 ≤ δu)
    (hmodel : InexactModel K f g L δl δu) (xstar : Euclid d) (hxstar : xstar ∈ K.carrier)
    {N : ℕ} (hN : 0 < N) :
    f (accelRun K f g L N).x - f xstar ≤
      ‖xstar‖ ^ 2 / (2 * accelerationWeight L N) + (N + 1) * δl + N * δu := by
  have hl := accelRun_invariant K hzero f g hL hmodel N
  have hu := accelRun_potential_upper K hzero f g hL hmodel xstar hxstar N
  have hm := quadraticPotential_min K (accelRun K f g L N).w (accelRun K f g L N).c xstar hxstar
  have he := accumulatedError_bound N (accelerationWeight_mono hL) hδl hδu
  apply accelerated_error_bound (accelerationWeight_pos hL hN) hl _ he
  nlinarith

end

end ExactValue
