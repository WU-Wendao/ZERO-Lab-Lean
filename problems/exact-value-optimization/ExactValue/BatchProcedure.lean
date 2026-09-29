import ExactValue.UpperConvergence

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def batchGradient (d : ℕ) (h : ℝ) (v : ℕ → ℝ) (n : ℕ) : Euclid d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm
    (fun i => (v (n * (d + 1) + i.val + 1) - v (n * (d + 1))) / h)

def batchNext {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v : ℕ → ℝ)
    (n : ℕ) (st : AccelState d) : AccelState d :=
  let y := accelY K L n st
  let α := accelerationStep L n
  let g := batchGradient d h v n
  let w := st.w + α • g
  { x := coupledPoint (accelerationWeight L n) α st.x (K.project (-w))
    w := w
    c := st.c + α * (v (n * (d + 1)) - ⟪g, y⟫_ℝ) }

def batchRun {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v : ℕ → ℝ) : ℕ → AccelState d
  | 0 => ⟨0, 0, 0⟩
  | n + 1 => batchNext K L h v n (batchRun K L h v n)

def batchY {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v : ℕ → ℝ) (n : ℕ) : Euclid d :=
  accelY K L n (batchRun K L h v n)

def batchPoint {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v : ℕ → ℝ) (t : ℕ) : Euclid d :=
  let y := batchY K L h v (t / (d + 1))
  if hi : t % (d + 1) = 0 then y else
    y + h • EuclideanSpace.single ⟨t % (d + 1) - 1, by
      have hmod : t % (d + 1) < d + 1 := Nat.mod_lt t (by omega)
      omega⟩ 1

theorem batchIndex_lt (n d i : ℕ) (hi : i < d + 1) :
    n * (d + 1) + i < (n + 1) * (d + 1) := by
  rw [Nat.add_mul, one_mul]
  omega

theorem batchGradient_congr {d : ℕ} (h : ℝ) (v v' : ℕ → ℝ) (n : ℕ)
    (hv : ∀ t, t < (n + 1) * (d + 1) → v t = v' t) :
    batchGradient d h v n = batchGradient d h v' n := by
  have hbase := hv (n * (d + 1)) (by simpa only [Nat.add_zero] using batchIndex_lt n d 0 (Nat.succ_pos d))
  ext i
  change (v (n * (d + 1) + i.val + 1) - v (n * (d + 1))) / h = _
  rw [hbase, hv _ (by simpa only [Nat.add_assoc] using batchIndex_lt n d (i.val + 1) (by omega))]
  rfl

theorem batchRun_congr {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v v' : ℕ → ℝ)
    (n : ℕ) (hv : ∀ t, t < n * (d + 1) → v t = v' t) :
    batchRun K L h v n = batchRun K L h v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun t ht => hv t (ht.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ n))))
    have hbase := hv (n * (d + 1)) (by simpa only [Nat.add_zero] using batchIndex_lt n d 0 (Nat.succ_pos d))
    have hg := batchGradient_congr h v v' n hv
    simp only [batchRun]
    rw [heq]
    simp only [batchNext, hbase, hg]

theorem batchRun_mem {d : ℕ} (K : ClosedConvexDomain d) (hzero : (0 : Euclid d) ∈ K.carrier)
    {L : ℝ} (hL : 0 < L) (h : ℝ) (v : ℕ → ℝ) (n : ℕ) : (batchRun K L h v n).x ∈ K.carrier := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact coupledPoint_mem K (accelerationWeight_nonneg hL n) (accelerationStep_pos hL n)
      ih (K.project_mem _)

theorem batchY_mem {d : ℕ} (K : ClosedConvexDomain d) (hzero : (0 : Euclid d) ∈ K.carrier)
    {L : ℝ} (hL : 0 < L) (h : ℝ) (v : ℕ → ℝ) (n : ℕ) : batchY K L h v n ∈ K.carrier :=
  coupledPoint_mem K (accelerationWeight_nonneg hL n) (accelerationStep_pos hL n)
    (batchRun_mem K hzero hL h v n) (K.project_mem _)

theorem batchPoint_norm {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (v : ℕ → ℝ) (n : ℕ) :
    ‖batchPoint (ballDomain (d := d) (R / 2) (by positivity)) L h v n‖ ≤ R := by
  let K := ballDomain (d := d) (R / 2) (by positivity)
  have hzero : (0 : Euclid d) ∈ K.carrier := by simpa [K, ballDomain] using (show 0 ≤ R / 2 by positivity)
  have hy : ‖batchY K L h v (n / (d + 1))‖ ≤ R / 2 := by
    simpa [K, ballDomain] using batchY_mem K hzero hL h v (n / (d + 1))
  unfold batchPoint
  split_ifs with hi
  · exact hy.trans (by linarith)
  · exact displaced_query_in_ball hy hh hhR (by simp [EuclideanSpace.norm_single])

theorem batchGradient_continuous (d : ℕ) (h : ℝ) (n : ℕ) :
    Continuous (fun v : ℕ → ℝ => batchGradient d h v n) := by
  have hc : Continuous (fun v : ℕ → ℝ => fun i : Fin d =>
      (v (n * (d + 1) + i.val + 1) - v (n * (d + 1))) / h) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply (π := fun _ : ℕ => ℝ) (n * (d + 1) + i.val + 1)).sub
      (continuous_apply (n * (d + 1)))).div_const h
  exact (PiLp.continuous_equiv_symm 2 (fun _ : Fin d => ℝ)).comp hc

theorem accelY_continuous_of_fields {X : Type*} [TopologicalSpace X] {d : ℕ}
    (K : ClosedConvexDomain d) (L : ℝ) (n : ℕ) (st : X → AccelState d)
    (hx : Continuous (fun v => (st v).x)) (hw : Continuous (fun v => (st v).w)) :
    Continuous (fun v => accelY K L n (st v)) := by
  exact (continuous_const.smul hx).add
    (continuous_const.smul (K.project_continuous.comp hw.neg))

theorem batchRun_continuous_fields {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (n : ℕ) :
    Continuous (fun v : ℕ → ℝ => (batchRun K L h v n).x) ∧
      Continuous (fun v : ℕ → ℝ => (batchRun K L h v n).w) := by
  induction n with
  | zero => exact ⟨continuous_const, continuous_const⟩
  | succ n ih =>
    have hg := batchGradient_continuous d h n
    have hw := ih.2.add ((continuous_const (y := accelerationStep L n)).smul hg)
    exact ⟨(continuous_const.smul ih.1).add
      (continuous_const.smul (K.project_continuous.comp hw.neg)), hw⟩

theorem batchY_continuous {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (n : ℕ) :
    Continuous (fun v : ℕ → ℝ => batchY K L h v n) :=
  accelY_continuous_of_fields K L n (fun v => batchRun K L h v n)
    (batchRun_continuous_fields K L h n).1 (batchRun_continuous_fields K L h n).2

theorem batchPoint_continuous {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (n : ℕ) :
    Continuous (fun v : ℕ → ℝ => batchPoint K L h v n) := by
  unfold batchPoint
  split_ifs with hi
  · exact batchY_continuous K L h _
  · exact (batchY_continuous K L h _).add continuous_const

end

end ExactValue
