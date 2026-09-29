import ExactValue.BatchProcedure
import ExactValue.ValueAlgorithm

set_option autoImplicit false

namespace ExactValue

noncomputable section

def historyValues {d n : ℕ} {R : ℝ} (h : QueryHistory d R n) (t : ℕ) : ℝ :=
  if ht : t < n then (h ⟨t, ht⟩).2 else 0

theorem historyValues_continuous {d n : ℕ} (R : ℝ) :
    Continuous (fun h : QueryHistory d R n => historyValues h) := by
  apply continuous_pi
  intro t
  unfold historyValues
  split_ifs with ht
  · exact (continuous_apply (π := fun _ : Fin n => QueryBall d R × ℝ) ⟨t, ht⟩).snd
  · exact continuous_const

def policyValue {d : ℕ} {R : ℝ}
    (Q : (n : ℕ) → QueryHistory d R n → QueryBall d R) (f : Euclid d → ℝ) (n : ℕ) : ℝ :=
  f (Q n (policyHistory Q f n))

theorem policyHistory_value {d : ℕ} {R : ℝ}
    (Q : (n : ℕ) → QueryHistory d R n → QueryBall d R) (f : Euclid d → ℝ)
    (n : ℕ) (i : Fin n) : (policyHistory Q f n i).2 = policyValue Q f i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [policyHistory, Fin.snoc_last]
      rfl
    · simp only [policyHistory, Fin.snoc_castSucc]
      exact ih j

theorem historyValues_policy {d n : ℕ} {R : ℝ}
    (Q : (k : ℕ) → QueryHistory d R k → QueryBall d R) (f : Euclid d → ℝ)
    (t : ℕ) (ht : t < n) : historyValues (policyHistory Q f n) t = policyValue Q f t := by
  rw [historyValues, dif_pos ht]
  exact policyHistory_value Q f n ⟨t, ht⟩

def batchValueAlgorithm {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (N : ℕ) : ValueAlgorithm d R ((d + 1) * N) where
  query n hist := ⟨batchPoint (ballDomain (R / 2) (by positivity)) L h (historyValues hist) n,
    batchPoint_norm hR hL hh hhR _ n⟩
  output hist := ⟨(batchRun (ballDomain (R / 2) (by positivity)) L h (historyValues hist) N).x, by
    have hz : (0 : Euclid d) ∈ (ballDomain (R / 2) (by positivity)).carrier := by
      simpa [ballDomain] using (show 0 ≤ R / 2 by positivity)
    have hm := batchRun_mem (ballDomain (d := d) (R / 2) (by positivity)) hz hL h (historyValues hist) N
    have hn : ‖(batchRun (ballDomain (d := d) (R / 2) (by positivity)) L h (historyValues hist) N).x‖ ≤ R / 2 := by
      simpa [ballDomain] using hm
    linarith⟩
  query_borel := by
    intro n
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (batchPoint_continuous _ L h n).comp (historyValues_continuous R)
  output_borel := by
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (batchRun_continuous_fields _ L h N).1.comp (historyValues_continuous R)

theorem batchPoint_congr {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v v' : ℕ → ℝ)
    (t : ℕ) (hv : ∀ i, i < (t / (d + 1)) * (d + 1) → v i = v' i) :
    batchPoint K L h v t = batchPoint K L h v' t := by
  have heq := batchRun_congr K L h v v' (t / (d + 1)) hv
  unfold batchPoint batchY
  rw [heq]

theorem batch_algorithm_query {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (N : ℕ) (f : Euclid d → ℝ) (t : ℕ) :
    let A := batchValueAlgorithm (d := d) hR hL hh hhR N
    (A.query t (policyHistory A.query f t) : Euclid d) =
      batchPoint (ballDomain (R / 2) (by positivity)) L h (policyValue A.query f) t := by
  dsimp only
  change batchPoint _ L h (historyValues (policyHistory _ f t)) t = _
  apply batchPoint_congr
  intro i hi
  apply historyValues_policy
  have hmul : (t / (d + 1)) * (d + 1) ≤ t := by
    simpa only [Nat.mul_comm] using Nat.mul_div_le t (d + 1)
  omega

theorem batchPoint_at_base {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    batchPoint K L h v (n * (d + 1)) = batchY K L h v n := by
  simp [batchPoint]

theorem batchPoint_at_coordinate {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ)
    (v : ℕ → ℝ) (n : ℕ) (i : Fin d) :
    batchPoint K L h v (n * (d + 1) + i.val + 1) =
      batchY K L h v n + h • EuclideanSpace.single i 1 := by
  have hi : i.val + 1 < d + 1 := by omega
  have hdiv : (n * (d + 1) + i.val + 1) / (d + 1) = n := by
    rw [Nat.add_assoc, Nat.mul_comm n (d + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  have hmod : (n * (d + 1) + i.val + 1) % (d + 1) = i.val + 1 := by
    rw [Nat.add_assoc, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]
  simp [batchPoint, hdiv, hmod]

theorem batchRun_eq_accelRun {d : ℕ} (K : ClosedConvexDomain d) (L h : ℝ)
    (v : ℕ → ℝ) (f : Euclid d → ℝ)
    (hv : ∀ t, v t = f (batchPoint K L h v t)) (n : ℕ) :
    batchRun K L h v n = accelRun K f (finiteGradient f h) L n := by
  have hgrad (k : ℕ) : batchGradient d h v k = finiteGradient f h (batchY K L h v k) := by
    ext i
    change (v (k * (d + 1) + i.val + 1) - v (k * (d + 1))) / h = _
    rw [hv _, hv _, batchPoint_at_base, batchPoint_at_coordinate]
    rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    have hbase := hv (n * (d + 1))
    rw [batchPoint_at_base] at hbase
    simp only [batchRun, accelRun, batchNext, accelNext, hgrad n, hbase, batchY]
    rw [ih]

theorem batch_algorithm_result {d : ℕ} {R L h : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hh : 0 ≤ h) (hhR : h ≤ R / 2) (N : ℕ) (f : Euclid d → ℝ) :
    (batchValueAlgorithm (d := d) hR hL hh hhR N).result f =
      (accelRun (ballDomain (R / 2) (by positivity)) f (finiteGradient f h) L N).x := by
  let A := batchValueAlgorithm (d := d) hR hL hh hhR N
  let K := ballDomain (d := d) (R / 2) (by positivity)
  let v := policyValue A.query f
  have hv (t : ℕ) : v t = f (batchPoint K L h v t) := by
    exact congrArg f (batch_algorithm_query hR hL hh hhR N f t)
  have hrun := batchRun_eq_accelRun K L h v f hv N
  have hhist : batchRun K L h (historyValues (policyHistory A.query f ((d + 1) * N))) N =
      batchRun K L h v N := by
    apply batchRun_congr
    intro t ht
    exact historyValues_policy A.query f t (by simpa only [Nat.mul_comm] using ht)
  change (batchRun K L h (historyValues (policyHistory A.query f ((d + 1) * N))) N).x = _
  rw [hhist, hrun]

end

end ExactValue
