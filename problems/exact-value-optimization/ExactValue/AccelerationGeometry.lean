import ExactValue.AccelerationWeights
import ExactValue.ProjectedQuadratic

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def coupledPoint {d : ℕ} (A α : ℝ) (x z : Euclid d) : Euclid d :=
  (A / (A + α)) • x + (α / (A + α)) • z

theorem coupledPoint_mem {d : ℕ} (K : ClosedConvexDomain d) {A α : ℝ}
    (hA : 0 ≤ A) (hα : 0 < α) {x z : Euclid d} (hx : x ∈ K.carrier) (hz : z ∈ K.carrier) :
    coupledPoint A α x z ∈ K.carrier := by
  apply K.convex hx hz (by positivity) (by positivity)
  rw [← add_div, div_self (by positivity : A + α ≠ 0)]

theorem coupledPoint_sub {d : ℕ} (A α : ℝ) (x z z' : Euclid d) :
    coupledPoint A α x z' - coupledPoint A α x z = (α / (A + α)) • (z' - z) := by
  simp only [coupledPoint, smul_sub]
  abel

theorem coupledPoint_identity {d : ℕ} {A α : ℝ} (h : A + α ≠ 0) (x z z' : Euclid d) :
    A • (x - coupledPoint A α x z) + α • (z' - coupledPoint A α x z) = α • (z' - z) := by
  ext i
  simp only [coupledPoint, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem coupledPoint_inner {d : ℕ} {A α : ℝ} (h : A + α ≠ 0) (x z z' g : Euclid d) :
    A * ⟪g, x - coupledPoint A α x z⟫_ℝ + α * ⟪g, z' - coupledPoint A α x z⟫_ℝ =
      α * ⟪g, z' - z⟫_ℝ := by
  have hi := congrArg (fun v : Euclid d => ⟪g, v⟫_ℝ) (coupledPoint_identity h x z z')
  simpa only [inner_add_right, inner_smul_right] using hi

theorem coupledPoint_upper {d : ℕ} {f : Euclid d → ℝ} {A α L δu : ℝ}
    (hA : 0 ≤ A) (hα : 0 < α) (hrec : A + α = L * α ^ 2) (x z z' g : Euclid d)
    (hmodel : f (coupledPoint A α x z') ≤ f (coupledPoint A α x z) +
      ⟪g, coupledPoint A α x z' - coupledPoint A α x z⟫_ℝ +
      L / 2 * ‖coupledPoint A α x z' - coupledPoint A α x z‖ ^ 2 + δu) :
    (A + α) * f (coupledPoint A α x z') ≤
      (A + α) * f (coupledPoint A α x z) + α * ⟪g, z' - z⟫_ℝ +
      ‖z' - z‖ ^ 2 / 2 + (A + α) * δu := by
  have hpos : 0 < A + α := by positivity
  rw [coupledPoint_sub, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < α / (A + α))] at hmodel
  have hh := mul_le_mul_of_nonneg_left hmodel hpos.le
  have hlin : (A + α) * (α / (A + α)) = α := by field_simp
  have hquad : (A + α) * (L / 2) * (α / (A + α)) ^ 2 = 1 / 2 := by
    field_simp
    nlinarith
  have hq := congrArg (fun v : ℝ => v * ‖z' - z‖ ^ 2) hquad
  have hl := congrArg (fun v : ℝ => v * ⟪g, z' - z⟫_ℝ) hlin
  nlinarith

theorem accelerated_estimate_step {d : ℕ} (K : ClosedConvexDomain d)
    {f : Euclid d → ℝ} {A α L E δl δu c : ℝ}
    (hA : 0 ≤ A) (hα : 0 < α) (hrec : A + α = L * α ^ 2)
    (x w g : Euclid d) (z' : Euclid d) (hz' : z' ∈ K.carrier)
    (hind : A * f x - E ≤ quadraticPotential w c (K.project (-w)))
    (hlower : f (coupledPoint A α x (K.project (-w))) +
      ⟪g, x - coupledPoint A α x (K.project (-w))⟫_ℝ - δl ≤ f x)
    (hupper : f (coupledPoint A α x z') ≤ f (coupledPoint A α x (K.project (-w))) +
      ⟪g, coupledPoint A α x z' - coupledPoint A α x (K.project (-w))⟫_ℝ +
      L / 2 * ‖coupledPoint A α x z' - coupledPoint A α x (K.project (-w))‖ ^ 2 + δu) :
    (A + α) * f (coupledPoint A α x z') - (E + A * δl + (A + α) * δu) ≤
      quadraticPotential (w + α • g)
        (c + α * (f (coupledPoint A α x (K.project (-w))) -
          ⟪g, coupledPoint A α x (K.project (-w))⟫_ℝ)) z' := by
  rw [quadraticPotential_update]
  have hproj := quadraticPotential_project K w c z' hz'
  have hlo := mul_le_mul_of_nonneg_left hlower hA
  have hcouple := coupledPoint_inner (by positivity : A + α ≠ 0) x (K.project (-w)) z' g
  have hup := coupledPoint_upper hA hα hrec x (K.project (-w)) z' g hupper
  nlinarith

end

end ExactValue
