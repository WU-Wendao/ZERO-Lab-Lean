import ExactValue.Projection

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

namespace ClosedConvexDomain

variable {d : ℕ} (K : ClosedConvexDomain d)

theorem project_eq_self {x : Euclid d} (hx : x ∈ K.carrier) : K.project x = x := by
  have hn := K.project_min x x hx
  rw [sub_self, norm_zero] at hn
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))).symm

theorem project_continuous : Continuous K.project := by
  have heq : K.project = fun x => x - K.residual x := by
    funext x
    unfold residual
    abel
  rw [heq]
  exact continuous_id.sub K.residual_lipschitz.continuous

end ClosedConvexDomain

def quadraticPotential {d : ℕ} (w : Euclid d) (c : ℝ) (x : Euclid d) : ℝ :=
  ‖x‖ ^ 2 / 2 + ⟪w, x⟫_ℝ + c

theorem quadraticPotential_project {d : ℕ} (K : ClosedConvexDomain d)
    (w : Euclid d) (c : ℝ) (x : Euclid d) (hx : x ∈ K.carrier) :
    quadraticPotential w c (K.project (-w)) + ‖x - K.project (-w)‖ ^ 2 / 2 ≤
      quadraticPotential w c x := by
  have hp := K.project_optimality (-w) x hx
  simp only [inner_sub_left, inner_neg_left, inner_sub_right] at hp
  rw [norm_sub_sq_real]
  unfold quadraticPotential
  rw [real_inner_comm (K.project (-w)) x]
  nlinarith [real_inner_self_eq_norm_sq (K.project (-w))]

theorem quadraticPotential_min {d : ℕ} (K : ClosedConvexDomain d)
    (w : Euclid d) (c : ℝ) (x : Euclid d) (hx : x ∈ K.carrier) :
    quadraticPotential w c (K.project (-w)) ≤ quadraticPotential w c x := by
  have := quadraticPotential_project K w c x hx
  nlinarith [sq_nonneg ‖x - K.project (-w)‖]

theorem quadraticPotential_update {d : ℕ} (w g y x : Euclid d) (c α fy : ℝ) :
    quadraticPotential (w + α • g) (c + α * (fy - ⟪g, y⟫_ℝ)) x =
      quadraticPotential w c x + α * (fy + ⟪g, x - y⟫_ℝ) := by
  simp only [quadraticPotential, inner_add_left, real_inner_smul_left, inner_sub_right]
  ring

end

end ExactValue
