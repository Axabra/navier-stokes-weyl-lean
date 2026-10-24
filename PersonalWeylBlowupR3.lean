import PersonalBlowupR3
import GeometricSubmission

/-!
# Personal finite-time R3 blow-up in the exact zero-Weyl geometry

This file places the locally reconstructed forced R3 witness in the genuine
exact Weyl representative

`phi = 0`, `Q = 0`, `g_hat = g_Euclidean`.

In that representative the metric connection is the explicit Euclidean
Levi-Civita connection certified in `GeometricSubmission.lean`.  The theorem
below checks directly, for every `0 < t < 1`, that the reconstructed fields
satisfy the paper operator equation `N_nu(u,p) = f`.  Pointwise-speed and H3
blow-up at `t = 1` are then exported for these same fields.
-/

noncomputable section

open Set

namespace AxabraPersonalWeylBlowupR3

/-- The reconstructed R3 witness together with its exact zero-Weyl geometric
realization and the paper operator equation before the singular time. -/
structure PersonalZeroWeylBlowupWitness (nu : ℝ) where
  classical : AxabraPersonalBlowupR3.PersonalBlowupWitness nu
  geometry :
    AxabraWeylZeroGaugeGeometryOpenAIBridge.PaperZeroGaugeEuclideanGeometry
  paper_navier_stokes :
    ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ∀ x : NavierStokesR3.ProblemStatement.Space,
        AxabraWeylZeroGaugeGeometryOpenAIBridge.PaperEuclideanNSOperator nu
          (NavierStokes.ProblemStatement.temporalDerivative classical.velocity t x)
          (NavierStokes.ProblemStatement.advection classical.velocity t x)
          (NavierStokes.ProblemStatement.pressureGradient classical.pressure t x)
          (NavierStokes.ProblemStatement.spatialLaplacian classical.velocity t x) =
            classical.force (t, x)

/-- Construct the exact zero-Weyl realization of the personal R3 witness. -/
noncomputable def construct_personal_zero_weyl_blowup_R3
    (nu : ℝ) (hnu : 0 < nu) : PersonalZeroWeylBlowupWitness nu := by
  let w := AxabraPersonalBlowupR3.construct_personal_blowup_R3 nu hnu
  refine {
    classical := w
    geometry :=
      AxabraWeylZeroGaugeGeometryOpenAIBridge.paper_zero_gauge_euclidean_geometry
    paper_navier_stokes := ?_
  }
  intro t ht x
  have h := w.properties.navier_stokes t ht x
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual at h
  unfold AxabraWeylZeroGaugeGeometryOpenAIBridge.PaperEuclideanNSOperator
  calc
    NavierStokes.ProblemStatement.temporalDerivative w.velocity t x +
          NavierStokes.ProblemStatement.advection w.velocity t x +
          NavierStokes.ProblemStatement.pressureGradient w.pressure t x -
          nu • NavierStokes.ProblemStatement.spatialLaplacian w.velocity t x =
        NavierStokes.ProblemStatement.temporalDerivative w.velocity t x +
          NavierStokes.ProblemStatement.advection w.velocity t x -
          nu • NavierStokes.ProblemStatement.spatialLaplacian w.velocity t x +
          NavierStokes.ProblemStatement.pressureGradient w.pressure t x := by
      abel
    _ = w.force (t, x) := h

/-- The exact-Weyl representative has the same pointwise finite-time
singularity as the locally reconstructed classical witness. -/
theorem personal_zero_weyl_speed_unbounded_at_one
    (nu : ℝ) (hnu : 0 < nu) :
    NavierStokesR3.ProblemStatement.SpeedUnboundedAtOne
      (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.velocity :=
  (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.properties.speed_unbounded

/-- The same exact-Weyl velocity has unbounded Euclidean derivative-H3 norm
in every left neighbourhood of `t = 1`. -/
theorem personal_zero_weyl_h3_unbounded_at_one
    (nu : ℝ) (hnu : 0 < nu) :
    ∀ M : ℝ, 0 < M → ∀ delta : ℝ, 0 < delta →
      ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ 1 - delta < t ∧
        M < NavierStokesR3.H3Embedding.derivativeH3Norm
          (fun x =>
            (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.velocity
              (t, x)) :=
  (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.h3_unbounded_at_one

/-- No global smooth finite-energy continuation exists for the force carried
by this exact zero-Weyl realization. -/
theorem personal_zero_weyl_no_global_finite_energy_solution
    (nu : ℝ) (hnu : 0 < nu) :
    ¬ Nonempty
      (NavierStokesR3.ProblemStatement.GlobalFiniteEnergySolution nu
        (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.force) :=
  (construct_personal_zero_weyl_blowup_R3 nu hnu).classical.no_global_finite_energy_solution

#check construct_personal_zero_weyl_blowup_R3
#check personal_zero_weyl_speed_unbounded_at_one
#check personal_zero_weyl_h3_unbounded_at_one
#check personal_zero_weyl_no_global_finite_energy_solution

#print axioms construct_personal_zero_weyl_blowup_R3
#print axioms personal_zero_weyl_speed_unbounded_at_one
#print axioms personal_zero_weyl_h3_unbounded_at_one
#print axioms personal_zero_weyl_no_global_finite_energy_solution

end AxabraPersonalWeylBlowupR3
