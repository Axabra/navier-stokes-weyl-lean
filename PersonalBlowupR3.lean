import NavierStokes.R3.ActualCandidate
import NavierStokes.R3.CandidateBreakdown
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.H3Blowup

/-!
# AXABRA local reconstruction of the forced R3 blow-up witness

This certificate deliberately does not import or invoke any of the terminal
statements

* `NavierStokes.Comparator.navier_stokes_breakdown_R3`,
* `NavierStokesR3.theorem_1_1`, or
* `NavierStokesR3.breakdownStatement`.

Instead it starts from the selected viscosity-one candidate, performs the
viscosity scaling locally, and exposes the actual finite-time obstruction:
pointwise speed and the Euclidean derivative H3 norm are unbounded in every
left neighbourhood of `t = 1`.  It also proves that the same smooth compactly
supported force admits no global smooth finite-energy continuation.

The mathematical construction reproduced here comes from the pinned
`openai/NavierStokesAndEuler` development.  The purpose of this file is a
standalone AXABRA-side reconstruction and audit, not a claim of independent
priority for the underlying blow-up mechanism.
-/

noncomputable section

open Set

namespace AxabraPersonalBlowupR3

/-- A locally assembled R3 witness at arbitrary positive viscosity.

The `properties` field contains the smooth pre-singular solution, compact
spatial support, smooth compactly supported force, zero initial velocity,
incompressibility, the Navier--Stokes equation, bounded kinetic energy before
time one, and pointwise speed blow-up.  The additional fields make the two
terminal analytic consequences explicit in the exported type. -/
structure PersonalBlowupWitness (nu : ℝ) where
  velocity : NavierStokesR3.ProblemStatement.VelocityField
  pressure : NavierStokesR3.ProblemStatement.PressureField
  force : NavierStokesR3.ProblemStatement.VelocityField
  support : Set NavierStokesR3.ProblemStatement.Space
  properties : NavierStokesR3.ProblemStatement.CandidateProperties
    nu velocity pressure force support
  h3_unbounded_at_one :
    ∀ M : ℝ, 0 < M → ∀ delta : ℝ, 0 < delta →
      ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ 1 - delta < t ∧
        M < NavierStokesR3.H3Embedding.derivativeH3Norm
          (fun x => velocity (t, x))
  no_global_finite_energy_solution :
    ¬ Nonempty
      (NavierStokesR3.ProblemStatement.GlobalFiniteEnergySolution nu force)

/-- Assemble the viscosity-one whole-space candidate directly from the fixed
physical witness.  This is the local copy of the construction step that turns
the selected stage data into compact Euclidean fields and a smooth force whose
support is separated from time zero. -/
theorem personal_candidate_one_with_initial_rest :
    ∃ u : NavierStokesR3.ProblemStatement.VelocityField,
    ∃ p : NavierStokesR3.ProblemStatement.PressureField,
    ∃ f : NavierStokesR3.ProblemStatement.VelocityField,
    ∃ K : Set NavierStokesR3.ProblemStatement.Space,
      NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K ∧
        ∀ t : ℝ, |t| ≤ 3 / 8 →
          ∀ x : NavierStokesR3.ProblemStatement.Space,
            u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, hf, _⟩ :=
    NavierStokes.ActualCandidateAssembly.selected_witness
  refine ⟨_, _, _, _,
    NavierStokesR3.ActualCandidate.of_localized_fields hc hf, ?_⟩
  intro t ht x
  exact ⟨NavierStokes.TimeLocalization.activatedVelocity_zero_early _ ht x,
    NavierStokes.TimeLocalization.activatedPressure_zero_early _ ht x⟩

/-- Prove existence of the complete finite-time R3 witness without using any
terminal breakdown theorem.  The witness is singular exactly at the fixed
time `t = 1` in the explicit speed and H3 senses recorded above. -/
theorem exists_personal_blowup_R3 (nu : ℝ) (hnu : 0 < nu) :
    Nonempty (PersonalBlowupWitness nu) := by
  obtain ⟨u, p, f, K, hc, _⟩ := personal_candidate_one_with_initial_rest
  have hscaled :
      NavierStokesR3.ProblemStatement.CandidateProperties nu
        (NavierStokesR3.ViscosityScaling.scaledVelocity nu u)
        (NavierStokesR3.ViscosityScaling.scaledPressure nu p)
        (NavierStokesR3.ViscosityScaling.scaledVelocity nu f)
        ((fun x : NavierStokesR3.ProblemStatement.Space => Real.sqrt nu • x) '' K) :=
    NavierStokesR3.ViscosityScaling.candidate_at_viscosity hc hnu
  refine ⟨{
    velocity := NavierStokesR3.ViscosityScaling.scaledVelocity nu u
    pressure := NavierStokesR3.ViscosityScaling.scaledPressure nu p
    force := NavierStokesR3.ViscosityScaling.scaledVelocity nu f
    support :=
      (fun x : NavierStokesR3.ProblemStatement.Space => Real.sqrt nu • x) '' K
    properties := hscaled
    h3_unbounded_at_one :=
      NavierStokesR3.H3Embedding.candidate_h3Norm_unbounded hscaled
    no_global_finite_energy_solution := ?_
  }⟩
  rintro ⟨v⟩
  exact hc.no_global_solution_one
    ⟨NavierStokesR3.ViscosityScaling.normalized_global_solution hnu v⟩

/-- Select the locally reconstructed witness.  The only extraction principle
used here is Lean's standard classical choice. -/
noncomputable def construct_personal_blowup_R3 (nu : ℝ) (hnu : 0 < nu) :
    PersonalBlowupWitness nu :=
  Classical.choice (exists_personal_blowup_R3 nu hnu)

/-- The exported pointwise finite-time singularity, stated without hiding it
behind the negation of a global-existence structure. -/
theorem personal_speed_unbounded_at_one (nu : ℝ) (hnu : 0 < nu) :
    NavierStokesR3.ProblemStatement.SpeedUnboundedAtOne
      (construct_personal_blowup_R3 nu hnu).velocity :=
  (construct_personal_blowup_R3 nu hnu).properties.speed_unbounded

/-- The exported H3 blow-up statement in every left neighbourhood of time one. -/
theorem personal_h3_unbounded_at_one (nu : ℝ) (hnu : 0 < nu) :
    ∀ M : ℝ, 0 < M → ∀ delta : ℝ, 0 < delta →
      ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ 1 - delta < t ∧
        M < NavierStokesR3.H3Embedding.derivativeH3Norm
          (fun x => (construct_personal_blowup_R3 nu hnu).velocity (t, x)) :=
  (construct_personal_blowup_R3 nu hnu).h3_unbounded_at_one

/-- The exported failure of global smooth finite-energy continuation for the
same explicitly assembled force and zero initial datum. -/
theorem personal_no_global_finite_energy_solution (nu : ℝ) (hnu : 0 < nu) :
    ¬ Nonempty
      (NavierStokesR3.ProblemStatement.GlobalFiniteEnergySolution nu
        (construct_personal_blowup_R3 nu hnu).force) :=
  (construct_personal_blowup_R3 nu hnu).no_global_finite_energy_solution

#check personal_candidate_one_with_initial_rest
#check exists_personal_blowup_R3
#check construct_personal_blowup_R3
#check personal_speed_unbounded_at_one
#check personal_h3_unbounded_at_one
#check personal_no_global_finite_energy_solution

#print axioms personal_candidate_one_with_initial_rest
#print axioms exists_personal_blowup_R3
#print axioms construct_personal_blowup_R3
#print axioms personal_speed_unbounded_at_one
#print axioms personal_h3_unbounded_at_one
#print axioms personal_no_global_finite_energy_solution

end AxabraPersonalBlowupR3
