import NavierStokes.ComparatorSolution

/-!
# Axabra paper zero-gauge equation bridge to the published OpenAI Navier--Stokes theorem

This certificate follows the shortest route actually needed for the OpenAI target while
staying inside the equations of the revised Weyl paper.

It does NOT use the unavailable `CovariantDerivative.LeviCivita` module from a newer
Mathlib revision.  Instead it formalizes directly the paper's own exact Weyl formulas in
the special exact representative

  φ = 0,  Q = 0,  exp(-2φ)=1,

and proves that every Weyl correction term vanishes.  In particular the paper connection
formula

  D_X Y = ∇_X Y + Q(X)Y + Q(Y)X - g(X,Y)Q♯

reduces literally to `D_X Y = ∇_X Y`, the incompressibility formula

  div_hat u = div_g u + n q

reduces to `div_g u`, and the exact gauge momentum operator reduces to the Euclidean
Navier--Stokes operator of the paper's classical limit.

The external force is attached only after this Euclidean operator has been identified:
the paper has `N_ν(u,p)=0`, while the OpenAI Comparator theorem uses `N_ν(u,p)=f`.

No Weyl energy identity is used.  The whole-space wrapper only transports the energy side
condition already present in the public OpenAI theorem type.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace AxabraWeylPaperZeroGaugeEquationsOpenAIBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## 1. Exact zero Weyl gauge from the paper -/

/-- Zero Weyl potential. -/
def paperPhiZero : ℝ³ → ℝ := fun _ => 0

/-- Zero Weyl one-form. -/
def paperQZero : ℝ³ → (ℝ³ →L[ℝ] ℝ) := fun _ => 0

/-- `Q = dφ` holds exactly for the zero representative. -/
theorem paper_q_zero_is_exact (x : ℝ³) :
    fderiv ℝ paperPhiZero x = paperQZero x := by
  change fderiv ℝ (fun _ : ℝ³ => (0 : ℝ)) x = (0 : ℝ³ →L[ℝ] ℝ)
  exact fderiv_const_apply (𝕜 := ℝ) (E := ℝ³) (x := x) (0 : ℝ)

/-- The zero Weyl one-form evaluates to zero on every vector. -/
theorem paper_q_zero_eval (x X : ℝ³) : paperQZero x X = 0 := by
  simp [paperQZero]

/-- The normalized conformal factor is one in the zero gauge. -/
theorem paper_zero_gauge_conformal_factor : Real.exp (2 * (0 : ℝ)) = 1 := by
  norm_num

/-- Pointwise form of the paper's torsion-free Weyl connection formula
`D_X Y = ∇_X Y + Q(X)Y + Q(Y)X - g(X,Y)Q♯`. -/
def PaperWeylConnectionPoint
    (nablaXY X Y Qsharp : ℝ³)
    (QX QY gXY : ℝ) : ℝ³ :=
  nablaXY + QX • Y + QY • X - gXY • Qsharp

/-- In the exact metric representative `Q=0`, the paper's Weyl connection formula
reduces identically to the underlying metric connection. -/
theorem paper_weyl_connection_zero_gauge
    (nablaXY X Y : ℝ³) (gXY : ℝ) :
    PaperWeylConnectionPoint nablaXY X Y 0 0 0 gXY = nablaXY := by
  simp [PaperWeylConnectionPoint]

/-- The conformal material acceleration from the paper. -/
def PaperGaugeMaterial
    (q normU2 : ℝ)
    (dt adv u Qsharp : ℝ³) : ℝ³ :=
  dt + adv + (2 * q) • u - normU2 • Qsharp

/-- In the zero gauge, the conformal material correction vanishes. -/
theorem paper_material_zero_gauge
    (normU2 : ℝ) (dt adv u : ℝ³) :
    PaperGaugeMaterial 0 normU2 dt adv u 0 = dt + adv := by
  simp [PaperGaugeMaterial]

/-- Exact viscous bracket in the paper's gauge expansion:
`Δ_B u + Ric♯(u) + (2-n) grad q + 2n E(u)(Q♯,·)♯ + 2n q Q♯`. -/
def PaperGaugeViscousBracket
    (n q : ℝ)
    (bochner ric gradQ strainQ Qsharp : ℝ³) : ℝ³ :=
  bochner + ric + (2 - n) • gradQ
    + (2 * n) • strainQ + (2 * n * q) • Qsharp

/-- In the flat zero gauge all Weyl/curvature corrections vanish and the viscous
bracket is just the Euclidean Laplacian term. -/
theorem paper_viscous_zero_gauge_flat
    (lap : ℝ³) :
    PaperGaugeViscousBracket 3 0 lap 0 0 0 0 = lap := by
  simp [PaperGaugeViscousBracket]

/-- Exact-gauge incompressibility operator `div_g u + n q`. -/
def PaperGaugeIncompressibilityOperator (n divG q : ℝ) : ℝ :=
  divG + n * q

/-- At `q=0`, the paper's incompressibility equation is ordinary divergence free. -/
theorem paper_divergence_zero_gauge (divG : ℝ) :
    PaperGaugeIncompressibilityOperator 3 divG 0 = divG := by
  simp [PaperGaugeIncompressibilityOperator]

/-! ## 2. Exact paper operator and direct classical reduction -/

/-- Left-minus-right exact Weyl-gauge Navier--Stokes operator used by the revised paper. -/
def PaperGaugeNSOperator
    (n rho eta em2phi q normU2 : ℝ)
    (dt adv u Qsharp gradP bochner ric gradQ strainQ : ℝ³) : ℝ³ :=
  rho • PaperGaugeMaterial q normU2 dt adv u Qsharp
    + em2phi • gradP
    - eta • (em2phi •
        PaperGaugeViscousBracket n q bochner ric gradQ strainQ Qsharp)

/-- Classical Euclidean Navier--Stokes operator recovered in the paper's flat `Q=0` limit. -/
def PaperEuclideanNSOperator
    (nu : ℝ) (dt adv gradP lap : ℝ³) : ℝ³ :=
  dt + adv + gradP - nu • lap

/-- This is the direct equation chain from the paper formulas: at
`n=3`, `ρ=1`, `η=ν`, `exp(-2φ)=1`, `Q=0`, `q=0`, and zero Ricci curvature,
the exact Weyl-gauge operator is literally the Euclidean Navier--Stokes operator. -/
theorem paper_zero_gauge_flat_operator_reduction
    (nu normU2 : ℝ)
    (dt adv u gradP lap : ℝ³) :
    PaperGaugeNSOperator 3 1 nu 1 0 normU2
      dt adv u 0 gradP lap 0 0 0
      = PaperEuclideanNSOperator nu dt adv gradP lap := by
  simp [PaperGaugeNSOperator, PaperGaugeMaterial,
    PaperGaugeViscousBracket, PaperEuclideanNSOperator]

/-- The paper's unforced flat equation `N_ν(u,p)=0` is the standard classical equation. -/
theorem paper_zero_gauge_flat_unforced_iff
    (nu normU2 : ℝ)
    (dt adv u gradP lap : ℝ³) :
    (PaperGaugeNSOperator 3 1 nu 1 0 normU2
      dt adv u 0 gradP lap 0 0 0 = 0)
      ↔
    (dt + adv = nu • lap - gradP) := by
  rw [paper_zero_gauge_flat_operator_reduction]
  constructor
  · intro h
    unfold PaperEuclideanNSOperator at h
    calc
      dt + adv
          = (dt + adv + gradP - nu • lap) + nu • lap - gradP := by abel
      _ = nu • lap - gradP := by rw [h]; abel
  · intro h
    unfold PaperEuclideanNSOperator
    calc
      dt + adv + gradP - nu • lap
          = (nu • lap - gradP) + gradP - nu • lap := by rw [h]
      _ = 0 := by abel

/-! ## 3. OpenAI force attached after the paper operator is identified -/

/-- The public OpenAI pointwise forced equation is precisely the paper's Euclidean
operator with an external right-hand side `f`. -/
theorem paper_euclidean_operator_forced_iff_comparator_core
    (nu : ℝ) (dt adv gradP lap force : ℝ³) :
    (PaperEuclideanNSOperator nu dt adv gradP lap = force)
      ↔
    (dt + adv = nu • lap - gradP + force) := by
  constructor
  · intro h
    calc
      dt + adv
          = (dt + adv + gradP - nu • lap) + nu • lap - gradP := by abel
      _ = force + nu • lap - gradP := by
        rw [show dt + adv + gradP - nu • lap = force by
          simpa [PaperEuclideanNSOperator] using h]
      _ = nu • lap - gradP + force := by abel
  · intro h
    unfold PaperEuclideanNSOperator
    calc
      dt + adv + gradP - nu • lap
          = (nu • lap - gradP + force) + gradP - nu • lap := by rw [h]
      _ = force := by abel

/-- Direct bridge from the exact paper gauge operator in the zero-gauge flat
representative to the OpenAI Comparator PDE. -/
theorem paper_zero_gauge_flat_forced_to_comparator_core
    (nu normU2 : ℝ)
    (dt adv u gradP lap force : ℝ³)
    (h : PaperGaugeNSOperator 3 1 nu 1 0 normU2
      dt adv u 0 gradP lap 0 0 0 = force) :
    dt + adv = nu • lap - gradP + force := by
  have hE : PaperEuclideanNSOperator nu dt adv gradP lap = force := by
    rw [← paper_zero_gauge_flat_operator_reduction nu normU2 dt adv u gradP lap]
    exact h
  exact (paper_euclidean_operator_forced_iff_comparator_core
    nu dt adv gradP lap force).mp hE

/-! ## 4. Global wrappers -/

/-- Whole-space solution conditions with the PDE written using the paper's exact
zero-gauge flat operator.  The energy fields are copied only because OpenAI's public
whole-space theorem includes them; no Weyl energy identity is used. -/
structure PaperZeroGaugeFlatForcedRn
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  exact_zero_gauge : ∀ x : ℝ³, fderiv ℝ paperPhiZero x = paperQZero x
  paper_navier_stokes : ∀ x, ∀ t ≥ 0,
    PaperGaugeNSOperator 3 1 nu 1 0 (‖v x t‖ ^ 2)
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (v x t)
      0
      (gradient (p · t) x)
      (Δ (v · t) x)
      0 0 0
      = f x t
  paper_div_free : ∀ x, ∀ t ≥ 0,
    PaperGaugeIncompressibilityOperator 3
      (NavierStokes.Comparator.divergence (v · t) x) 0 = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- Map the paper-equation wrapper to OpenAI's public whole-space solution structure. -/
theorem PaperZeroGaugeFlatForcedRn.toComparator
    {nu : ℝ} {u₀ : ℝ³ → ℝ³} {f : ℝ³ → ℝ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : PaperZeroGaugeFlatForcedRn nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn
      nu u₀ f v p := by
  refine {
    navier_stokes := ?_
    div_free := ?_
    initial_condition := h.initial_condition
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    integrable := h.integrable
    globally_bounded_energy := h.globally_bounded_energy
  }
  · intro x t ht
    exact paper_zero_gauge_flat_forced_to_comparator_core
      nu (‖v x t‖ ^ 2)
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (v x t)
      (gradient (p · t) x)
      (Δ (v · t) x)
      (f x t)
      (h.paper_navier_stokes x t ht)
  · intro x t ht
    simpa [PaperGaugeIncompressibilityOperator] using h.paper_div_free x t ht

/-- Periodic analogue. -/
structure PaperZeroGaugeFlatForcedPeriodic
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  exact_zero_gauge : ∀ x : ℝ³, fderiv ℝ paperPhiZero x = paperQZero x
  paper_navier_stokes : ∀ x, ∀ t ≥ 0,
    PaperGaugeNSOperator 3 1 nu 1 0 (‖v x t‖ ^ 2)
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (v x t)
      0
      (gradient (p · t) x)
      (Δ (v · t) x)
      0 0 0
      = f x t
  paper_div_free : ∀ x, ∀ t ≥ 0,
    PaperGaugeIncompressibilityOperator 3
      (NavierStokes.Comparator.divergence (v · t) x) 0 = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)
  isOnePeriodic_velocity : ∀ t ≥ 0, NavierStokes.Comparator.IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, NavierStokes.Comparator.IsOnePeriodic (p · t)

/-- Map the periodic paper-equation wrapper to OpenAI's public periodic structure. -/
theorem PaperZeroGaugeFlatForcedPeriodic.toComparator
    {nu : ℝ} {u₀ : ℝ³ → ℝ³} {f : ℝ³ → ℝ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : PaperZeroGaugeFlatForcedPeriodic nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
      nu u₀ f v p := by
  refine {
    navier_stokes := ?_
    div_free := ?_
    initial_condition := h.initial_condition
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    isOnePeriodic_velocity := h.isOnePeriodic_velocity
    isOnePeriodic_pressure := h.isOnePeriodic_pressure
  }
  · intro x t ht
    exact paper_zero_gauge_flat_forced_to_comparator_core
      nu (‖v x t‖ ^ 2)
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (v x t)
      (gradient (p · t) x)
      (Δ (v · t) x)
      (f x t)
      (h.paper_navier_stokes x t ht)
  · intro x t ht
    simpa [PaperGaugeIncompressibilityOperator] using h.paper_div_free x t ht

/-! ## 5. Composition with the published OpenAI C/D theorems -/

/-- OpenAI theorem (C), transferred to the exact zero-gauge flat equations of the paper. -/
theorem openai_breakdown_transfers_to_paper_zero_gauge_R3
    (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, PaperZeroGaugeFlatForcedRn nu u₀ f v p) := by
  rcases NavierStokes.Comparator.navier_stokes_breakdown_R3 nu hnu with
    ⟨u₀, f, hu₀, hf, hbreak⟩
  refine ⟨u₀, f, hu₀, hf, ?_⟩
  rintro ⟨v, p, hw⟩
  apply hbreak
  exact ⟨v, p, hw.toComparator⟩

/-- OpenAI theorem (D), transferred to the periodic zero-gauge flat equations. -/
theorem openai_breakdown_transfers_to_paper_zero_gauge_periodic
    (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, PaperZeroGaugeFlatForcedPeriodic nu u₀ f v p) := by
  rcases NavierStokes.Comparator.navier_stokes_breakdown_periodic nu hnu with
    ⟨u₀, f, hu₀, hf, hbreak⟩
  refine ⟨u₀, f, hu₀, hf, ?_⟩
  rintro ⟨v, p, hw⟩
  apply hbreak
  exact ⟨v, p, hw.toComparator⟩

#check paper_q_zero_is_exact
#check paper_weyl_connection_zero_gauge
#check paper_material_zero_gauge
#check paper_viscous_zero_gauge_flat
#check paper_divergence_zero_gauge
#check paper_zero_gauge_flat_operator_reduction
#check paper_zero_gauge_flat_unforced_iff
#check paper_euclidean_operator_forced_iff_comparator_core
#check paper_zero_gauge_flat_forced_to_comparator_core
#check PaperZeroGaugeFlatForcedRn.toComparator
#check PaperZeroGaugeFlatForcedPeriodic.toComparator
#check openai_breakdown_transfers_to_paper_zero_gauge_R3
#check openai_breakdown_transfers_to_paper_zero_gauge_periodic

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
#print axioms paper_q_zero_is_exact
#print axioms paper_weyl_connection_zero_gauge
#print axioms paper_material_zero_gauge
#print axioms paper_viscous_zero_gauge_flat
#print axioms paper_divergence_zero_gauge
#print axioms paper_zero_gauge_flat_operator_reduction
#print axioms paper_zero_gauge_flat_unforced_iff
#print axioms paper_euclidean_operator_forced_iff_comparator_core
#print axioms paper_zero_gauge_flat_forced_to_comparator_core
#print axioms PaperZeroGaugeFlatForcedRn.toComparator
#print axioms PaperZeroGaugeFlatForcedPeriodic.toComparator
#print axioms openai_breakdown_transfers_to_paper_zero_gauge_R3
#print axioms openai_breakdown_transfers_to_paper_zero_gauge_periodic

end
end AxabraWeylPaperZeroGaugeEquationsOpenAIBridge
