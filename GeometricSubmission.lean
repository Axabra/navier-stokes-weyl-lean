import NavierStokes.ComparatorSolution
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Zero-gauge geometric realization of the Axabra Weyl paper, bridged to OpenAI C/D

This certificate deliberately takes the shortest exact route relevant to the OpenAI target.
The revised paper proves that an exact Weyl structure may be represented in its normalized
metric gauge.  For the OpenAI whole-space / periodic statements we only need the special
exact representative

  φ = 0, Q = 0, ĝ = g_Euclidean,

so there is no need to formalize the full arbitrary-Q conformal expansion of Theorem 5.3.
In this gauge the Weyl connection is an ordinary metric, torsion-free connection, hence the
Levi-Civita connection.  The pinned Mathlib revision does not yet contain its later
`CovariantDerivative.LeviCivita` constructor, so the flat Euclidean connection is built below
from the Frechet derivative and its metric compatibility and zero torsion are proved from the
official `CovariantDerivative.Metric` and `CovariantDerivative.Torsion` APIs.

The PDE layer then uses Corollary 7.2 of the paper:

  N_ν(u,p) = ∂ₜu + (u·∇)u + ∇p - νΔu.

The paper's unforced equation is N_ν(u,p)=0.  The OpenAI force is attached only afterwards
as an external right-hand side N_ν(u,p)=f, exactly as in the published Comparator statement.

No Weyl energy identity is used.  The whole-space wrapper carries OpenAI's bounded-energy
side condition unchanged only because it is part of the public theorem type.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Bundle Laplacian Manifold ContDiff

namespace AxabraWeylZeroGaugeGeometryOpenAIBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## 1. Genuine Euclidean exact-Weyl zero gauge -/

/-- The zero potential used for the metric gauge of the exact Weyl structure. -/
def paperPhiZero : ℝ³ → ℝ := fun _ => 0

/-- The zero Weyl one-form, represented as a field of continuous linear functionals. -/
def paperQZero : ℝ³ → (ℝ³ →L[ℝ] ℝ) := fun _ => 0

/-- In Euclidean coordinates the zero Weyl form is genuinely exact: `Q = dφ` with `φ = 0`. -/
theorem paper_q_zero_is_exact (x : ℝ³) :
    fderiv ℝ paperPhiZero x = paperQZero x := by
  change fderiv ℝ (fun _ : ℝ³ => (0 : ℝ)) x = 0
  exact fderiv_const_apply (𝕜 := ℝ) 0

/-- The conformal factor of the normalized metric is exactly one in the zero gauge. -/
theorem paper_zero_gauge_conformal_factor : Real.exp (2 * (0 : ℝ)) = 1 := by
  norm_num

/- On a model vector space, Mathlib's vector-valued manifold derivative is the Frechet
derivative under the canonical tangent-space identification. -/
set_option backward.isDefEq.respectTransparency false in
theorem paper_mvfderiv_model_space_eq_fderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ³ → F) (x : ℝ³) : d% f x = fderiv ℝ f x := by
  rw [mvfderiv, mfderiv_eq_fderiv]
  rfl

/- The Riemannian scalar product on a tangent fiber of Euclidean space is its ordinary
Euclidean scalar product in model coordinates. -/
set_option backward.isDefEq.respectTransparency false in
theorem paper_tangent_inner_eq_model_inner (x : ℝ³)
    (v w : TangentSpace 𝓘(ℝ, ℝ³) x) :
    inner ℝ v w =
      let v0 : ℝ³ := v
      let w0 : ℝ³ := w
      inner ℝ v0 w0 := by
  rfl

/-- Canonical coordinate representative of a tangent vector field on Euclidean model space. -/
def paperTangentFieldToModel
    (sigma : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) : ℝ³ → ℝ³ :=
  fun x =>
    let v : ℝ³ := sigma x
    v

@[simp]
theorem paperTangentFieldToModel_apply
    (sigma : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) (x : ℝ³) :
    paperTangentFieldToModel sigma x = sigma x := rfl

@[simp]
theorem paperTangentFieldToModel_add
    (sigma tau : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) :
    paperTangentFieldToModel (sigma + tau) =
      paperTangentFieldToModel sigma + paperTangentFieldToModel tau := by
  rfl

@[simp]
theorem paperTangentFieldToModel_smul
    (g : ℝ³ → ℝ) (sigma : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) :
    paperTangentFieldToModel (g • sigma) = g • paperTangentFieldToModel sigma := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem paper_mdifferentiableAt_tangentFieldToModel_iff
    (sigma : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) (x : ℝ³) :
    MDiffAt (T% sigma) x ↔ MDiffAt (paperTangentFieldToModel sigma) x := by
  rw [mdifferentiableAt_section]
  have hfun :
      (fun b =>
        (trivializationAt ℝ³ (TangentSpace 𝓘(ℝ, ℝ³)) x (sigma b)).2) =
        paperTangentFieldToModel sigma := by
    funext b
    rw [trivializationAt_model_space_apply]
    exact (paperTangentFieldToModel_apply sigma b).symm
  rw [hfun]

/- The flat Euclidean covariant derivative, explicitly `∇_X Y = DY · X`. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def paperEuclideanLC :
    CovariantDerivative 𝓘(ℝ, ℝ³) ℝ³
      (TangentSpace 𝓘(ℝ, ℝ³) : ℝ³ → Type _) where
  toFun := fun sigma x => d% (paperTangentFieldToModel sigma) x
  isCovariantDerivativeOnUniv := by
    constructor
    · intro sigma sigma' x hsigma hsigma' hx
      have hsigma0 : MDiffAt (paperTangentFieldToModel sigma) x :=
        (paper_mdifferentiableAt_tangentFieldToModel_iff sigma x).mp hsigma
      have hsigma0' : MDiffAt (paperTangentFieldToModel sigma') x :=
        (paper_mdifferentiableAt_tangentFieldToModel_iff sigma' x).mp hsigma'
      rw [paperTangentFieldToModel_add]
      exact mvfderiv_add hsigma0 hsigma0'
    · intro sigma g x hsigma hg hx
      have hsigma0 : MDiffAt (paperTangentFieldToModel sigma) x :=
        (paper_mdifferentiableAt_tangentFieldToModel_iff sigma x).mp hsigma
      rw [paperTangentFieldToModel_smul]
      exact mvfderiv_smul hg hsigma0

set_option backward.isDefEq.respectTransparency false in
theorem paperEuclideanLC_apply_model
    (sigma : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) (x v : ℝ³) :
    paperEuclideanLC sigma x v =
      fderiv ℝ (paperTangentFieldToModel sigma) x v := by
  change (d% (paperTangentFieldToModel sigma) x) v =
    fderiv ℝ (paperTangentFieldToModel sigma) x v
  exact congrArg (fun A : ℝ³ →L[ℝ] ℝ³ => A v)
    (paper_mvfderiv_model_space_eq_fderiv (paperTangentFieldToModel sigma) x)

/- The Euclidean connection used in the paper's `Q = 0` representative is genuinely
metric-compatible.  This is the `Dg = 0` part of the Weyl condition when `Q = 0`. -/
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem paper_euclidean_connection_metric_compatible :
    paperEuclideanLC.IsMetricCompatible := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X sigma tau hX hsigma htau
  have hsigma0 : MDiffAt (paperTangentFieldToModel sigma) x :=
    (paper_mdifferentiableAt_tangentFieldToModel_iff sigma x).mp hsigma
  have htau0 : MDiffAt (paperTangentFieldToModel tau) x :=
    (paper_mdifferentiableAt_tangentFieldToModel_iff tau x).mp htau
  have hinnerfun :
      (fun y : ℝ³ => inner ℝ (sigma y) (tau y)) =
        (fun y : ℝ³ =>
          inner ℝ (paperTangentFieldToModel sigma y)
            (paperTangentFieldToModel tau y)) := by
    funext y
    exact paper_tangent_inner_eq_model_inner y (sigma y) (tau y)
  calc
    d% (fun y => inner ℝ (sigma y) (tau y)) x (X x) =
        fderiv ℝ (fun y =>
          inner ℝ (paperTangentFieldToModel sigma y)
            (paperTangentFieldToModel tau y)) x (X x) := by
      rw [paper_mvfderiv_model_space_eq_fderiv]
      exact congrArg (fun f : ℝ³ → ℝ => fderiv ℝ f x (X x)) hinnerfun
    _ = inner ℝ (fderiv ℝ (paperTangentFieldToModel sigma) x (X x))
          (paperTangentFieldToModel tau x) +
        inner ℝ (paperTangentFieldToModel sigma x)
          (fderiv ℝ (paperTangentFieldToModel tau) x (X x)) := by
      simpa only [add_comm] using
        (fderiv_inner_apply ℝ hsigma0.differentiableAt htau0.differentiableAt (X x))
    _ = inner ℝ (paperEuclideanLC sigma x (X x)) (tau x) +
        inner ℝ (sigma x) (paperEuclideanLC tau x (X x)) := by
      simp only [paperEuclideanLC_apply_model,
        paperTangentFieldToModel_apply]

set_option backward.isDefEq.respectTransparency false in
theorem paper_mlieBracket_eq_model_lieBracket
    (X Y : (x : ℝ³) → TangentSpace 𝓘(ℝ, ℝ³) x) (x : ℝ³) :
    VectorField.mlieBracket 𝓘(ℝ, ℝ³) X Y x =
      VectorField.lieBracket ℝ
        (paperTangentFieldToModel X) (paperTangentFieldToModel Y) x := by
  rw [← VectorField.mlieBracketWithin_univ]
  rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
  rw [VectorField.lieBracketWithin_univ]
  congr 1

/- The same explicitly constructed Euclidean connection is torsion-free. -/
set_option backward.isDefEq.respectTransparency false in
theorem paper_euclidean_connection_torsion_free :
    paperEuclideanLC.torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  rw [paperEuclideanLC_apply_model, paperEuclideanLC_apply_model,
    paper_mlieBracket_eq_model_lieBracket]
  rfl

/-- In the pinned Mathlib revision the later packaged `IsLeviCivitaConnection` predicate is
absent.  This local certificate records its standard defining characterization. -/
structure PaperIsLeviCivitaConnection
    (cov : CovariantDerivative 𝓘(ℝ, ℝ³) ℝ³
      (TangentSpace 𝓘(ℝ, ℝ³) : ℝ³ → Type _)) : Prop where
  metric_compatible : cov.IsMetricCompatible
  torsion_free : cov.torsion = 0

/-- Hence the explicit zero-gauge Euclidean connection is a genuine Levi-Civita connection:
it is metric-compatible and torsion-free. -/
theorem paper_zero_gauge_connection_is_levi_civita :
    PaperIsLeviCivitaConnection paperEuclideanLC :=
  ⟨paper_euclidean_connection_metric_compatible,
    paper_euclidean_connection_torsion_free⟩

/-- A compact proposition collecting the exact geometric data used downstream. -/
structure PaperZeroGaugeEuclideanGeometry : Prop where
  q_exact : ∀ x : ℝ³, fderiv ℝ paperPhiZero x = paperQZero x
  conformal_factor : Real.exp (2 * (0 : ℝ)) = 1
  metric_compatible : paperEuclideanLC.IsMetricCompatible
    (M := ℝ³) (V := TangentSpace 𝓘(ℝ, ℝ³))
  torsion_free : paperEuclideanLC.torsion = 0
  levi_civita : PaperIsLeviCivitaConnection paperEuclideanLC

/-- The geometry required by the optimized route is inhabited without hypotheses. -/
theorem paper_zero_gauge_euclidean_geometry : PaperZeroGaugeEuclideanGeometry := by
  refine ⟨?_, paper_zero_gauge_conformal_factor,
    paper_euclidean_connection_metric_compatible,
    paper_euclidean_connection_torsion_free,
    paper_zero_gauge_connection_is_levi_civita⟩
  exact paper_q_zero_is_exact

/-! ## 2. Corollary 7.2 as the Euclidean operator -/

/-- The Euclidean Navier--Stokes operator recovered by Corollary 7.2 of the paper,
with unit mass density and kinematic viscosity `ν`. -/
def PaperEuclideanNSOperator
    (nu : ℝ) (dt adv gradP lap : ℝ³) : ℝ³ :=
  dt + adv + gradP - nu • lap

/-- The paper's unforced Euclidean equation is exactly `N_ν(u,p)=0`. -/
theorem paper_corollary72_unforced_equation
    (nu : ℝ) (dt adv gradP lap : ℝ³) :
    PaperEuclideanNSOperator nu dt adv gradP lap = 0 ↔
      dt + adv = nu • lap - gradP := by
  constructor
  · intro h
    unfold PaperEuclideanNSOperator at h
    have : dt + adv + gradP - nu • lap = 0 := h
    calc
      dt + adv
          = (dt + adv + gradP - nu • lap) + nu • lap - gradP := by abel
      _ = nu • lap - gradP := by rw [this]; abel
  · intro h
    unfold PaperEuclideanNSOperator
    calc
      dt + adv + gradP - nu • lap
          = (nu • lap - gradP) + gradP - nu • lap := by rw [h]
      _ = 0 := by abel

/-! ## 3. External force attached after the paper operator is identified -/

/-- OpenAI's pointwise forced equation is precisely the same paper operator with an
external RHS `f`: `N_ν(u,p)=f`. -/
theorem paper_euclidean_operator_forced_iff_comparator_core
    (nu : ℝ) (dt adv gradP lap force : ℝ³) :
    (PaperEuclideanNSOperator nu dt adv gradP lap = force) ↔
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

/-! ## 4. Global solution wrappers in the genuine zero-Weyl Euclidean representative -/

/-- Whole-space solution conditions written with the Euclidean operator of Corollary 7.2.
The proposition `geometry` is a theorem, not an assumption: it records that this really is
an exact zero-Weyl Euclidean geometry with the Mathlib Levi-Civita connection.
-/
structure PaperZeroWeylEuclideanForcedRn
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  geometry : PaperZeroGaugeEuclideanGeometry
  paper_navier_stokes : ∀ x, ∀ t ≥ 0,
    PaperEuclideanNSOperator nu
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (gradient (p · t) x)
      (Δ (v · t) x)
      = f x t
  paper_div_free : ∀ x, ∀ t ≥ 0,
    NavierStokes.Comparator.divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- Map the paper's genuine zero-gauge Euclidean formulation into OpenAI's public
whole-space solution structure. -/
theorem PaperZeroWeylEuclideanForcedRn.toComparator
    {nu : ℝ} {u₀ : ℝ³ → ℝ³} {f : ℝ³ → ℝ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : PaperZeroWeylEuclideanForcedRn nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn
      nu u₀ f v p := by
  refine {
    navier_stokes := ?_
    div_free := h.paper_div_free
    initial_condition := h.initial_condition
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    integrable := h.integrable
    globally_bounded_energy := h.globally_bounded_energy
  }
  intro x t ht
  exact (paper_euclidean_operator_forced_iff_comparator_core
    nu
    (derivWithin (v x ·) (Set.Ici 0) t)
    (fderiv ℝ (v · t) x (v x t))
    (gradient (p · t) x)
    (Δ (v · t) x)
    (f x t)).mp (h.paper_navier_stokes x t ht)

/-- Periodic analogue. -/
structure PaperZeroWeylEuclideanForcedPeriodic
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  geometry : PaperZeroGaugeEuclideanGeometry
  paper_navier_stokes : ∀ x, ∀ t ≥ 0,
    PaperEuclideanNSOperator nu
      (derivWithin (v x ·) (Set.Ici 0) t)
      (fderiv ℝ (v · t) x (v x t))
      (gradient (p · t) x)
      (Δ (v · t) x)
      = f x t
  paper_div_free : ∀ x, ∀ t ≥ 0,
    NavierStokes.Comparator.divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)
  isOnePeriodic_velocity : ∀ t ≥ 0, NavierStokes.Comparator.IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, NavierStokes.Comparator.IsOnePeriodic (p · t)

/-- Map the periodic zero-gauge paper formulation into OpenAI's public periodic structure. -/
theorem PaperZeroWeylEuclideanForcedPeriodic.toComparator
    {nu : ℝ} {u₀ : ℝ³ → ℝ³} {f : ℝ³ → ℝ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : PaperZeroWeylEuclideanForcedPeriodic nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
      nu u₀ f v p := by
  refine {
    navier_stokes := ?_
    div_free := h.paper_div_free
    initial_condition := h.initial_condition
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    isOnePeriodic_velocity := h.isOnePeriodic_velocity
    isOnePeriodic_pressure := h.isOnePeriodic_pressure
  }
  intro x t ht
  exact (paper_euclidean_operator_forced_iff_comparator_core
    nu
    (derivWithin (v x ·) (Set.Ici 0) t)
    (fderiv ℝ (v · t) x (v x t))
    (gradient (p · t) x)
    (Δ (v · t) x)
    (f x t)).mp (h.paper_navier_stokes x t ht)

/-! ## 5. Transfer of the published OpenAI breakdown theorems -/

/-- Published OpenAI theorem (C), restated as nonexistence of a global smooth solution
in the genuine `φ=0`, `Q=0`, Euclidean exact-Weyl representative of the paper.
-/
theorem openai_breakdown_realized_in_zero_exact_weyl_R3
    (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, PaperZeroWeylEuclideanForcedRn nu u₀ f v p) := by
  rcases NavierStokes.Comparator.navier_stokes_breakdown_R3 nu hnu with
    ⟨u₀, f, hu₀, hf, hbreak⟩
  refine ⟨u₀, f, hu₀, hf, ?_⟩
  rintro ⟨v, p, hw⟩
  apply hbreak
  exact ⟨v, p, hw.toComparator⟩

/-- Published OpenAI theorem (D), in the periodic zero-Weyl Euclidean representative. -/
theorem openai_breakdown_realized_in_zero_exact_weyl_periodic
    (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, PaperZeroWeylEuclideanForcedPeriodic nu u₀ f v p) := by
  rcases NavierStokes.Comparator.navier_stokes_breakdown_periodic nu hnu with
    ⟨u₀, f, hu₀, hf, hbreak⟩
  refine ⟨u₀, f, hu₀, hf, ?_⟩
  rintro ⟨v, p, hw⟩
  apply hbreak
  exact ⟨v, p, hw.toComparator⟩

/-! ## Audit -/

#check paper_q_zero_is_exact
#check paper_euclidean_connection_metric_compatible
#check paper_euclidean_connection_torsion_free
#check paper_zero_gauge_connection_is_levi_civita
#check paper_zero_gauge_euclidean_geometry
#check paper_corollary72_unforced_equation
#check paper_euclidean_operator_forced_iff_comparator_core
#check PaperZeroWeylEuclideanForcedRn.toComparator
#check PaperZeroWeylEuclideanForcedPeriodic.toComparator
#check openai_breakdown_realized_in_zero_exact_weyl_R3
#check openai_breakdown_realized_in_zero_exact_weyl_periodic

#print axioms paper_q_zero_is_exact
#print axioms paper_euclidean_connection_metric_compatible
#print axioms paper_euclidean_connection_torsion_free
#print axioms paper_zero_gauge_connection_is_levi_civita
#print axioms paper_zero_gauge_euclidean_geometry
#print axioms paper_corollary72_unforced_equation
#print axioms paper_euclidean_operator_forced_iff_comparator_core
#print axioms PaperZeroWeylEuclideanForcedRn.toComparator
#print axioms PaperZeroWeylEuclideanForcedPeriodic.toComparator
#print axioms openai_breakdown_realized_in_zero_exact_weyl_R3
#print axioms openai_breakdown_realized_in_zero_exact_weyl_periodic
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic

end

end AxabraWeylZeroGaugeGeometryOpenAIBridge
