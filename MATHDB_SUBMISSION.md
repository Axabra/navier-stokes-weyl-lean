# MathDB submission draft — problem 315852 / JSP-000005

## Summary

Kernel-checked geometric realization of the AXABRA exact-zero-Weyl gauge, followed by a complete transfer of the Navier–Stokes breakdown alternatives (C) and (D). The AXABRA contribution is the explicit flat connection, its metric/torsion certificate, and the verified solution-structure bridge; the imported blow-up construction remains credited to OpenAI.

The package additionally supplies `PersonalBlowupR3.lean`, a local
reconstruction of the whole-space candidate which does not invoke any terminal
breakdown theorem.  It exposes directly the smooth pre-singular fields, the
smooth compactly supported force, bounded kinetic energy before `t = 1`,
unbounded pointwise speed, unbounded derivative-H3 norm, and impossibility of a
global smooth finite-energy continuation.

`PersonalWeylBlowupR3.lean` packages the same explicit witness with the exact
zero-Weyl Euclidean geometry and proves `N_nu(u,p) = f` in the paper's operator
notation for every `0 < t < 1`.  Thus the blow-up fields themselves, not only a
negated global-solution proposition, are available in the geometric interface.

## Label

Proof

## Requested review scope

This is submitted as an additional Lean realization and reproducible
geometric bridge for JSP-000005.  It does not request mathematical-solver
credit for the underlying blow-up construction and does not claim priority
over OpenAI's earlier complete formalization.  MathDB and the prize team should
determine whether the additional bridge is recordable or eligible under the
Lean category rules; no award entitlement is asserted by this upload.

## Solution text

### Contribution

This submission provides a fixed, reproducible Lean bridge from the revised
AXABRA exact-Weyl hydrodynamic equations to the classical three-dimensional
incompressible Navier–Stokes formulation used on this MathDB page.

In the exact representative

\[
\phi=0,\qquad Q=0,\qquad e^{-2\phi}=1,
\]

and for a flat metric with unit density, `GeometricSubmission.lean` constructs
the Euclidean connection explicitly as `∇_X Y = DY · X`. It proves with
Mathlib's covariant-derivative API that the connection is metric-compatible
and has zero torsion, hence satisfies the defining Levi-Civita
characterization. It then identifies the AXABRA Euclidean operator and
constructs maps from the AXABRA whole-space and periodic solution structures
to the published `NavierStokes.Comparator` structures.

The main AXABRA bridge declarations are:

- `paper_euclidean_connection_metric_compatible`;
- `paper_euclidean_connection_torsion_free`;
- `paper_zero_gauge_connection_is_levi_civita`;
- `paper_zero_gauge_euclidean_geometry`;
- `PaperZeroWeylEuclideanForcedRn.toComparator`;
- `PaperZeroWeylEuclideanForcedPeriodic.toComparator`.

Composing these maps with the pinned upstream theorems gives:

- `openai_breakdown_realized_in_zero_exact_weyl_R3`;
- `openai_breakdown_realized_in_zero_exact_weyl_periodic`.

These last declarations prove the complete published breakdown alternatives
(C) and (D) in the exact zero-gauge AXABRA interface.

### Attribution and scope

Axel Abdel Rahamane Meghezzi is the author of the AXABRA formal bridge and its
operator reductions. The underlying finite-time breakdown construction and
its complete Lean formalization are imported from the pinned
`openai/NavierStokesAndEuler` repository and remain credited to OpenAI. The
label **Proof** refers to the complete C/D theorem established by the composed
artifact. It is not a claim that the AXABRA bridge independently reconstructs
the upstream blow-up argument or establishes priority over it.

The new R3 file reconstructs the theorem locally from the pinned low-level
physical witness and repeats the scaling and continuation argument in the
AXABRA package.  Its mathematical mechanism is intentionally the published
OpenAI mechanism; “personal” here means a locally assembled, independently
auditable certificate rather than an originality claim.

The exact-Weyl realization uses `phi = 0` and `Q = d phi = 0`.  This is an
exact representative of Weyl geometry, not an approximation.  No claim is made
here that a nonzero-`Q` representative has been formalized.

### Geometric repair and September 2026 provenance

The proposed root file is `GeometricSubmission.lean`, repaired from the
September candidate
`Axabra_Weyl_ZERO_GAUGE_GEOMETRY_OpenAI_BRIDGE_20260912_062145.lean`. The
candidate's historical run failed because the pinned Mathlib revision has no
`CovariantDerivative.LeviCivita` module. The repair does not assume that
missing constructor: it builds the flat connection from the Frechet
derivative and proves metric compatibility and zero torsion directly.

`Submission.lean` remains the byte-for-byte accepted September baseline
`Axabra_Weyl_PAPER_ZERO_GAUGE_EQUATIONS_OpenAI_BRIDGE_20260912_064000.lean`.
The repaired geometric file is a new local certificate compiled on
2026-10-23; it is pending external MathDB review.

### Reproduction and fixed versions

- Proposed root proof file: `GeometricSubmission.lean`.
- Direct finite-time witness: `PersonalBlowupR3.lean`.
- Direct exact-Weyl finite-time witness: `PersonalWeylBlowupR3.lean`.
- Personal exact-Weyl R3 realization SHA-256:
  `63002a28726b797229df32d52e478810d8181a537bf66a20785be53f8a86e41b`.
- Personal R3 reconstruction SHA-256:
  `834494cf0b9dc49116b09fe7aa712966c628a9284a19b4e671dd5608b832cc3e`.
- SHA-256: `7d865bc0885ab2883873ccefd782cb90186b424b32fe4f9eedccad2770237232`.
- Accepted baseline SHA-256:
  `bbd75f3231691fc808ea4cff7c74be11d521d8bfc70474b572808191cab23c92`.
- Lean: `v4.34.0-rc2`.
- Pinned upstream commit:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- Geometric replay: Lean exit code 0; the axiom audit for the geometric anchor,
  bridge maps, and terminal C/D declarations contains only `propext`,
  `Classical.choice`, and `Quot.sound`.

Reproduction commands:

```text
lake update
lake exe cache get
lake build Submission
lake env lean PersonalBlowupR3.lean
lake env lean PersonalWeylBlowupR3.lean
lake env lean GeometricSubmission.lean
```

### Public record

- Zenodo: <https://doi.org/10.5281/zenodo.22974767>
- Upstream proof: <https://github.com/openai/NavierStokesAndEuler>
- MathDB problem: <https://mathdb.com/p/315852/navier-stokes-existence-and-smoothness>
- Public Lean repository: <https://github.com/Axabra/navier-stokes-weyl-lean>
