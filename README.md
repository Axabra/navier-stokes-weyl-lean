# AXABRA exact-Weyl / Navier--Stokes Lean bridge

Author of the AXABRA bridge: Axel Abdel Rahamane Meghezzi.

Public proof repository:
<https://github.com/Axabra/navier-stokes-weyl-lean>.

This repository contains two fixed Lean certificates for the AXABRA
exact-Weyl-to-Navier--Stokes bridge associated with MathDB problem 315852
(JSP-000005): the accepted September baseline and a repaired, stronger
geometric realization of the same zero-gauge route.

It now also contains `PersonalBlowupR3.lean`, an AXABRA-side reconstruction of
the forced whole-space candidate.  This file does not call the terminal
`navier_stokes_breakdown_R3`, `theorem_1_1`, or `breakdownStatement` results.
It assembles the viscosity-one candidate from the fixed physical witness,
performs the arbitrary-viscosity scaling locally, and exports pointwise-speed
and derivative-H3 blow-up in every left neighbourhood of `t = 1`.

`PersonalWeylBlowupR3.lean` then realizes those same fields in the exact Weyl
representative `phi = 0`, `Q = d phi = 0`, with the Euclidean metric and the
certified Euclidean Levi-Civita connection.  It proves the paper operator
equation directly for every `0 < t < 1` and preserves both the pointwise-speed
and derivative-H3 blow-up at `t = 1`.

## Result and scope

`GeometricSubmission.lean` explicitly constructs the flat Euclidean
covariant derivative as `∇_X Y = DY · X`. It proves, using Mathlib's actual
Riemannian metric and torsion APIs, that this connection is
metric-compatible and torsion-free. Together with `Q = dφ = 0` and the unit
conformal factor, this gives the exact zero-Weyl Euclidean geometry used by
the AXABRA paper. The file then identifies the paper's Euclidean
Navier--Stokes operator, maps the AXABRA solution structures to the published
`NavierStokes.Comparator` structures, and composes those maps with the
published breakdown theorems for alternatives (C) and (D).

The AXABRA contribution is the formal bridge and its operator reductions.
The underlying finite-time breakdown construction and its complete Lean
formalization are imported from `openai/NavierStokesAndEuler` and remain
credited to OpenAI. Thus, "complete" describes the theorem obtained by the
pinned composition; it is not a claim that Axel Meghezzi independently
authored the upstream blow-up construction or has priority over it.

`PersonalBlowupR3.lean` is a local reconstruction and packaging of that same
mathematical mechanism, not a new provenance claim.  Unlike the earlier bridge
theorems, however, it exposes the singular witness itself rather than only the
negation of a global-solution structure.

`PersonalWeylBlowupR3.lean` is the corresponding exact geometric realization.
The zero gauge is a genuine exact-Weyl representative, not an approximation;
the file does not claim a nonzero-`Q` representative or independent priority
for the underlying blow-up mechanism.

## Geometric repair and September baseline

The historical `Submission.lean` is the exact accepted September artifact
`Axabra_Weyl_PAPER_ZERO_GAUGE_EQUATIONS_OpenAI_BRIDGE_20260912_064000.lean`.
Its SHA-256 and replay status are recorded below; the original local replay log
is intentionally excluded from the public repository because it contains local
machine paths.

The September geometric candidate
`Axabra_Weyl_ZERO_GAUGE_GEOMETRY_OpenAI_BRIDGE_20260912_062145.lean` failed
only because it imported a later, unavailable
`CovariantDerivative.LeviCivita` module. `GeometricSubmission.lean` repairs
that defect against the pinned revision by constructing the flat connection
from the Frechet derivative and proving the two defining Levi-Civita
properties directly. This repaired geometric file compiled locally on
2026-10-23 with exit code `0`; it has not yet received MathDB review.

## Principal declarations

- `personal_candidate_one_with_initial_rest`
- `construct_personal_blowup_R3`
- `personal_speed_unbounded_at_one`
- `personal_h3_unbounded_at_one`
- `personal_no_global_finite_energy_solution`
- `construct_personal_zero_weyl_blowup_R3`
- `personal_zero_weyl_speed_unbounded_at_one`
- `personal_zero_weyl_h3_unbounded_at_one`
- `personal_zero_weyl_no_global_finite_energy_solution`
- `paper_euclidean_connection_metric_compatible`
- `paper_euclidean_connection_torsion_free`
- `paper_zero_gauge_connection_is_levi_civita`
- `paper_zero_gauge_euclidean_geometry`
- `PaperZeroWeylEuclideanForcedRn.toComparator`
- `PaperZeroWeylEuclideanForcedPeriodic.toComparator`
- `openai_breakdown_realized_in_zero_exact_weyl_R3`
- `openai_breakdown_realized_in_zero_exact_weyl_periodic`

## Fixed versions

- Personal exact-Weyl R3 realization SHA-256:
  `63002a28726b797229df32d52e478810d8181a537bf66a20785be53f8a86e41b`
- Personal R3 reconstruction SHA-256:
  `834494cf0b9dc49116b09fe7aa712966c628a9284a19b4e671dd5608b832cc3e`
- Repaired geometric file SHA-256:
  `7d865bc0885ab2883873ccefd782cb90186b424b32fe4f9eedccad2770237232`
- Accepted September baseline `Submission.lean` SHA-256:
  `bbd75f3231691fc808ea4cff7c74be11d521d8bfc70474b572808191cab23c92`
- Upstream repository: <https://github.com/openai/NavierStokesAndEuler>
- Upstream commit:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
- Lean: `v4.34.0-rc2`
- Mathlib revision inherited from the pinned upstream project:
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`

## Reproduction

```text
lake update
lake exe cache get
lake build Submission
lake env lean PersonalBlowupR3.lean
lake env lean PersonalWeylBlowupR3.lean
lake env lean GeometricSubmission.lean
```

The geometric replay is summarized in
`verification/geometric-replay-20261023.json`. Its terminal declarations and
geometric anchor use only Lean's standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`; there are no `sorry`, `admit`, custom
`axiom`, or `unsafe` declarations in the file.

The direct R3 reconstruction is summarized in
`verification/personal-blowup-r3-20261023.json` and has the same clean axiom
boundary.

The exact-Weyl realization is summarized in
`verification/personal-weyl-blowup-r3-20261023.json`; the complete package
replay succeeds with 9,390 jobs and its four exported declarations have the
same clean axiom boundary.

## Public record

- Zenodo record: <https://doi.org/10.5281/zenodo.22974767>
- MathDB problem: <https://mathdb.com/p/315852/navier-stokes-existence-and-smoothness>
- Justin Sun Prize identifier: `JSP-000005`

See `ATTRIBUTION.md` for the exact division between the OpenAI mathematical
construction and the AXABRA bridge contribution.  This repository is not a
claim of solver priority or of priority over OpenAI's earlier complete Lean
formalization.
