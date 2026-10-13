# The classical planar isoperimetric theorem in Lean 4

For every continuous rectifiable simple closed planar curve, this repository
proves `4 * π * A ≤ L²`, with equality **if and only if its image is a circle
of positive radius**. Both orientations, nonconvex curves, and arbitrary
continuous rectifiable parametrizations are covered.

The public theorem in [Main.lean](Isoperimetric/Main.lean) is:

```lean
theorem Isoperimetric.classical_isoperimetric
    (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Set.Icc 0 1))
    (hclosed : γ 0 = γ 1)
    (hsimple : Set.InjOn γ (Set.Ico 0 1))
    (hrectifiable : BoundedVariationOn γ (Set.Icc 0 1)) :
    4 * Real.pi * area γ ≤ length γ ^ 2 ∧
      (4 * Real.pi * area γ = length γ ^ 2 ↔
        ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r)
```

[Statement.lean](Isoperimetric/Statement.lean) defines `trace γ = γ '' Icc 0 1`,
`length γ = (eVariationOn γ (Icc 0 1)).toReal`, and
`area γ = (volume (enclosed γ)).toReal`. The enclosed set is MovingSofa's genuine
Jordan interior: points outside the trace with bounded complement component.
[Jordan.lean](Isoperimetric/Jordan.lean) proves measurability, boundedness, finite
volume, finite variation, and positive length. No smoothness, orientation, or
analytic identity is assumed by the final theorem. The original specification
is retained unchanged in [GOAL.txt](GOAL.txt).

## Proof

- The interval loop descends to a Jordan curve on the circle. MovingSofa's
  Jordan separation gives its interior and frontier. Splitting into two
  injective arcs identifies Hausdorff boundary length with total variation;
  raw and normalized Hausdorff measure are reconciled explicitly.
- [Inequality.lean](Isoperimetric/Inequality.lean) specializes Humanfia's complete
  geometric isoperimetric inequality to the Jordan interior in dimension two.
- [Parametrization.lean](Isoperimetric/Parametrization.lean) and
  [Energy.lean](Isoperimetric/Energy.lean) construct an absolutely continuous
  Lipschitz loop with speed `L` almost everywhere, preserving image, length,
  interior, area, and signed Stieltjes area. Its energy is `L²`.
- [Topology/Orientation.lean](Isoperimetric/Topology/Orientation.lean) derives
  winding orientation from the geometric hypotheses. At a regular arclength
  point a short normal segment meets the curve once. A continuous argument
  calculation proves a unit winding jump across it. Jordan separation, local
  constancy, and vanishing in the unbounded component give interior winding
  uniformly `1` or `-1`. MovingSofa's area theorem then identifies the signed
  boundary functional with actual Lebesgue area, handling reversal explicitly.
- [Analysis/Wirtinger.lean](Isoperimetric/Analysis/Wirtinger.lean) extends Fourier
  integration by parts and sharp Wirtinger to absolute continuity with an `L²`
  derivative. The planar estimate and completion of squares force the rotational
  ODE almost everywhere at equality. Absolute continuity solves this ODE with
  an integrating factor; its image is a positive-radius circle.
- [Circle.lean](Isoperimetric/Circle.lean) and
  [CircleInterior.lean](Isoperimetric/CircleInterior.lean) prove circle length
  `2 * π * r` and genuine interior area `π * r²`, including the equality converse
  for every permitted parametrization with that image.

TauCeti's endpoint-preserving smooth approximation is also reused in
[Topology/SmoothApproximation.lean](Isoperimetric/Topology/SmoothApproximation.lean),
which proves approximation preserving topological winding. The final orientation
proof uses a direct continuous argument jump and does not require smooth approximation.

## Build and audit

Install Elan, then run:

```sh
bash scripts/prepare-dependencies.sh
bash scripts/check.sh
```

The default build compiles every local mathematical module and only the needed
dependency modules. [AxiomAudit.lean](AxiomAudit.lean) checks all local theorems,
the final inequality and equality characterization, and essential reused bridges.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. CI enforces the
build, audit, and absence of local proof placeholders or bypasses. Humanfia's
incomplete `Challenge` benchmark template is excluded from the import closure.

## Pins and credits

Formalization by Kim Morrison, with Codex assistance, using Mathlib, Humanfia's
Lean Eval archive, MovingSofa, and TauCeti. Local analytic proofs include
attributed adaptations of Mathlib's Fourier coefficient algebra and TauCeti's
Parseval argument, strengthened to absolute continuity.

| Source | Exact revision |
| --- | --- |
| Lean | `v4.35.0-rc1` |
| Mathlib | `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76` |
| [Humanfia Lean Eval archive](https://huggingface.co/datasets/humanfia-lab/lean-eval-source/tree/6a6d9f67a91d546677321aeea559c2857b697635/problems/isoperimetric_inequality) | `6a6d9f67a91d546677321aeea559c2857b697635` |
| [MovingSofa](https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127) | `4d5569131940815f47a9ccf3e90a4c5043c56127` |
| [TauCeti](https://github.com/TauCetiProject/TauCeti/tree/aa1f50f094b85057c11f0bb07177ff27a32dbd7f) | `aa1f50f094b85057c11f0bb07177ff27a32dbd7f` |

All transitive pins are in `lake-manifest.json`. Humanfia is a Git dependency
with package subdirectory `problems/isoperimetric_inequality`, not vendored.
[Its compatibility patch](patches/humanfia-lean-4.35.patch) replaces one
`ae_restrict_iff` rewrite with `ae_restrict_mem`, changing no definition or
statement. The archive is cloned without partial-clone filters because its
promised-blob fetches fail with HTTP 500.

[The MovingSofa configuration patch](patches/movingsofa-upstream-tauceti.patch)
removes its vendored TauCeti library declaration. The upstream dependency becomes
the sole provider of TauCeti modules; no mathematical source is changed. The
preparation script checks source pins and applies both patches idempotently.
The imported TauCeti modules compile with the root pins without a source patch.
The adapted Wirtinger source revision is `8014353f314435299acce5b6faa19d781530cfa2`.

## Catalogue comparison

This proves the full rectifiable simple closed curve scope of
[Freek Wiedijk's HOL Light entry 43](https://www.cs.ru.nl/~freek/100/hol.html#43)
and [HOL Light's `ISOPERIMETRIC_THEOREM`](https://github.com/jrh13/hol-light/blob/master/100/isoperimetric.ml),
and also proves the circle converse and positivity of its radius.
A ready-to-send catalogue entry is provided in `CATALOGUE.txt`.

The requested macOS path `/Users/kim/projects/lean/isoperimetric` is not writable
on this Linux host. The working repository is `/home/kim/isoperimetric`; the build
is independent of its absolute path.
