# Planar isoperimetric theorem in Lean 4

**In development: the full geometric inequality and the circle converse are
proved. General equality rigidity still needs the Jordan winding orientation
bridge.** The complete requested scope is retained in [GOAL.txt](GOAL.txt).

For `γ : ℝ → EuclideanSpace ℝ (Fin 2)`, the current public theorem is
`Isoperimetric.RectifiableJordan.isoperimetric`:

```lean
ContinuousOn γ (Set.Icc 0 1)
γ 0 = γ 1
Set.InjOn γ (Set.Ico 0 1)
BoundedVariationOn γ (Set.Icc 0 1)
-- imply
4 * Real.pi * area γ ≤ length γ ^ 2
```

These four assumptions are bundled by `RectifiableJordan`. The definitions in
[Statement.lean](Isoperimetric/Statement.lean) set the trace to `γ '' Icc 0 1`,
length to `(eVariationOn γ (Icc 0 1)).toReal`, and area to
`(volume (enclosed γ)).toReal`. The enclosed set is MovingSofa's genuine Jordan
interior: points outside the trace whose complement component is bounded.
Area is not defined by a boundary integral. The geometric assumptions impose no
orientation, convexity, smoothness, or absolute continuity.

The target equality characterization, recorded as the unproved proposition
`ClassicalIsoperimetric`, is

```lean
4 * Real.pi * area γ = length γ ^ 2 ↔
  ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r
```

## Proof architecture and current results

- [Jordan.lean](Isoperimetric/Jordan.lean) descends the interval parametrization
  to `AddCircle 1`, proving that its trace is a Jordan curve in MovingSofa's
  circle-based definition. Jordan separation then proves that the enclosed set
  is open, connected, bounded, measurable, and has finite volume, with frontier
  equal to the trace. It also proves that length is finite and positive.
- [Arclength.lean](Isoperimetric/Arclength.lean) splits the loop at `1/2` into
  injective arcs. Their overlap consists only of the two endpoints and has zero
  one-dimensional Hausdorff measure. MovingSofa's arc theorem and additivity
  establish that Hausdorff length equals total variation.
- [Boundary.lean](Isoperimetric/Boundary.lean) proves that raw and Euclidean
  Hausdorff measures coincide in dimension one. It specializes Humanfia's
  complete geometric isoperimetric theorem to dimension two and the unit-disk
  volume constant `π`.
- [Inequality.lean](Isoperimetric/Inequality.lean) assembles the geometric
  inequality for the original arbitrary parametrization.
- [Parametrization.lean](Isoperimetric/Parametrization.lean) uses Mathlib's natural
  parametrization to construct a Lipschitz loop on `[0,1]`, with constant speed
  equal to the geometric length in the total-variation sense. It proves that
  this loop is again a rectifiable Jordan parametrization and preserves trace,
  length, enclosed set, and area.
- [Energy.lean](Isoperimetric/Energy.lean) proves that the arclength loop is
  absolutely continuous, its derivative has norm equal to the geometric length
  almost everywhere and belongs to `L²`, and its loop energy is the squared
  geometric length.
- [SignedArea.lean](Isoperimetric/SignedArea.lean) proves that arclength
  reparametrization preserves MovingSofa's signed Stieltjes area and identifies
  that functional with the usual coordinate boundary integral.
  [StieltjesDensity.lean](Isoperimetric/StieltjesDensity.lean) supplies the
  derivative density for absolutely continuous coordinates without assuming
  everywhere differentiability.
- [Analysis/Wirtinger.lean](Isoperimetric/Analysis/Wirtinger.lean) proves the sharp
  scalar periodic Wirtinger inequality for absolutely continuous real functions
  with square-integrable derivative. It extends the Fourier coefficient
  integration-by-parts identity to this regularity, then uses genuine Parseval.
- [Analysis/Planar.lean](Isoperimetric/Analysis/Planar.lean) proves that coordinate
  derivatives agree with projections of the vector derivative almost everywhere,
  then assembles scalar Wirtinger into the sharp planar estimate for the
  arclength loop.
- [Analysis/Area.lean](Isoperimetric/Analysis/Area.lean) identifies the signed area
  with the centered vector determinant integral. The rotation and
  [completion-of-squares](Isoperimetric/Analysis/CompletionSquare.lean) modules
  prove that signed-area equality forces the rotational ODE almost everywhere.
  [RotationalODE.lean](Isoperimetric/Analysis/RotationalODE.lean) solves it using
  absolute continuity and an integrating factor; [CircularImage.lean](Isoperimetric/Analysis/CircularImage.lean)
  proves that its image is exactly a circle of positive radius, handling both signs.
- [CircleInterior.lean](Isoperimetric/CircleInterior.lean) proves that the genuine
  interior of a positive-radius circle is its open disk. [Circle.lean](Isoperimetric/Circle.lean)
  proves its geometric length is `2 * π * r`, and transfers the circle equality
  to every permitted parametrization with that image.
- [GeometricArea.lean](Isoperimetric/GeometricArea.lean) reuses MovingSofa's
  Lebesgue-area bridge and treats clockwise orientation by reversing the BV path.
  It proves geometric equality rigidity once a genuine winding orientation is
  supplied. **That extra input has not yet been derived from the four advertised
  curve hypotheses.** The remaining mathematical bridge is that every such loop
  winds uniformly `1` or uniformly `-1` around its bounded Jordan component.
  The final unrestricted equality theorem and catalogue entry await that proof.

- [Topology/RegularPoint.lean](Isoperimetric/Topology/RegularPoint.lean) finds a
  nonzero derivative at an interior arclength parameter and constructs a short
  normal segment meeting the trace only at that point.
  [SmoothApproximation.lean](Isoperimetric/Topology/SmoothApproximation.lean)
  reuses TauCeti's endpoint-preserving Bernstein approximation for continuous
  complex paths. [WindingStability.lean](Isoperimetric/Topology/WindingStability.lean)
  proves that sufficiently small uniform perturbations preserve the topological
  winding of a continuous closed loop. These are inputs to the remaining
  orientation proof; they do not yet establish it.

## Reproducible build

Install Elan, then run:

```sh
bash scripts/prepare-dependencies.sh
bash scripts/check.sh
```

The default `lake build` compiles every local mathematical module and the
necessary dependency modules. It does not build the unrelated MovingSofa
development or Humanfia's incomplete `Challenge` benchmark template.
[AxiomAudit.lean](AxiomAudit.lean) checks every local theorem and essential reused
bridges against the allowlist `propext`, `Classical.choice`, `Quot.sound`, and
rejects importing `Challenge`. CI runs the build and audit.

## Dependency pins and credits

| Source | Exact revision |
| --- | --- |
| Lean | `v4.35.0-rc1` |
| Mathlib | `c32e1ec0d1eb5237ba344eee50162f45d5b0fc76` |
| [Humanfia Lean Eval archive](https://huggingface.co/datasets/humanfia-lab/lean-eval-source/tree/6a6d9f67a91d546677321aeea559c2857b697635/problems/isoperimetric_inequality) | `6a6d9f67a91d546677321aeea559c2857b697635` |
| [MovingSofa](https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127) | `4d5569131940815f47a9ccf3e90a4c5043c56127` |
| [TauCeti](https://github.com/TauCetiProject/TauCeti/tree/aa1f50f094b85057c11f0bb07177ff27a32dbd7f) | `aa1f50f094b85057c11f0bb07177ff27a32dbd7f` |

All transitive dependency revisions are recorded in `lake-manifest.json`.
Humanfia is consumed as a Git dependency with the Lake package subdirectory
`problems/isoperimetric_inequality`; its source archive is not vendored here.
[The compatibility patch](patches/humanfia-lean-4.35.patch) replaces one
`ae_restrict_iff` rewrite with a direct use of `ae_restrict_mem` in
`Submission/BrunnMinkowski/PrekopaLeindler.lean`. It changes no definitions or
theorem statements. The preparation script checks the archive revision and
applies the patch idempotently.
The script fetches the Humanfia Git archive without partial-clone filters before
Lake resolves it: the archive server's promised-blob fetches fail with HTTP 500.
The source URL, package subdirectory, and revision remain those in the manifest.

MovingSofa provides the Jordan separation and injective-arc Hausdorff length
proofs. Mathlib supplies the measure normalization and unit-disk volume results.
The analytic module contains attributed adaptations of Mathlib's Fourier
coefficient algebra and TauCeti's Parseval argument at revision
`8014353f314435299acce5b6faa19d781530cfa2`, strengthening the real scalar theorem
to absolute continuity. The upstream sharp Wirtinger and symplectic loop bound
still require derivatives everywhere.

TauCeti is also consumed directly as a pinned Git dependency for its smooth
approximation theorem. [The MovingSofa configuration patch](patches/movingsofa-upstream-tauceti.patch)
removes the vendored `TauCeti` library declaration, making the upstream package
its sole module provider. It changes no mathematical source. The preparation
script verifies MovingSofa's pin and applies this patch before Lake loads the
package configuration. The required modules compile against the root Lean and
Mathlib pins without a TauCeti source patch, despite TauCeti's own newer toolchain.
Only imported modules are built. Its straight-segment winding jump theorem was
also compiled successfully in this environment, but its piecewise `C¹`
hypothesis still needs a proved bridge to the original Lipschitz loop.

## Comparison with the HOL Light theorem

[Freek Wiedijk's entry 43](https://www.cs.ru.nl/~freek/100/hol.html#43) credits
[HOL Light's classical theorem](https://github.com/jrh13/hol-light/blob/master/100/isoperimetric.ml).
This repository targets that full rectifiable simple closed curve scope, with
equality precisely for circle images. The present inequality matches the
geometric scope, but the missing equality characterization means this
development is not yet a complete replacement for that entry.

The specification's macOS path `/Users/kim/projects/lean/isoperimetric` cannot be
created on this Linux host because `/Users` is not writable. The active local
repository is `/home/kim/isoperimetric`; build commands are independent of its
absolute path.
