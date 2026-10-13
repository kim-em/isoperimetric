# Planar isoperimetric theorem in Lean 4

**In development: the full geometric inequality is proved; equality rigidity is
not yet proved.** The complete requested scope is retained in [GOAL.txt](GOAL.txt).

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
- The remaining work is the Lipschitz arclength parametrization and its analytic
  area bridge, sharp Wirtinger at this regularity, almost-everywhere circular ODE
  rigidity, and the positive-radius circle converse. The final combined theorem
  and catalogue entry must wait for those proofs.

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

All transitive dependency revisions are recorded in `lake-manifest.json`.
Humanfia is consumed as a Git dependency with the Lake package subdirectory
`problems/isoperimetric_inequality`; its source archive is not vendored here.
[The compatibility patch](patches/humanfia-lean-4.35.patch) replaces one
`ae_restrict_iff` rewrite with a direct use of `ae_restrict_mem` in
`Submission/BrunnMinkowski/PrekopaLeindler.lean`. It changes no definitions or
theorem statements. The preparation script checks the archive revision and
applies the patch idempotently.

MovingSofa provides the Jordan separation and injective-arc Hausdorff length
proofs. Mathlib supplies the measure normalization and unit-disk volume results.
For the remaining analytic work, TauCeti revision
`8014353f314435299acce5b6faa19d781530cfa2` was inspected: its sharp Wirtinger and
symplectic loop bound still require derivatives everywhere. MovingSofa already
declares a vendored `TauCeti` library, so a second overlapping Lake dependency is
not added.

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
