/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Check every public and private local theorem, essential reused bridges, and final geometric results.
-/

open Lean Elab Command
run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `Challenge then
    throwError "The benchmark template Challenge is in the import closure"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let bridges : Array Name := #[
    `Submission.isoperimetric,
    `MeasureTheory.hausdorffMeasure_image_Icc_eq_eVariationOn,
    `MovingSofa.jordan_separation,
    `MovingSofa.IsJordanCurve.frontier_jordanInterior,
    `MovingSofa.intervalStieltjes_absoluteContinuity,
    `MovingSofa.intervalStieltjesIntegral_eq_integral_mul_of_density,
    `MovingSofa.curveAreaFunctional_eq_of_comp_monotone_surjective,
    `MovingSofa.curveArea_eq_jordanInterior_area]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let isLocalTheorem := (privateToUserName name).getRoot == `Isoperimetric && info.isTheorem
    if isLocalTheorem || bridges.contains name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  for bridge in bridges do
    unless env.contains bridge do
      throwError "Missing essential bridge {bridge}"
  for finalTheorem in #[`Isoperimetric.classical_isoperimetric,
      `Isoperimetric.classical_isoperimetric_specification,
      `Isoperimetric.RectifiableJordan.classical_isoperimetric,
      `Isoperimetric.RectifiableJordan.circle_of_area_equality,
      `Isoperimetric.RectifiableJordan.equality_of_circle] do
    unless env.contains finalTheorem do
      throwError "Missing final geometric theorem {finalTheorem}"
  logInfo m!"Axiom audit passed for {checked} declarations"
