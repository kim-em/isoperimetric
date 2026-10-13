import Isoperimetric
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Check every local theorem and the essential reused geometric bridges. -/
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
    if (name.getRoot == `Isoperimetric && info.isTheorem) || bridges.contains name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
      logInfo m!"{name}: {axioms}"
      checked := checked + 1
  for bridge in bridges do
    unless env.contains bridge do
      throwError "Missing essential bridge {bridge}"
  unless env.contains `Isoperimetric.RectifiableJordan.isoperimetric do
    throwError "Missing public geometric inequality"
  logInfo m!"Axiom audit passed for {checked} declarations"
