module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PresentationTwistComparison

/-!
# The two twists `𝒪(1)` of a projective bundle agree

The projective bundle of a quasi-coherent module `ℰ` on `X` carries two twists `𝒪(1)`: the
twisting sheaf of the relative `Proj` situation of `Sym(ℰ)`, on
`Stacks.RelativeProj.projectiveBundle`, and the tautological twist of `Stacks.Chow.bundle`, the
presentation the projective space bundle formula and axiom (A3) of the Weil cohomology chapter are
stated at. This file proves that they agree, through the comparison of the two presentations:
`Stacks.ProjectiveBundle.nonempty_presentationTwistIso`. Over each affine open of `X` both are the
absolute twist of `Proj Γ(U, Sym ℰ)`; the chart comparisons glue because their descriptions over a
nested pair of affine opens agree (`Stacks.ProjectiveBundle.chartFactorTwistHom_eq_of_le`).

## Main results

* `Stacks.ProjectiveBundle.glueTargetLe_presentation`: the nested-chart hypothesis of the glueing
  `Stacks.ProjectiveBundle.nonempty_glueTwistIso`, for the inverse comparison of presentations.
* `Stacks.ProjectiveBundle.nonempty_presentationTwistIso`: **the two twists agree**.

## Implementation notes

The glueing `Stacks.ProjectiveBundle.nonempty_glueTwistIso` is stated at bare chart data and
instantiated here once. Its nested-chart hypothesis is stated through the two named sides
`Stacks.ProjectiveBundle.glueTargetLeLHS` and `Stacks.ProjectiveBundle.glueTargetLeRHS`, which are
identified with the chart descriptions by `rfl` one side at a time, in
`Stacks.ProjectiveBundle.glueTargetLeLHS_presentation` and
`Stacks.ProjectiveBundle.glueTargetLeRHS_presentation`: comparing the whole statement at once
exhausts the kernel's budget.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.SymGraded
open Stacks.Chow.GenuineChern

universe u

namespace Stacks.ProjectiveBundle

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

open Stacks.RelativeProj.Situation (relativeProjChart gradedSectionRestriction
  irrelevant_le_map_gradedSectionRestriction projMap_comp_relativeProjChart twistSheaf
  twistSheafChartIso)

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- For a nested pair `W' ≤ W` of affine opens, the left side `glueTargetLeLHS` of the
nested-chart hypothesis, for the inverse comparison of presentations, is the chart description
`chartFactorTwistHom` through the chart of `W'` with the graded map mixed along `W' ≤ W`. -/
theorem glueTargetLeLHS_presentation {W W' : (symSituation E).base.affineOpens} (h : W' ≤ W) :
    glueTargetLeLHS (presInv E hqc) (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      (schemeSheafGradedAlgebra E hqc) (toBaseAffine E)
      (fun W => (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
        (toBaseAffine E W).2) ((1 : ℕ) : ℤ)
      (fun W => Stacks.Chow.GenuineChern.chartTwistIso E hqc (toBaseAffine E W).1
        (toBaseAffine E W).2)
      (presGradedHom E hqc) (irrelevant_le_map_situationGradedHom E hqc)
      (relativeProjChart_comp_presentationIso_inv_eq E hqc) h =
    chartFactorTwistHom hqc (relativeProjChart (symSituation E) W') (presInv E hqc)
        (toBaseAffine E W).2
        (mixedGradedHom (schemeSheafGradedAlgebra E hqc) (toBaseAffine E W).1 h
          (presGradedHom E hqc W)) (irrelevant_le_map_situationGradedHom_comp E hqc h)
        (relativeProjChart_comp_presentationIso_inv_eq_of_le E hqc h) := rfl

/-- For an affine open `W'`, the right side `glueTargetLeRHS` of the nested-chart hypothesis, for
the inverse comparison of presentations, is the chart description `chartFactorTwistHom` over the
chart of `W'`. -/
theorem glueTargetLeRHS_presentation (W' : (symSituation E).base.affineOpens) :
    glueTargetLeRHS (presInv E hqc) (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      (schemeSheafGradedAlgebra E hqc) (toBaseAffine E)
      (fun W => (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
        (toBaseAffine E W).2) ((1 : ℕ) : ℤ)
      (fun W => Stacks.Chow.GenuineChern.chartTwistIso E hqc (toBaseAffine E W).1
        (toBaseAffine E W).2)
      (presGradedHom E hqc) (irrelevant_le_map_situationGradedHom E hqc)
      (relativeProjChart_comp_presentationIso_inv_eq E hqc) W' =
    chartFactorTwistHom hqc (relativeProjChart (symSituation E) W') (presInv E hqc)
        (toBaseAffine E W').2 (presGradedHom E hqc W')
        (irrelevant_le_map_situationGradedHom E hqc W')
        (relativeProjChart_comp_presentationIso_inv_eq E hqc W') := rfl

/-- The chart description over a nested pair is the chart description through the smaller chart,
for the inverse comparison of presentations: `Stacks.ProjectiveBundle.chartFactorTwistHom_eq_of_le`
read at the bare chart data of the glueing. -/
theorem glueTargetLe_presentation :
    GlueTargetLe (presInv E hqc) (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      (schemeSheafGradedAlgebra E hqc) (toBaseAffine E)
      (fun W => (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
        (toBaseAffine E W).2) ((1 : ℕ) : ℤ)
      (fun W => Stacks.Chow.GenuineChern.chartTwistIso E hqc (toBaseAffine E W).1
        (toBaseAffine E W).2)
      (presGradedHom E hqc) (irrelevant_le_map_situationGradedHom E hqc)
      (relativeProjChart_comp_presentationIso_inv_eq E hqc) :=
  fun {_ W'} h =>
    (glueTargetLeLHS_presentation E hqc h).trans
      ((chartFactorTwistHom_eq_of_le E hqc h).trans (glueTargetLeRHS_presentation E hqc W').symm)

/-- **The two twists `𝒪(1)` of the projective bundle of a quasi-coherent module agree.** The
tautological twist of the presentation `Stacks.Chow.bundle` of `𝐏(ℰ)`, read on the situation model
`Stacks.RelativeProj.projectiveBundle` through the comparison of presentations, is the twisting
sheaf `𝒪(1)` of the relative `Proj` situation of `Sym(ℰ)`. -/
theorem nonempty_presentationTwistIso :
    Nonempty ((Scheme.Modules.pullback (presInv E hqc)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      twistSheaf (symSituation E) ((1 : ℕ) : ℤ)) :=
  nonempty_glueTwistIso (presInv E hqc) (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    (schemeSheafGradedAlgebra E hqc) (toBaseAffine E)
    (fun W => (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
        (toBaseAffine E W).2) ((1 : ℕ) : ℤ)
    (fun W => Stacks.Chow.GenuineChern.chartTwistIso E hqc (toBaseAffine E W).1
        (toBaseAffine E W).2)
    (presGradedHom E hqc) (irrelevant_le_map_situationGradedHom E hqc)
    (relativeProjChart_comp_presentationIso_inv_eq E hqc) (glueTargetLe_presentation E hqc)
    (fun W => isIso_twistMap_presGradedHom E hqc W)

end Stacks.ProjectiveBundle

end
