module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaSheafSchemeFunctoriality
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeConsistency

/-!
# The `θ` half of clause (3) of Stacks Tag 01O9, along a nested pair of opens of the base

`…GradedPowerMap.relativeChart_affineDatum_resLE` proves the consistency of the clause (3)
prescriptions of [Stacks, Tag 01O9] along a nested pair of opens `Z ≤ V` of the base for the
**morphism** `r_{ℒ,ψ}`, off the hypothesis `hχ` it discharges there as
`…GradedPowerMap.affineDatum_hchi`. This file proves the same for the **other** output of
[Stacks, Tag 01NK], the map `θ`, in every integer degree.

That was the rung the gluing of the relative `θ` was missing. The nested compatibility compares
`θ` for two different graded rings — `𝒜(V)` and `𝒜(Z)` — *and* two different schemes —
`f^{-1}(V)` and `f^{-1}(Z)`. The graded-ring half is
`…ProjChartGradedThetaRingFunctoriality.intChartSection_comap` with its sheaf-level form
`…ProjChartGradedThetaSheafRingFunctoriality.pushTheta_comap_app_basicOpen`; the scheme half is
`…ProjChartGradedIntThetaSchemeFunctoriality.intChartSection_pullback` with its sheaf-level form
`…ProjChartGradedThetaSheafSchemeFunctoriality.pushTheta_app_basicOpen_pullback`, and this file
instantiates the latter at the data the global `(ℒ, ψ)` of [Stacks, Tag 01O8] induces.

## Main definitions

* `…GradedPowerMap.nestedDatum`: the induced datum over `Z`, restricted along `𝒜(V) → 𝒜(Z)` and
  transported onto the pullback of `ℒ|_{f^{-1}(V)}` — the left-hand side of `affineDatum_hchi`,
  packaged as a `…ProjChartFullGraded.GradedSections` so that the scheme functoriality applies.

## Main results

* `…GradedPowerMap.nestedDatum_toFun`: `affineDatum_hchi`, read as the hypothesis the scheme
  functoriality takes.
* `…GradedPowerMap.chartOpen_nestedDatum`: the chart open of `nestedDatum` is the preimage of the
  chart open of the datum over `V`.
* `…GradedPowerMap.intChartSection_nestedDatum`: **the chart comparison of the datum over `Z` is
  the pullback of the chart comparison of the datum over `V`**, in every integer degree.
* `…GradedPowerMap.pushTheta_nestedDatum`: **the same at sheaf level**, on the sections over
  `D₊(g)`.

## Implementation notes

Nothing is transported along an equality of objects and no new mathematics is done: each statement
is an application of the corresponding statement in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaSheafSchemeFunctoriality`
with `affineDatum_hchi` in the hypothesis slot. `nestedDatum_toFun` is `affineDatum_hchi` verbatim:
`…GradedSections.congrModule_toFun` holds by `rfl`, so the datum's value *is* the transported value
`affineDatum_hchi` speaks about.

## Status of the glued `θ`

`θ` is glued, and clause (1) is proved, elsewhere and by a different route: the pushforward form of
`θ` is glued over the charts of [Stacks, Tag 01NQ] as `…GradedPowerMap.thetaPush`, where the
agreement of two chart data is checked on standard opens by multiplicativity and cancellation
rather than by the functoriality recorded here; `θ` itself is `…GradedPowerMap.theta` and clause (1)
is `…GradedPowerMap.theta_clauseOne`. No tag is carried here.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (restrictCompIso)
open Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback (intPullSectionOn)
open Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback (intCompare)
open Stacks.AlgebraicGeometry.ProjChartGradedIntThetaSchemeFunctoriality
  (intChartSection_pullback)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaSheafSchemeFunctoriality
  (chartOpen_eq_preimage pushTheta_app_basicOpen_pullback)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (pushTheta)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections (congrModule)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) {Z V : S.Opens} (h : Z ≤ V)

/-- **The induced datum over `Z`, restricted to the graded ring `𝒜(V)` and transported onto the
pullback of the module over `f^{-1}(V)`.** This is the left-hand side of
`…GradedPowerMap.affineDatum_hchi`, packaged as a datum of graded sections so that the
functoriality of `θ` in the scheme applies to it directly. -/
def nestedDatum : GradedSections (A.grading V)
    ((Scheme.Modules.pullback (T.homOfLE (f.preimage_mono h))).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)) :=
  congrModule (restrictCompIso P.L (f.preimage_mono h))
    (comap (A.res h) (P.affineDatum Z))

/-- `affineDatum_hchi`, read as the hypothesis the functoriality of `θ` in the scheme takes: the
values of `nestedDatum` are the pullbacks of the values of the datum over `V`. -/
theorem nestedDatum_toFun (n : ℕ) (a : A.grading V n) :
    (P.nestedDatum h).toFun n a
      = Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection
          (T.homOfLE (f.preimage_mono h))
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n ((P.affineDatum V).toFun n a) :=
  P.affineDatum_hchi h n a

variable {e : ℕ} {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e)

include hg he

/-- **The chart opens of the two induced data agree**: the chart open of `nestedDatum` in
`f^{-1}(Z)` is the preimage of the chart open of the datum over `V` in `f^{-1}(V)`. -/
theorem chartOpen_nestedDatum :
    (P.nestedDatum h).chartOpen g
      = (T.homOfLE (f.preimage_mono h)) ⁻¹ᵁ (P.affineDatum V).chartOpen g :=
  chartOpen_eq_preimage (A.grading V) (T.homOfLE (f.preimage_mono h)) (P.affineDatum V)
    (P.nestedDatum h) (P.nestedDatum_toFun h) hg he

/-- **The `θ` half of clause (3) of [Stacks, Tag 01O9] along a nested pair of opens of the base,
at chart level**: the chart comparison of the induced datum over `Z` is the pullback of the chart
comparison of the induced datum over `V`, in **every** integer degree.

The counterpart for the morphism `r_{ℒ,ψ}` is
`…GradedPowerMap.relativeChart_affineDatum_resLE`; this is the same statement for the other output
of [Stacks, Tag 01NK], which the gluing of the relative `θ` consumes. Nothing is carried: the
hypothesis is `…GradedPowerMap.affineDatum_hchi`. -/
theorem intChartSection_nestedDatum (n : ℤ)
    (y : gradedPiece (A.grading V) (integerGrading (S := A.sectionRing V) (A.grading V)) g n) :
    intChartSection (P.nestedDatum h) hg ((P.nestedDatum h).chartOpen_eq hg he).le he n y
      = intPullSectionOn (T.homOfLE (f.preimage_mono h))
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)
          (intCompare (T.homOfLE (f.preimage_mono h))
            ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)) n
          (P.chartOpen_nestedDatum h hg he).le
          (intChartSection (P.affineDatum V) hg
            ((P.affineDatum V).chartOpen_eq hg he).le he n y) :=
  intChartSection_pullback (T.homOfLE (f.preimage_mono h))
    ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) (P.affineDatum V) (P.nestedDatum h)
    (P.nestedDatum_toFun h) hg ((P.affineDatum V).chartOpen_eq hg he).le
    (P.chartOpen_nestedDatum h hg he).le ((P.nestedDatum h).chartOpen_eq hg he).le he n y

/-- **The same at sheaf level**: `θ` of the induced datum over `Z`, on the sections over `D₊(g)`
of `Proj 𝒜(V)`, is the pullback of `θ` of the induced datum over `V`. -/
theorem pushTheta_nestedDatum (n : ℤ)
    (s : Γ(twistM (A.grading V) n, AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    ((P.nestedDatum h).chartTargetIso n g).hom
        ((pushTheta (A.grading V) (P.nestedDatum h) n).app
          (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) s)
      = intPullSectionOn (T.homOfLE (f.preimage_mono h))
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)
          (intCompare (T.homOfLE (f.preimage_mono h))
            ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)) n
          (P.chartOpen_nestedDatum h hg he).le
          (intChartSection (P.affineDatum V) hg
            ((P.affineDatum V).chartOpen_eq hg he).le he n
            (sectionsTwistEquivGradedPiece (A.grading V) hg he n s)) :=
  pushTheta_app_basicOpen_pullback (A.grading V) (T.homOfLE (f.preimage_mono h))
    (P.affineDatum V) (P.nestedDatum h) (P.nestedDatum_toFun h) hg he n s

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
