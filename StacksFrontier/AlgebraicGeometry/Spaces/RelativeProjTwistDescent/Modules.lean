module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationDatum

/-!
# The twists `𝒪_P(n)` of the relative Proj of Situation 0849

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`X = U/R` a presentation of its base, so that `P = P_U/P_R` with `P_U = U ×_X P` and
`P_R = R ×_X P`.  The twist `𝒪(n)` of Stacks 01NR on the scheme of `P_U` and the scheme transition
`t^*𝒪(n) ≅ s^*𝒪(n)` on `P_R` of
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition` satisfy the cocycle and unit
conditions (`…presentationSchemeCocycle_twistTransition`,
`…presentationSchemeUnit_twistTransition`),
so they descend through Stacks 03M3 to a quasi-coherent `𝒪_P`-module `𝒪_P(n)`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistModule`: **the twist `𝒪_P(n)`**, a
  quasi-coherent `𝒪_P`-module on the small étale site of `P`.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleChartIso`: the identification of its
  inverse image along the chart `P_U ⟶ P` with (the module attached through Stacks 03DX (2) to) the
  twist `𝒪(n)` of Stacks 01NR on the scheme of `P_U`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_twistModule`: `𝒪_P(n)` is
  quasi-coherent.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistModuleChartIso_comm`: the chart
  identification carries the canonical transition morphism of the inverse image to the transition
  of the twists.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The twist `𝒪_P(n)` of the relative Proj `P = Proj_X(𝒜)` of Situation 0849** (Stacks 084D):
the quasi-coherent `𝒪_P`-module obtained by descending the twist `𝒪(n)` of Stacks 01NR on the
scheme of `P_U = U ×_X P`, with the transition of
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition`, along the presentation
`P = P_U/P_R` over a presentation `X = U/R` of the base (Stacks 03M3). -/
def twistModule (n : ℤ) :
    QuasicoherentSheaves.{u, u} s.site s.base s.containsBase s.relativeProjFunctor
      s.isAlgebraicSpace_relativeProjFunctor :=
  presentationDescendedModule
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
    (s.presentationSchemeCocycle_twistTransition Px n)
    (s.presentationSchemeUnit_twistTransition Px n)

/-- **The twist `𝒪_P(n)` is quasi-coherent** on the small étale site of `P`. -/
theorem isQuasicoherentOnSite_twistModule (n : ℤ) :
    (s.twistModule Px n).obj.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_presentationDescendedModule _ _ _ _ _

/-- **The inverse image of `𝒪_P(n)` along the chart `P_U ⟶ P` is the twist `𝒪(n)` of Stacks 01NR on
the scheme of `P_U`**, read as a module on the representable algebraic space `P_U` through
Stacks 03DX (2). -/
def twistModuleChartIso (n : ℤ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).obj
        (s.twistModule Px n).obj ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
          (s.twistPieceQcoh Px.U Px.toSpace n)).obj :=
  presentationDescendedModuleChartIso _ _ _ _ _

/-- **The chart identification of `𝒪_P(n)` carries the canonical transition morphism of its inverse
image to the transition of the twists**. -/
theorem twistModuleChartIso_comm (n : ℤ) :
    TransitionCommutes s.site s.base s.containsBase
      (U := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).objects)
      (V := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).arrows)
      (a := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).target)
      (b := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).source)
      ((presentationQuasicoherentEquivalence (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).functor.obj (s.twistModule Px n)).alpha
      (presentationSchemeTransition (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor) (s.twistPieceQcoh Px.U Px.toSpace n)
        (s.twistTransition Px n))
      (s.twistModuleChartIso Px n).hom :=
  presentationDescendedModuleChartIso_comm _ _ _ _ _

end AlgebraicGeometry.Space.RelativeProjSituation

end
