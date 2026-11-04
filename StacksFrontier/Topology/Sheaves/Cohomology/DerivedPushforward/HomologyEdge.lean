module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactnessOfPushforwardAndPullback

/-!
# The cohomology edge morphism of the derived direct image

For a morphism of ringed spaces `f : X ⟶ Y` the derived direct image `Rf_*` and the degreewise
direct image `f_*` are compared on cohomology sheaves by a canonical map

> `H^q(Rf_* K) ⟶ f_* H^q(K)`.

It is the unique natural transformation out of `Rf_* ⋙ H^q`, as a right derived functor of
`K ↦ H^q(f_* K)`, extending the comparison of `H^q` with the left exact functor `f_*` on the
homotopy category. It is not an isomorphism in general.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison`: the
  edge morphism `H^q(Rf_* -) ⟶ f_* H^q(-)`, for every morphism of ringed spaces and every
  degree.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison_fac_app`:
  the degree-`q` cohomology of the comparison `f_* M ⟶ Rf_* M`, followed by the edge morphism, is
  the comparison of `H^q` with `f_*` on the homotopy category.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The cohomology edge morphism `H^q(Rf_* K) ⟶ f_* H^q(K)` of the derived direct image: the
unique natural transformation out of `Rf_* ⋙ H^q`, as a right derived functor of
`K ↦ H^q(f_* K)`, extending the comparison of `H^q` with the left exact `f_*` on the homotopy
category. -/
def derivedPushforwardHomologyComparison (q : ℤ) :
    derivedPushforward f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q ⟶
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q ⋙
        modulePushforward f :=
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
    (modulePushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
    (exists_quasiIso_isKInjective X) q

/-- At a complex `M` of `𝒪_X`-modules, the degree-`q` cohomology of the comparison
`f_* M ⟶ Rf_* M` followed by the edge morphism is the comparison of `H^q` with `f_*` on the
homotopy category. -/
theorem derivedPushforwardHomologyComparison_fac_app (q : ℤ)
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).map
          ((derivedPushforwardUnit f).app M) ≫
        (derivedPushforwardHomologyComparison f q).app (DerivedCategory.Qh.obj M) =
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopyHomologyComparisonToDerived
        (modulePushforward f) q).app M :=
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison_fac_app
    (modulePushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
    (exists_quasiIso_isKInjective X) q M

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
