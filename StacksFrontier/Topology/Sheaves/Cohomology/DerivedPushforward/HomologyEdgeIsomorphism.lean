module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.BoundedBelowEdgeIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomologyEdge
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# When the cohomology edge morphism of the derived direct image is invertible

For a morphism of ringed spaces `f : X ⟶ Y` the edge morphism

> `H^q(Rf_* K) ⟶ f_* H^q(K)`

of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison`
exists for every `f`, every `q` and every `K`, and `HomologyEdge.lean` is careful to say that it
is not an isomorphism in general — the degreewise direct image is not exact.

It **is** one as soon as two things hold of `K`: that it is cohomologically bounded below, and
that each of its cohomology sheaves is right acyclic for the degreewise direct image, i.e. that
all the higher direct images of all the `H^j(K)` vanish. That is
`Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE` for an arbitrary unbounded
right derived functor, and the edge morphism of the direct image is that construction at the
direct image, so this file is its instantiation and nothing more.

The regime this is for: an **affine** morphism and a `K` with quasi-coherent cohomology. There
[Stacks, Tag 01XC] gives the acyclicity — in the form
`Stacks.Cohomology.AffineComparison.rightAcyclic_pushforward_of_isAffineHom` — and the edge
morphism becomes the degeneration of the Leray spectral sequence that [Stacks, Tag 089W] is the
global-sections form of. Conclusion (c) of [Stacks, Tag 0EX3] meets the edge morphism in exactly
that regime, over a pair of affine opens, along the restriction of the square's horizontal
morphism.

## Main results

* `…DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardHomologyComparison_app_of_isGE`:
  **the edge morphism is invertible at a cohomologically bounded below object all of whose
  cohomology sheaves are right acyclic for the degreewise direct image**, with no hypothesis on
  the morphism of ringed spaces and in every degree.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyIso`: the same as
  an isomorphism `H^q(Rf_* K) ≅ f_* H^q(K)`.

## The comparison with [Stacks, Tag 089W]

**Proved.** `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_hom_eq`
(`AlgebraicGeometry/AffineCohomologyComparison/UnboundedModel.lean:387`) reads
[Stacks, Tag 089W] at the unbounded model: for an affine morphism of schemes and a quasi-coherent
`F`, `cohomologyIsoPushforward` is restriction of scalars pulled inside the right derived
functor, the crossing of the two models at `F` inverted, the comparison of the two iterated
derived functors, `RG` of the collapse of `Rf_*`, and the crossing of the two models at `f_* F`.

Its four inputs, in order of depth:

* `CategoryTheory.Functor.boundedDerivedIso` — the `D⁺`-to-`D` crossing of a right derived
  functor at an arbitrary additive functor, with its pinning;
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app` — the crossing
  between the two models at a single complex **is** that one;
* `CategoryTheory.Functor.boundedDerivedIso_hom_app_comp_rightDerivedFunctorPlusComp` — the
  composition comparison on `D⁺` is the one on `D`;
* `Stacks.Cohomology.AffineComparison.map_rightDerivedFunctorPlusObjSingleIso_inv` — the collapse
  at an acyclic object matches.

The edge morphism inverted here is the half of the route that this file supplies. The route's
remaining factor, the comparison of the two iterated derived pushforwards, is
[Stacks, Tag 079W]'s pair of composition isomorphisms
(`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_natTrans_eq_compIso`).

## Implementation notes

*Nothing is re-derived.* The invertibility criterion is proved once, for an arbitrary right
derived functor on an unbounded derived category, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/BoundedBelowEdgeIsomorphism.lean`:
a bounded below object is represented by a complex of injectives concentrated in degrees `≥ n`,
which is K-injective, and there the edge morphism is the complex-level comparison, invertible
because each cohomology object is acyclic.
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison` is
literally `derivedHomologyComparison` at `modulePushforward f`, `derivedPushforward f` and
`derivedPushforwardUnit f`, so the criterion applies with no transport: the three arguments are
the same terms the definition uses, and the `IsRightDerivedFunctor` instance is the one already
registered for the total right derived functor.

*The acyclicity is a hypothesis and not an affineness assumption.* Stated at
`CategoryTheory.Functor.rightAcyclic` of the degreewise direct image, the criterion covers the
affine case, the exact case and the closed-immersion case alike, and a consumer supplies whichever
vanishing statement it holds. Specialising to affine morphisms of schemes would force the
statement across the two spellings of the modules on a scheme —
`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules _`, equal types with different `Abelian`
instances, as `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedModelCrossing.lean` records — and `Functor.rightAcyclic` at the two
instances is not the same term.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The cohomology edge morphism of the derived direct image is invertible at a bounded below
object with acyclic cohomology sheaves.** For a morphism of ringed spaces `f : X ⟶ Y`, a degree
`q`, an object `K` of `D(𝒪_X)` with no cohomology below some `n`, and the hypothesis that every
cohomology sheaf `H^j(K)` is right acyclic for the degreewise direct image `f_*`, the edge
morphism

`H^q(Rf_* K) ⟶ f_* H^q(K)`

is an isomorphism.

This is `Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE` at
`modulePushforward f`, the edge morphism of the direct image being that general construction
there. No hypothesis is placed on `f` itself: for an affine morphism of schemes and a `K` with
quasi-coherent cohomology the acyclicity is [Stacks, Tag 01XC]. -/
theorem isIso_derivedPushforwardHomologyComparison_app_of_isGE (q n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) [K.IsGE n]
    (hH : ∀ j : ℤ, (modulePushforward f).rightAcyclic
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) j).obj K)) :
    IsIso ((derivedPushforwardHomologyComparison f q).app K) :=
  Stacks.BoundedBelowEdge.isIso_derivedHomologyComparison_app_of_isGE (modulePushforward f)
    (derivedPushforward f) (derivedPushforwardUnit f) (exists_quasiIso_isKInjective X) q K n hH

/-- **The cohomology edge morphism of the derived direct image, as an isomorphism**, at a
cohomologically bounded below object whose cohomology sheaves are right acyclic for the degreewise
direct image:

`H^q(Rf_* K) ≅ f_* H^q(K)`.

This is the degeneration a consumer rewrites with; its forward direction is the edge morphism
itself, so every identity proved about the edge morphism applies to it unchanged. -/
def derivedPushforwardHomologyIso (q n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) [K.IsGE n]
    (hH : ∀ j : ℤ, (modulePushforward f).rightAcyclic
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) j).obj K)) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).obj
        ((derivedPushforward f).obj K) ≅
      (modulePushforward f).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q).obj K) :=
  haveI := isIso_derivedPushforwardHomologyComparison_app_of_isGE f q n K hH
  asIso ((derivedPushforwardHomologyComparison f q).app K)

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
