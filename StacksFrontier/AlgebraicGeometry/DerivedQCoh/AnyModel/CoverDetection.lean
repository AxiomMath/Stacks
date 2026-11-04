module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Restriction to two covering opens detects isomorphisms, at an arbitrary model

Let `X` be a scheme covered by two opens `U` and `V`. A morphism of `D(𝒪_X)` whose restrictions
to `U` and to `V` are invertible is invertible, and an object whose two restrictions vanish
vanishes. Both statements are read here at an **arbitrary** model of the three derived
categories, through free `[HasDerivedCategory.{w} _]` binders.

The detection itself is `isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar`, in
the namespace `Stacks.Cohomology.PushforwardRestriction`, proved by reducing through
`DerivedCategory.isIso_iff` to the cohomology sheaves and checking on stalks, every point lying in
one of the two opens. It is stated with `ExtensionByZeroModules.jStar`, restriction to an open of
the underlying topological space. The statements here use Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the open immersion `U.ι`, and the two
restrictions are identified on derived categories with the model left free.

## Main definitions

* `Stacks.DerivedQCoh.AnyModel.derivedJStarIsoRestrictFunctor` — the crossing on derived
  categories, at an arbitrary model of each side.

## Main results

* `Stacks.DerivedQCoh.AnyModel.isIso_of_isIso_derivedRestrict_of_cover` — a morphism of `D(𝒪_X)`
  invertible on each of two covering opens is invertible.
* `Stacks.DerivedQCoh.AnyModel.isZero_of_isZero_derivedRestrict_of_cover` — an object of
  `D(𝒪_X)` vanishing on each of two covering opens vanishes.

## Implementation notes

**Why not `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.** That is the
same crossing, but it declares no `HasDerivedCategory` binder, so the two models in its type are
whatever instance search finds, which is `CategoryTheory.HasDerivedCategory.standard` — its
derived categories have morphisms in `Type (u + 1)`. A statement at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, where morphisms are in `Type u`, cannot
be fed to it. The construction below is the same one with the two models as binders.

**Why six exactness instances are passed as terms.** `Scheme.Modules X` is a `def` for
`SheafOfModules X.ringCatSheaf`, and `Stacks.StrictlyPerfect.OXMod X.toRingedSpace` is that type
a third time; the three agree definitionally but not reducibly, so typeclass synthesis does not
cross between them and fails for whichever functor is not written in the spelling in force. The
functors themselves need no comparison:
`ExtensionByZeroModules.jStar U X.ringCatSheaf` and
`AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U` are the same term, so the
module-level comparison `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` is
already the one needed.

**Relation to `Stacks.Cohomology.GlueingComplexes.isIso_of_isIso_derivedPullback_of_cover`.**
That is the ringed-space statement, for a pair of arbitrary open immersions and in the
derived-pullback spelling, and its file installs the standard model as a file-local instance. It
is the same thin instantiation of the same model-free detection lemma; neither is derivable from
the other, because the model is fixed there and free here, and because the spellings of
restriction differ.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.PushforwardRestriction
open ZeroObject

universe u w w'

namespace Stacks.DerivedQCoh.AnyModel

/-- **Restriction to an open subscheme on derived categories, in the two vocabularies, at an
arbitrary model.** The functor induced by `ExtensionByZeroModules.jStar`, restriction of
`𝒪_X`-modules to the open subspace `U`, is the one induced by Mathlib's restriction along the
open immersion `U.ι`.

The module-level identification is
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` — the two functors are
pushforwards along the same functor on opens, along morphisms of sheaves of rings that are equal
— and this carries it to derived categories through
`CategoryTheory.Functor.mapDerivedCategoryCongr`. The two models are binders, and all six
exactness instances are supplied as terms. -/
def derivedJStarIsoRestrictFunctor (X : Scheme.{u}) (U : X.Opens)
    [hX : HasDerivedCategory.{w} X.Modules] [hU : HasDerivedCategory.{w'} U.toScheme.Modules] :
    @Functor.mapDerivedCategory _ _ _ hX _ _ _ hU (jStar U X.ringCatSheaf)
        (RingedSpace.restrictModules_additive X.toRingedSpace U)
        (RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U)
        (RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U) ≅
      @Functor.mapDerivedCategory _ _ _ hX _ _ _ hU
        (Scheme.Modules.restrictFunctor U.ι) _ _ _ :=
  have hL : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  have hC : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  @Functor.mapDerivedCategoryCongr _ _ _ hX _ _ _ hU _ _
    (RingedSpace.restrictModules_additive X.toRingedSpace U)
    (RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U)
    (RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U)
    (Scheme.Modules.restrictFunctor_additive U.ι) hL hC
    (RingedSpace.restrictModulesIsoRestrictFunctor X U)

variable {X : Scheme.{u}} (U V : X.Opens) (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
  [hX : HasDerivedCategory.{w} X.Modules] [hU : HasDerivedCategory.{w} U.toScheme.Modules]
  [hV : HasDerivedCategory.{w} V.toScheme.Modules]

include hUV

/-- **A morphism of `D(𝒪_X)` invertible on two covering opens is invertible.** Both restrictions
are Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the inclusion of the open,
and the model of each of the three derived categories is free.

This is `isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar` after
`Stacks.DerivedQCoh.AnyModel.derivedJStarIsoRestrictFunctor` on each of the two opens. -/
theorem isIso_of_isIso_derivedRestrict_of_cover
    {E F : DerivedCategory X.Modules} (f : E ⟶ F)
    (hfU : IsIso ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map f))
    (hfV : IsIso ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map f)) :
    IsIso f :=
  @isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar _ X.ringCatSheaf U V hUV hX hU hV
    (RingedSpace.restrictModules_additive X.toRingedSpace U)
    (RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U)
    (RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U)
    (RingedSpace.restrictModules_additive X.toRingedSpace V)
    (RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace V)
    (RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace V)
    E F f
    ((NatIso.isIso_map_iff (derivedJStarIsoRestrictFunctor X U) f).mpr hfU)
    ((NatIso.isIso_map_iff (derivedJStarIsoRestrictFunctor X V) f).mpr hfV)

/-- **An object of `D(𝒪_X)` vanishing on two covering opens vanishes.** The unique map to a zero
object restricts to a map between zero objects on each of the two opens, hence is invertible
there; so it is invertible, by
`Stacks.DerivedQCoh.AnyModel.isIso_of_isIso_derivedRestrict_of_cover`. -/
theorem isZero_of_isZero_derivedRestrict_of_cover {M : DerivedCategory X.Modules}
    (hMU : IsZero ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj M))
    (hMV : IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj M)) :
    IsZero M := by
  have h0 : IsZero (0 : DerivedCategory X.Modules) := isZero_zero _
  have hiso : IsIso (0 : M ⟶ (0 : DerivedCategory X.Modules)) :=
    isIso_of_isIso_derivedRestrict_of_cover U V hUV _
      (hMU.isIso ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map_isZero h0) _)
      (hMV.isIso ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map_isZero h0) _)
  exact h0.of_iso (@asIso _ _ _ _ _ hiso)

end Stacks.DerivedQCoh.AnyModel

end
