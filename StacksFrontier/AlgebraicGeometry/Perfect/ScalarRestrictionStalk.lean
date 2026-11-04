module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpenExactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalars

/-!
# The stalk of restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`

Let `f : X ⟶ S` be a morphism of schemes and let `y` be a point of `X`. An `𝒪_X`-module read as
an `f^{-1}𝒪_S`-module by `AlgebraicGeometry.Scheme.Hom.scalarRestriction` has the same underlying
sheaf of abelian groups, so its stalk at `y` is the stalk of the original module, read over the
stalk ring `(f^{-1}𝒪_S)_y` along the stalk map of `f^{-1}𝒪_S ⟶ 𝒪_X`. This file records that
comparison and its transport to the derived categories.

This is the companion step for the *coefficients* that the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening` record as still owed, in the
form in which it is owed: the stalk of
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` read over the stalk of `f^{-1}𝒪_S`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkFunctorScalarRestrictionIso`: the comparison on modules.
* `AlgebraicGeometry.Scheme.Hom.derivedStalkFunctorScalarRestrictionIso`: the same comparison on
  derived categories, for arbitrary models of the three derived categories involved.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionCompDerivedStalkIso`: the splitting that
  turns the previous one into a statement about
  `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction`.

## Implementation notes

The module-level statement is
`AlgebraicGeometry.SheafOfModules.stalkFunctorRestrictScalarsFunctorIso` at the structural map
`AlgebraicGeometry.Scheme.Hom.inverseImageRingToStructure` of `f`; nothing has to be proved
there, and the content of this file is that the instantiation typechecks — the source of that
structural map is the structure sheaf of `AlgebraicGeometry.RingedSpace.inverseImage`, whose
carrier *is* the carrier of `X`, so a point of `X` is a point of the inverse-image ringed space on
the nose. The six instances recording exactness of the two stalk functors are the same
observation: `AlgebraicGeometry.RingedSpace.additive_stalkFunctor` and its companions are stated
for a point of `W.carrier`, which at the inverse-image ringed space is the carrier of `X` only
after a `def` is unfolded, so they are applied as terms rather than found by instance search.

The derived statement is the module-level one transported by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`. Both functors it compares are
exact — restriction of scalars along a map of sheaves of rings is
`AlgebraicGeometry.Scheme.Hom.exactFunctor_scalarRestriction`, the stalk functor of a ringed
space is `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor` and its colimit
companion, and restriction of scalars along a ring homomorphism is
`StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits` and its companion — so no
resolution intervenes, and only `D(𝒪_X)`, `D(f^{-1}𝒪_S)` and the two derived categories of stalk
modules are involved, each at a model the consumer chooses.

The exactness of the right-hand composite is *transported across the module-level isomorphism*
rather than assembled from its two factors. The reason is the implicit `Ring` arguments of
`ModuleCat.restrictScalars`: there are two routes to a `Ring` structure on the `RingCat`-valued
stalk of the structure sheaf — `RingCat`'s own and `CommRing.toRing` of
`AlgebraicGeometry.RingedSpace.commRing_stalk_structureSheafOfRings` — and with this file's
import closure instance search does not reproduce the one the isomorphism's own type carries.
Transporting along the isomorphism pins it, with no `set_option` and nothing weakened.

The coefficient ring of the right-hand side is `(f^{-1}𝒪_S)_y`, not `𝒪_{S, f y}`. Rewriting it as
the latter is a separate step: it is
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap`, which identifies
`AlgebraicGeometry.Scheme.Hom.stalkMap` with the stalk of the structural map through the
comparison `(f^{-1}𝒪_S)_y ≅ 𝒪_{S, f y}`, but that equation lives in `CommRingCat` while
`AlgebraicGeometry.SheafOfModules.stalkFunctor` reads the stalk in `RingCat`, so the two are
separated by `SemilinearStalk.commStalkRingEquiv`. That crossing is not made here.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' e u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (y : X)

/-- **The stalk of a restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`.** The stalk at `y` of an
`𝒪_X`-module read as an `f^{-1}𝒪_S`-module is the stalk of the module, read over `(f^{-1}𝒪_S)_y`
along the induced map of stalk rings. -/
public def stalkFunctorScalarRestrictionIso :
    scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y ≅
      SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
        ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom :=
  SheafOfModules.stalkFunctorRestrictScalarsFunctorIso (inverseImageRingToStructure f) y

/-! ### Exactness of the two stalk functors, seated at the spellings used above

`AlgebraicGeometry.RingedSpace.additive_stalkFunctor` and its finite-limit and finite-colimit
companions are stated for a ringed space `W` and a point of `W.carrier`. For
`W = AlgebraicGeometry.RingedSpace.inverseImage S.toRingedSpace f.base` that carrier *is* the
carrier of `X`, but only after unfolding a plain `def`, which instance search does not do. The
three instances below are the same instances applied as terms, where the unfolding is available,
and they are what lets `CategoryTheory.Functor.mapDerivedCategory` be formed at this spelling. -/

/-- `AlgebraicGeometry.RingedSpace.additive_stalkFunctor` at the inverse-image ringed space, with
the point written as a point of `X`. -/
public instance additive_stalkFunctor_inverseImage :
    (SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) y).Additive :=
  RingedSpace.additive_stalkFunctor (RingedSpace.inverseImage S.toRingedSpace f.base) y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor` at the inverse-image
ringed space, with the point written as a point of `X`. -/
public instance preservesFiniteLimits_stalkFunctor_inverseImage :
    PreservesFiniteLimits (SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  RingedSpace.preservesFiniteLimits_stalkFunctor
    (RingedSpace.inverseImage S.toRingedSpace f.base) y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_stalkFunctor` at the inverse-image
ringed space, with the point written as a point of `X`. -/
public instance preservesFiniteColimits_stalkFunctor_inverseImage :
    PreservesFiniteColimits (SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  RingedSpace.preservesFiniteColimits_stalkFunctor
    (RingedSpace.inverseImage S.toRingedSpace f.base) y

/-- `AlgebraicGeometry.RingedSpace.additive_stalkFunctor` at the ringed space of `X`, with the
point written as a point of `X`. -/
public instance additive_stalkFunctor_scheme :
    (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y).Additive :=
  RingedSpace.additive_stalkFunctor X.toRingedSpace y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor` at the ringed space of
`X`, with the point written as a point of `X`. -/
public instance preservesFiniteLimits_stalkFunctor_scheme :
    PreservesFiniteLimits
      (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y) :=
  RingedSpace.preservesFiniteLimits_stalkFunctor X.toRingedSpace y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_stalkFunctor` at the ringed space of
`X`, with the point written as a point of `X`. -/
public instance preservesFiniteColimits_stalkFunctor_scheme :
    PreservesFiniteColimits
      (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y) :=
  RingedSpace.preservesFiniteColimits_stalkFunctor X.toRingedSpace y

/-! The three exactness facts for `ModuleCat.restrictScalars` at the stalk map are seated as
*terms*, not left to instance search. Mathlib's instances for them are found when this file's
imports are cut down to the stalk API alone and are not found with
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons` in the import
closure; nothing is weakened by naming them, and `set_option` is not an option. -/

/-- Restriction of scalars along the stalk map of `f^{-1}𝒪_S ⟶ 𝒪_X` is additive: on underlying
abelian groups it does not move the morphism. -/
public theorem additive_restrictScalars_ringStalkMap :
    (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap
        (inverseImageRingToStructure f).hom y).hom).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along the stalk map of `f^{-1}𝒪_S ⟶ 𝒪_X` preserves finite limits. -/
public theorem preservesFiniteLimits_restrictScalars_ringStalkMap :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits
    (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom

/-- Restriction of scalars along the stalk map of `f^{-1}𝒪_S ⟶ 𝒪_X` preserves finite colimits. -/
public theorem preservesFiniteColimits_restrictScalars_ringStalkMap :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u}
      (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits
    (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom

/-! The exactness of the two composites. The left-hand one is the composite of two functors
whose own instances are available, and the right-hand one is transported across
`AlgebraicGeometry.Scheme.Hom.stalkFunctorScalarRestrictionIso`: being isomorphic to an exact
additive functor, it is one. Transporting is what pins the implicit `Ring` arguments of
`ModuleCat.restrictScalars` to the ones the isomorphism itself carries, which is why instance
search cannot be left to find them. -/

/-- The composite computing the left-hand side of the comparison is additive. -/
public instance additive_scalarRestriction_comp_stalkFunctor :
    (scalarRestriction f ⋙
      SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) y).Additive :=
  inferInstance

/-- The composite computing the left-hand side of the comparison preserves finite limits. -/
public instance preservesFiniteLimits_scalarRestriction_comp_stalkFunctor :
    PreservesFiniteLimits
      (scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  CategoryTheory.Limits.comp_preservesFiniteLimits _ _

/-- The composite computing the left-hand side of the comparison preserves finite colimits. -/
public instance preservesFiniteColimits_scalarRestriction_comp_stalkFunctor :
    PreservesFiniteColimits
      (scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) y) :=
  CategoryTheory.Limits.comp_preservesFiniteColimits _ _

/-- The composite computing the right-hand side of the comparison is additive, because it is
isomorphic to the left-hand one. -/
public instance additive_stalkFunctor_comp_restrictScalars :
    (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
      ModuleCat.restrictScalars.{u}
        (SemilinearStalk.ringStalkMap
          (inverseImageRingToStructure f).hom y).hom).Additive :=
  Functor.additive_of_iso (stalkFunctorScalarRestrictionIso f y)

/-- The composite computing the right-hand side of the comparison preserves finite limits,
because it is isomorphic to the left-hand one. -/
public instance preservesFiniteLimits_stalkFunctor_comp_restrictScalars :
    PreservesFiniteLimits
      (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
        ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom) :=
  CategoryTheory.Limits.preservesFiniteLimits_of_natIso (stalkFunctorScalarRestrictionIso f y)

/-- The composite computing the right-hand side of the comparison preserves finite colimits,
because it is isomorphic to the left-hand one. -/
public instance preservesFiniteColimits_stalkFunctor_comp_restrictScalars :
    PreservesFiniteColimits
      (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
        ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom y).hom) :=
  CategoryTheory.Limits.preservesFiniteColimits_of_natIso (stalkFunctorScalarRestrictionIso f y)

section Derived

variable [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [HasDerivedCategory.{e} (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
    (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))]

/-- **The derived stalk of restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`.** Taking the stalk at
`y` after reading an `𝒪_X`-module over `f^{-1}𝒪_S` is taking the stalk at `y` and reading it over
`(f^{-1}𝒪_S)_y` along the induced map of stalk rings, in the derived categories.

This is `AlgebraicGeometry.Scheme.Hom.stalkFunctorScalarRestrictionIso` transported by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`; both functors it compares are
exact, so no resolution intervenes and only two derived-category models are involved.

`AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionCompDerivedStalkIso` splits the left-hand
side into `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` followed by the derived stalk,
which is the form in which a consumer of relative perfectness meets it. -/
public def derivedStalkFunctorScalarRestrictionIso :
    (scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory ≅
      (SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) y ⋙
        ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap
            (inverseImageRingToStructure f).hom y).hom).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
    (stalkFunctorScalarRestrictionIso f y)

/-- **The derived stalk of a derived restriction of scalars is computed in two steps.** The
descent to derived categories of `scalarRestriction f` followed by the stalk functor is
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` followed by the derived stalk functor.

This is `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and it is what turns
`AlgebraicGeometry.Scheme.Hom.derivedStalkFunctorScalarRestrictionIso` into a statement about
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction`. -/
public def derivedScalarRestrictionCompDerivedStalkIso :
    (scalarRestriction f ⋙
        SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory ≅
      derivedScalarRestriction f ⋙
        (SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (scalarRestriction f)
    (SheafOfModules.stalkFunctor
      (structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base)) y)

end Derived

end AlgebraicGeometry.Scheme.Hom

end
