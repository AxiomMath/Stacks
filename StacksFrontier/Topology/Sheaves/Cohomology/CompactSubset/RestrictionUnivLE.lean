module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PushforwardInjectives
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of abelian sheaves to a subset, in a coefficient universe of its own

Let `X` be a topological space and `Z ⊆ X` a subset. The inverse image of abelian sheaves along
the inclusion `Z → X` is available in the library only with the coefficient universe pinned to
the universe of the space: `TopCat.Sheaf.pullback` is declared for `X Y : TopCat.{w}` with
`[Category.{w} A]`, so `A = AddCommGrpCat.{t}` forces the spaces into `TopCat.{t}`. At
the shape the derived clause of [Stacks, Tag 0DCU] has — spaces in `TopCat.{u}`, coefficients
`AddCommGrpCat.{max (u + 1) v}` — writing the restriction fails with

```
failed to synthesize instance of type class
  Category.{u, max (u + 2) (v + 1)} AddCommGrpCat
```

This file removes the pinning. Mathlib's site-level `Functor.sheafPullback` has no such
constraint, and `TopCat.Sheaf.pullback A f` is *by definition*
`(Opens.map f).sheafPullback A _ _`, so the general construction specialises to Mathlib's with
no isomorphism to mediate: `restrictionFunctorUnivLE_eq_pullback` is `rfl`. Left exactness at mixed
universes comes from
`Stacks.Topology.preservesFiniteLimits_sheafPullbackOpensMap`.

Sheafification, which both the construction and its left exactness need, is available at mixed
universes with no new work: `Stacks.SheafOfModules.coefficientSheafification` already supplies
`HasSheafify J AddCommGrpCat.{t}` for any site dominated by `t`, and `Opens X` for
`X : TopCat.{s}` is dominated by `t` whenever `UnivLE.{s, t}`. That instance is what makes these
statements non-vacuous; without it the mixed-universe sheaf category is not even known to be
abelian. The pinned restatement
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_opens`, for an object of a
locally quasi-compact Zariski situation at the coefficient universe `max (u + 1) v`, is therefore
not needed here.

## Main definitions

All in the namespace `Stacks.Topology`.

* `restrictionFunctorUnivLE`: the inverse image of abelian sheaves along the inclusion of a
  subset, at a coefficient universe independent of the space. The library's
  `Stacks.Topology.restrictionFunctor`
  (`StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMap`) is this functor
  with the coefficient universe pinned to the space's, and is *definitionally* its `t := s` case.

## Main results

* `hasSheafify_opens`, `isGrothendieckAbelian_sheafOpens`, `enoughInjectives_sheafOpens`,
  `hasExt_sheafOpens`, `hasInjectiveResolutions_sheafOpens`: the mixed-universe category of
  abelian sheaves on a space is Grothendieck abelian, has enough injectives and injective
  resolutions, and has `Ext`-groups in the coefficient universe itself. These are what keep the
  mixed-universe statements here from being vacuous: the `Ext` index in particular is
  *not* `CategoryTheory.HasExt.standard`'s.
* `restrictionFunctorUnivLE_eq_pullback`, `restrictionFunctorUnivLE_eq_restrictionFunctor`: at
  `t := s` the construction is Mathlib's `TopCat.Sheaf.pullback` and the library's
  `Stacks.Topology.restrictionFunctor`, by `rfl` in both cases, so nothing is weakened.
* `preservesFiniteLimits_restrictionFunctorUnivLE`: the restriction is left exact at mixed
  universes.
* `preservesInjectiveObjects_subsetPushforward`: hence the direct image along the inclusion
  preserves injectives at mixed universes.

## Implementation notes

The dominance hypothesis is `UnivLE.{s, t}`, the form
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PushforwardInjectives` already
uses and which holds unconditionally at `t = max (s + 1) v`.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe t s

noncomputable section

/-- **Sheafification of abelian presheaves on the opens of a space, in any dominating coefficient
universe.** This is `Stacks.SheafOfModules.coefficientSheafification` at the site `Opens X`. It is
restated here because the general instance is *not found by instance search* at a coefficient
universe of the form `max s t`: the library also carries
`Stacks.CotangentComplex.hasSheafifyAddCommGrpCat`, of shape `HasSheafify J AddCommGrpCat.{max u
v w}`, and unifying `max s t` with `max s ?w` leaves an unsolvable universe constraint. Writing
the coefficient universe as a variable of its own rather than a `max` makes the search succeed. -/
instance hasSheafify_opens (X : TopCat.{s}) [UnivLE.{s, t}] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{t} :=
  Stacks.SheafOfModules.coefficientSheafification (Opens.grothendieckTopology X)

/-- **Abelian sheaves on a space form a Grothendieck abelian category at the size of their own
homs, in any coefficient universe dominating the space.** `Opens X` is essentially `t`-small, so
this is `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`; the pinned instance
`CategoryTheory.Sheaf.instIsGrothendieckAbelian` cannot be used, because it asks for
`IsGrothendieckAbelian.{s} AddCommGrpCat.{t}`, whose `LocallySmall.{s}` field is false for
`s < t`. -/
theorem isGrothendieckAbelian_sheafOpens (X : TopCat.{s}) [UnivLE.{s, t}] :
    IsGrothendieckAbelian.{t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{t}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{t} _ _

/-- **Abelian sheaves on a space have enough injectives in any coefficient universe dominating
the space.** This is the hypothesis every consumer of the mixed-universe derived apparatus of
[Stacks, Tag 0DCU] carries — see
`Stacks.Topology.LocallyQuasiCompactZariskiSituation`'s
`isZero_zariskiRightDerivedPresheaf_pushforward_opensToSlice` — and, since it is an assumption
and not an instance there, the fact that it is *inhabited* at mixed universes is what keeps those
statements from being vacuous. -/
theorem enoughInjectives_sheafOpens (X : TopCat.{s}) [UnivLE.{s, t}] :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{t}) :=
  (isGrothendieckAbelian_sheafOpens.{t} X).enoughInjectives

/-- **`Ext`-groups of abelian sheaves on a space exist in the coefficient universe itself**, for
any coefficient universe dominating the space. This is the hypothesis
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf` needs in order to take its values in the
coefficients rather than one universe up, and it is *not* supplied by
`CategoryTheory.HasExt.standard`, which gives the index `max (objects) (homs)` — one universe too
big. It comes instead from Grothendieck abelianness at the index of the homs. -/
theorem hasExt_sheafOpens (X : TopCat.{s}) [UnivLE.{s, t}] :
    HasExt.{t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{t}) :=
  have := isGrothendieckAbelian_sheafOpens.{t} X
  inferInstance

/-- **Abelian sheaves on a space have injective resolutions in any coefficient universe dominating
the space.** -/
theorem hasInjectiveResolutions_sheafOpens (X : TopCat.{s}) [UnivLE.{s, t}] :
    HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{t}) :=
  have := enoughInjectives_sheafOpens.{t} X
  inferInstance

variable (X : TopCat.{s}) (Z : Set X)

/-- The preimage map of opens along the inclusion of a subset is a continuous functor of sites.
Mathlib proves this for every map of spaces, but as an instance whose `f` is explicit, so
instance search does not find it at a concrete map; it is therefore supplied by name here. The
library's other copy, in
`StacksFrontier.Topology.Sheaves.ClosedImmersion.PushforwardAlgStruct`, is `private` and so
unavailable to a public declaration in another module. -/
instance isContinuous_opensMap_subsetInclusion :
    (Opens.map (Stacks.subsetInclusion X Z)).IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (Stacks.subsetInclusion X Z))
    (coverPreserving_opens_map (Stacks.subsetInclusion X Z))

/-- **The inverse image of abelian sheaves along the inclusion of a subset, with the coefficient
universe freed from that of the space.** Mathlib's `TopCat.Sheaf.pullback` is this functor with
the coefficient universe pinned; see `restrictionFunctorUnivLE_eq_pullback`. -/
@[ega "0 3.7.1" "special case"]
abbrev restrictionFunctorUnivLE [UnivLE.{s, t}] :
    X.Sheaf AddCommGrpCat.{t} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{t} :=
  (Opens.map (Stacks.subsetInclusion X Z)).sheafPullback AddCommGrpCat.{t}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))

/-- **Nothing is weakened: at `t := s` the restriction above is Mathlib's pullback**, and not
merely isomorphic to it — `TopCat.Sheaf.pullback A f` is by definition
`(Opens.map f).sheafPullback A _ _`. -/
theorem restrictionFunctorUnivLE_eq_pullback :
    restrictionFunctorUnivLE X Z
      = TopCat.Sheaf.pullback AddCommGrpCat.{s} (subsetInclusion X Z) :=
  rfl

/-- The same statement against the library's own pinned name for this functor,
`Stacks.Topology.restrictionFunctor` of
`StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMap`. -/
theorem restrictionFunctorUnivLE_eq_restrictionFunctor :
    restrictionFunctorUnivLE X Z = restrictionFunctor X Z :=
  rfl

/-- **The restriction to a subset is left exact at mixed universes.** This is
`Stacks.Topology.preservesFiniteLimits_sheafPullbackOpensMap` for the inclusion of `Z`. -/
instance preservesFiniteLimits_restrictionFunctorUnivLE [UnivLE.{s, t}] :
    PreservesFiniteLimits ((Opens.map (Stacks.subsetInclusion X Z)).sheafPullback
      AddCommGrpCat.{t} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z))) :=
  have _hX : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{t} :=
    Stacks.SheafOfModules.coefficientSheafification (Opens.grothendieckTopology X)
  have _hZ : HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t} :=
    Stacks.SheafOfModules.coefficientSheafification (Opens.grothendieckTopology (TopCat.of Z))
  preservesFiniteLimits_sheafPullbackOpensMap.{t} (Stacks.subsetInclusion X Z)

/-- **The direct image along the inclusion of a subset preserves injective abelian sheaves at
mixed universes.** This is `Stacks.Topology.preservesInjectiveObjects_sheafPushforwardOpensMap`
for the inclusion of `Z`; it is the input the flasqueness step of [Stacks, Tag 09V3] needs. -/
@[sga "4 V 4.9" "special case"]
theorem preservesInjectiveObjects_subsetPushforward [UnivLE.{s, t}] :
    ((Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous AddCommGrpCat.{t}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z))).PreservesInjectiveObjects :=
  preservesInjectiveObjects_sheafPushforwardOpensMap.{t} (Stacks.subsetInclusion X Z)

end

end Stacks.Topology

end
