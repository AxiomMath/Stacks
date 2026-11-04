module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionStalkOnImage
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkLength
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The two spellings of the derived stalk, compared as functors

The derived stalk at a point `x` of a scheme `X` is taken in two spellings:

* `AlgebraicGeometry.derivedStalkFunctor x`, over the local ring `𝒪_{X,x}`, which is
  `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` on derived categories.  This is the spelling
  `AlgebraicGeometry.derivedPullbackStalkIso` and everything about Tor independence — in
  particular `RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent` —
  are stated in.
* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x`, over the
  `RingCat`-valued stalk of the sheaf of rings.  This is the spelling of the stalkwise criterion
  for invertibility and of the derived stalk of a pushforward along a closed immersion
  (`Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes`).

`AlgebraicGeometry.restrictScalarsStalkFunctorIso` compares the two *underived* stalk functors.
This file carries that comparison to the derived categories, as an isomorphism of functors.

## Main definitions

* `AlgebraicGeometry.modulesRingCatStalkFunctor`: the `RingCat`-stalk functor with its source
  written `X.Modules` and its target written at the stalk ring that
  `AlgebraicGeometry.ringCatStalkRingEquiv` is stated for.
* `AlgebraicGeometry.restrictScalarsStalkMapSquareIso`: the germ square of a morphism of schemes,
  as an isomorphism of composites of restriction-of-scalars functors.

## Main results

* `AlgebraicGeometry.derivedStalkSpellingFunctorIso`: the derived stalk over the local ring
  `𝒪_{X,x}` is the derived stalk over the `RingCat`-valued stalk of the sheaf of rings, followed
  by restriction of scalars along `AlgebraicGeometry.ringCatStalkRingEquiv`, **as an isomorphism
  of functors** out of `DerivedCategory X.Modules`.
* `AlgebraicGeometry.derivedStalkSpellingFunctorIsoOfRingSheaf`: the same at the
  `structureSheafRing` spelling of the sheaf of rings, which is the one the
  closed-immersion computation of a derived pushforward stalk is stated at.
* `AlgebraicGeometry.stalkRingMap_comp_ringCatStalkRingEquiv_symm`: the `RingCat`-valued and the
  `CommRingCat`-valued germ maps of a morphism of schemes agree through
  `AlgebraicGeometry.ringCatStalkRingEquiv`.
* `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`: **the derived stalk of
  `Ri_*` on the image of a closed immersion, in the local-ring spelling** — the first consumer of
  the bridge, and the form in which that computation enters a diagram alongside
  `AlgebraicGeometry.derivedPullbackStalkIso`.

## What this enables

`AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff` compares the two derived stalks of a single
*morphism*.  That is enough to conclude that a map is invertible, and not enough to *state* a
diagram: Stacks 0E23 needs the stalk of the derived pullback
(`AlgebraicGeometry.derivedPullbackStalkIso`, local-ring spelling), the Tor-independent base
change comparison (Stacks 0661, local-ring spelling) and the derived stalk of `Ri_*`
(`Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes`, `RingCat` spelling)
composed into one chain of isomorphisms of functors.  With
`derivedStalkSpellingFunctorIsoOfRingSheaf` the third can be whiskered into the spelling of the
first two, so the chain is a single diagram of functors on `DerivedCategory X.Modules`.
`derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` carries that out for the third: it is
`Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes` with every category and every
stalk ring in it rewritten to the local-ring spelling, so it composes with the first two directly.

## Implementation notes

*The clash.*  `X.Modules` is a `def` unfolding to `SheafOfModules X.ringCatSheaf`, and
`AlgebraicGeometry.Scheme.Modules.Hom` is a `def` unfolding to `SheafOfModules.Hom`, so the two
categories carry two instance paths — `Scheme.Modules.instCategory` against
`SheafOfModules.instCategory`, and `Scheme.Modules.instAbelian.toPreadditive` against
`SheafOfModules.instPreadditive`.  Each pair is definitionally equal at default transparency and
neither is equal to the other at *reducible* transparency, which is the transparency instance
synthesis runs at.  The same is true one category along: the target of
`AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x` is `ModuleCat` of the stalk of
`X.ringCatSheaf.obj`, while the source of restriction of scalars along
`AlgebraicGeometry.ringCatStalkRingEquiv` is `ModuleCat` of the stalk of
`X.presheaf ⋙ forget₂ CommRingCat RingCat`; `sheafCompose` stands between them, so the two
`Ring` instances on the stalk ring are two terms as well.

The consequence is not that some instance is missing but that it is not *found*: with both
spellings present in one composite, `CategoryTheory.Functor.instAdditiveComp` reports a hard
synthesis failure for `Additive` of the composite — and likewise `PreservesFiniteLimits` and
`PreservesFiniteColimits` — even though each factor's instance is found on its own.  That is what
blocks `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`, whose
hypotheses are exactly those three on each of its two functors.

*The resolution.*  `modulesRingCatStalkFunctor` is the `RingCat`-stalk functor restated at both
of the spellings the local-ring side uses — source `X.Modules`, target the stalk of
`X.presheaf ⋙ forget₂ CommRingCat RingCat` — with its three exactness instances re-seated there.
It is the same functor, accepted by definitional unfolding, and after it every composite in sight
is presented in one spelling, so all three instances fire and the derived comparison is the
underived one carried along `mapDerivedCategoryIsoOfNatIso` with
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` splitting the composite.
This is the idiom of `Stacks.TildeStalk.specStalkFunctor`, where the stalk functor had to be
restated at `(Spec R).Modules` for the same reason.

The statements then need no restated vocabulary:
`(modulesRingCatStalkFunctor x).mapDerivedCategory` *is*
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x`, so the results below are
stated with the library's own derived stalk functor and the restated one appears only in their
proofs.

*Routes not taken.*  Making the local-ring spelling reducible to the other is not available:
`Scheme.Modules.instCategory` is already `instance_reducible`, and what would have to become
reducible is `AlgebraicGeometry.Scheme.Modules.Hom` together with `sheafCompose` — definitions on
`main` and in Mathlib, whose reducibility is not this file's to change, and changing it would
alter instance search for every consumer of `X.Modules`.  An additive equivalence between the two
categories would be a second way to say that they are one category, and would still leave the
stalk-ring half of the clash untouched.  Restating the `RingCat`-spelling *results* in the
local-ring spelling would duplicate them; restating the one *functor* they are built from, which
is what is done here, does not.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (x : X)

/-! ### The `RingCat`-stalk functor, restated -/

/-- **The `RingCat`-stalk functor at the local-ring side's spelling.**  This is
`AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x` and nothing else, with its
source written `X.Modules` and its target written at the stalk of
`X.presheaf ⋙ forget₂ CommRingCat RingCat` — the two spellings that
`Stacks.ModuleSkyscraper.modulesStalkFunctor` and `AlgebraicGeometry.ringCatStalkRingEquiv`
present. -/
def modulesRingCatStalkFunctor :
    X.Modules ⥤ ModuleCat.{u} (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x

/-- `modulesRingCatStalkFunctor` is additive, being the stalk functor and nothing else.
Re-seating the instance at this spelling is what lets `Additive` be found for the composite with
restriction of scalars. -/
instance modulesRingCatStalkFunctor_additive : (modulesRingCatStalkFunctor x).Additive :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor_additive X.ringCatSheaf x

/-- `modulesRingCatStalkFunctor` preserves finite limits, being the stalk functor and nothing
else. -/
instance modulesRingCatStalkFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (modulesRingCatStalkFunctor x) :=
  inferInstanceAs
    (PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x))

/-- `modulesRingCatStalkFunctor` preserves finite colimits, being the stalk functor and nothing
else. -/
instance modulesRingCatStalkFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (modulesRingCatStalkFunctor x) :=
  inferInstanceAs
    (PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x))

/-- `AlgebraicGeometry.restrictScalarsStalkFunctorIso` read at the restated spelling: both of its
sides are functors out of `X.Modules` here, so the exactness instances of both are found. -/
def modulesRingCatStalkFunctorIso :
    modulesRingCatStalkFunctor x ⋙
        ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x :=
  AlgebraicGeometry.restrictScalarsStalkFunctorIso x

/-! ### The derived comparison -/

open Stacks.Cohomology.PerfectComplexTriangles in
/-- **The two derived stalk functors differ by restriction of scalars.**  The derived stalk at `x`
over the local ring `𝒪_{X,x}` is the derived stalk over the `RingCat`-valued stalk of the sheaf of
rings, followed by restriction of scalars along `AlgebraicGeometry.ringCatStalkRingEquiv`.

This is `modulesRingCatStalkFunctorIso` carried along `mapDerivedCategoryIsoOfNatIso`, with
`mapDerivedCategoryCompIso` splitting the composite.  Both are available because every functor
occurring is presented at one spelling; see the implementation notes. -/
def derivedStalkSpellingFunctorIso :
    AlgebraicGeometry.derivedStalkFunctor x ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategory :=
  (mapDerivedCategoryIsoOfNatIso _ _ (modulesRingCatStalkFunctorIso x)).symm ≪≫
    mapDerivedCategoryCompIso (modulesRingCatStalkFunctor x)
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom)

open Stacks.Cohomology.PerfectComplexTriangles in
/-- `derivedStalkSpellingFunctorIso` at the `structureSheafRing` spelling of
the sheaf of rings of `X`.  That is the spelling
`Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes` is stated at, so this is the
form in which the derived stalk of a pushforward along a closed immersion can be whiskered into a
diagram of functors on `DerivedCategory X.Modules`. -/
def derivedStalkSpellingFunctorIsoOfRingSheaf :
    AlgebraicGeometry.derivedStalkFunctor x ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
          (structureSheafRing X.toRingedSpace) x ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategory :=
  (mapDerivedCategoryIsoOfNatIso _ _ (modulesRingCatStalkFunctorIso x)).symm ≪≫
    mapDerivedCategoryCompIso (modulesRingCatStalkFunctor x)
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom)

/-! ### The germ square of the two spellings -/

/-- **The germ maps of a morphism of schemes agree across the two spellings of the stalk ring.**
Restricting scalars along `AlgebraicGeometry.ringCatStalkRingEquiv` at `x` and then applying the
`RingCat`-valued germ map of `Stacks.RingedSpace.stalkRingMap` is applying the `CommRingCat`-valued
germ map of the underlying morphism of presheafed spaces and then restricting scalars at `f x`.

This is `Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso` with both comparison isomorphisms
moved to the other side; `AlgebraicGeometry.ringCatStalkRingEquiv` and
`Stacks.RingedSpace.ringStalkCommIso` are the same comparison, one as a ring equivalence and one as
an isomorphism of `RingCat`. -/
theorem stalkRingMap_comp_ringCatStalkRingEquiv_symm {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom.comp
        (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom =
      (ringCatStalkRingEquiv z).symm.toRingHom.comp
        (i.toLRSHom.toShHom.hom.stalkMap z).hom := by
  have key : ((Stacks.RingedSpace.ringStalkCommIso Z.toRingedSpace z).hom.hom).comp
        (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom =
      ((i.toLRSHom.toShHom.hom.stalkMap z).hom).comp
        (Stacks.RingedSpace.ringStalkCommIso X.toRingedSpace
          (i.toLRSHom.toShHom.hom.base z)).hom.hom :=
    congrArg RingCat.Hom.hom
      (Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso i.toLRSHom.toShHom z)
  refine RingHom.ext fun a => ?_
  have h0 : (ringCatStalkRingEquiv z)
        ((Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom
          ((ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm a)) =
      (i.toLRSHom.toShHom.hom.stalkMap z).hom
        ((ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z))
          ((ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm a)) :=
    DFunLike.congr_fun key _
  rw [RingEquiv.apply_symm_apply] at h0
  exact (ringCatStalkRingEquiv z).eq_symm_apply.2 h0

/-- **The germ square, as an isomorphism of restriction-of-scalars functors.**  Restricting
scalars along the `RingCat`-valued germ map and then along
`AlgebraicGeometry.ringCatStalkRingEquiv` at `f z` is restricting scalars along
`ringCatStalkRingEquiv` at `z` and then along the `CommRingCat`-valued germ map.

Both composites are restriction of scalars along one ring homomorphism by
`ModuleCat.restrictScalarsComp'`, and the two homomorphisms are equal by
`stalkRingMap_comp_ringCatStalkRingEquiv_symm`. -/
def restrictScalarsStalkMapSquareIso {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    ModuleCat.restrictScalars.{u, u, u}
        (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom ⋙
      ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom ≅
    ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv z).symm.toRingHom ⋙
      ModuleCat.restrictScalars.{u, u, u} (i.toLRSHom.toShHom.hom.stalkMap z).hom :=
  (ModuleCat.restrictScalarsComp'.{u}
      (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom
      (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom _ rfl).symm ≪≫
    ModuleCat.restrictScalarsComp'.{u} (i.toLRSHom.toShHom.hom.stalkMap z).hom
      (ringCatStalkRingEquiv z).symm.toRingHom _
      (stalkRingMap_comp_ringCatStalkRingEquiv_symm i z)

/-! ### Exactness instances re-seated at the `structureSheafRing` spelling of the stalk ring

The source of restriction of scalars along `AlgebraicGeometry.ringCatStalkRingEquiv` is
`ModuleCat` of the stalk of `X.presheaf ⋙ forget₂ CommRingCat RingCat`, while the target of the
`RingCat`-valued germ map is `ModuleCat` of the stalk of the `structureSheafRing` of `X` — two
spellings of one ring.  In the composite the second wins, and at that spelling none of the
three exactness classes is found even though each is found at the first spelling; these three
re-seat them, by `inferInstanceAs` and nothing else.  The two for the germ map re-seat the `local`
instances of `ClosedImmersionStalkOnImage.lean`, which do not reach here. -/

/-- `Additive` for restriction of scalars along `ringCatStalkRingEquiv`, at the
`structureSheafRing` spelling of the stalk ring. -/
local instance additive_restrictScalarsRingSheafStalk (W : Scheme.{u}) (w : W) :
    (ModuleCat.restrictScalars.{u, u, u}
      (S := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing W.toRingedSpace).obj w))
      (ringCatStalkRingEquiv w).symm.toRingHom).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars.{u, u, u}
    (ringCatStalkRingEquiv w).symm.toRingHom).Additive)

/-- `PreservesFiniteLimits` for restriction of scalars along `ringCatStalkRingEquiv`, at the
`structureSheafRing` spelling of the stalk ring. -/
local instance preservesFiniteLimits_restrictScalarsRingSheafStalk (W : Scheme.{u}) (w : W) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u}
      (S := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing W.toRingedSpace).obj w))
      (ringCatStalkRingEquiv w).symm.toRingHom) :=
  inferInstanceAs (PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u}
    (ringCatStalkRingEquiv w).symm.toRingHom))

/-- `PreservesFiniteColimits` for restriction of scalars along `ringCatStalkRingEquiv`, at the
`structureSheafRing` spelling of the stalk ring. -/
local instance preservesFiniteColimits_restrictScalarsRingSheafStalk (W : Scheme.{u}) (w : W) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u}
      (S := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing W.toRingedSpace).obj w))
      (ringCatStalkRingEquiv w).symm.toRingHom) :=
  inferInstanceAs (PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u}
    (ringCatStalkRingEquiv w).symm.toRingHom))

/-- Restriction of scalars along the `RingCat`-valued germ map preserves finite limits. -/
local instance preservesFiniteLimits_restrictScalars_stalkRingMap'
    {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (j : Z ⟶ X) (y : Z.carrier) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap j y).hom) :=
  Stacks.preservesFiniteLimits_restrictScalars (Stacks.RingedSpace.stalkRingMap j y)

/-- Restriction of scalars along the `RingCat`-valued germ map preserves finite colimits. -/
local instance preservesFiniteColimits_restrictScalars_stalkRingMap'
    {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (j : Z ⟶ X) (y : Z.carrier) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap j y).hom) :=
  Stacks.preservesFiniteColimits_restrictScalars (Stacks.RingedSpace.stalkRingMap j y)

/-! ### The derived stalk of a derived pushforward, in the local-ring spelling -/

open Stacks.Cohomology.PerfectComplexTriangles in
/-- **The derived stalk of `Ri_*` on the image, in the local-ring spelling.**  For a closed
immersion of schemes `i : Z ⟶ X` and `z : Z`, the derived stalk at `i z` over the local ring
`𝒪_{X,i z}` of `Ri_* K` is the derived stalk at `z` over `𝒪_{Z,z}` with scalars restricted along
`𝒪_{X,i z} ⟶ 𝒪_{Z,z}` — **as an isomorphism of functors** on `DerivedCategory Z.Modules`.

This is `Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes`, which is stated in the
`RingCat`-stalk spelling, carried across `derivedStalkSpellingFunctorIsoOfRingSheaf` at both points
and then along `restrictScalarsStalkMapSquareIso`.  It is the form in which the computation mates
with `AlgebraicGeometry.derivedPullbackStalkIso` and with Stacks 0661,
`RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent`, which live over
the local rings; with it the chain of isomorphisms Stacks 0E23 needs is a single diagram of
functors. -/
def derivedStalkDerivedPushforwardIsoOfSchemesLocalRing {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (z : Z) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z) ≅
      AlgebraicGeometry.derivedStalkFunctor z ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (derivedStalkSpellingFunctorIsoOfRingSheaf (i.toLRSHom.toShHom.hom.base z)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes i z) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((mapDerivedCategoryCompIso
            (ModuleCat.restrictScalars.{u, u, u}
              (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom)
            (ModuleCat.restrictScalars.{u, u, u}
              (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom)).symm ≪≫
        mapDerivedCategoryIsoOfNatIso _ _ (restrictScalarsStalkMapSquareIso i z) ≪≫
        mapDerivedCategoryCompIso
          (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv z).symm.toRingHom)
          (ModuleCat.restrictScalars.{u, u, u} (i.toLRSHom.toShHom.hom.stalkMap z).hom)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedStalkSpellingFunctorIsoOfRingSheaf z).symm _

end AlgebraicGeometry

end

end
