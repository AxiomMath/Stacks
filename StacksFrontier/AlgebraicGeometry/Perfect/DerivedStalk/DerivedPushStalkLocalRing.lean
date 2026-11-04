module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingGermBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TrianglesComponents

/-!
# The derived stalk of a pushforward on the image, over the local rings

For a closed immersion of schemes `i : Z ⟶ X` and a point `z` of `Z`, the comparison map
`(i_*M)_{i z} ⟶ M_z` of Tag 00AE is an isomorphism, and
`AlgebraicGeometry.pushStalkFunctorIso` reads it as an isomorphism of functors

`i_* ⋙ (−)_{i z} ≅ (−)_z ⋙ restrictScalars (i^♯_z)`

over the local rings `𝒪_{X,i z}` and `𝒪_{Z,z}`.  Every functor occurring is exact, so the
isomorphism descends to the unbounded derived categories; this file carries it there and reads the
result against the chosen derived pushforward `Ri_*` of Tag 079W, which is `i_*` on derived
categories because `i_*` is exact (Tag 08KS).

The point of doing this over the local rings is the counit compatibility.  The stalk formula of
Tag 0098 is compatible with the adjunction `i^* ⊣ i_*` in the local-ring spelling, by
`Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`, and in that spelling only;
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` reaches the same pair of
functors from the `RingCat`-stalk spelling instead, through
`AlgebraicGeometry.derivedStalkSpellingFunctorIsoOfRingSheaf` at both points and
`AlgebraicGeometry.restrictScalarsStalkMapSquareIso` on the germ square, so nothing in its
construction mentions that adjunction.  The isomorphism built here descends from the map whose
compatibility with the adjunction is known.

## Main definitions

* `AlgebraicGeometry.derivedPushStalkFunctorIso`: **the derived stalk of `Ri_*` on the image, in
  the local-ring spelling, as the derived image of `AlgebraicGeometry.pushStalkFunctorIso`.**

## Main results

* `AlgebraicGeometry.derivedPushStalkFunctorIso_eq`: the definition pinned as an equation of
  isomorphisms.
* `AlgebraicGeometry.derivedPushStalkFunctorIso_hom_app`: its component at an arbitrary object,
  with the three descent comparisons left named.
* `AlgebraicGeometry.derivedPushStalkFunctorIso_hom_app_Q`: **its component at the class of a
  complex, computed** — the degreewise germ map of Tag 00AE, conjugated by the comparisons of the
  derived actions with the localization.  This is what makes the isomorphism usable in a
  computation rather than only in a diagram.

## Implementation notes

*Why `rw` and `simp` cannot act on these composites, and what does.*  `X.Modules` carries two
instance paths — one through `Scheme.Modules`, one through `SheafOfModules` — which are
definitionally but not *reducibly* equal, and `DerivedCategory X.Modules` inherits both.  A
rewrite with `Iso.trans_hom` must synthesise a `Category` instance for the functor category, and
the one it synthesises is not the one the goal's term carries, so the rewrite is rejected as
type-incorrect: `rw [Iso.trans_hom]` reports the pattern `(?α ≪≫ ?β).hom` "not found"
with an application type mismatch between the two `Category` instances underneath.  The cure is
not to rewrite.  `derivedPushStalkFunctorIso_hom_app` decomposes the four-factor composite at an
*arbitrary* object and is `rfl` — the decomposition is definitional, and `isDefEq` at default
transparency crosses the spelling in 0.7 s.  The same crossing inside a component
equation at `DerivedCategory.Q.obj P`, with the three comparisons already substituted, instead
exhausts the 200000-heartbeat `isDefEq` budget, which is why the pinning is taken first and
separately, at the level of isomorphisms and before any component is formed.

*Why `derivedPushStalkFunctorIso_hom_app_Q` ends with the `rfl` tactic.*  After the three
component formulas are rewritten in, the two sides of the goal print identically and are not
closed: what separates them is again the pair of `Category` instances, invisible in the output.
`rw`'s own closing `rfl` runs at reducible transparency and cannot see through it; the `rfl`
*tactic* can.  The `Eq.trans` is there for the same reason — its middle term is written out, so
nothing has to be matched against the goal.

*Why the three exactness instances are re-seated.*  `Scheme.Modules.pushforward i` and
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom` are the same functor —
definitionally, and the equation checks by `rfl` — but `Scheme.Modules.pushforward` is a `def`
whose unfolding is not reducible, and instance search runs at reducible transparency.  The three
instances the library proves for the ringed-space spelling are therefore not found at the
scheme spelling, which is the one `AlgebraicGeometry.pushStalkFunctorIso` is stated at.  The three
`local instance`s below are `inferInstanceAs` of exactly those, re-seated; no new mathematics
enters, and the alternative — restating `pushStalkFunctorIso` at the other spelling — would move
the crossing rather than remove it.

*Which descent helpers.*  `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`
and `…mapDerivedCategoryCompIso` are used, the same pair the rest of this directory is built
from, so the isomorphism composes with
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`'s own factors without a
further spelling change.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.PerfectComplexTriangles

noncomputable section

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- Pushforward of sheaves of modules along a morphism of schemes is additive.  This is
`Stacks.ClosedImmersion.additive_modulePushforward` re-seated at the `Scheme.Modules` spelling;
see the implementation notes. -/
local instance additive_schemeModulesPushforward :
    (Scheme.Modules.pushforward i).Additive :=
  inferInstanceAs (modulePushforward i.toLRSHom.toShHom).Additive

/-- Pushforward of sheaves of modules along a morphism of schemes is left exact.  This is
`Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward` re-seated at the
`Scheme.Modules` spelling. -/
local instance preservesFiniteLimits_schemeModulesPushforward :
    PreservesFiniteLimits (Scheme.Modules.pushforward i) :=
  inferInstanceAs (PreservesFiniteLimits (modulePushforward i.toLRSHom.toShHom))

/-- **The derived stalk of `Ri_*` on the image, over the local rings.**  For a closed immersion
of schemes `i : Z ⟶ X` and `z : Z`, the derived stalk at `i z` over `𝒪_{X,i z}` of `Ri_* K` is the
derived stalk of `K` at `z` over `𝒪_{Z,z}` with scalars restricted along `𝒪_{X,i z} ⟶ 𝒪_{Z,z}`,
as an isomorphism of functors on `DerivedCategory Z.Modules`.

It is the derived image of `AlgebraicGeometry.pushStalkFunctorIso`: `Ri_*` is `i_*` on derived
categories by `Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`, and the
underived isomorphism descends because every functor in it is exact, the two
`mapDerivedCategoryCompIso` splitting the two composites. -/
def derivedPushStalkFunctorIso :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z) ≅
      AlgebraicGeometry.derivedStalkFunctor z ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i) _ ≪≫
    (mapDerivedCategoryCompIso (Scheme.Modules.pushforward i)
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z))).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _
      (AlgebraicGeometry.pushStalkFunctorIso i z
        (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing) ≪≫
    mapDerivedCategoryCompIso (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z)
      (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom)

/-- The definition, pinned as an equation of isomorphisms.  Crossing the
`derivedStalkFunctor` / `mapDerivedCategory` spelling once here, at the level of isomorphisms and
before any component is taken, is cheap; the same crossing inside a four-factor component
equation exhausts the `isDefEq` budget. -/
theorem derivedPushStalkFunctorIso_eq :
    derivedPushStalkFunctorIso i z =
      Functor.isoWhiskerRight
          (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i)
          (derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)) ≪≫
        (mapDerivedCategoryCompIso (Scheme.Modules.pushforward i)
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z))).symm ≪≫
        mapDerivedCategoryIsoOfNatIso
            (Scheme.Modules.pushforward i ⋙
              Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z))
            (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
              ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom)
            (pushStalkFunctorIso i z
              (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing) ≪≫
        mapDerivedCategoryCompIso (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z)
          (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom) :=
  rfl


/-- Rung 1: the component of `derivedPushStalkFunctorIso`, with the three descent comparisons
left named. -/
theorem derivedPushStalkFunctorIso_hom_app (K : DerivedCategory Z.Modules) :
    (derivedPushStalkFunctorIso i z).hom.app K =
      (derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).hom.app
            K) ≫
        (mapDerivedCategoryCompIso (Scheme.Modules.pushforward i)
            (Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z))).inv.app K ≫
        (mapDerivedCategoryIsoOfNatIso
            (Scheme.Modules.pushforward i ⋙
              Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z))
            (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
              ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom)
            (pushStalkFunctorIso i z
              (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing)).hom.app K ≫
        (mapDerivedCategoryCompIso (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z)
          (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom)).hom.app K :=
  rfl


/-- Rung 2: the same at the class of a complex, with the three descent comparisons evaluated. -/
theorem derivedPushStalkFunctorIso_hom_app_Q (P : CochainComplex Z.Modules ℤ) :
    (derivedPushStalkFunctorIso i z).hom.app (DerivedCategory.Q.obj P) =
      (derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes i).hom.app
            (DerivedCategory.Q.obj P)) ≫
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (i.base z)).mapDerivedCategory.map
              ((Scheme.Modules.pushforward i).mapDerivedCategoryFactors.hom.app P) ≫
            (Stacks.ModuleSkyscraper.modulesStalkFunctor X
                (i.base z)).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            (Scheme.Modules.pushforward i ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor X
                (i.base z)).mapDerivedCategoryFactors.inv.app P) ≫
          ((Scheme.Modules.pushforward i ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor X
                (i.base z)).mapDerivedCategoryFactors.hom.app P ≫
              DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex
                  (pushStalkFunctorIso i z
                    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing)
                  (ComplexShape.up ℤ)).hom.app P) ≫
              (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
                ModuleCat.restrictScalars.{u, u, u}
                  (i.stalkMap z).hom).mapDerivedCategoryFactors.inv.app P) ≫
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
                  ModuleCat.restrictScalars.{u, u, u}
                    (i.stalkMap z).hom).mapDerivedCategoryFactors.hom.app P ≫
              (ModuleCat.restrictScalars.{u, u, u}
                  (i.stalkMap z).hom).mapDerivedCategoryFactors.inv.app
                (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P) ≫
              (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory.map
                ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
                  z).mapDerivedCategoryFactors.inv.app P)) :=
  Eq.trans (derivedPushStalkFunctorIso_hom_app i z (DerivedCategory.Q.obj P))
    (by rw [mapDerivedCategoryCompIso_inv_app, mapDerivedCategoryIsoOfNatIso_hom_app,
      mapDerivedCategoryCompIso_hom_app]
        rfl)

end AlgebraicGeometry

end

end
