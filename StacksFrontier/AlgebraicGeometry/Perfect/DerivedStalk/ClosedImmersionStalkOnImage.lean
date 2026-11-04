module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.StalkPushforwardModule
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The derived stalk of `Ri_*` on the image of a closed immersion

Let `i : (Z, 𝒪_Z) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces whose underlying map is inducing,
and let `z : Z`. Pushforward of sheaves of modules along `i` is exact when it preserves finite
colimits, so `Ri_*` is the functor `i_*` induces on derived categories, and the stalk of `i_* M`
at `i(z)` is the stalk of `M` at `z` with scalars restricted along the germ map
`𝒪_{X,i(z)} ⟶ 𝒪_{Z,z}`. This file carries that computation to the unbounded derived category:

`(Ri_* K)_{i(z)} ≅ (𝒪_{X,i(z)} ⟶ 𝒪_{Z,z})^* (K_z)`,

as an isomorphism of functors. Together with the vanishing of `(Ri_* K)_x` off the image
(`Stacks.ClosedImmersion.isZero_derivedStalk_mapDerivedCategory_of_notMemRange`) this computes
every derived stalk of `Ri_* K` for a closed embedding `i`.

## Main definitions

* `Stacks.ClosedImmersion.derivedStalkPushforwardModuleFunctorIso`: the computation for the
  functor `i_*` induces on derived categories.
* `Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIso`: the same for `Ri_*`.
* `Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes`: the same for a closed
  immersion of schemes, where the exactness and inducing hypotheses are discharged.

## Implementation notes

The underived computation `Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso` is an
isomorphism of functors `i_* ⋙ (-)_{i(z)} ≅ (-)_z ⋙ restrictScalars`, and all four functors in
it are exact: pushforward by the hypothesis, the two stalk functors by
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` and its colimit
counterpart, and restriction of scalars by `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`.
So the derived statement is the underived one carried along
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`, with
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` splitting each of the two
composites. `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor` is by definition
`mapDerivedCategory` of the stalk functor, so the two spellings of each side are the same term.

`PreservesFiniteColimits (modulePushforward i)` is an instance binder rather than a hypothesis,
for the reason given in `ClosedImmersionPushforward.lean`: it is needed to elaborate
`(modulePushforward i).mapDerivedCategory`, which occurs in the statement.

Nothing here is tagged. Stacks 0E23's single clause is the assertion that a base change
comparison map is an isomorphism; this is one of its inputs, and the statement itself is
Stacks 00AE read on the image rather than off it, carried to the derived category, which is a
clause of neither 00AE nor 08KS.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.ClosedImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along the germ map preserves finite limits.  Mathlib's instance is
stated for commutative rings, and the stalk of `structureSheafRing X` is `RingCat`-valued. -/
local instance preservesFiniteLimits_restrictScalars_stalkRingMap
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (z : Z.carrier) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap i z).hom) :=
  Stacks.preservesFiniteLimits_restrictScalars (Stacks.RingedSpace.stalkRingMap i z)

/-- Restriction of scalars along the germ map preserves finite colimits. -/
local instance preservesFiniteColimits_restrictScalars_stalkRingMap
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (z : Z.carrier) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u, u, u}
      (Stacks.RingedSpace.stalkRingMap i z).hom) :=
  Stacks.preservesFiniteColimits_restrictScalars (Stacks.RingedSpace.stalkRingMap i z)

section RingedSpace

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (z : Z.carrier)

/-- **The derived stalk of `i_* K` on the image.** For a morphism of ringed spaces with inducing
underlying map and exact pushforward, the derived stalk at `i(z)` of the functor `i_*` induces on
derived categories is the derived stalk at `z` with scalars restricted along the germ map
`𝒪_{X,i(z)} ⟶ 𝒪_{Z,z}`. -/
def derivedStalkPushforwardModuleFunctorIso
    [PreservesFiniteColimits (modulePushforward i)]
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base)) :
    (modulePushforward i).mapDerivedCategory ⋙
        AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) (i.hom.base z) ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing Z) z ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategory :=
  (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
        (modulePushforward i)
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
          (i.hom.base z))).symm ≪≫
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso _ _
        (stalkPushforwardModuleFunctorIso i z hi) ≪≫
      Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z)
        (ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom)

/-- **The derived stalk of `Ri_* K` on the image.** `Ri_*` is `i_*` on derived categories by
`derivedPushforwardIsoMapDerivedCategory`, so this is
`derivedStalkPushforwardModuleFunctorIso` read for the chosen derived pushforward. -/
def derivedStalkDerivedPushforwardIso
    [PreservesFiniteColimits (modulePushforward i)]
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base)) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i ⋙
        AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) (i.hom.base z) ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing Z) z ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategory :=
  Functor.isoWhiskerRight (derivedPushforwardIsoMapDerivedCategory i)
      (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X)
        (i.hom.base z)) ≪≫
    derivedStalkPushforwardModuleFunctorIso i z hi

end RingedSpace

section Scheme

/-- `derivedStalkDerivedPushforwardIso` for a closed immersion of schemes, where exactness of
the pushforward and the inducing hypothesis both come from the closed immersion. -/
def derivedStalkDerivedPushforwardIsoOfSchemes {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (z : Z.toRingedSpace.carrier) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X.toRingedSpace)
          (i.toLRSHom.toShHom.hom.base z) ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing Z.toRingedSpace) z ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom).mapDerivedCategory :=
  derivedStalkDerivedPushforwardIso i.toLRSHom.toShHom z
    (isClosedEmbedding_base_toShHom i).isInducing

end Scheme

end Stacks.ClosedImmersion

end

end
