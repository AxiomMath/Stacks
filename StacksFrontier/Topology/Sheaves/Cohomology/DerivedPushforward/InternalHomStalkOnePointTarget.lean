module

public import
 StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkPresentationFromTheStalk

/-!
# The stalk of a derived internal hom, through the one-point space

This file studies the canonical map of Tag 0GM8

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`,

with the point `x` presented as the one-point ringed space `Y = {x}`, the identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` is `pointStalkDerivedEquiv` (the stalk functor), its compatibility with
derived pullback is `pointStalkPullbackComparison`, and the target is read as
`stalkOnePointDerivedHom`, the derived internal hom of the one-point space transported along that
identification.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomStalk.stalkOnePointDerivedHom`: `RHom` over `𝒪_{X,x}` as
  computed on the one-point space `Y = {x}`.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointPullbackOfStalkIso`: the derived pullback of
  `K` to `Y` is the stalk `K_x` read back through the identification.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkSheafHomMapOnePoint`: the displayed map of
  Tag 0GM8 with this spelling of its target.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMapOnePoint_iff`: the displayed
  map is invertible exactly when the canonical map of Tag 08I3 along `Y = {x} ⟶ X` is.
* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMapOnePoint_singleUnit`: the
  displayed map is invertible at `K = 𝒪_X[0]`, for every `M`.
* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_inv_comp_comp_hom_iff`: a morphism flanked by
  isomorphisms is invertible exactly when it is.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.DerivedInternalHomStalk

open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Invertibility of a morphism flanked by isomorphisms -/

section Composites

variable {C : Type*} [Category C] {A A' B B' : C}

/-- A morphism flanked by the inverse of an isomorphism on the left and an isomorphism on the
right is invertible only if it is. -/
theorem isIso_of_isIso_inv_comp_comp_hom (u : A ≅ A') (f : A ⟶ B) (v : B ≅ B')
    (h : IsIso (u.inv ≫ f ≫ v.hom)) : IsIso f :=
  have := IsIso.of_isIso_comp_left u.inv (f ≫ v.hom)
  IsIso.of_isIso_comp_right f v.hom

/-- A morphism flanked by isomorphisms is invertible exactly when it is. -/
theorem isIso_inv_comp_comp_hom_iff (u : A ≅ A') (f : A ⟶ B) (v : B ≅ B') :
    IsIso (u.inv ≫ f ≫ v.hom) ↔ IsIso f :=
  ⟨isIso_of_isIso_inv_comp_comp_hom u f v, fun _ ↦ inferInstance⟩

end Composites

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### `RHom` over the local ring, computed on the one-point space -/

/-- **`RHom` over `𝒪_{X,x}`, as computed on the one-point space `Y = {x}`**: the derived internal
hom of `Y` transported along `pointStalkDerivedEquiv`, the identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` given by the stalk functor. -/
def stalkOnePointDerivedHom :
    (DerivedCategory (ModuleCat.{u} (stalkRing X x)))ᵒᵖ ×
        DerivedCategory (ModuleCat.{u} (stalkRing X x)) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  (pointStalkDerivedEquiv X x).inverse.op.prod (pointStalkDerivedEquiv X x).inverse ⋙
    Functor.uncurry.obj (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf) ⋙
      (pointStalkDerivedEquiv X x).functor

variable (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))

/-- **The derived pullback of `K` to the one-point space `Y = {x}` is the stalk `K_x`, read back
through the identification `D(𝒪_Y) ≌ D(𝒪_{X,x})`.** -/
def pointPullbackOfStalkIso :
    (pointStalkDerivedEquiv X x).inverse.obj ((derivedStalk X x).obj K) ≅
      (derivedPullbackFunctor (pointHom X x)).obj K :=
  (pointStalkDerivedEquiv X x).inverse.mapIso ((pointStalkPullbackComparison X x).app K).symm ≪≫
    ((pointStalkDerivedEquiv X x).unitIso.app
      ((derivedPullbackFunctor (pointHom X x)).obj K)).symm

/-- The canonical map of Tag 08I3 along `Y = {x} ⟶ X`, with its target rewritten so that both
arguments of the one-point internal hom are stalks. -/
def onePointSheafHomStalkLeg :
    ((Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf).obj
          (op ((derivedPullbackFunctor (pointHom X x)).obj K))).obj
        ((derivedPullbackFunctor (pointHom X x)).obj M) ≅
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf)).obj
        (op ((pointStalkDerivedEquiv X x).inverse.obj ((derivedStalk X x).obj K)),
          (pointStalkDerivedEquiv X x).inverse.obj ((derivedStalk X x).obj M)) :=
  (Functor.uncurry.obj
      (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf)).mapIso
    (Iso.prod (pointPullbackOfStalkIso X x K).op (pointPullbackOfStalkIso X x M).symm)

/-- **The displayed map of Tag 0GM8**, `R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`, with
`RHom` over the local ring spelled as the derived internal hom of the one-point space
`Y = {x}` read through the stalk identification.

It is the canonical map of Tag 08I3 along `Y ⟶ X`, read through that identification. -/
def stalkSheafHomMapOnePoint :
    (derivedStalk X x).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj M) ⟶
      (stalkOnePointDerivedHom X x).obj
        (op ((derivedStalk X x).obj K), (derivedStalk X x).obj M) :=
  ((pointStalkPullbackComparison X x).app
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj M)).inv ≫
    (pointStalkDerivedEquiv X x).functor.map
        (derivedPullbackSheafHomMap (pointHom X x) K M) ≫
      ((pointStalkDerivedEquiv X x).functor.mapIso
        (onePointSheafHomStalkLeg X x K M)).hom

/-- **The displayed map of Tag 0GM8 is invertible exactly when the canonical map of Tag 08I3
along `Y = {x} ⟶ X` is.** -/
theorem isIso_stalkSheafHomMapOnePoint_iff :
    IsIso (stalkSheafHomMapOnePoint X x K M) ↔
      IsIso (derivedPullbackSheafHomMap (pointHom X x) K M) :=
  (isIso_inv_comp_comp_hom_iff _ _ _).trans
    (isIso_iff_of_reflects_iso _ (pointStalkDerivedEquiv X x).functor)

/-! ### The structure sheaf -/

/-- For a ringed space `X`, a point `x` of `X` and `M ∈ D(𝒪_X)`, the displayed map

`R𝓗om_{𝒪_X}(𝒪_X[0], M)_x ⟶ RHom_{𝒪_{X,x}}((𝒪_X[0])_x, M_x)`

is an isomorphism, the right-hand side being the derived internal hom of the one-point space
`Y = {x}` read through the stalk identification. -/
theorem isIso_stalkSheafHomMapOnePoint_singleUnit :
    IsIso (stalkSheafHomMapOnePoint X x (singleUnit X) M) :=
  (isIso_stalkSheafHomMapOnePoint_iff X x (singleUnit X) M).2
    (isIso_derivedPullbackSheafHomMap_singleUnit (pointHom X x) M)

end Stacks.Cohomology.DerivedInternalHomStalk

end
