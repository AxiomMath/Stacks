module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEmerton
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesGerbe

/-!
# Stacks 0CKI from the quasi-coherence of the band (Stacks 0CKG (2))

`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_isGerbe_of_isQuasicoherent` proves Stacks
0CKI from three gerbe inputs on the category `𝒞` of smooth lifts of Stacks 0CJP and the band of
Stacks 0CKG (2). This file discharges the gerbe inputs: `𝒞` is a stack (Stacks 0CJU,
`EtaleSmoothLift.isStack_proj`), locally nonempty and locally connected (Stacks 0CJX,
`EtaleSmoothLift.locallyNonempty_proj`, `EtaleSmoothLift.locallyConnected_proj`).

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_band_isQuasicoherent`: Stacks 0CKI
  from the band of the gerbe `𝒞` being a quasi-coherent `𝒪_W`-module, in exactly the form of the
  conclusion of Stacks 0CKG (2).

## References

* [Stacks Project, Tag 0CKI](https://stacks.math.columbia.edu/tag/0CKI)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJX](https://stacks.math.columbia.edu/tag/0CJX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace EtaleSmoothLift

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- **Stacks 0CKI from the quasi-coherence of the band.** Let `W` be affine and let the band `𝒢`
of the gerbe of smooth lifts `𝒞 ⟶ W_{spaces,étale}` (Stacks 0CJY) be a quasi-coherent
`𝒪_W`-module, as Stacks 0CKG (2) asserts. Then there is a cartesian square as in Stacks 0CKI with
`x'` smooth and `W'` affine. The gerbe inputs are Stacks 0CJU and 0CJX. -/
theorem exists_lift_of_band_isQuasicoherent (hW : Space.IsAffineSpace B S hS W.obj)
    (hband : haveI : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibered :=
        isFiberedInGroupoids_proj.isFibered
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ∃ (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
        (θ : ∀ (U : Space.SpacesEtale B S hS W)
          (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
          (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf y y ⋙
              uliftFunctor.{u + 1, u + 1}),
        (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a b : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) (a * b)).down =
              ((θ U y).hom.app (op g) a).down ≫ ((θ U y).hom.app (op g) b).down) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
              (y z : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : y ⟶ z)
              (g : Over U) (a : 𝒢.obj.obj (op g.left)),
            ((θ U z).hom.app (op g) a).down =
              Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
                ((θ U y).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) a).down =
              (Functor.pullbackFiberIdIso
                  ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y g.hom)).inv ≫
                ((θ g.left ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                    g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
                  (Functor.pullbackFiberIdIso
                    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                      g.hom)).hom) ∧
          ∃ M : SheafOfModules.{u + 1} (Space.structureRingSheaf B S hS W),
            M.IsQuasicoherentOnSite ∧
              Nonempty ((Space.spacesEtaleAbelianRestriction B S hS W).obj
                ((sheafCompose _ commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢) ≅
                (SheafOfModules.toSheaf _).obj M)) :
    ∃ (W' : AlgebraicSpaces B S hS) (i : W ⟶ W')
      (x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳')
      (α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'),
      AlgebraicStacks.IsSmooth B S hS x' ∧
        Nonempty (IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) ∧
        Space.IsAffineSpace B S hS W'.obj :=
  exists_lift_of_isGerbe_of_isQuasicoherent hW isStack_proj locallyNonempty_proj
    locallyConnected_proj hband

end EtaleSmoothLift

end AlgebraicGeometry.Stack
