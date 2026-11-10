module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# Morphisms out of a product of finite étale covers

For a finite étale cover `A` of `S` and a morphism `g : T ⟶ S`, morphisms of `S`-schemes out of
the product `A ×_S T` in the slice category correspond to morphisms of finite étale covers of
`T` from the base change of `A`. This file collects that correspondence, the comparison
isomorphism it rests on, and their compatibility with a base change of the product.

## Main definitions

* `Stacks.FundamentalGroup.baseChangeLift`: the morphism into a base-changed cover determined by
  a morphism to the cover and one to the new base that agree over the old base.
* `Stacks.FundamentalGroup.prodLeftIsoBaseChange`: the product of `A` with `T` over `S` is the
  base change of `A` along `g`.
* `Stacks.FundamentalGroup.prodHomEquivBaseChangeHom` and
  `Stacks.FundamentalGroup.prodSelfHomEquiv`: morphisms out of the product, and out of the
  product with `S` itself, as morphisms of covers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- The morphism into a base-changed finite étale cover determined by a morphism to the cover
and a morphism to the new base that agree over the old base. -/
public def baseChangeLift {S T Z : Scheme.{u}} (U : FiniteEtaleOver S) (g : T ⟶ S)
    {a : Z ⟶ U.left} {b : Z ⟶ T} (hab : a ≫ U.hom = b ≫ g) :
    Z ⟶ ((finiteEtaleBaseChange g).obj U).left :=
  pullback.lift a b hab

/-- The lift into a base-changed cover, followed by the projection to the cover, is the given
morphism to the cover. -/
public theorem baseChangeLift_proj {S T Z : Scheme.{u}} (U : FiniteEtaleOver S) (g : T ⟶ S)
    {a : Z ⟶ U.left} {b : Z ⟶ T} (hab : a ≫ U.hom = b ≫ g) :
    baseChangeLift U g hab ≫ finiteEtaleBaseChangeProj g U = a :=
  pullback.lift_fst _ _ _

/-- The lift into a base-changed cover, followed by its structure morphism, is the given
morphism to the new base. -/
public theorem baseChangeLift_hom {S T Z : Scheme.{u}} (U : FiniteEtaleOver S) (g : T ⟶ S)
    {a : Z ⟶ U.left} {b : Z ⟶ T} (hab : a ≫ U.hom = b ≫ g) :
    baseChangeLift U g hab ≫ ((finiteEtaleBaseChange g).obj U).hom = b :=
  pullback.lift_snd _ _ _

/-- The morphism of `S`-schemes from `T`, viewed over `S` by `g`, to `S` itself. -/
public def overToSelf {S T : Scheme.{u}} (g : T ⟶ S) :
    (Over.mk g : Over S) ⟶ Over.mk (𝟙 S) :=
  Over.homMk g (Category.comp_id g)

/-- The product of a finite étale cover `A` with an `S`-scheme `T`, in the slice category over
`S`, is the base change of `A` along the structure morphism of `T`. -/
public def prodLeftIsoBaseChange {S T : Scheme.{u}} (A : FiniteEtaleOver S) (g : T ⟶ S) :
    (Over.mk A.hom ⨯ Over.mk g : Over S).left ≅ ((finiteEtaleBaseChange g).obj A).left :=
  Over.prodLeftIsoPullback (Over.mk A.hom) (Over.mk g)

/-- Under the identification of the product with the base change, the projection to the cover is
the first projection of the product. -/
public theorem prodLeftIsoBaseChange_hom_proj {S T : Scheme.{u}} (A : FiniteEtaleOver S)
    (g : T ⟶ S) :
    (prodLeftIsoBaseChange A g).hom ≫ finiteEtaleBaseChangeProj g A
      = (prod.fst (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left :=
  Over.prodLeftIsoPullback_hom_fst _ _

/-- Under the identification of the product with the base change, the structure morphism is the
second projection of the product. -/
public theorem prodLeftIsoBaseChange_hom_hom {S T : Scheme.{u}} (A : FiniteEtaleOver S)
    (g : T ⟶ S) :
    (prodLeftIsoBaseChange A g).hom ≫ ((finiteEtaleBaseChange g).obj A).hom
      = (prod.snd (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left :=
  Over.prodLeftIsoPullback_hom_snd _ _

/-- The inverse of the identification of the product with the base change, followed by the first
projection of the product, is the projection to the cover. -/
public theorem prodLeftIsoBaseChange_inv_fst {S T : Scheme.{u}} (A : FiniteEtaleOver S)
    (g : T ⟶ S) :
    (prodLeftIsoBaseChange A g).inv ≫
        (prod.fst (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left
      = finiteEtaleBaseChangeProj g A :=
  Over.prodLeftIsoPullback_inv_fst _ _

/-- The inverse of the identification of the product with the base change, followed by the
second projection of the product, is the structure morphism. -/
public theorem prodLeftIsoBaseChange_inv_snd {S T : Scheme.{u}} (A : FiniteEtaleOver S)
    (g : T ⟶ S) :
    (prodLeftIsoBaseChange A g).inv ≫
        (prod.snd (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left
      = ((finiteEtaleBaseChange g).obj A).hom :=
  Over.prodLeftIsoPullback_inv_snd _ _

/-- Morphisms of `S`-schemes out of the product of `A` with `T` are morphisms of finite étale
covers of `T` between the two base changes. -/
public def prodHomEquivBaseChangeHom {S T : Scheme.{u}} (A B : FiniteEtaleOver S) (g : T ⟶ S) :
    ((Over.mk A.hom ⨯ Over.mk g : Over S) ⟶ Over.mk B.hom) ≃
      ((finiteEtaleBaseChange g).obj A ⟶ (finiteEtaleBaseChange g).obj B) where
  toFun ξ := MorphismProperty.Over.homMk
    (baseChangeLift B g (a := (prodLeftIsoBaseChange A g).inv ≫ ξ.left)
      (b := ((finiteEtaleBaseChange g).obj A).hom) (by
        have hw : ξ.left ≫ B.hom = (Over.mk A.hom ⨯ Over.mk g : Over S).hom := Over.w ξ
        have hsnd : (prod.snd (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left ≫ g
            = (Over.mk A.hom ⨯ Over.mk g : Over S).hom := Over.w prod.snd
        rw [Category.assoc, hw, ← hsnd, ← Category.assoc, prodLeftIsoBaseChange_inv_snd]))
    (baseChangeLift_hom _ _ _)
  invFun Φ := Over.homMk
    ((prodLeftIsoBaseChange A g).hom ≫ Φ.left ≫ finiteEtaleBaseChangeProj g B) (by
      have hsnd : (prod.snd (X := (Over.mk A.hom : Over S)) (Y := Over.mk g)).left ≫ g
          = (Over.mk A.hom ⨯ Over.mk g : Over S).hom := Over.w prod.snd
      rw [← hsnd, ← prodLeftIsoBaseChange_hom_hom]
      simp only [Category.assoc, Over.mk_hom]
      rw [finiteEtaleBaseChangeProj_comp_hom, reassoc_of% MorphismProperty.Over.w Φ])
  left_inv ξ := by
    refine Over.OverMorphism.ext ?_
    change (prodLeftIsoBaseChange A g).hom ≫ baseChangeLift B g _ ≫
      finiteEtaleBaseChangeProj g B = ξ.left
    rw [baseChangeLift_proj, Iso.hom_inv_id_assoc]
  right_inv Φ := by
    refine MorphismProperty.Over.Hom.ext (finiteEtaleBaseChangeProj_hom_ext g B ?_ ?_)
    · change baseChangeLift B g _ ≫ finiteEtaleBaseChangeProj g B
        = Φ.left ≫ finiteEtaleBaseChangeProj g B
      rw [baseChangeLift_proj]
      change (prodLeftIsoBaseChange A g).inv ≫ (prodLeftIsoBaseChange A g).hom ≫
        Φ.left ≫ finiteEtaleBaseChangeProj g B = Φ.left ≫ finiteEtaleBaseChangeProj g B
      rw [Iso.inv_hom_id_assoc]
    · change baseChangeLift B g _ ≫ ((finiteEtaleBaseChange g).obj B).hom
        = Φ.left ≫ ((finiteEtaleBaseChange g).obj B).hom
      rw [baseChangeLift_hom, MorphismProperty.Over.w Φ]

/-- The product of `A` with `S` itself, in the category of `S`-schemes, is `A`. -/
public def prodSelfIso {S : Scheme.{u}} (A : FiniteEtaleOver S) :
    (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S).left ≅ A.left :=
  prodLeftIsoBaseChange A (𝟙 S) ≪≫ finiteEtalePullbackIdIso A

/-- The identification of `A ×_S S` with `A` is the first projection of the product. -/
public theorem prodSelfIso_hom {S : Scheme.{u}} (A : FiniteEtaleOver S) :
    (prodSelfIso A).hom
      = (prod.fst (X := (Over.mk A.hom : Over S)) (Y := Over.mk (𝟙 S))).left :=
  prodLeftIsoBaseChange_hom_proj A (𝟙 S)

/-- Morphisms of `S`-schemes out of the product of `A` with `S` itself are morphisms of finite
étale covers `A ⟶ B`. -/
public def prodSelfHomEquiv {S : Scheme.{u}} (A B : FiniteEtaleOver S) :
    ((Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S) ⟶ Over.mk B.hom) ≃ (A ⟶ B) where
  toFun ξ := MorphismProperty.Over.homMk ((prodSelfIso A).inv ≫ ξ.left) (by
    have hw : ξ.left ≫ B.hom = (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S).hom := Over.w ξ
    have hfst : (prod.fst (X := (Over.mk A.hom : Over S)) (Y := Over.mk (𝟙 S))).left ≫ A.hom
        = (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S).hom := Over.w prod.fst
    rw [Category.assoc, hw, ← hfst, ← prodSelfIso_hom, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp])
  invFun φ := Over.homMk ((prodSelfIso A).hom ≫ φ.left) (by
    have hfst : (prod.fst (X := (Over.mk A.hom : Over S)) (Y := Over.mk (𝟙 S))).left ≫ A.hom
        = (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S).hom := Over.w prod.fst
    calc ((prodSelfIso A).hom ≫ φ.left) ≫ B.hom
        = (prodSelfIso A).hom ≫ φ.left ≫ B.hom := Category.assoc _ _ _
      _ = (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S).hom := by
          rw [MorphismProperty.Over.w φ, prodSelfIso_hom, hfst])
  left_inv ξ := Over.OverMorphism.ext (Iso.hom_inv_id_assoc _ _)
  right_inv φ := MorphismProperty.Over.Hom.ext (Iso.inv_hom_id_assoc _ _)

/-- Base change along `g` of a morphism of finite étale covers of `S`, read through the two
identifications of morphisms out of a product, is precomposition with the product of the
identity of `A` and the morphism `Over.mk g ⟶ Over.mk (𝟙 S)`. -/
public theorem prodHomEquivBaseChangeHom_prod_map {S T : Scheme.{u}} (g : T ⟶ S)
    (A B : FiniteEtaleOver S) (ξ : (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S) ⟶ Over.mk B.hom) :
    prodHomEquivBaseChangeHom A B g (prod.map (𝟙 (Over.mk A.hom : Over S)) (overToSelf g) ≫ ξ)
      = (finiteEtaleBaseChange g).map (prodSelfHomEquiv A B ξ) := by
  refine finiteEtaleOver_hom_ext g ?_
  rw [finiteEtaleBaseChangeProj_naturality]
  change baseChangeLift B g _ ≫ finiteEtaleBaseChangeProj g B
    = finiteEtaleBaseChangeProj g A ≫ (prodSelfIso A).inv ≫ ξ.left
  rw [baseChangeLift_proj]
  have hfst : (prodLeftIsoBaseChange A g).inv ≫
      (prod.map (𝟙 (Over.mk A.hom : Over S)) (overToSelf g)).left ≫ (prodSelfIso A).hom
      = finiteEtaleBaseChangeProj g A := by
    rw [prodSelfIso_hom, ← Over.comp_left, prod.map_fst, Over.comp_left, Over.id_left,
      Category.comp_id, prodLeftIsoBaseChange_inv_fst]
  rw [← hfst, Over.comp_left]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end Stacks.FundamentalGroup

end
