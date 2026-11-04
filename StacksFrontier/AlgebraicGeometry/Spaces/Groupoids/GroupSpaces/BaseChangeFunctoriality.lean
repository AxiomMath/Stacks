module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Determinant

/-!
# Functoriality of the group algebraic space attached to a group scheme

`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` attaches to a group scheme `G`
over `S` lying in the big fppf site the group algebraic space `G_B = B ×_S G` over an algebraic
space `B`. A homomorphism of group schemes `G ⟶ H` over `S` induces a homomorphism
`G_B ⟶ H_B` of group algebraic spaces: on points it is composition with the homomorphism.

## Main definitions

* `CategoryTheory.overProdMap` — the morphism `B ⨯ P ⟶ B ⨯ Q` over `B` induced by `P ⟶ Q`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteMap` — the homomorphism
  `G_B ⟶ H_B` induced by a homomorphism of group schemes.

## Main results

The criterion `CategoryTheory.isMonHom_of_points` and the instance
`CategoryTheory.isMonHom_whiskerRight_forget` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Determinant` are used.

* `CategoryTheory.isMonHom_overProdMap` — `B ⨯ P ⟶ B ⨯ Q` is a homomorphism over `B` when
  `P ⟶ Q` is a homomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace CategoryTheory

/-- The morphism `B ⨯ P ⟶ B ⨯ Q` over `B` induced by a morphism `P ⟶ Q`. -/
public noncomputable def overProdMap {𝒟 : Type*} [Category 𝒟] [HasBinaryProducts 𝒟] (B : 𝒟)
    {P Q : 𝒟} (τ : P ⟶ Q) :
    (Over.mk (prod.fst : B ⨯ P ⟶ B) : Over B) ⟶ Over.mk (prod.fst : B ⨯ Q ⟶ B) :=
  Over.homMk (prod.map (𝟙 B) τ) (by simp)

/-- The underlying morphism of `overProdMap B τ` is `prod.map (𝟙 B) τ`. -/
public lemma overProdMap_left {𝒟 : Type*} [Category 𝒟] [HasBinaryProducts 𝒟] (B : 𝒟) {P Q : 𝒟}
    (τ : P ⟶ Q) : (overProdMap B τ).left = prod.map (𝟙 B) τ := rfl

/-- `B ⨯ P ⟶ B ⨯ Q` is a homomorphism of group objects over `B` when `P ⟶ Q` is a homomorphism
of group objects. -/
public theorem isMonHom_overProdMap {𝒟 : Type*} [Category 𝒟] [CartesianMonoidalCategory 𝒟]
    [HasBinaryProducts 𝒟] (B : 𝒟) [CartesianMonoidalCategory (Over B)] {P Q : 𝒟}
    [GrpObj P] [GrpObj Q] (τ : P ⟶ Q) [IsMonHom τ] : IsMonHom (overProdMap B τ) := by
  have key : ∀ (X : Over B) (a : X ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)),
      overProdFstHomMulEquiv B Q X (a ≫ overProdMap B τ) =
        overProdFstHomMulEquiv B P X a ≫ τ := by
    intro X a
    simp [overProdFstHomMulEquiv_apply, overProdMap_left]
  refine isMonHom_of_points _ (fun {X} => ?_) (fun {X} a b => ?_)
  · apply (overProdFstHomMulEquiv B Q X).injective
    rw [key, map_one, map_one, MonObj.one_comp]
  · apply (overProdFstHomMulEquiv B Q X).injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The morphism of the restricted functors of points induced by a homomorphism of group schemes
`G ⟶ H` over `S` lying in the big fppf site: composition with it. -/
public noncomputable def pointsOnSiteMap {G H : BigFppfOver 𝒞 S hS}
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (hH : GrpObj ((toSchemeOver 𝒞 S hS).obj H))
    (f : (toSchemeOver 𝒞 S hS).obj G ⟶ (toSchemeOver 𝒞 S hS).obj H)
    (hf : letI := hG; letI := hH; IsMonHom f) :
    pointsOnSite 𝒞 S hS G hG ⟶ pointsOnSite 𝒞 S hS H hH :=
  letI := hG
  letI := hH
  Functor.whiskerLeft (toSchemeOver 𝒞 S hS).op
    (yonedaGrp.map (Grp.homMk (A := ⟨(toSchemeOver 𝒞 S hS).obj G⟩)
      (B := ⟨(toSchemeOver 𝒞 S hS).obj H⟩) f))

/-- `AlgebraicGeometry.Space.pointsOnSiteMap` is composition with the homomorphism. -/
public lemma pointsOnSiteMap_app_apply {G H : BigFppfOver 𝒞 S hS}
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (hH : GrpObj ((toSchemeOver 𝒞 S hS).obj H))
    (f : (toSchemeOver 𝒞 S hS).obj G ⟶ (toSchemeOver 𝒞 S hS).obj H)
    (hf : letI := hG; letI := hH; IsMonHom f) (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (x : (toSchemeOver 𝒞 S hS).obj T.unop ⟶ (toSchemeOver 𝒞 S hS).obj G) :
    (pointsOnSiteMap 𝒞 S hS hG hH f hf).app T x = x ≫ f :=
  rfl

/-- **The homomorphism of group algebraic spaces `G_B ⟶ H_B` induced by a homomorphism of group
schemes `G ⟶ H` over `S`.** On the underlying fibre products it is `B ⨯ G ⟶ B ⨯ H`, the
identity on `B` and composition with the homomorphism on points of the second factor. -/
public noncomputable def GroupAlgebraicSpace.ofGroupSchemeInSiteMap
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    {G H : BigFppfOver 𝒞 S hS}
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (hH : GrpObj ((toSchemeOver 𝒞 S hS).obj H))
    (f : (toSchemeOver 𝒞 S hS).obj G ⟶ (toSchemeOver 𝒞 S hS).obj H)
    (hf : letI := hG; letI := hH; IsMonHom f) :
    GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB G hG ⟶
      GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 S hS B hB H hH :=
  ObjectProperty.homMk (@Grp.homMk _ _ _ _ _ (overProdMap B
    (Functor.whiskerRight (pointsOnSiteMap 𝒞 S hS hG hH f hf) (forget GrpCat)))
    (isMonHom_overProdMap B
      (Functor.whiskerRight (pointsOnSiteMap 𝒞 S hS hG hH f hf) (forget GrpCat))))

/-- The underlying morphism over `B` of
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteMap`. -/
public lemma GroupAlgebraicSpace.ofGroupSchemeInSiteMap_hom
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (hB : IsAlgebraicSpace 𝒞 S hS B)
    {G H : BigFppfOver 𝒞 S hS}
    (hG : GrpObj ((toSchemeOver 𝒞 S hS).obj G)) (hH : GrpObj ((toSchemeOver 𝒞 S hS).obj H))
    (f : (toSchemeOver 𝒞 S hS).obj G ⟶ (toSchemeOver 𝒞 S hS).obj H)
    (hf : letI := hG; letI := hH; IsMonHom f) :
    (GroupAlgebraicSpace.ofGroupSchemeInSiteMap 𝒞 S hS B hB hG hH f hf).hom.hom.hom =
      overProdMap B
        (Functor.whiskerRight (pointsOnSiteMap 𝒞 S hS hG hH f hf) (forget GrpCat)) :=
  rfl

end AlgebraicGeometry.Space

end
