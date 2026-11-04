module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase

/-!
# Points under the change of base of Stacks 04SG

Let `g : V ⟶ S` be a morphism of a big fppf site and let `X` be a presheaf on the big fppf site of
`S` together with a morphism to the representable presheaf of `g`. The equivalence
`AlgebraicGeometry.smallerBasePresheafEquivalence` of Stacks 04SG attaches to it a presheaf `X_V`
on the big fppf site of `V`. This file shows that the point spaces of Stacks 03BY of `X_V` over `V`
and of `X` over `S` are homeomorphic, so that a closed subset of `|X|` is the same thing as a
closed subset of `|X_V|`.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseInverseRelocalizeIso`: the lower-shriek extension of `X_V`
  along `g` is `X` again.
* `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph`: the homeomorphism
  `|X_V| ≃ₜ |X|`.

## Main results

* `AlgebraicGeometry.Space.isClosed_preimage_pointsSmallerBaseInverseHomeomorph_iff`: a subset of
  `|X|` is closed exactly when its inverse image in `|X_V|` is.

## Implementation notes

The homeomorphism is the composite of `AlgebraicGeometry.Space.pointsRelocalize`, which reads the
points of `X_V` over `V` as points of its lower-shriek extension over `S` and is a bijective,
continuous and closed map, with the homeomorphism `AlgebraicGeometry.Space.pointsHomeomorphOfIso`
induced by the identification `AlgebraicGeometry.Space.smallerBaseInverseRelocalizeIso` of that
extension with `X`. That identification is written out on sections, rather than read off the counit
of the equivalence, so that the point of `X` attached to a section of `X_V` can be computed.

## References

* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology


variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- The morphism of the big fppf site of `S` from an object `T` to `Over.mk (ψ ≫ g)`, for a
factorization `ψ` of the structure morphism of `T` through `g`: it is the identity on underlying
schemes. -/
def smallerBaseFactorHom {T : BigFppfOver B S hS} {ψ : T.left ⟶ B.obj hV} (h : ψ ≫ g = T.hom) :
    T ⟶ (Over.mk (ψ ≫ g) : BigFppfOver B S hS) :=
  Over.homMk (𝟙 T.left) (by simpa using h)

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseFactorHom`, again the identity on
underlying schemes. -/
def smallerBaseFactorHomInv {T : BigFppfOver B S hS} {ψ : T.left ⟶ B.obj hV}
    (h : ψ ≫ g = T.hom) : (Over.mk (ψ ≫ g) : BigFppfOver B S hS) ⟶ T :=
  Over.homMk (𝟙 T.left) (by simpa using h.symm)

/-- The sections over `T` of the lower-shriek extension along `g : V ⟶ S` of the presheaf `X_V`
over `V` that Stacks 04SG attaches to a presheaf `X` over the representable presheaf of `g` are the
sections of `X` over `T`. A section of the extension over `T` is a factorization `ψ : T ⟶ V` of the
structure morphism together with a section of `X` over `T →ψ V →g S` lying over `ψ`; it goes to
that section, restricted along the identity of `T`. -/
noncomputable def smallerBaseInverseRelocalizeEquiv
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    ((OverShriek.relocalizePresheafFunctor g).obj
        ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X)).obj T ≃ X.left.obj T :=
    { toFun := fun y => X.left.map
        (smallerBaseFactorHom B V S hV hS g (OverShriek.relocalizeFactors g _ y)).op y.1.2.1
      invFun := fun t => OverShriek.relocalizeMk g _ (X.hom.app T t).left
        ⟨X.left.map (smallerBaseFactorHomInv B V S hV hS g (Over.w (X.hom.app T t))).op t,
          (NatTrans.naturality_apply X.hom
            (smallerBaseFactorHomInv B V S hV hS g (Over.w (X.hom.app T t))).op t).trans
            (Over.OverMorphism.ext (Category.id_comp _))⟩
        (Over.w (X.hom.app T t))
      left_inv := by
        rintro ⟨⟨ψ, s⟩, hψ⟩
        have hψ0 : ψ ≫ g = T.unop.hom := hψ
        have h1 : X.hom.app T (X.left.map (smallerBaseFactorHom B V S hV hS g hψ0).op s.1) =
            smallerBaseFactorHom B V S hV hS g hψ0 ≫ X.hom.app _ s.1 :=
          NatTrans.naturality_apply X.hom (smallerBaseFactorHom B V S hV hS g hψ0).op s.1
        have h2 : (X.hom.app _ s.1).left = ψ := congrArg Over.Hom.left s.2
        have hψ' : (X.hom.app T (X.left.map
            (smallerBaseFactorHom B V S hV hS g hψ0).op s.1)).left = ψ := by
          rw [h1, Over.comp_left]
          exact (congrArg (fun k => 𝟙 _ ≫ k) h2).trans (Category.id_comp ψ)
        let e : (Over.mk (X.hom.app T (X.left.map
            (smallerBaseFactorHom B V S hV hS g hψ0).op s.1)).left : Over (B.obj hV)) ⟶
            Over.mk ψ := Over.homMk (𝟙 _) ((Category.id_comp ψ).trans hψ'.symm)
        apply Subtype.ext
        refine Eq.trans ?_ (OverShriek.sigmaMk_eq_self _ s e rfl)
        refine congrArg (Sigma.mk _) (Subtype.ext ?_)
        refine (FunctorToTypes.map_comp_apply X.left
          (smallerBaseFactorHom B V S hV hS g hψ0).op _ s.1).symm.trans
          (congrArg (fun k => X.left.map k s.1) (Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_)))
        rfl
      right_inv := by
        intro t
        refine (FunctorToTypes.map_comp_apply X.left
          (smallerBaseFactorHomInv B V S hV hS g (Over.w (X.hom.app T t))).op _ t).symm.trans ?_
        have : smallerBaseFactorHom B V S hV hS g (Over.w (X.hom.app T t)) ≫
            smallerBaseFactorHomInv B V S hV hS g (Over.w (X.hom.app T t)) = 𝟙 _ :=
          Over.OverMorphism.ext (by simp [smallerBaseFactorHom, smallerBaseFactorHomInv])
        have hop : (smallerBaseFactorHomInv B V S hV hS g (Over.w (X.hom.app T t))).op ≫
            (smallerBaseFactorHom B V S hV hS g (Over.w (X.hom.app T t))).op = 𝟙 _ := by
          rw [← op_comp, this, op_id]
        exact (congrArg (fun k => X.left.map k t) hop).trans (FunctorToTypes.map_id_apply _ _) }

/-- The lower-shriek extension along `g : V ⟶ S` of the presheaf `X_V` over `V` that Stacks 04SG
attaches to a presheaf `X` over the representable presheaf of `g` is `X` again, through the
bijections `AlgebraicGeometry.Space.smallerBaseInverseRelocalizeEquiv`. -/
noncomputable def smallerBaseInverseRelocalizeIso
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    (OverShriek.relocalizePresheafFunctor g).obj
        ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X) ≅ X.left :=
  NatIso.ofComponents (fun T => (smallerBaseInverseRelocalizeEquiv B V S hV hS g X T).toIso)
    (by
      intro T T' f
      ext ⟨⟨ψ, s⟩, hψ⟩
      refine (FunctorToTypes.map_comp_apply X.left _ _ s.1).symm.trans
        (Eq.trans ?_ (FunctorToTypes.map_comp_apply X.left _ f s.1))
      refine congrArg (fun k => X.left.map k s.1) (Quiver.Hom.unop_inj ?_)
      refine Over.OverMorphism.ext ?_
      change 𝟙 _ ≫ f.unop.left = f.unop.left ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- The identification `AlgebraicGeometry.Space.smallerBaseInverseRelocalizeIso` on a section:
the section of `X` carried by a section of the lower-shriek extension, restricted along the
identity of the underlying scheme. -/
theorem smallerBaseInverseRelocalizeIso_hom_app
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {T : (BigFppfOver B S hS)ᵒᵖ}
    (y : ((OverShriek.relocalizePresheafFunctor g).obj
      ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X)).obj T) :
    (smallerBaseInverseRelocalizeIso B V S hV hS g X).hom.app T y =
      X.left.map
        (smallerBaseFactorHom B V S hV hS g (OverShriek.relocalizeFactors g _ y)).op y.1.2.1 :=
  rfl

/-- **The points of a presheaf over a smaller base.** For a presheaf `X` on the big fppf site of
`S` over the representable presheaf of `g : V ⟶ S`, the point space of Stacks 03BY of the presheaf
`X_V` on the big fppf site of `V` that Stacks 04SG attaches to it is homeomorphic to the point
space of `X`. -/
noncomputable def pointsSmallerBaseInverseHomeomorph
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    points B V hV ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X) ≃ₜ
      points B S hS X.left :=
  ((Equiv.ofBijective _ (pointsRelocalize_bijective B V S hV hS g _)).toHomeomorphOfContinuousClosed
      (continuous_pointsRelocalize B V S hV hS g _)
      (isClosedMap_pointsRelocalize B V S hV hS g _)).trans
    (pointsHomeomorphOfIso B S hS (smallerBaseInverseRelocalizeIso B V S hV hS g X))

/-- The homeomorphism `|X_V| ≃ₜ |X|` reads a point over `V` as a point of the lower-shriek
extension over `S` and then transports it to `X`. -/
theorem pointsSmallerBaseInverseHomeomorph_apply
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (x : points B V hV ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X)) :
    pointsSmallerBaseInverseHomeomorph B V S hV hS g X x =
      pointsMap B S hS _ (smallerBaseInverseRelocalizeIso B V S hV hS g X).hom
        (pointsRelocalize B V S hV hS g _ x) :=
  rfl

/-- A subset `T` of `|X|` is closed exactly when its inverse image in `|X_V|` under the
homeomorphism `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` is closed. -/
theorem isClosed_preimage_pointsSmallerBaseInverseHomeomorph_iff
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (T : Set (points B S hS X.left)) :
    IsClosed (pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' T) ↔ IsClosed T :=
  (pointsSmallerBaseInverseHomeomorph B V S hV hS g X).isClosed_preimage

end AlgebraicGeometry.Space

end
