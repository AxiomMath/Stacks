module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFaithful

/-!
# The morphism of algebraic spaces underlying a morphism of base-change functors

Let `η : F^R(X, L) ⟶ F^R(X', L')` be a morphism of the functors over the site attached by `F^R` to
two polarized families of algebraic spaces over `T`. Forgetting the polarizations and identifying
the base changes with those of Stacks 0E93
(`AlgebraicGeometry.PolarizedOverSpace.baseChangeComparison`), `η` becomes a morphism of
base-change functors of Stacks 0E93, which comes from a unique isomorphism `f : X ≅ X'` over `T`
(Stacks 0E93, full faithfulness). On every base change, `f` is the morphism of fibre products given
by the component of `η`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.fullBaseMap`: the isomorphism `X ≅ X'` over `T`.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.yoneda_map_comp_fibreFst_fullBaseMap`: the components of
  `η` are the morphisms of fibre products induced by `fullBaseMap η`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  AlgebraicSpaces.fiberProduct Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd
  Grpd.forgetToCat MorphismProperty

attribute [local instance] Space.isFlat_isStableUnderBaseChange

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}
  {ξ ξ' : PolarizedSpacesOver B T} (η : baseChangeRepresented ξ ⟶ baseChangeRepresented ξ')

/-- A morphism of base-change functors of polarized families, read on the base changes of
Stacks 0E93. -/
def spacesBaseChangeHom : spacesBaseChange ξ.of.obj.base ⟶ spacesBaseChange ξ'.of.obj.base :=
  (baseChangeComparison ξ).inv ≫ BasedCategory.whiskerRight η (forgetModulesBased B) ≫
    (baseChangeComparison ξ').hom

/-- **The isomorphism over `T` underlying a morphism of base-change functors** (Stacks 0E93). -/
def fullBaseMap : ξ.of.obj.base ⟶ ξ'.of.obj.base :=
  (SpacesOverSpace.baseChangeFunctor (B := B) (S := integerBase) (hS := hZ B)
    (P := SpacesOverSpace.properFlatProperty B integerBase (hZ B)) (T := T)).preimage
    (spacesBaseChangeHom η)

/-- The base-change functor sends `fullBaseMap η` to `spacesBaseChangeHom η`. -/
theorem baseChangeFunctor_map_fullBaseMap :
    (SpacesOverSpace.baseChangeFunctor (B := B) (S := integerBase) (hS := hZ B)
      (P := SpacesOverSpace.properFlatProperty B integerBase (hZ B)) (T := T)).map
        (fullBaseMap η) = spacesBaseChangeHom η :=
  Functor.map_preimage _ _

/-- The map of presheaf fibre products of a morphism of base-change functors. -/
theorem baseChangeCommaHom_fullBaseMap (a : (Points T).obj) :
    (SpacesOverSpace.baseChangeCommaHom (fullBaseMap η).hom.iso.hom a).left.hom =
      (fibreIsoPullback ξ a).inv ≫ yoneda.map (η.app a).hom.hom.base.left ≫
        (fibreIsoPullback ξ' a).hom :=
  congrArg (fun θ : spacesBaseChange ξ.of.obj.base ⟶ spacesBaseChange ξ'.of.obj.base =>
    (θ.app a).hom.hom.left.hom) (baseChangeFunctor_map_fullBaseMap η)

/-- **The components of `η` are the morphisms of fibre products induced by `fullBaseMap η`.** -/
theorem yoneda_map_comp_fibreFst_fullBaseMap (a : (Points T).obj) :
    yoneda.map (η.app a).hom.hom.base.left ≫ fibreFst ξ' a =
      fibreFst ξ a ≫ (fullBaseMap η).hom.iso.hom.left.hom := by
  have h := congrArg (fun k => (fibreIsoPullback ξ a).hom ≫ k ≫ pullback.snd _ _)
    (baseChangeCommaHom_fullBaseMap η a)
  have L₁ := SpacesOverSpace.baseChangeCommaHom_left_snd (fullBaseMap η).hom.iso.hom a
  have step : yoneda.map (η.app a).hom.hom.base.left ≫ fibreFst ξ' a =
      (fibreIsoPullback ξ a).hom ≫ ((fibreIsoPullback ξ a).inv ≫
        yoneda.map (η.app a).hom.hom.base.left ≫ (fibreIsoPullback ξ' a).hom) ≫
        pullback.snd _ _ :=
    (congrArg (yoneda.map (η.app a).hom.hom.base.left ≫ ·)
      (fibreIsoPullback_hom_snd ξ' a)).symm.trans
      ((Iso.hom_inv_id_assoc (fibreIsoPullback ξ a) _).symm.trans
        (congrArg ((fibreIsoPullback ξ a).hom ≫ ·)
          ((Category.assoc _ _ _).trans (congrArg ((fibreIsoPullback ξ a).inv ≫ ·)
            (Category.assoc _ _ _))).symm))
  refine step.trans (h.symm.trans ?_)
  refine (congrArg ((fibreIsoPullback ξ a).hom ≫ ·) L₁).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (fibreIsoPullback_hom_snd ξ a))

end AlgebraicGeometry.PolarizedOverSpace

end
