module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoMonoidal

/-!
# The representative model comparison of [stacks 0E1W], inverted

`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso` writes the
hom direction of the model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` of [stacks 0E1W] as a composite of
five isomorphisms, one of which is the inverse of the [stacks 0A63] transpose

`(Model.homEquiv (Q P) (Q K) (Q I)).symm (tensorIso ≫ Q W)`

of the degreewise monoidality isomorphism. This file computes the inv direction as the composite
of the inverses in the opposite order, in which that transpose occurs un-inverted.

## Main results

* `CategoryTheory.Iso.inv_eq_of_hom_eq_comp_five` — an isomorphism whose hom direction is a
  composite of five isomorphisms has for its inv direction the composite of their inverses in the
  opposite order.
* `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` — the inv
  direction of the model comparison of [stacks 0E1W], in which no `CategoryTheory.inv` occurs.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Iso

universe v u

/-- **An isomorphism given as a composite of five isomorphisms, inverted.**  If the hom direction
of `e` is `a ≫ b ≫ c ≫ d ≫ g` for isomorphisms `a`, `b`, `c`, `d`, `g`, then its inv direction is
`g⁻¹ ≫ d⁻¹ ≫ c⁻¹ ≫ b⁻¹ ≫ a⁻¹`. -/
theorem inv_eq_of_hom_eq_comp_five {C : Type u} [Category.{v} C]
    {X₁ X₂ X₃ X₄ X₅ X₆ : C} (e : X₁ ≅ X₆)
    (a : X₁ ≅ X₂) (b : X₂ ≅ X₃) (c : X₃ ≅ X₄) (d : X₄ ≅ X₅) (g : X₅ ≅ X₆)
    (h : e.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ g.hom) :
    e.inv = g.inv ≫ d.inv ≫ c.inv ≫ b.inv ≫ a.inv := by
  rw [← cancel_epi e.hom, hom_inv_id, h]
  simp

end CategoryTheory.Iso

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditiveMonoidalInverse :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The inverse of the representative model comparison of [stacks 0E1W].** It is the composite
of the inverses of the five factors of
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso` in the
opposite order, with the [stacks 0A63] transpose of the degreewise monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, followed by `q`, occurring un-inverted.
-/
public theorem derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    (hK : CochainComplex.KFlat.{u, u} K) :
    letI : IsIso (α.app K) :=
      BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F α K hK
    letI := BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := adj.homEquiv (P ⊗ K) J
        ((extendScalarsMonoidalIso f P K).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK).inv =
      (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
          (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
            (asIso (α.app K)) (Iso.refl _)).hom ≫
        ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app Z).hom ≫
          ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
              DerivedCategory.Q.map W)) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).hom ≫
              (BaseChange.homModelIso K I (Iso.refl _)
                ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
                  @asIso _ _ _ _ (DerivedCategory.Q.map q)
                    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).inv := by
  intro adj Z P W
  have : IsIso (α.app K) := BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F α K hK
  have := BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
  have : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
        (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
          DerivedCategory.Q.map W)) :=
    isIso_homEquiv_symm_tensorIso f K J I q hK
  exact CategoryTheory.Iso.inv_eq_of_hom_eq_comp_five
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK)
    (BaseChange.homModelIso K I (Iso.refl _)
      ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
        @asIso _ _ _ _ (DerivedCategory.Q.map q)
          ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance)))
    ((DerivedInternalHom.Model.adjunction R).homIso K I).symm
    (asIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
      (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
        DerivedCategory.Q.map W))).symm
    ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app Z).symm
    ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.mapIso
      (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
        (asIso (α.app K)) (Iso.refl _))).symm
    (derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso f F α K J I q hK)

end Stacks.DerivedHom.BaseChangeIso

end
