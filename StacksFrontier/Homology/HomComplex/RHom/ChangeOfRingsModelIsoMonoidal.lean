module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorHomTranspose
public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTransposeLocalization

/-!
# The representative model comparison of [stacks 0E1W] through the monoidality isomorphism

`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` is the factor through which the
morphism of [stacks 0E1X] reads the change-of-rings isomorphism of [stacks 0E1W]. Over a K-flat `K`
and a K-injective `I`, this file writes it as a composite whose only chain map is the monoidality
isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of degreewise extension of
scalars, together with representative isomorphisms, the chosen quasi-isomorphism `q` and the
counit of degreewise extension–restriction of scalars. It combines
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_homComplex` with
`Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_eq`, which expresses the
inverse localization of `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` through the
inverse of a [stacks 0A63] transpose.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`: the
  value of the model comparison with no Hom-complex change-of-rings map in it.

## Implementation notes

The statement is at a single universe: for `f' : ULift R →+* ULift A` the two rings and all their
modules live in one universe.

No `@[stacks]` attribute is placed here: the theorem covers no tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditiveMonoidalValue :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The representative model comparison of [stacks 0E1W] with the monoidality isomorphism
of degreewise extension of scalars as its only chain map.** Over a K-flat `K` and a K-injective
`I`, the hom of `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` is the composite
of a representative isomorphism, a component of
`CategoryTheory.Functor.mapDerivedCategoryFactors`, [stacks 0A63] data, and the inverse of the
[stacks 0A63] transpose of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` followed by
the uncurried counit and `q`. -/
public theorem derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso
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
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
            DerivedCategory.Q.map W)) :=
      isIso_homEquiv_symm_tensorIso f K J I q hK
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK).hom =
      (BaseChange.homModelIso K I (Iso.refl _)
          ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
            @asIso _ _ _ _ (DerivedCategory.Q.map q)
              ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        ((DerivedInternalHom.Model.adjunction R).homIso K I).inv ≫
          inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
              DerivedCategory.Q.map W)) ≫
            ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app Z).inv ≫
              (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
                (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
                  (asIso (α.app K)) (Iso.refl _)).inv := by
  intro adj Z P W
  have : IsIso (α.app K) := BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F α K hK
  have := BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
  rw [derivedHomChangeOfRingsModelIso_hom_eq_homComplex f F α K J I q hK,
    inv_Q_map_homComplexChangeOfRingsMap_eq f K J I q hK, Category.assoc]

end Stacks.DerivedHom.BaseChangeIso

end
