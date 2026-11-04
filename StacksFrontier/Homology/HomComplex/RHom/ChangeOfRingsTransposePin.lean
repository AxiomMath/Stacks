module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTransposeLocalization

/-!
# Pinning the transpose of a chain map that presents a morphism of the derived category

`Stacks.DerivedHom.BaseChangeIso.exists_uncurry_unit_value` factors a chain map
`w : X ⟶ Hom^._A(A (x)_R K₀, J)|_R` as the degreewise unit of extension of scalars followed by the
restriction of a transpose `t`, and evaluates the [stacks 0A63] uncurrying of `w` in terms of `t`.
It produces `t` existentially.

The transpose of [stacks 0GMT] localizes unconditionally, by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_Q_map`, so the
localization of `t`, read through the comparison of the chosen model with degreewise extension of
scalars, is the inverse derived transpose of the localization of `w`.  At a K-flat `X` that
comparison is invertible and the equation solves for `DerivedCategory.Q.map t` outright.

The localized uncurrying is then determinate as well: uncurrying localizes to the derived
transpose of [stacks 0A63] at a K-flat Hom-source and a K-injective target, by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`, and `A (x)_R K₀` is K-flat
whenever `K₀` is.  So a morphism of the derived category presented by `w` determines
`DerivedCategory.Q.map (uncurry t)` with no existential left in it.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.comparison_app_comp_Q_map_eq_homEquiv_symm` — **the transpose,
  pinned**: the comparison at `X` followed by the localization of `t` is the inverse derived
  transpose of [stacks 0GMT] of the localization of `w`, read through
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.
* `Stacks.DerivedHom.BaseChangeIso.Q_map_uncurry_eq_homEquiv` — **the localized uncurrying as a
  derived transpose**: `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`
  solved for the uncurrying.
* `Stacks.DerivedHom.BaseChangeIso.Q_map_uncurry_eq_of_unit_comp` — the two together: the
  localized uncurrying of the transpose of `w`, valued in the localization of `w` alone.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChangeIso

universe u wR wA

section Uncurry

variable {A : Type u} [CommRing A] [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

/-- **The localized uncurrying of a chain map, as a derived transpose of [stacks 0A63].**
For K-flat `K` and K-injective `I`, the localization of the uncurrying of `t : P ⟶ Hom^.(K, I)` is
the inverse of the K-flat description of the derived tensor product followed by the derived
transpose of the localization of `t`. -/
public theorem Q_map_uncurry_eq_homEquiv
    (P K I : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) [I.IsKInjective]
    (t : P ⟶ CochainComplex.HomComplexR A K I) :
    DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry t) =
      ((DerivedInternalHom.Model.adjunction A).tensorIso P K hK).inv ≫
        DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj I)
          (DerivedCategory.Q.map t ≫ ((DerivedInternalHom.Model.adjunction A).homIso K I).inv) :=
  (Iso.eq_inv_comp _).mpr
    (DerivedInternalHom.Model.homEquiv_map_uncurry P K I hK t).symm

end Uncurry

section Transpose

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)] [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

/-- Extension of scalars along `f` is an additive functor. -/
local instance extendScalarsAdditivePin : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance extendScalarsLeftAdjointPin :
    (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint

/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance restrictScalarsRightAdjointPin :
    (ModuleCat.restrictScalars.{u, u, u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isRightAdjoint

/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance restrictScalarsLeftAdjointPin :
    (ModuleCat.restrictScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).isLeftAdjoint

variable (B : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
    (DerivedCategory (ModuleCat.{u} A)))
  (alpha : DerivedCategory.Q ⋙ B ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hB : B.IsLeftDerivedFunctor alpha
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

include hB in
/-- **The transpose of a chain map presenting a morphism, pinned.**

Let `t` be a chain map out of the degreewise extension of scalars of `X` and let `w` be the
degreewise unit at `X` followed by its restriction.  Then the comparison of the model `B` with
degreewise extension of scalars at `X`, followed by the localization of `t`, is the inverse
derived transpose of [stacks 0GMT] of the localization of `w` read through
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
public theorem comparison_app_comp_Q_map_eq_homEquiv_symm
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (W : CochainComplex (ModuleCat.{u} A) ℤ)
    (t : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X ⟶ W)
    (w : X ⟶ ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W)
    (hw : w = ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app X ≫
        ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map t) :
    alpha.app X ≫ DerivedCategory.Q.map t =
      ((derivedExtensionScalarsAdjunction.{u, u, u} f B alpha).homEquiv
          (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj W)).symm
        (DerivedCategory.Q.map w ≫
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.inv.app W) := by
  have hdeg : ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv X W t = w :=
    (CategoryTheory.Adjunction.homEquiv_unit _ X W t).trans hw.symm
  refine (Equiv.eq_symm_apply _).mpr ?_
  refine (derivedExtensionScalarsAdjunction_homEquiv_Q_map.{u, u, u} f B alpha X W t).trans ?_
  exact congrArg (fun z => DerivedCategory.Q.map z ≫
    (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.inv.app W) hdeg

include hB in
/-- **The localized uncurrying of the transpose of `w`, valued in `w` alone.**

Let `K₀` be K-flat, `J` K-injective, and suppose the comparison of `B` with degreewise extension of
scalars is invertible at `X`. If `w` is the degreewise unit at `X` followed by the restriction of
`t`, then the localization of the uncurrying of `t` is the derived transpose of [stacks 0A63] of
the inverse comparison at `X` composed with the inverse derived transpose of [stacks 0GMT] of the
localization of `w`. -/
public theorem Q_map_uncurry_eq_of_unit_comp
    (X K₀ : CochainComplex (ModuleCat.{u} R) ℤ) (hK₀ : K₀.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    [hiso : IsIso (alpha.app X)]
    (t : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ⟶
      CochainComplex.HomComplexR A
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) J)
    (w : X ⟶ ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) J))
    (hw : w = ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app X ≫
        ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map t) :
    DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry t) =
      ((DerivedInternalHom.Model.adjunction A).tensorIso
            (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)
            (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀)
            (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K₀ hK₀)).inv ≫
        DerivedInternalHom.Model.homEquiv
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X))
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀))
          (DerivedCategory.Q.obj J)
          ((inv (alpha.app X) ≫
              ((derivedExtensionScalarsAdjunction.{u, u, u} f B alpha).homEquiv
                  (DerivedCategory.Q.obj X)
                  (DerivedCategory.Q.obj (CochainComplex.HomComplexR A
                    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj K₀) J))).symm
                (DerivedCategory.Q.map w ≫
                  (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.inv.app
                    (CochainComplex.HomComplexR A
                      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K₀) J))) ≫
            ((DerivedInternalHom.Model.adjunction A).homIso
              (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K₀) J).inv) := by
  have ht : DerivedCategory.Q.map t =
      inv (alpha.app X) ≫
        ((derivedExtensionScalarsAdjunction.{u, u, u} f B alpha).homEquiv
            (DerivedCategory.Q.obj X)
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR A
              (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K₀) J))).symm
          (DerivedCategory.Q.map w ≫
            (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.inv.app
              (CochainComplex.HomComplexR A
                (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K₀) J)) :=
    (IsIso.eq_inv_comp (alpha.app X)).mpr
      (comparison_app_comp_Q_map_eq_homEquiv_symm.{u, wR, wA} f B alpha X _ t w hw)
  refine (Q_map_uncurry_eq_homEquiv.{u, wA} _ _ J
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K₀ hK₀) t).trans ?_
  exact congrArg (fun z => ((DerivedInternalHom.Model.adjunction A).tensorIso _ _
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K₀ hK₀)).inv ≫
    DerivedInternalHom.Model.homEquiv _ _ (DerivedCategory.Q.obj J)
      (z ≫ ((DerivedInternalHom.Model.adjunction A).homIso _ J).inv)) ht

end Transpose

end Stacks.DerivedHom.BaseChangeIso

end
