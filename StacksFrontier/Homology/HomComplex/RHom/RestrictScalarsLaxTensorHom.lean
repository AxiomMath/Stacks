module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorSide
public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorAssoc

/-!
# The lax monoidal structure map of restriction of scalars against the internal Hom

Let `f : R → A` be a homomorphism of commutative rings, `K` a complex of `R`-modules, `J` a
complex of `A`-modules and `q : J|_R ⟶ I` a map of complexes of `R`-modules. Write
`ρ : X|_R ⊗_R Y|_R ⟶ (X ⊗_A Y)|_R` for the lax monoidal structure map
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars on cochain
complexes, `Z = Hom_A(A ⊗_R K, J)` for the internal Hom complex over `A` and `P = Z|_R`. This file
computes the **restricted evaluation**

`W = (𝟙_P ⊗ₘ η_K) ≫ ρ_{Z, A ⊗_R K} ≫ (ev_{A ⊗_R K, J})|_R ≫ q`,

with `η` the unit of degreewise extension--restriction and `ev` the evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`: `W` is the uncurrying of the
Hom-side change-of-rings map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`, that is

`W = (c_q ⊗ₘ 𝟙_K) ≫ ev_{K, I}`,

the chain-level [stacks 0E1W] comparison `c_q : Z|_R ⟶ Hom_R(K, I)` tensored with the identity,
followed by the evaluation of the Hom complex over `R`. No K-flatness or K-injectivity is assumed.
As a consequence, the inverse of the model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` of [stacks 0E1W] is expressed
through `homComplexChangeOfRingsMap`, with no `ρ` left in it.

Everything here is at the equal-universe `ModuleCat.{u}` with `{R A : Type u}`. The unit
constraints of `ρ` are not proved here: degreewise extension of scalars on cochain complexes
carries no monoidal unit comparison in the library.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_uncurry_changeOfRingsMap` -- **the
  compatibility of `ρ` with the internal Hom**: the restricted evaluation is the uncurrying of
  the Hom-side change-of-rings map of [stacks 0E1W].
* `Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` -- the same
  identity with the uncurrying expanded, which displays the right-hand side as the evaluation of
  a Hom complex over `R` precomposed with the [stacks 0E1W] comparison.
* `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_changeOfRingsMap` --
  **the model comparison of [stacks 0E1W] with its transpose read as that uncurrying**.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditiveLaxTensorHom :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The lax monoidal structure map of restriction of scalars against the internal Hom.**

Let `f : R → A` be a homomorphism of commutative rings, `K` a complex of `R`-modules, `J` a
complex of `A`-modules and `q : J|_R ⟶ I` a map of complexes of `R`-modules.  Write
`Z = Hom_A(A ⊗_R K, J)` for the internal Hom complex over `A` and `P = Z|_R`.  Then the
**restricted evaluation**

`(𝟙_P ⊗ₘ η_K) ≫ ρ_{Z, A ⊗_R K} ≫ (ev_{A ⊗_R K, J})|_R ≫ q`

-- the unit of degreewise extension--restriction whiskered into the second variable, the lax
monoidal structure map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor`, the restriction of
the evaluation of `Z`, and `q` -- is the uncurrying of the Hom-side change-of-rings map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`, the chain-level map underlying the
change-of-rings isomorphism of [stacks 0E1W]. -/
public theorem restrictedEvaluation_eq_uncurry_changeOfRingsMap
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) :
    (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) ⊗ₘ
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K) ≫
      CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (DerivedInternalHom.Model.evaluationMor
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ≫ q =
      DerivedInternalHom.Model.uncurry
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) := by
  set adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  set Z := CochainComplex.HomComplexR A
    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
  set P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
  have h : adj.homEquiv P Z (adj.counit.app Z) = 𝟙 P :=
    (adj.homEquiv_unit P Z (adj.counit.app Z)).trans (adj.right_triangle_components Z)
  refine (homEquiv_monoidalIso_inv_uncurry_counit_comp f K J q).symm.trans
    ((homComplexChangeOfRingsMap_uncurry_monoidalIso f P K J I q (adj.counit.app Z)).trans ?_)
  rw [h]
  exact congrArg _ (Category.id_comp _)

/-- **The restricted evaluation as an evaluation over the smaller ring**: the evaluation over `A`
of the internal Hom complex `Hom_A(A ⊗_R K, J)`, restricted to `R` and read through the lax
monoidal structure map of restriction of scalars, is the evaluation over `R` of `Hom_R(K, I)`
precomposed with the chain-level [stacks 0E1W] comparison
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` in the first variable. -/
public theorem restrictedEvaluation_eq_tensorHom_evaluationMor
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) :
    (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) ⊗ₘ
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K) ≫
      CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (DerivedInternalHom.Model.evaluationMor
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ≫ q =
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q ⊗ₘ 𝟙 K) ≫
        DerivedInternalHom.Model.evaluationMor K I :=
  (restrictedEvaluation_eq_uncurry_changeOfRingsMap f K J I q).trans
    (DerivedInternalHom.Model.uncurry_eq_tensorHom_evaluationMor
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q))

/-- **The model comparison of [stacks 0E1W] with its transpose read as the uncurrying of the
change-of-rings map.**

The inverse of `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`, with its fourth
factor written as the inverse transpose of the uncurrying of
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`, so that neither
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` nor
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` occurs in it. -/
public theorem derivedHomChangeOfRingsModelIso_inv_eq_changeOfRingsMap
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
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK).inv =
      (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
          (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
            (asIso (α.app K)) (Iso.refl _)).hom ≫
        ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app Z).hom ≫
          ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
              DerivedCategory.Q.map
                (DerivedInternalHom.Model.uncurry
                  (BaseChange.homComplexChangeOfRingsMap f K J I q)))) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).hom ≫
              (BaseChange.homModelIso K I (Iso.refl _)
                ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
                  @asIso _ _ _ _ (DerivedCategory.Q.map q)
                    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).inv := by
  intro Z P
  rw [derivedHomChangeOfRingsModelIso_inv_eq_restrictedEvaluation f F α K J I q hK,
    restrictedEvaluation_eq_uncurry_changeOfRingsMap f K J I q]

end Stacks.DerivedHom.BaseChangeIso

end
