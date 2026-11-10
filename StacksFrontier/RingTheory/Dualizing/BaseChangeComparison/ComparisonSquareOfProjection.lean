module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquare
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction

/-!
# The comparison square of [stacks 0E2A] at an arbitrary pair of projection formulas

The reduction of the comparison square of [stacks 0E2A] to the tensor-comparison obligation runs
through `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility`,
`Dualizing.projectionFormulaCompatibility_of_algebraActionSquare`,
`Dualizing.projectionFormulaCompatibility_of_algebraAction`,
`Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibility` and
`Dualizing.tensorComparisonCompatibility_of_kFlat`.  Every one of those steps is an instance of a
statement about an arbitrary square of adjunctions with projection formulas on two of its edges,
and the particular projection formula `Dualizing.derivedExtendRestrictScalarsTensorIso` is used
nowhere except as the argument passed to those statements.

This file runs the same chain with the two projection formulas, at `R → A` and at
`R' → A ⊗_R R'`, replaced by arbitrary isomorphisms `pf` and `pf'` of the same functors, and the
bridges `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` by
`Dualizing.derivedHomRestrictScalarsInternalHomIso` at `pf` and `pf'`.

## Main definitions

* `Dualizing.ProjectionFormulaCompatibilityOf` — the equality of the two transposes of the
  comparison square, at `pf` and `pf'`.
* `Dualizing.algebraActionLeftOf`, `Dualizing.algebraActionRightOf` — the two algebra actions at
  `pf'` and at `pf`.
* `Dualizing.TensorComparisonCompatibilityOf` — the tensor-comparison obligation at `pf` and
  `pf'`.

## Main results

* `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility_of_pf` —
  the comparison square, from the equality of the two transposes.
* `Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibilityOf` — the two algebra actions
  agree at `W` as soon as the obligation holds at `W|_R`.
* `Dualizing.tensorComparisonCompatibilityOf_of_kFlat` — the obligation has only to be checked at
  K-flat complexes.
* `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_pf` — **the comparison square of
  [stacks 0E2A], with the bridges at `pf` and `pf'`, from the obligation at K-flat complexes.**

## Implementation notes

The proofs are those of the canonical chain with `pf` and `pf'` passed to the abstract lemmas in
place of the two instances of `Dualizing.derivedExtendRestrictScalarsTensorIso`.  As there, the
steps are chained with `Eq.trans` and `congrArg` rather than `rw`, because several sources and
targets are definitionally but not syntactically equal.

No `@[stacks]` attribute is placed here: the obligation is still open.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

variable
  (pf : Ff ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ≅
    derivedExtendRestrictScalarsTensorFunctor.{uR, uA, max v uRp} (algebraMap R A))
  (pf' : Fi ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≅
    derivedExtendRestrictScalarsTensorFunctor.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)

section Transposes

/-- **The transpose of the right-hand side of the comparison square, at `pf`.**
`Dualizing.homEquiv_sourceIso_comp_derivedHomBaseChange` with the bridge over `R → A` built from
an arbitrary projection formula `pf`. -/
theorem homEquiv_sourceIso_comp_derivedHomBaseChange_of_pf
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj K)
        (((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom.app K ≫
            baseChangeR.map
              ((derivedHomRestrictScalarsInternalHomIso.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf pf).hom.app K)) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            (pf.inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K) :=
  DerivedHomAdjunction.homEquiv_comp_rightAdjointUniq_comp_homEquiv_symm_app
    (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R)
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R')
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
      comparisonR)
    (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR)
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A))
    pf K _

/-- **The transpose of the left-hand side of the comparison square, at `pf'`.**
`Dualizing.homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso` with the bridge over
`R' → A ⊗_R R'` built from an arbitrary projection formula `pf'`. -/
theorem homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso_of_pf
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj K)
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
              baseChangeA comparisonA hA).app K) ≫
          ((derivedHomRestrictScalarsInternalHomIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai pf').hom.app
              (baseChangeR.obj K) ≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.map
              (((derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                      baseChangeA comparisonA hA).hom.op,
                  𝟙 (baseChangeR.obj K)) :
                (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom),
                  baseChangeR.obj K) ⟶
                  (Opposite.op (baseChangeR.obj
                      (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                    baseChangeR.obj K)))) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                baseChangeA comparisonA hA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        pf'.inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            ((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom.app K ≫
              baseChangeR.map
                ((derivedHomAdjunction.{uR, uA, max v uRp}
                  (algebraMap R A)).counit.app K)) :=
  DerivedHomAdjunction.homEquiv_map_comp_rightAdjointUniq_comp_hom_map
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R')
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedHomAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)
    pf'
    ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
      baseChangeA comparisonA hA).app K)
    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA comparisonA hA)
    _
    (restrictScalars_map_derivedHomBaseChange_app_comp_counit hTor baseChangeR comparisonR
      hR baseChangeA comparisonA hA K)

/-- **The comparison square of [stacks 0E2A], from the equality of the two transposes, at `pf` and
`pf'`.** `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility`
with the two bridges built from arbitrary projection formulas. -/
theorem restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility_of_pf
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj :
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                baseChangeA comparisonA hA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        pf'.inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            ((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom.app K ≫
              baseChangeR.map
                ((derivedHomAdjunction.{uR, uA, max v uRp}
                  (algebraMap R A)).counit.app K)) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            (pf.inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)) :
    (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
        ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
          baseChangeA comparisonA hA).app K) =
      ((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).app K ≪≫
          baseChangeR.mapIso
            ((derivedHomRestrictScalarsInternalHomIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf pf).app K)).hom ≫
        Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫
          ((derivedHomRestrictScalarsInternalHomIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai pf').app
              (baseChangeR.obj K) ≪≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.mapIso
              (Iso.prod
                (Iso.op (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                  baseChangeA comparisonA hA))
                (Iso.refl (baseChangeR.obj K)))).inv := by
  have h := ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').homEquiv _ _ _).injective
    ((homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso_of_pf hTor baseChangeR
        comparisonR baseChangeA comparisonA Fi alphai pf' K).trans
      (hProj.trans (homEquiv_sourceIso_comp_derivedHomBaseChange_of_pf hTor baseChangeR
        comparisonR baseChangeA comparisonA Ff alphaf pf K).symm))
  exact ((Iso.eq_comp_inv _).2 h).trans (Category.assoc _ _ _)

end Transposes

section AlgebraAction

/-- Two composites of pairs of morphisms have equal images under a bifunctor as soon as the two
components are equal. -/
private theorem map_prod_comp_eq_of_comp_eq {C : Type*} [Category C] (T : C × C ⥤ C)
    {A B E F B' D' C₁ D : C} (f : A ⟶ B) (g : C₁ ⟶ D) (h : B ⟶ E) (k : D ⟶ F)
    (f' : A ⟶ B') (g' : C₁ ⟶ D') (h' : B' ⟶ E) (k' : D' ⟶ F)
    (hfh : f ≫ h = f' ≫ h') (hgk : g ≫ k = g' ≫ k') :
    T.map (show (A, C₁) ⟶ (B, D) from (f, g)) ≫ T.map (show (B, D) ⟶ (E, F) from (h, k)) =
      T.map (show (A, C₁) ⟶ (B', D') from (f', g')) ≫
        T.map (show (B', D') ⟶ (E, F) from (h', k')) :=
  (T.map_comp _ _).symm.trans ((congrArg T.map (Prod.ext hfh hgk)).trans (T.map_comp _ _))

/-- **The equality of the two transposes of the comparison square, at `pf` and `pf'`.**
`Dualizing.ProjectionFormulaCompatibility` with the two instances of
`Dualizing.derivedExtendRestrictScalarsTensorIso` replaced by `pf` and `pf'`; it is the hypothesis
of `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility_of_pf`. -/
def ProjectionFormulaCompatibilityOf
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) : Prop :=
  (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).hom) :
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
          baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
    pf'.inv.app
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
        ((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom.app K ≫
          baseChangeR.map
            ((derivedHomAdjunction.{uR, uA, max v uRp}
              (algebraMap R A)).counit.app K)) =
  (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      (((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom.app K,
          𝟙 (baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
          baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.obj
                ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
            baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
    derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj
          ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
      baseChangeR.map
        (pf.inv.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategory.map
            ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
              alphaf).counit.app
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
          (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)

/-- **The algebra-action square implies the projection-formula compatibility, at `pf` and
`pf'`.** `Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` with arbitrary
projection formulas: post-composing the square with the derived base change of the evaluation
counit of [stacks 0A70] is the compatibility. -/
theorem projectionFormulaCompatibilityOf_of_algebraActionSquare
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hAct :
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                baseChangeA comparisonA hA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        pf'.inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            (restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom.app K =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            (pf.inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))) :
    ProjectionFormulaCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf' K := by
  have reassoc : ∀ {W X Y Z T U : DerivedCategory (ModuleCat.{max v uR uA uRp} R')}
      (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) (e : T ⟶ U),
      a ≫ b ≫ c ≫ (d ≫ e) = (a ≫ b ≫ c ≫ d) ≫ e := by
    intros
    simp only [Category.assoc]
  refine Eq.trans (reassoc _ _ _ _ _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ baseChangeR.map
    ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)) hAct) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)) ?_
  exact congrArg (fun z => _ ≫ _ ≫ z)
    ((baseChangeR.map_comp _ _).symm.trans
      (congrArg baseChangeR.map (Category.assoc _ _ _)))

/-- The `A ⊗_R R'`-action at the projection formula `pf'`, transported by the comparison of
[stacks 0661]: `Dualizing.algebraActionLeft` with `pf'` in place of
`Dualizing.derivedExtendRestrictScalarsTensorIso`. -/
def algebraActionLeftOf :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  Functor.whiskerLeft
      (baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      ((Functor.curry.obj
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor).flip.map
        (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA).hom) ≫
    Functor.whiskerLeft
      (baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory)
      pf'.inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft baseChangeA
        (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit)
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≫
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA).hom

/-- The derived base change of the `A`-action at the projection formula `pf`, preceded by the
comparison of [stacks 0661]: `Dualizing.algebraActionRight` with `pf` in place of
`Dualizing.derivedExtendRestrictScalarsTensorIso`. -/
def algebraActionRightOf :
    algebraActionSource baseChangeR baseChangeA ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory ⋙
        baseChangeR :=
  Functor.whiskerRight
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA).hom
      ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensorAt
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
    Functor.whiskerLeft
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory)
        (derivedTensorBaseChangeSquare.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
          comparisonR (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory)
            pf.inv ≫
          Functor.whiskerRight
            (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).counit
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory))
        baseChangeR

/-- **The component of `Dualizing.algebraActionLeftOf`.** -/
theorem algebraActionLeftOf_app (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf').app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W)),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                baseChangeA comparisonA hA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj W),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        pf'.inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W)) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj W)) ≫
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR
              baseChangeA comparisonA hA).hom.app W :=
  rfl

/-- **The component of `Dualizing.algebraActionRightOf`.** -/
theorem algebraActionRightOf_app (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf).app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR
                baseChangeA comparisonA hA).hom.app W,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj W),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            (pf.inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app W)) :=
  rfl

/-- **The compatibility at every object, from the equality of the two algebra actions, at `pf`
and `pf'`.** -/
theorem projectionFormulaCompatibilityOf_of_algebraAction
    (h : algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf' =
      algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf' K := by
  refine projectionFormulaCompatibilityOf_of_algebraActionSquare hTor baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai pf pf' K ?_
  rw [restrictionBaseChangeIso_hom_app hTor baseChangeR comparisonR hR baseChangeA
    comparisonA hA K]
  exact congrArg (fun z => NatTrans.app z
    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) h

/-- **The two algebra actions at `pf` and `pf'` agree as soon as they agree on classes of
complexes.** -/
theorem algebraActionOf_eq_of_qObj
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
          pf').app (DerivedCategory.Q.obj X) =
        (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
          pf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf' =
      algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)) h

/-- **The two algebra actions at `pf` and `pf'` agree as soon as they agree on a resolving class
of complexes of `A`-modules.** -/
theorem algebraActionOf_eq_of_resolving
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ → Prop)
    (hres : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      ∃ (Y : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) (p : Y ⟶ X), P Y ∧ QuasiIso p)
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ, P X →
      (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
          pf').app (DerivedCategory.Q.obj X) =
        (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
          pf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf' =
      algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf := by
  refine algebraActionOf_eq_of_qObj hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai pf pf' ?_
  intro X
  obtain ⟨Y, p, hY, hp⟩ := hres X
  have := hp
  have key : (algebraActionSource baseChangeR baseChangeA).map (DerivedCategory.Q.map p) ≫
        (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
          pf').app (DerivedCategory.Q.obj X) =
      (algebraActionSource baseChangeR baseChangeA).map (DerivedCategory.Q.map p) ≫
        (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
          pf).app (DerivedCategory.Q.obj X) := by
    rw [(algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
        pf').naturality,
      (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
        pf).naturality, h Y hY]
  exact (cancel_epi _).1 key

/-- **The two algebra actions at `pf` and `pf'` agree as soon as they agree on classes of K-flat
complexes of `A`-modules.** -/
theorem algebraActionOf_eq_of_kFlat
    (h : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
          pf').app (DerivedCategory.Q.obj X) =
        (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
          pf).app (DerivedCategory.Q.obj X)) :
    algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf' =
      algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf :=
  algebraActionOf_eq_of_resolving hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai pf pf' CochainComplex.KFlat.{uA, max v uR uRp}
    (fun X => by
      obtain ⟨Y, p, hY, _, hp, _⟩ :=
        CochainComplex.KFlat.exists_kFlat_resolution.{uA, max v uR uRp} X
      exact ⟨Y, p, hY, hp⟩)
    h

end AlgebraAction

section TensorComparison

include hf hA hR hi in
/-- **The tensor-comparison obligation at `pf` and `pf'`.**
`Dualizing.TensorComparisonCompatibility` with the two instances of
`Dualizing.derivedExtendRestrictScalarsTensorIso` replaced by `pf` and `pf'`: at an object `X` of
`D(R)`, the lax monoidal structure map of derived base change at `(X, A)`, followed by the
comparison `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` built from `pf`, `pf'`, the
square isomorphism and the comparison of [stacks 0661], is tensoring the identity with the base
change of the algebra. -/
def TensorComparisonCompatibilityOf
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) : Prop :=
  derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR X
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
      Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
        pf pf'
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
          Fi alphai)
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA) X =
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 (baseChangeR.obj X),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        (baseChangeR.obj X,
            baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj X,
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom))

/-- **The two algebra actions at `pf` and `pf'` agree at an object, granted
`Dualizing.TensorComparisonCompatibilityOf` at its restriction.**
`Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibility` with arbitrary projection
formulas. -/
theorem algebraAction_app_eq_of_tensorComparisonCompatibilityOf
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A))
    (h : TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf'
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategory.obj W)) :
    (algebraActionLeftOf hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai
        pf').app W =
      (algebraActionRightOf hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf
        pf).app W := by
  rw [algebraActionLeftOf_app hTor baseChangeR comparisonR baseChangeA comparisonA Fi alphai pf' W,
    algebraActionRightOf_app hTor baseChangeR comparisonR baseChangeA comparisonA Ff alphaf pf W]
  exact Stacks.CategoryTheory.BaseChange.comp_counit_eq_of_tensorComparisonOfIso
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    pf pf'
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA comparisonA hA)
    (derivedBaseChangeSquareIso_mate_eq' hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai)
    W
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      (((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom.app W,
          𝟙 (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))))
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)))
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W)),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
      ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.obj W)
      (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
    (by
      rw [derivedExtendRestrictScalarsTensorFunctor_map]
      exact map_prod_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ _
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm))
    h


/-- **The tensor-comparison obligation at `pf` and `pf'` transfers along an isomorphism.**
`Dualizing.tensorComparisonCompatibility_of_iso` with arbitrary projection formulas: both sides
are natural in the object, by `Dualizing.derivedTensorBaseChange_naturality` and
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_naturality`. -/
theorem tensorComparisonCompatibilityOf_of_iso
    {X Y : DerivedCategory (ModuleCat.{max v uR uA uRp} R)} (e : X ≅ Y)
    (h : TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf' X) :
    TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf' Y := by
  replace h : _ = _ := h
  change _ = _
  -- naturality of the lax structure map in its first variable
  have hmu := derivedTensorBaseChange_naturality.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR e.hom
    (𝟙 (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
  rw [baseChangeR.map_id] at hmu
  -- naturality of the comparison
  have hcomp := Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_naturality pf pf'
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA) e.hom
  rw [derivedExtendRestrictScalarsTensorFunctor_map,
    derivedExtendRestrictScalarsTensorFunctor_map] at hcomp
  -- cancel the bifunctor applied to the isomorphism
  refine (Iso.cancel_iso_hom_left
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
        max v uR uA uRp + 1} R').tensor.mapIso
      ((baseChangeR.mapIso e).prod (Iso.refl (baseChangeR.obj
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))))) _ _).mp ?_
  have hpair : ((baseChangeR.mapIso e).prod (Iso.refl (baseChangeR.obj
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))))).hom =
      (baseChangeR.map e.hom,
        𝟙 (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) := rfl
  dsimp only [CategoryTheory.Functor.mapIso_hom]
  rw [hpair]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) hmu) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) hcomp) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) h) ?_
  -- both sides are the bifunctor at `(baseChangeR.map e.hom, derivedBaseChangeAlgebraIso.hom)`
  exact map_prod_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ _
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The tensor-comparison obligation at `pf` and `pf'` has only to be checked at K-flat
complexes.** Every object of `D(R)` is isomorphic to the class of a K-flat complex
(`Dualizing.exists_kFlat_iso`), and `Dualizing.tensorComparisonCompatibilityOf_of_iso` transfers
the obligation along that isomorphism. -/
theorem tensorComparisonCompatibilityOf_of_kFlat
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai pf pf' (DerivedCategory.Q.obj K))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai pf pf' X := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_kFlat_iso.{uR, max v uA uRp} X
  exact tensorComparisonCompatibilityOf_of_iso hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai pf pf' e.symm (h K hK)

end TensorComparison

section Square

/-- **The comparison square of [stacks 0E2A], with the bridges at `pf` and `pf'`, from the
tensor-comparison obligation at K-flat complexes.** The restriction along `R' → A ⊗_R R'` of the
base-change morphism of [stacks 0E29] is, under the source and target identifications built from
the bridges `Dualizing.derivedHomRestrictScalarsInternalHomIso` at `pf` and at `pf'`, the
derived-Hom base-change morphism of [stacks 0E1X], as soon as
`Dualizing.TensorComparisonCompatibilityOf` holds at the classes of K-flat complexes of
`R`-modules.

The chain: the obligation at every object (`Dualizing.tensorComparisonCompatibilityOf_of_kFlat`),
hence the equality of the two algebra actions
(`Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibilityOf`), hence the equality of the
two transposes (`Dualizing.projectionFormulaCompatibilityOf_of_algebraAction`), hence the square
(`Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility_of_pf`). -/
theorem restrictScalars_map_derivedHomBaseChange_app_eq_of_pf
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai pf pf' (DerivedCategory.Q.obj K))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
        ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
          baseChangeA comparisonA hA).app K) =
      ((restrictionBaseChangeIso hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).app K ≪≫
          baseChangeR.mapIso
            ((derivedHomRestrictScalarsInternalHomIso.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf pf).app K)).hom ≫
        Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫
          ((derivedHomRestrictScalarsInternalHomIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai pf').app
              (baseChangeR.obj K) ≪≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.mapIso
              (Iso.prod
                (Iso.op (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR
                  baseChangeA comparisonA hA))
                (Iso.refl (baseChangeR.obj K)))).inv :=
  restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility_of_pf hTor
    baseChangeR comparisonR baseChangeA comparisonA Ff alphaf Fi alphai pf pf' K
    (projectionFormulaCompatibilityOf_of_algebraAction hTor baseChangeR comparisonR baseChangeA
      comparisonA Ff alphaf Fi alphai pf pf'
      (NatTrans.ext (funext fun W =>
        algebraAction_app_eq_of_tensorComparisonCompatibilityOf hTor baseChangeR comparisonR
          baseChangeA comparisonA Ff alphaf Fi alphai pf pf' W
          (tensorComparisonCompatibilityOf_of_kFlat hTor baseChangeR comparisonR baseChangeA
            comparisonA Ff alphaf Fi alphai pf pf' h _)))
      K)

end Square

end Dualizing

end
