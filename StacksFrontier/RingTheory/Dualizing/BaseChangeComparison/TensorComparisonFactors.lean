module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictionIsoComputation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor
import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransport

/-!
# The factors of the tensor comparison at a K-flat complex

`Dualizing.tensorComparisonCompatibility_of_kFlat` reduces the obligation
`Dualizing.TensorComparisonCompatibility` to the classes of K-flat complexes of `R`-modules.  At
such a class the four factors of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` are
`pf.inv`, `Θ.inv`, `Rf'` of `γ.hom` and `pf'.hom`, and three of them were not available in the
shape the comparison reads them:

* `Dualizing.derivedBaseChangeSquareIso` had no component formula at all — only the equation
  `Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison` against the composite comparison
  along the bottom-and-right edge.  That comparison is invertible at a K-flat complex, by
  `StacksDraft.DerivedExtensionScalarsModelComp.isIso_compComparisonOfEq_app_of_kFlat`, so the
  equation determines the component there.
* `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` computes `Θ.inv` at the class of a
  complex of `A`-modules, while the comparison reads it at `Ff X`.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` computes `pf'.hom` at the class
  of a K-flat complex of `R'`-modules, while the comparison reads it at `baseChangeR X`.

Both mismatches are transports along a comparison morphism that is invertible at a K-flat
complex, and the complexes that appear — the degreewise extensions of scalars of a K-flat complex
along `R → A` and along `R → R'` — are themselves K-flat, by
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`.  This file records the two
invertibilities and the three component formulas.

## Main results

* `Dualizing.isIso_alphaf_app_of_kFlat`, `Dualizing.isIso_comparisonR_app_of_kFlat` and
  `Dualizing.isIso_comparisonA_app_extendScalars_of_kFlat` — the comparison morphisms the two
  transports divide by are invertible at a K-flat complex.
* `Dualizing.kFlat_extendScalars_algebraMap` and `Dualizing.kFlat_extendScalars_algebraMapR` —
  the two degreewise extensions of scalars of a K-flat complex are K-flat.
* `Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat` and
  `Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj` — **the component formula for the
  base-change square isomorphism** at the class of a K-flat complex, and the invertibility that
  makes the characterizing equation determine it.
* `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_of_iso` — `Θ.inv` at an arbitrary object,
  from its value at a class.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_of_iso` — `pf'.hom` at an arbitrary
  object, from its value at a class.

## Implementation notes

No `@[stacks]` attribute is placed here: `Dualizing.TensorComparisonCompatibility` is still open,
so nothing in this file covers a tag.  What is closed is the availability of its factors in the
shape the comparison consumes them.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
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

set_option linter.checkUnivs false in
/-- The comparison of the chosen model of derived extension of scalars along `R → A` is
invertible at a K-flat complex. -/
theorem isIso_alphaf_app_of_kFlat
    [hf : Ff.IsLeftDerivedFunctor alphaf
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    IsIso (alphaf.app K) :=
  CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, max v uRp}
    (algebraMap R A) Ff alphaf K hK

set_option linter.checkUnivs false in
/-- The comparison of the chosen model of derived extension of scalars along `R → R'` is
invertible at a K-flat complex. -/
theorem isIso_comparisonR_app_of_kFlat
    [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    IsIso (comparisonR.app K) :=
  CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR K hK

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

set_option linter.checkUnivs false in
/-- The degreewise extension of scalars of a K-flat complex of `R`-modules along `R → A` is
K-flat; this is [stacks 06Y1]. -/
theorem kFlat_extendScalars_algebraMap
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    CochainComplex.KFlat.{uA, max v uR uRp}
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uA, max v uRp}
    (algebraMap R A) K hK

set_option linter.checkUnivs false in
/-- The degreewise extension of scalars of a K-flat complex of `R`-modules along `R → R'` is
K-flat; this is [stacks 06Y1]. -/
theorem kFlat_extendScalars_algebraMapR
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    CochainComplex.KFlat.{uRp, max v uR uA}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uRp, max v uA}
    (algebraMap R R') K hK

include hA in
/-- The comparison of the chosen model of derived extension of scalars along
`A → A ⊗_R R'` is invertible at the degreewise extension of scalars of a K-flat complex of
`R`-modules along `R → A`: that complex is K-flat by
`Dualizing.kFlat_extendScalars_algebraMap`. -/
theorem isIso_comparisonA_app_extendScalars_of_kFlat
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    IsIso (comparisonA.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uA, max uA uRp, max v uR}
    (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA _
    (kFlat_extendScalars_algebraMap.{uR, uA, uRp, v} K hK)

include hR hi in
/-- **The composite comparison along the bottom-and-right edge of the square is invertible at a
K-flat complex.**  This is
`StacksDraft.DerivedExtensionScalarsModelComp.isIso_compComparisonOfEq_app_of_kFlat` at the two
edges `R → R'` and `R' → A ⊗_R R'`; it is what makes
`Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison` determine the component of the
square isomorphism. -/
theorem isIso_compComparisonOfEq_right_app_of_kFlat
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hP : CochainComplex.KFlat.{uR, max v uA uRp} P) :
    IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app P) :=
  @StacksDraft.DerivedExtensionScalarsModelComp.isIso_compComparisonOfEq_app_of_kFlat.{uR,
      uRp, max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
    R R' (TensorProduct R A R') _ _ _ _ _ _
    (algebraMap R R')
    (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom
    baseChangeR comparisonR Fi alphai hR hi
    (algebraMap R (TensorProduct R A R'))
    algebraMap_tensorProduct_comp_right P hP

include hf hA hR hi in
/-- **The component formula for the base-change square isomorphism at a K-flat complex.**
`Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison` says that the component at the
class of `P`, followed by the composite comparison along `R → R' → A ⊗_R R'`, is the composite
comparison along `R → A → A ⊗_R R'`.  The former is invertible at a K-flat `P`, by
`Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`, so the equation determines the component
outright.

This is the component formula the base-change square isomorphism did not have. -/
theorem derivedBaseChangeSquareIso_hom_app_q_obj
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app P)] :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
          Fi alphai).hom.app (DerivedCategory.Q.obj P) =
      (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
          max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
          max v uR uA uRp + 1}
          (algebraMap R A) (algebraMap A (TensorProduct R A R'))
          Ff alphaf baseChangeA comparisonA
          (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_left).app P ≫
        CategoryTheory.inv
          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
            max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
            max v uR uA uRp + 1}
            (algebraMap R R')
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom
            baseChangeR comparisonR Fi alphai
            (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_right).app P) := by
  rw [← derivedBaseChangeSquareIso_hom_app_comp_comparison Ff alphaf baseChangeA comparisonA
      baseChangeR comparisonR Fi alphai P,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The comparison of [stacks 0661] at an arbitrary object, from its value at a class.**
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` computes the inverse comparison at the
class of a complex of `A`-modules; the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` reads it at `Ff X` instead.  Any
isomorphism of the two objects transports the value, by naturality.

Taken with `Dualizing.isIso_alphaf_app_of_kFlat`, which supplies the isomorphism
`Ff (Q K) ≅ Q (A ⊗_R K)` for a K-flat `K`, and
`Dualizing.isIso_comparisonA_app_extendScalars_of_kFlat`, which discharges the hypothesis of
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` at `A ⊗_R K`, this evaluates `Θ.inv` at
the object the comparison reads it at. -/
theorem restrictionBaseChangeIsoGeneral_inv_app_of_iso
    (Y : DerivedCategory (ModuleCat.{max v uR uA uRp} A))
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ)
    (e : Y ≅ DerivedCategory.Q.obj K) :
    (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
          baseChangeA comparisonA hA).inv.app Y =
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory ⋙ baseChangeR).map e.hom ≫
        (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).inv.app (DerivedCategory.Q.obj K) ≫
          (baseChangeA ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map e.inv :=
  Stacks.DerivedHom.BaseChange.natTrans_app_eq_of_iso
    (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
      baseChangeA comparisonA hA).inv e

include hi in
/-- **The projection formula over `R'` at an arbitrary object, from its value at a class.**
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` computes the component at the
class of a K-flat complex of `R'`-modules; the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` reads it at `baseChangeR X` instead.  Any
isomorphism of the two objects transports the value, by naturality.

Taken with `Dualizing.isIso_comparisonR_app_of_kFlat`, which supplies the isomorphism
`baseChangeR (Q K) ≅ Q (R' ⊗_R K)` for a K-flat `K`, and
`Dualizing.kFlat_extendScalars_algebraMapR`, which says that `R' ⊗_R K` is K-flat over `R'` and so
discharges the hypothesis of
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`, this evaluates `pf'.hom` at the
object the comparison reads it at. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_of_iso
    (Y : DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R') ℤ)
    (e : Y ≅ DerivedCategory.Q.obj K) :
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app Y =
      (Fi ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map e.hom ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
            (DerivedCategory.Q.obj K) ≫
          (derivedExtendRestrictScalarsTensorFunctor.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).map e.inv :=
  Stacks.DerivedHom.BaseChange.natTrans_app_eq_of_iso
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom e

end Dualizing

end
