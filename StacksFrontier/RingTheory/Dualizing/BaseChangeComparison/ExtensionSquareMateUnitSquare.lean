module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnit

/-!
# The mate of the base-change square isomorphism, with no hypothesis left

`Dualizing.derivedBaseChangeSquareIso_mate_eq` reduces the Beck--Chevalley description of
`Dualizing.derivedBaseChangeSquareIso` to one unit identity per cochain complex of `R`-modules,
and `RingTheory.TorIndependence.unit_comp_compComparisonOfEq` proves that identity for an
arbitrary commutative square of commutative rings. This file joins the two: for

```
  R ---> A
  |      |
  v      v
  R' --> A tensor_R R'
```

at four arbitrary models of derived extension of scalars, one along each edge, the mate of the
inverse square isomorphism along the extension-of-scalars adjunctions of [stacks 0GMT] at
`R -> A` and at `R' -> A tensor_R R'` is the inverse comparison of [stacks 0661].  No Tor
independence beyond the packaging of `Dualizing.restrictionBaseChangeIsoGeneral` as an
isomorphism, and no K-flatness, is used.

## Main results

* `Dualizing.unit_comp_compComparisonOfEq` — the unit identity that
  `Dualizing.derivedBaseChangeSquareIso_mate_eq` asks for, at the base-change square.
* `Dualizing.derivedBaseChangeSquareIso_mate_eq'` — **the Beck--Chevalley description, with no
  hypothesis**: the mate of the inverse of `Dualizing.derivedBaseChangeSquareIso` is the inverse
  of `Dualizing.restrictionBaseChangeIsoGeneral`.

## Implementation notes

The general identity cannot be transported to the base-change square by `exact`.  At
`A' = A tensor_R R'` the two statements agree only up to several hundred sites of universe
spelling, and up to the route taken to `Ring (A tensor_R R')` — `CommRing.toRing` of the tensor
product's commutative ring structure on one side, `Algebra.TensorProduct.instRing` on the other.
The levels are equal and the rings are the same, so the elaborator accepts the transport, but the
kernel's recheck of that agreement does not finish inside the heartbeat budget.

What works is to rebuild the identity here, so that unification reads the models, the instances
and the universe levels off the base-change square itself.  Three restatements do it, each cheap,
and each a declaration of its own so that each carries its own budget:

* `Dualizing.restrictionBaseChangeIsoGeneral_inv_eq_includeRight` spells the inverse comparison
  of [stacks 0661] with the inclusion `R' -> A tensor_R R'` rather than with the `algebraMap` of
  `Algebra.TensorProduct.rightAlgebra`.  The two are the same morphism, and the inclusion is the
  spelling the unit identity uses.
* `Dualizing.compComparisonOfEq_app_eq_right` and `Dualizing.compComparisonOfEq_app_eq_left`
  resolve the two composite comparisons at a cochain complex. They restate and reprove
  `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq` at the square, so that
  their right-hand sides are written in the square's own spelling and rewriting with them leaves a
  goal that the remaining steps match syntactically. Rewriting with the general lemma instead
  leaves a goal in its universe spelling, on which even `CategoryTheory.Functor.map_comp` no
  longer matches.
* `Dualizing.unit_comp_compComparisonOfEq_resolved` is the identity with both composite
  comparisons already resolved; this is where the six rewrites of the general proof run.

`attribute [local instance_reducible] CochainComplex.extendScalarsLarge` is what lets the
composite comparisons of `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq` be
*written* here: their comparison arguments are typed by `extensionOfScalarsComplexGeneral`, a
chain of plain definitions over that `instance_reducible` one.

No `@[stacks]` attribute is placed here: [stacks 0661] is proved as
`RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent`, and this is a
further characterisation of it.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

open RingTheory.TorIndependence

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom
attribute [local instance_reducible] CochainComplex.extendScalarsLarge

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

include hR hA in
/-- The inverse of `Dualizing.restrictionBaseChangeIsoGeneral` is the derived comparison of
[stacks 065Z] along the square, spelled with the inclusion `R' → A ⊗_R R'` of `R`-algebras rather
than with the `algebraMap` of `Algebra.TensorProduct.rightAlgebra`. -/
theorem restrictionBaseChangeIsoGeneral_inv_eq_includeRight :
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA).inv =
      (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A)
        (algebraMap R R') (algebraMap A (TensorProduct R A R'))
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (algebraMap_tensorProduct_comp_left.trans algebraMap_tensorProduct_comp_right.symm)
        baseChangeR baseChangeA comparisonR comparisonA).2.1 :=
  rfl

omit hR hi in
/-- **The composite comparison along `R → R' → A ⊗_R R'`, resolved at a cochain complex.**  This
is `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq` at the base-change
square, restated so that its right-hand side is written in the square's own spelling of the module
universe and of the instances. -/
theorem compComparisonOfEq_app_eq_right (hcc : R →+* TensorProduct R A R')
    (hfg : (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom.comp (algebraMap R R') = hcc)
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
        max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
        (algebraMap R R')
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        baseChangeR comparisonR Fi alphai hcc hfg).app P =
      Fi.map (comparisonR.app P) ≫
        alphai.app (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom hcc hfg)
            (ComplexShape.up ℤ)).app P) := by
  subst hfg
  simp only [comp_obj, AlgHom.toRingHom_eq_coe,
    StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq,
    StacksDraft.DerivedExtensionScalarsModelComp.compComparison, eqToHom_naturality, eqToHom_refl,
    Category.id_comp, NatTrans.comp_app, extendScalarsCompInvOfEq]
  rfl

omit hf hA in
/-- **The composite comparison along `R → A → A ⊗_R R'`, resolved at a cochain complex.**  The
companion of `Dualizing.compComparisonOfEq_app_eq_right` for the top-and-right edge. -/
theorem compComparisonOfEq_app_eq_left (hcc : R →+* TensorProduct R A R')
    (hfg : (algebraMap A (TensorProduct R A R')).comp (algebraMap R A) = hcc)
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
        max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
        (algebraMap R A) (algebraMap A (TensorProduct R A R'))
        Ff alphaf baseChangeA comparisonA hcc hfg).app P =
      baseChangeA.map (alphaf.app P) ≫
        comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
          (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp} (algebraMap R A)
              (algebraMap A (TensorProduct R A R')) hcc hfg)
            (ComplexShape.up ℤ)).app P) := by
  subst hfg
  simp only [comp_obj, StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq,
    StacksDraft.DerivedExtensionScalarsModelComp.compComparison, eqToHom_refl, Category.comp_id,
    NatTrans.comp_app, extendScalarsCompInvOfEq]
  rfl

include hf hA hR hi in
/-- **The unit identity with both composite comparisons already resolved.**  At the class of a
cochain complex `P` of `R`-modules, the unit of [stacks 0GMT] along `R' → A ⊗_R R'` at
`baseChangeR(P)`, read against the resolved composite comparison along `R → R' → A ⊗_R R'`, agrees
with `baseChangeR` of the unit along `R → A`, then the derived comparison of [stacks 065Z], then
the resolved composite comparison along `R → A → A ⊗_R R'`.

Nothing is assumed beyond the four models: no Tor independence, no K-flatness. -/
theorem unit_comp_compComparisonOfEq_resolved
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi
      alphai).unit.app
          (baseChangeR.obj (DerivedCategory.Q.obj P)) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} (Algebra.TensorProduct.includeRight : R' →ₐ[R]
          TensorProduct R A R').toRingHom).mapDerivedCategory.map
          (Fi.map (comparisonR.app P) ≫
            alphai.app (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
                  (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
                  (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
                (ComplexShape.up ℤ)).app P)) =
      baseChangeR.map ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
        alphaf).unit.app
            (DerivedCategory.Q.obj P)) ≫
        (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A) (algebraMap R R')
          (algebraMap A (TensorProduct R A R')) (Algebra.TensorProduct.includeRight : R' →ₐ[R]
          TensorProduct R A R').toRingHom (algebraMap_tensorProduct_comp_left.trans
          algebraMap_tensorProduct_comp_right.symm)
            baseChangeR baseChangeA comparisonR comparisonA).2.1.app (Ff.obj (DerivedCategory.Q.obj
              P)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} (Algebra.TensorProduct.includeRight : R'
            →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            (baseChangeA.map (alphaf.app P) ≫
              comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  (extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp} (algebraMap R A)
                    (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
                    algebraMap_tensorProduct_comp_left)
                  (ComplexShape.up ℤ)).app P)) := by
  have : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uR, uRp}
      (algebraMap R R')).isLeftAdjoint
  have : (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
      (algebraMap A (TensorProduct R A R'))).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, max uA uRp}
      (algebraMap A (TensorProduct R A R'))).isLeftAdjoint
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map]
  slice_lhs 1 2 => rw [Adjunction.unit_naturality]
  slice_lhs 2 3 => rw [derivedExtensionScalarsAdjunction_unit_app.{uRp, max uA uRp, max v uR}
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
      (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)]
  simp only [Category.assoc]
  have hphii := (ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A
        R').toRingHom).mapDerivedCategoryFactors.inv.naturality
    (show ((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A
      R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R
          R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.extendScalars.{uR, max uA uRp, max v uR uA uRp} (algebraMap R (TensorProduct R A
        R'))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P from
      (NatTrans.mapHomologicalComplex
        (extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom (algebraMap
          R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
        (ComplexShape.up ℤ)).app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hphii
  slice_lhs 3 4 => rw [← hphii]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  rw [unit_comp_derivedBaseChangeComparison_fst_complex.{uR, uA, uRp, v} (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R')) (Algebra.TensorProduct.includeRight : R'
    →ₐ[R] TensorProduct R A R').toRingHom (algebraMap R (TensorProduct R A R'))
    algebraMap_tensorProduct_comp_left algebraMap_tensorProduct_comp_right
    baseChangeR baseChangeA comparisonR comparisonA P]
  have hnatC := (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R')) (Algebra.TensorProduct.includeRight : R'
    →ₐ[R] TensorProduct R A R').toRingHom
    (algebraMap_tensorProduct_comp_left.trans algebraMap_tensorProduct_comp_right.symm) baseChangeR
      baseChangeA comparisonR comparisonA).2.1.naturality (alphaf.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatC
  slice_rhs 2 3 => rw [← hnatC]
  slice_rhs 1 2 => rw [← CategoryTheory.Functor.map_comp,
    derivedExtensionScalarsAdjunction_unit_app.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf P,
    CategoryTheory.Functor.map_comp]
  have hcounit := derivedBaseChangeComparison_snd_app_comp_counit.{uR, uA, uRp, max uA uRp, v}
    (algebraMap R A) (algebraMap R R') (algebraMap A (TensorProduct R A R'))
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
      (algebraMap_tensorProduct_comp_left.trans algebraMap_tensorProduct_comp_right.symm)
      baseChangeR baseChangeA comparisonR comparisonA
    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have hstep : (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R')) (Algebra.TensorProduct.includeRight : R'
    →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap_tensorProduct_comp_left.trans algebraMap_tensorProduct_comp_right.symm)
              baseChangeR baseChangeA comparisonR comparisonA).2.1.app
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R
            A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} (Algebra.TensorProduct.includeRight : R' →ₐ[R]
          TensorProduct R A R').toRingHom).mapDerivedCategory.map
          (comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (baseChangeR.map ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R
              A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
          comparisonR.app (((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R
              A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A) (algebraMap R
              R') (algebraMap A (TensorProduct R A R')) (Algebra.TensorProduct.includeRight : R'
              →ₐ[R] TensorProduct R A R').toRingHom (algebraMap_tensorProduct_comp_left.trans
              algebraMap_tensorProduct_comp_right.symm)
              baseChangeR baseChangeA comparisonR comparisonA).1 (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R
              A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} (Algebra.TensorProduct.includeRight : R' →ₐ[R]
          TensorProduct R A R').toRingHom).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct
            R A R'))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R
              A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
    rw [← hcounit]
    simp
  slice_rhs 3 4 => rw [hstep]
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Category.assoc]
  have hnatg := comparisonR.naturality
    (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA} (algebraMap R
      A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatg
  slice_rhs 1 2 => rw [hnatg]
  have hphii2 := (ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A
        R').toRingHom).mapDerivedCategoryFactors.inv.naturality
    (show ((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R
      A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.extendScalars.{uR, max uA uRp, max v uR uA uRp} (algebraMap R (TensorProduct R A
        R'))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P from
      (NatTrans.mapHomologicalComplex
        (extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp} (algebraMap R A) (algebraMap A
          (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_left)
        (ComplexShape.up ℤ)).app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hphii2
  slice_rhs 4 5 => rw [← hphii2]
  slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  dsimp only [Functor.id_obj]

include hf hA hR hi in
/-- **The unit identity of `Dualizing.derivedBaseChangeSquareIso_mate_eq`, proved.**  At the class
of a cochain complex `P` of `R`-modules, the unit of [stacks 0GMT] along `R' → A ⊗_R R'` at
`baseChangeR(P)`, read against the composite comparison along `R → R' → A ⊗_R R'`, agrees with
`baseChangeR` of the unit along `R → A`, then the inverse comparison of [stacks 0661], then the
composite comparison along `R → A → A ⊗_R R'`.

Nothing is assumed beyond the four models; `hTor` enters only through the packaging of
`Dualizing.restrictionBaseChangeIsoGeneral` as an isomorphism. -/
theorem unit_comp_compComparisonOfEq
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
      (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).unit.app
            (baseChangeR.obj (DerivedCategory.Q.obj P)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
              max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
              max v uR uA uRp + 1}
              (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom
              baseChangeR comparisonR Fi alphai
              (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_right).app P) =
        baseChangeR.map
            ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).unit.app (DerivedCategory.Q.obj P)) ≫
          (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).inv.app (Ff.obj (DerivedCategory.Q.obj P)) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
              max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
              max v uR uA uRp + 1}
              (algebraMap R A) (algebraMap A (TensorProduct R A R'))
              Ff alphaf baseChangeA comparisonA
              (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_left).app P) := by
  rw [restrictionBaseChangeIsoGeneral_inv_eq_includeRight hTor baseChangeR comparisonR
      baseChangeA comparisonA,
    compComparisonOfEq_app_eq_right baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right P,
    compComparisonOfEq_app_eq_left baseChangeA comparisonA Ff alphaf
      (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left P]
  exact unit_comp_compComparisonOfEq_resolved baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai P

include hf hA hR hi in
/-- **The mate of the base-change square isomorphism is the comparison of [stacks 0661].**  The
unconditional form of `Dualizing.derivedBaseChangeSquareIso_mate_eq`: its hypothesis is
`Dualizing.unit_comp_compComparisonOfEq`.

At four arbitrary models of derived extension of scalars, one along each edge of

```
  R ---> A
  |      |
  v      v
  R' --> A tensor_R R'
```

the mate of the inverse of `Dualizing.derivedBaseChangeSquareIso` along the extension-of-scalars
adjunctions of [stacks 0GMT] at `R → A` and at `R' → A ⊗_R R'` is the inverse of
`Dualizing.restrictionBaseChangeIsoGeneral`, the unwhiskered comparison of [stacks 0661].  No
K-flatness is used, and no Tor independence beyond the packaging of that comparison as an
isomorphism. -/
theorem derivedBaseChangeSquareIso_mate_eq' :
    mateEquiv
        (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
        (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
        (TwoSquare.mk _ _ _ _
          (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
            comparisonR Fi alphai).inv) =
      TwoSquare.mk _ _ _ _
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR
          baseChangeA comparisonA hA).inv :=
  derivedBaseChangeSquareIso_mate_eq hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai
    (unit_comp_compComparisonOfEq hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai)

end Dualizing

end
