module
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BaseChangeSquareModels
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMateDualizing

/-!
# The base-change square iso of models is the mate of the comparison of Stacks 0661, reduced

`Dualizing.derivedBaseChangeSquareIso` compares the two ways of extending scalars around

```
  R ---> A
  |      |
  v      v
  R' --> A tensor_R R'
```

at four arbitrary models. This file reduces the statement that the Beck--Chevalley mate of its
inverse, along the extension-of-scalars adjunctions of [stacks 0GMT] at `R -> A` and at
`R' -> A tensor_R R'`, is the inverse of the comparison `Dualizing.restrictionBaseChangeIsoGeneral`
of [stacks 0661], to one identity per cochain complex of `R`-modules. The projection-formula
compatibility of [stacks 0E2A] reads the square isomorphism through this mate. Along `R -> R'`
and `A -> A tensor_R R'` the corresponding mate is the comparison of [stacks 065Z],
`RingTheory.TorIndependence.derivedBaseChangeMate_eq`.

The remaining identity says that the unit of [stacks 0GMT] along `R' -> A tensor_R R'`, read
against the composite comparison along `R -> R' -> A tensor_R R'`, agrees with the unit along
`R -> A` pushed through the comparison of [stacks 0661], read against the composite comparison
along `R -> A -> A tensor_R R'`. It is `Dualizing.unit_comp_compComparisonOfEq`, and the
unconditional form of the reduction is `Dualizing.derivedBaseChangeSquareIso_mate_eq'`, both in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnitSquare`.

## Main results

* `Dualizing.derivedBaseChangeSquareIso_mate_eq`: granted the per-complex unit identity, the mate
  of the inverse square isomorphism is the inverse comparison of [stacks 0661].

## Implementation notes

`attribute [local instance_reducible] CochainComplex.extendScalarsLarge` lets the composite
comparisons `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq` be written here:
their comparison arguments are typed by `extensionOfScalarsComplexGeneral`, a chain of plain
definitions over that `instance_reducible` one, and without the attribute the section variables
`comparisonR` and `comparisonA` are rejected at that position.

The two `Functor.IsLeftDerivedFunctor` arguments of `Dualizing.restrictionBaseChangeIsoGeneral`
are taken from the instance binders, so that they agree on the nose with the ones
`Dualizing.unit_comp_restrictionBaseChangeIsoGeneral_inv` resolves.

No `@[stacks]` attribute is placed here: the theorem is conditional on the unit identity.

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

include hf hA hR hi in
/-- **The mate of the base-change square isomorphism is the comparison of [stacks 0661], granted
one unit identity per cochain complex.**

The hypothesis `hunit` says: at the class of a cochain complex `P` of `R`-modules, the unit of
[stacks 0GMT] along `R' → A ⊗_R R'` at `baseChangeR(P)`, read against the composite comparison
along `R → R' → A ⊗_R R'`, agrees with `baseChangeR` of the unit along `R → A`, then the inverse
comparison of [stacks 0661], then the composite comparison along `R → A → A ⊗_R R'`. -/
theorem derivedBaseChangeSquareIso_mate_eq
    (hunit : ∀ P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
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
              algebraMap_tensorProduct_comp_left).app P)) :
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
          baseChangeA comparisonA hA).inv := by
  have : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uR, uRp}
      (algebraMap R R')).isLeftAdjoint
  have : (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
      (algebraMap A (TensorProduct R A R'))).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, max uA uRp}
      (algebraMap A (TensorProduct R A R'))).isLeftAdjoint
  have htower := (IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
    (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R'))
  have hmate := RingTheory.TorIndependence.derivedBaseChangeMate_eq.{uR, uA, uRp,
      max uA uRp, v}
    (algebraMap R A) (algebraMap R R') (algebraMap A (TensorProduct R A R'))
    (algebraMap R' (TensorProduct R A R'))
    htower
    baseChangeR baseChangeA comparisonR comparisonA
  have h0 : (mateEquiv
        (derivedExtensionScalarsAdjunction.{uA, max uA uRp, max v uR}
          (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA)
        (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
          (algebraMap R R') baseChangeR comparisonR)).symm
        (TwoSquare.mk _ _ _ _
          (RingTheory.TorIndependence.restrictSquareDerivedIso.{uR, uA, uRp, max uA uRp, v}
            (algebraMap R A) (algebraMap R R') (algebraMap A (TensorProduct R A R'))
            (algebraMap R' (TensorProduct R A R'))
            htower).hom) =
      TwoSquare.mk _ _ _ _
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR
          baseChangeA comparisonA hA).inv := by
    rw [restrictionBaseChangeIsoGeneral_inv_eq.{uR, uA, uRp, v} hTor baseChangeR comparisonR
      baseChangeA comparisonA]
    exact hmate
  refine (mateEquiv
      (derivedExtensionScalarsAdjunction.{uA, max uA uRp, max v uR}
        (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA)
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR)).injective ?_
  rw [← h0, Equiv.apply_symm_apply]
  refine Eq.trans (iterated_mateEquiv_conjugateEquiv
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR)
    (derivedExtensionScalarsAdjunction.{uA, max uA uRp, max v uR}
      (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA) _) ?_
  refine (Equiv.eq_symm_apply _).mp ?_
  refine derivedBaseChangeSquare_hom_ext Ff alphaf baseChangeA comparisonA _ _ _ fun P => ?_
  refine ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR).comp
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)).homEquiv _ _ |>.injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hiso := derivedBaseChangeSquareIso_hom_app_comp_comparison Ff alphaf baseChangeA
    comparisonA baseChangeR comparisonR Fi alphai P
  have hcancel : ∀ {Z : DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R'))}
      (w : (baseChangeR ⋙ Fi).obj (DerivedCategory.Q.obj P) ⟶ Z),
      (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app (DerivedCategory.Q.obj P) ≫
          (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).hom.app (DerivedCategory.Q.obj P) ≫ w = w := by
    intro Z w
    rw [← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]
  have hinv := Eq.trans (congrArg (fun z =>
      (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
        Fi alphai).inv.app (DerivedCategory.Q.obj P) ≫ z) hiso.symm) (hcancel _)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hinv]
  have hu := unit_conjugateEquiv_symm
    ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf).comp
      (derivedExtensionScalarsAdjunction.{uA, max uA uRp, max v uR}
        (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA))
    ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR).comp
      (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai))
    (TwoSquare.mk _ _ _ _
      (RingTheory.TorIndependence.restrictSquareDerivedIso.{uR, uA, uRp, max uA uRp, v}
        (algebraMap R A) (algebraMap R R') (algebraMap A (TensorProduct R A R'))
        (algebraMap R' (TensorProduct R A R'))
        htower).hom)
    (DerivedCategory.Q.obj P)
  refine Eq.trans ?_ (congrArg (fun z => z ≫
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp}
          (algebraMap R R')).mapDerivedCategory).map
      ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq
          (algebraMap R A) (algebraMap A (TensorProduct R A R'))
          Ff alphaf baseChangeA comparisonA
          (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_left).app P)) hu)
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  simp only [CategoryTheory.Functor.comp_map, Category.assoc]
  have hbeta := unit_comp_restrictionBaseChangeIsoGeneral_inv hTor baseChangeR
    comparisonR baseChangeA comparisonA (Ff.obj (DerivedCategory.Q.obj P))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hbeta ⊢
  slice_rhs 2 3 => rw [← hbeta]
  slice_rhs 1 2 => rw [← Adjunction.unit_naturality]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun z => (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR).unit.app (DerivedCategory.Q.obj P) ≫
    (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R R')).mapDerivedCategory.map z)
    (hunit P)

end Dualizing

end
