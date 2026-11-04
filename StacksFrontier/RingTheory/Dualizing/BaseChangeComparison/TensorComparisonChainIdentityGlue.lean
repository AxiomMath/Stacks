module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityBaseChange
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentitySwap

/-!
# The chain-level identity behind [stacks 0E2A], from its uniformly spelled form

`Dualizing.chainIdentity_of_aux` derives the chain-level identity behind [stacks 0E2A], in the
spelling of `CochainComplex.DerivedTensor.tensorComplex`,
`CochainComplex.DerivedTensor.extensionOfScalarsCochain` and
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso`, from the same identity with every tensor
product spelled at one universe argument, the tensor base-change isomorphism given on pure tensors,
and the comparison of [stacks 0661] and the swap of the two composition isomorphisms read through
`Dualizing.chainBaseChangeComparison` and `Dualizing.chainExtendScalarsSwap`.  The value on pure
tensors is `Dualizing.isTensorBaseChangeIso_apply_bcTmulC`.

## Implementation notes

The two statements differ by spellings that the elaborator identifies but the kernel does not
finish identifying when asked to check one against the other directly.  The goal is therefore first
rewritten, by the whole-morphism equations `Dualizing.chainExtendScalarsSwap_eq` and the defining
equation of `Dualizing.chainBaseChangeComparison`, into the shape of the hypothesis.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
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

variable [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
  (hP : CochainComplex.KFlat.{uR, max v uA uRp} P)
  (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)) [QuasiIso p]


omit [QuasiIso p] in
/-- `Dualizing.chainIdentity` from its form with uniform universe spellings and the base-change
isomorphism given on pure tensors. -/
theorem chainIdentity_of_aux
    (haux : ∀ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : HomologicalComplex.mapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) ≅
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)))
    (_he : ∀ (a b n : ℤ)
      (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
      (k : K.X a) (z : P.X b),
      (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)
            a b n hab).hom
        ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
          (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ)) n 1
        ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z))),
    e.hom ≫
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (chainExtendScalarsSwap.{uR, uA, uRp, v} K) ≫
      (extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
      (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ))
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : tensorComplex.{uRp, max uR (max v uA)}
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
      (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
        (tensorComplex.{uR, max uRp (max v uA)} K P))
    (he : IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e) :
    e.hom ≫
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA uRp} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      (NatTrans.mapHomologicalComplex
        (RingTheory.TorIndependence.derivedBaseChangeComparison
          (algebraMap R A) (algebraMap R R')
          (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
          ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
            (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
          baseChangeR baseChangeA comparisonR comparisonA).1
        (ComplexShape.up ℤ)).app
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
            (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
              (algebraMap R A)
              (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K ≫
          ((NatIso.mapHomologicalComplex
            (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom
              (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
            (ComplexShape.up ℤ)).app K).inv) ≫
      (extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
      (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) := by
  rw [← chainExtendScalarsSwap_eq.{uR, uA, uRp, v} (R' := R') K]
  have hT : (NatTrans.mapHomologicalComplex
        (RingTheory.TorIndependence.derivedBaseChangeComparison
          (algebraMap R A) (algebraMap R R')
          (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
          ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
            (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
          baseChangeR baseChangeA comparisonR comparisonA).1
        (ComplexShape.up ℤ)).app
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) =
      chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := rfl
  rw [hT]
  exact haux K e (fun a b n hab k z =>
    isTensorBaseChangeIso_apply_bcTmulC.{uR, uA, uRp, v} K P e he a b n hab k z)

end Dualizing
