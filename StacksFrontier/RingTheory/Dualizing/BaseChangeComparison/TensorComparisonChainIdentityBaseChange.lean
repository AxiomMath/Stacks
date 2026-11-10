module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityPieces

/-!
# The tensor base-change isomorphism on pure tensors

A chain isomorphism `e : (R' ⊗_R K) ⊗_{R'} (R' ⊗_R P) ≅ R' ⊗_R (K ⊗_R P)` satisfying
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso` is, on each homogeneous summand, the inverse
of `TensorProduct.AlgebraTensorModule.distribBaseChange`.  This file records its value on the pure
tensors `(1 ⊗ k) ⊗ (1 ⊗ z)`, which is `1 ⊗ (k ⊗ z)`, in the form the chain-level identity behind
[stacks 0E2A] reads it.

## Main results

* `Dualizing.isTensorBaseChangeIso_apply_bcTmulC` — the value of `e` on `(1 ⊗ k) ⊗ (1 ⊗ z)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

set_option linter.checkUnivs false in
/-- The tensor base-change isomorphism on pure tensors `(1 ⊗ k) ⊗ (1 ⊗ z)`. -/
theorem isTensorBaseChangeIso_apply_bcTmulC (K P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (e : tensorComplex.{uRp, max uR (max v uA)}
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
        ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
      (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
        (tensorComplex.{uR, max uRp (max v uA)} K P))
    (he : IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e)
    (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (k : K.X a) (z : P.X b) :
    (e.hom.f n).hom ((HomologicalComplex.ιMapBifunctor
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a b n hab).hom
      ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))) =
    bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
      (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ)) n 1
      ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
        (ComplexShape.up ℤ) a b n hab).hom (k ⊗ₜ[R] z)) := by
  have h := ConcreteCategory.congr_hom (he a b n hab)
    ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P b 1 z))
  refine h.trans ?_
  have h2 := by
    let := (algebraMap R R').toAlgebra
    exact TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul (R := R) (A := R')
      (N := K.X a) (Q := P.X b) k z (1 : R') (1 : R')
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg (ConcreteCategory.hom ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
    (algebraMap R R')).map (HomologicalComplex.ιMapBifunctor K P
      (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ) a b n hab)))
    (?_ : _ = bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 (k ⊗ₜ[R] z))).trans rfl
  exact h2.trans (by rw [mul_one]; rfl)

end Dualizing
