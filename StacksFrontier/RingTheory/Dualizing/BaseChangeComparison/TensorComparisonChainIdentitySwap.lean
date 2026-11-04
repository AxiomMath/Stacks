module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityPieces

/-!
# The swap of the two composition isomorphisms in the chain identity behind [stacks 0E2A]

`Dualizing.chainExtendScalarsSwap` is the composite, on complexes, of the two composition
isomorphisms of extensions of scalars around the square `R → A → A ⊗_R R' ← R' ← R`.  This file
computes it on the pure tensors `1 ⊗ (u ⊗ k)`, which is the third piece of
`Dualizing.chainIdentity`.

## Main results

* `Dualizing.extendScalarsComp_swap_f_bcTmulC` — the value on pure tensors for an arbitrary
  commutative square of ring maps.
* `Dualizing.chainExtendScalarsSwap_f` — the components of `Dualizing.chainExtendScalarsSwap`.
* `Dualizing.chainIdentity_piece₃` — the value of `Dualizing.chainExtendScalarsSwap` on
  `1 ⊗ (u ⊗ k)`.

## Implementation notes

Two kernel-level points decide the shape of the proofs.  The components of
`Dualizing.chainExtendScalarsSwap` are obtained by `congrArg` from the equation of whole
morphisms `Dualizing.chainExtendScalarsSwap_eq`, not by unfolding the definition under the
projection `HomologicalComplex.Hom.f`, which the kernel does not finish.  And the square lemma is
applied in the form `Dualizing.extendScalarsComp_swap_f_bcTmulC_tensorProduct`, whose target ring
is `A ⊗_R R'` itself: instantiating the version over an arbitrary commutative ring `B` leaves the
kernel to identify the ring structure `CommRing B` supplies on `A ⊗_R R'` with
`Algebra.TensorProduct.instSemiring`, through which the composition isomorphisms are typed, and
that identification does not finish either.

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


/-- The two composition isomorphisms of extensions of scalars around `R → A → B ← R' ← R`, on
complexes, carry `1 ⊗ (u ⊗ k)` to `h(u) ⊗ (1 ⊗ k)`. -/
theorem extendScalarsComp_swap_f_bcTmulC {B : Type (max uA uRp)} [CommRing B] (h : A →+* B)
    (i : R' →+* B) (hc : R →+* B) (hfh : h.comp (algebraMap R A) = hc)
    (hgi : i.comp (algebraMap R R') = hc)
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ) (u : A) (k : K.X a) :
    (((NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
        (algebraMap R A) h hc hfh) (ComplexShape.up ℤ)).app K).f a ≫
    (((NatIso.mapHomologicalComplex
      (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R') i hc hgi)
      (ComplexShape.up ℤ)).app K).inv).f a).hom
      (bcTmulC.{uA, max uA uRp, max v uR uA uRp} h
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a 1 (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k)) =
      bcTmulC.{uRp, max uA uRp, max v uR uA uRp} i
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a (h u)
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k) := by
  have h₁ := extendScalarsCompInvOfEq_app_bcTmul.{uR, uA, max uA uRp, max v uRp} (algebraMap R A)
    h hc hfh (K.X a) 1 u k
  rw [one_mul] at h₁
  have h₂ := extendScalarsCompIsoOfEq_inv_app_bcTmul.{uR, uRp, max uA uRp, max v uA}
    (algebraMap R R') i hc hgi (K.X a) (h u) k
  exact ModuleCat_hom_comp₂_eq h₁ h₂

/-- `Dualizing.extendScalarsComp_swap_f_bcTmulC` with the target ring the pushout
`A ⊗_R R'` itself, so that its ring structure is the one `Dualizing.chainExtendScalarsSwap` is
typed with. -/
theorem extendScalarsComp_swap_f_bcTmulC_tensorProduct (h : A →+* TensorProduct R A R')
    (i : R' →+* TensorProduct R A R') (hc : R →+* TensorProduct R A R')
    (hfh : h.comp (algebraMap R A) = hc)
    (hgi : i.comp (algebraMap R R') = hc)
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ) (u : A) (k : K.X a) :
    (((NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
        (algebraMap R A) h hc hfh) (ComplexShape.up ℤ)).app K).f a ≫
    (((NatIso.mapHomologicalComplex
      (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R') i hc hgi)
      (ComplexShape.up ℤ)).app K).inv).f a).hom
      (bcTmulC.{uA, max uA uRp, max v uR uA uRp} h
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a 1 (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k)) =
      bcTmulC.{uRp, max uA uRp, max v uR uA uRp} i
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a (h u)
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k) :=
  extendScalarsComp_swap_f_bcTmulC h i hc hfh hgi K a u k

/-- `Dualizing.chainExtendScalarsSwap` is the composite of the two composition isomorphisms of
extensions of scalars on complexes it is defined as. -/
theorem chainExtendScalarsSwap_eq (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    chainExtendScalarsSwap.{uR, uA, uRp, v} K = (NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
        (algebraMap R A)
        (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K ≫
    ((NatIso.mapHomologicalComplex
      (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom
        (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
      (ComplexShape.up ℤ)).app K).inv := rfl

/-- The component of `Dualizing.chainExtendScalarsSwap` in degree `a` is the composite of the
components of the two composition isomorphisms. Obtained from `Dualizing.chainExtendScalarsSwap_eq`
rather than by unfolding under the projection, which the kernel does not finish. -/
theorem chainExtendScalarsSwap_f (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ) :
    (chainExtendScalarsSwap.{uR, uA, uRp, v} K).f a = ((NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
        (algebraMap R A)
        (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K).f a ≫
    (((NatIso.mapHomologicalComplex
      (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom
        (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
      (ComplexShape.up ℤ)).app K).inv).f a :=
  (congrArg (fun φ => HomologicalComplex.Hom.f φ a) (chainExtendScalarsSwap_eq K)).trans
    (HomologicalComplex.comp_f _ _ a)

/-- The third piece of the chain identity: the two composition isomorphisms of extensions of
scalars carry `1 ⊗ (u ⊗ k)` to `u ⊗ (1 ⊗ k)`. -/
theorem chainIdentity_piece₃ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (u : A) (k : K.X a) :
    ((chainExtendScalarsSwap.{uR, uA, uRp, v} K).f a).hom
      (bcTmulC.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R'))
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) a 1 (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A) u k)) =
      bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        a (algebraMap A (TensorProduct R A R') u)
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k) := by
  rw [chainExtendScalarsSwap_f]
  exact extendScalarsComp_swap_f_bcTmulC_tensorProduct (algebraMap A (TensorProduct R A R'))
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left
    algebraMap_tensorProduct_comp_right K a u k

end Dualizing
