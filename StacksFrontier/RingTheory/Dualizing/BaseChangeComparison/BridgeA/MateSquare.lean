module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.MateReduction

/-!
# The comparison square for derived-Hom base change

Let `R → A` and `R → R'` be Tor independent. This file identifies the source and the target of
the restriction along `R' → A ⊗_R R'` of the derived-Hom base-change morphism
`Dualizing.derivedHomBaseChange` with the source and the target of the base-change morphism
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` for derived internal Homs over `R`.
Given that the resulting square commutes, `Dualizing.derivedHomBaseChange` is an isomorphism when
`A` is perfect over `R`, and when `R → R'` is flat, `A` is pseudo-coherent over `R` and `K` is
bounded below.

## Main definitions

* `Dualizing.mateSourceIso` — the source identification: restriction along `R' → A ⊗_R R'` of the
  derived base change of `RHom_R(A, K)` is the derived base change of the internal Hom
  `RHom_R(A, K)`.
* `Dualizing.mateTargetIso` — the target identification: restriction along `R' → A ⊗_R R'` of
  `RHom_{R'}(A ⊗_R R', K ⊗ᴸ_R R')` is the internal Hom over `R'` out of the derived base change
  of the algebra.

## Main results

* `Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare` — if `A` is perfect over
  `R` and the comparison square commutes, the derived-Hom base-change morphism is invertible.
* `Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_mateSquare` — the same when `R → R'` is
  flat, `A` is pseudo-coherent over `R` and `K` is bounded below.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

namespace Dualizing

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
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

/-- The source identification of the comparison square: the restriction along `R' → A ⊗_R R'` of
the derived base change of `RHom_R(A, K)` is the derived base change of the derived internal Hom
out of the algebra. -/
noncomputable def mateSourceIso
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
      (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≅
    baseChangeR.obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max v uR uA uRp} R).obj
        (Opposite.op
          ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (ModuleCat.of A (ULift.{max v uR uA uRp} A)))), K)) :=
  (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
      isLeftDerivedA).app K ≪≫
    baseChangeR.mapIso
      ((derivedHomRestrictScalarsInternalHomIsoCanonical.{uR, uA, max v uRp}
        (algebraMap R A)).app K)

/-- The target identification of the comparison square: the restriction along `R' → A ⊗_R R'` of
`RHom_{R'}(A ⊗_R R', K ⊗ᴸ_R R')` is the derived internal Hom over `R'` out of the derived base
change of the algebra. -/
noncomputable def mateTargetIso
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
      ((derivedHom.{uRp, max v uR, max uA uRp}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).obj (baseChangeR.obj K)) ≅
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uRp, max v uR uA uRp} R').obj
      (Opposite.op
        (baseChangeR.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (ModuleCat.of A (ULift.{max v uR uA uRp} A))))),
        baseChangeR.obj K) :=
  (derivedHomRestrictScalarsInternalHomIsoCanonical.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).app (baseChangeR.obj K) ≪≫
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uRp, max v uR uA uRp} R').mapIso
      (Iso.prod
        (Iso.op (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
          baseChangeA comparisonA isLeftDerivedA))
        (Iso.refl (baseChangeR.obj K)))

/-- If `A` is perfect as an `R`-module and the comparison square `hComparison`, built from
`Dualizing.mateSourceIso` and `Dualizing.mateTargetIso`, commutes, then the derived-Hom
base-change morphism at `K` is an isomorphism. -/
theorem isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare
    (hA : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        (mateSourceIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).hom ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
            R R')
            baseChangeR comparisonR
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K ≫
          (mateTargetIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_isPerfect_of_comparison hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hA K _ _ hComparison

/-- If `R → R'` is flat, `A` is pseudo-coherent over `R`, `K` is bounded below and the
comparison square `hComparison` commutes, then the derived-Hom base-change morphism at `K` is an
isomorphism. -/
theorem isIso_derivedHomBaseChange_app_of_flat_of_mateSquare
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b)
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        (mateSourceIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).hom ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
            R R')
            baseChangeR comparisonR
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K ≫
          (mateTargetIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_flat_of_comparison hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hFlat hA K b hK _ _ hComparison

end Dualizing

end
