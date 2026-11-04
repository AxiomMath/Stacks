module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.FiniteTorDimension
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonResolved

/-!
# Stacks 0BZM

Let `R → A` and `R → R'` be homomorphisms of commutative rings and `A' = A ⊗_R R'`. If `A` is
pseudo-coherent as an `R`-module, `R'` has finite Tor dimension as an `R`-module, and `A` and
`R'` are Tor independent over `R`, then the base-change morphism of Stacks 0E29,
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')`, is an isomorphism for every `K` in `D⁺(R)`.

The proof is the source's: by Stacks 0E2A the restriction of the morphism along `R' → A'` is,
up to isomorphisms of its source and target, the derived-Hom base-change morphism of Stacks 0E1X
at the algebra `A`, which is invertible by Stacks 0A6A (4); and restriction of scalars along
`R' → A'` reflects isomorphisms.

## Main results

* `Dualizing.isIso_derivedHomBaseChange_app_of_isModulePseudoCoherent_of_finiteTorDimension` —
  **Stacks 0BZM**.
* `Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_exists` — the reduction:
  invertibility at `K` from a comparison of the restricted morphism with the morphism of
  Stacks 0E1X at the algebra.

## Implementation notes

As in the construction of the morphism of Stacks 0E29, the two derived extensions of scalars, along
`R → R'` and along `A → A'`, are arguments together with the comparison morphisms exhibiting them
as left derived functors, so the statement holds at every model of them. The comparison of
Stacks 0E2A is `Dualizing.exists_restrictScalars_map_derivedHomBaseChange_app_eq`.

The hypotheses are the source's in the library's spellings: pseudo-coherence of `A` as an
`R`-module is `StacksDraft.PseudoCoherence.IsModulePseudoCoherent`, finite Tor dimension of `R'`
as an `R`-module is `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension` read off a certified
derived tensor product as in Stacks 0652, Tor independence is
`RingTheory.TorIndependence.TorIndependent`, and `D⁺(R)` is the `plus` part of the standard
t-structure.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe uR uA uRp v

namespace Dualizing

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

/-- The reduction of Stacks 0BZM to Stacks 0E2A: if the restriction along `R' → A ⊗_R R'` of the
base-change morphism of Stacks 0E29 at `K` is, up to isomorphisms of source and target, the
derived-Hom base-change morphism of Stacks 0E1X at the algebra `A`, then the hypotheses of
Stacks 0BZM make it invertible at `K`. -/
theorem isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_exists
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension D.tensor D.comparison
      D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v uR uA uRp} R)).plus K)
    (hEx : ∃ (sIso : _ ≅ baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom R).obj
            (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), K)))
      (tIso : _ ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom R').obj
          (Opposite.op (baseChangeR.obj
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))), baseChangeR.obj K)),
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        sIso.hom ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫ tIso.inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) := by
  obtain ⟨sIso, tIso, h⟩ := hEx
  exact isIso_derivedHomBaseChange_app_of_comparison hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA K _ sIso tIso h
    (isIso_derivedHomBaseChangeAtAlgebra_of_finiteTorDimension baseChangeR comparisonR
      isLeftDerivedR D hFinite hA K hK.choose hK.choose_spec)

/-- **Stacks 0BZM.** Let `R → A` and `R → R'` be homomorphisms of commutative rings and
`A' = A ⊗_R R'`. If `A` is pseudo-coherent as an `R`-module, `R'` has finite Tor dimension as an
`R`-module, and `A` and `R'` are Tor independent over `R`, then the base-change morphism
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')` of Stacks 0E29 is an isomorphism for every
`K` in `D⁺(R)`. -/
@[stacks 0BZM]
theorem isIso_derivedHomBaseChange_app_of_isModulePseudoCoherent_of_finiteTorDimension
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) A)
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension D.tensor D.comparison
      D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{max v uR uA uRp} R)).plus K) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_exists hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA D hFinite hA K hK
    (exists_restrictScalars_map_derivedHomBaseChange_app_eq.{uR, uA, uRp, v} (hA := isLeftDerivedA)
      (hR := isLeftDerivedR) hTor baseChangeR comparisonR baseChangeA comparisonA K)

end Dualizing

end
