module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison

/-!
# Reducing Stacks 0E2A to one comparison square

Let `R → A` and `R → R'` be Tor-independent ring maps and `A' = A ⊗_R R'`. Stacks 0E2A asserts
that the base-change morphism
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')`
of Stacks 0E29 is invertible exactly when the tensor--Hom diagonal
`R' ⊗ᴸ_R RHom_R(A, K) ⟶ RHom_R(A, R' ⊗ᴸ_R K)`
of Stacks 0BYN is. The proof has two halves. The first is a reduction: restriction of scalars
along `R' → A'` induces a conservative functor on derived categories, so invertibility may be
checked after applying it; that half is
`Dualizing.isIso_derivedHomBaseChange_app_of_restrictScalars`. The second half is the
identification of the restricted morphism with the derived-Hom base-change morphism of
Stacks 0E1X — "unwinding the left and right hand side exactly as in the proof of Stacks 0A6A".

The morphism of Stacks 0E29 is by construction the adjoint transpose, for the derived
restriction/Hom adjunction over `R' → A'`, of the base change along `R → R'` of the evaluation
counit over `R → A`. Hence its restriction along `R' → A'`, followed by the counit of that
adjunction, *is* that base-changed counit:
`restrictScalars_map_derivedHomBaseChange_app_comp_counit`. This equation is the sentence "applying
the functor `φ'_*` to (0E29) ... we obtain the base change map" in the proof of Stacks 0E2A.

`isIso_derivedHomBaseChange_app_of_comparison` takes as a hypothesis a comparison square, an
identification of the source and the target of the restricted morphism with the source and the
target of an invertible morphism of `D(R')` under which the two morphisms agree, and concludes the
invertibility assertion of Stacks 0E29. Together with the two invertibility criteria recorded
here, which instantiate Stacks 0A6A at the algebra itself, this gives Stacks 0BZM and Stacks 0BZP
conditionally on that square.

## Main results

* `Dualizing.restrictScalars_map_derivedHomBaseChange_app_comp_counit` — the restriction along
  `R' → A'` of the morphism of Stacks 0E29, composed with the counit of the derived
  restriction/Hom adjunction, is the derived base change of the evaluation counit.
* `Dualizing.isIso_derivedHomBaseChange_app_of_comparison` — a comparison square identifying the
  restricted morphism with an invertible morphism of `D(R')` makes the morphism of Stacks 0E29
  invertible.
* `Dualizing.isIso_derivedHomBaseChangeAtAlgebra_of_isPerfect` and
  `Dualizing.isIso_derivedHomBaseChangeAtAlgebra_of_flat` — the derived-Hom base-change morphism
  of Stacks 0E1X at the algebra `A`, viewed as a degree-zero complex of `R`-modules, is
  invertible when `A` is perfect over `R`, and when `R → R'` is flat, `A` is pseudo-coherent
  over `R` and `K` is bounded below. These are Stacks 0A6A cases (1) and (3) at the arguments in
  which Stacks 0E2A needs them.

## Implementation notes

The derived extension functors and the morphisms exhibiting their universal properties are
arguments, exactly as in `Dualizing.derivedHomBaseChange`, so nothing here depends on a choice
of model for unbounded derived extension of scalars. The three rings and the module size carry
independent universe parameters; the algebra enters as the restriction of scalars of `ULift A`
over `A`, as in `Dualizing.derivedBaseChangeAlgebraIso`.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extension of scalars along a ring homomorphism `f : S →+* T` is an additive functor. -/
local instance {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T) :
    (ModuleCat.extendScalars.{uS, uT, w} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

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

/-- The restriction of scalars along `R' → A ⊗_R R'` of the base-change morphism of Stacks 0E29,
followed by the counit of the derived restriction/Hom adjunction over `R' → A ⊗_R R'`, is the
derived base change along `R → R'` of the evaluation counit `Res_A^R RHom_R(A, K) ⟶ K`. -/
theorem restrictScalars_map_derivedHomBaseChange_app_comp_counit
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
        ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
          baseChangeA comparisonA isLeftDerivedA).app K) ≫
      (derivedHomAdjunction.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).counit.app (baseChangeR.obj K) =
    (restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom.app K ≫
      baseChangeR.map
        ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K) := by
  rw [derivedHomBaseChange_eq]
  have h := ((derivedHomAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).homEquiv
      (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
      (baseChangeR.obj K)).symm_apply_apply
    ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA).hom.app K ≫
      baseChangeR.map
        ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K))
  rwa [Adjunction.homEquiv_counit] at h

/-- Invertibility of the base-change morphism of Stacks 0E29 follows from a comparison square:
an identification of the source and of the target of its restriction along `R' → A ⊗_R R'` with
the source and the target of an invertible morphism of `D(R')`. -/
theorem isIso_derivedHomBaseChange_app_of_comparison
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    {Z W : DerivedCategory (ModuleCat.{max v uR uA uRp} R')} (β : Z ⟶ W)
    (sourceIso :
      (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
        (baseChangeA.obj
          ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≅ Z)
    (targetIso :
      (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
        ((derivedHom.{uRp, max v uR, max uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).obj (baseChangeR.obj K)) ≅ W)
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        sourceIso.hom ≫ β ≫ targetIso.inv)
    (hβ : IsIso β) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) := by
  refine isIso_derivedHomBaseChange_app_of_restrictScalars hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA K ?_
  rw [hComparison]
  infer_instance

/-- **Stacks 0A6A (1)** at the arguments of Stacks 0E2A: the derived-Hom base-change morphism of
Stacks 0E1X from the algebra `A`, viewed as a degree-zero complex of `R`-modules, is invertible
for every `K` when `A` is perfect as an `R`-module. -/
theorem isIso_derivedHomBaseChangeAtAlgebra_of_isPerfect
    (hA : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
      R R')
      baseChangeR comparisonR
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K) :=
  Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap R R')
    baseChangeR comparisonR _ K (Or.inl hA)

/-- **Stacks 0A6A (3)** at the arguments of Stacks 0E2A: the derived-Hom base-change morphism of
Stacks 0E1X from the algebra `A`, viewed as a degree-zero complex of `R`-modules, is invertible
when `R → R'` is flat, `A` is pseudo-coherent as an `R`-module and `K` is bounded below. -/
theorem isIso_derivedHomBaseChangeAtAlgebra_of_flat
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
      R R')
      baseChangeR comparisonR
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K) :=
  Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap R R')
    baseChangeR comparisonR _ K (Or.inr (Or.inr (Or.inl ⟨hFlat, hA, b, hK⟩)))

/-- **Stacks 0BZP, conditional on the comparison square of Stacks 0E2A.** If the restriction
along `R' → A ⊗_R R'` of the morphism of Stacks 0E29 is identified with the derived-Hom
base-change morphism of Stacks 0E1X at the algebra `A`, then that morphism is invertible as soon
as `A` is perfect as an `R`-module. -/
theorem isIso_derivedHomBaseChange_app_of_isPerfect_of_comparison
    (hA : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (sourceIso :
      (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≅
        baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max v uR uA uRp} R).obj
            (Opposite.op
              ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
                ((ModuleCat.restrictScalars (algebraMap R A)).obj
                  (ModuleCat.of A (ULift.{max v uR uA uRp} A)))), K)))
    (targetIso :
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
            baseChangeR.obj K))
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        sourceIso.hom ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
            R R')
            baseChangeR comparisonR
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K ≫
          targetIso.inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_comparison hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA K _ sourceIso targetIso hComparison
    (isIso_derivedHomBaseChangeAtAlgebra_of_isPerfect baseChangeR comparisonR isLeftDerivedR
      hA K)

/-- **The flat case of Stacks 0BZM, conditional on the comparison square of Stacks 0E2A.** With
the same identification as in
`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_comparison`, the morphism of Stacks 0E29
is invertible when `R → R'` is flat, `A` is pseudo-coherent as an `R`-module and `K` is bounded
below. -/
theorem isIso_derivedHomBaseChange_app_of_flat_of_comparison
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b)
    (sourceIso :
      (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≅
        baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max v uR uA uRp} R).obj
            (Opposite.op
              ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
                ((ModuleCat.restrictScalars (algebraMap R A)).obj
                  (ModuleCat.of A (ULift.{max v uR uA uRp} A)))), K)))
    (targetIso :
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
            baseChangeR.obj K))
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        sourceIso.hom ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
            R R')
            baseChangeR comparisonR
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K ≫
          targetIso.inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_comparison hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA K _ sourceIso targetIso hComparison
    (isIso_derivedHomBaseChangeAtAlgebra_of_flat baseChangeR comparisonR isLeftDerivedR
      hFlat hA K b hK)

end Dualizing

end
