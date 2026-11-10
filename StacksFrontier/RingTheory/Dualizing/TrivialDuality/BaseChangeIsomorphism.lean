module

public import StacksFrontier.Homology.Devissage.DerivedHomCoproductsLargeUniverse
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityCanonical
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonResolved
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# When base change for trivial duality is an isomorphism

Let `R → A` and `R → R'` be homomorphisms of commutative rings with `A` and `R'` Tor independent
over `R`, and let `A' = A ⊗_R R'`. The canonical base-change morphism
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')`
of Stacks 0E29 is `Dualizing.derivedHomBaseChange`. This file records the two finiteness
criteria for that morphism to be invertible.

* If `A` is pseudo-coherent as an `R`-module and `R'` has finite Tor dimension as an `R`-module,
  the morphism is invertible at every bounded-below object of `D(R)`.
* If `A` is perfect as an `R`-module, the morphism is invertible at *every* object of `D(R)`,
  with no boundedness hypothesis at all — so the comparison is an isomorphism of functors.

Both follow from the criterion of Stacks 0E2A: the morphism is invertible at `K` exactly when the
tensor--Hom diagonal `RHom_R(A, K) ⊗ᴸ_R R' ⟶ RHom_R(A, K ⊗ᴸ_R R')` of Stacks 0BYN is, and
Stacks 0ATK makes that diagonal invertible — part (4) under pseudo-coherence of `A`, finite Tor
dimension of `R'` and boundedness of `K`, part (1) under perfectness of `A` alone. The second
hypothesis list is stronger and the second conclusion is stronger too: perfectness is what
removes the boundedness of `K`, and the unbounded statement is not a formal consequence of the
bounded one.

The perfect case is proved with exactly the hypotheses of its source: the comparison square of
Stacks 0E2A is supplied by
`Dualizing.exists_restrictScalars_map_derivedHomBaseChange_app_eq`. So is the pseudo-coherent
case, in
`StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChangeIsomorphismFiniteTorDimension`.
The statements of the pseudo-coherent case recorded here carry one coherence hypothesis, `hAct`, a
compatibility of the two canonical projection formulas with the restriction/base-change
identification of Stacks 0661; see the implementation notes.

## Main results

* `Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension` — Stacks 0BZM under the
  compatibility `hAct`; the statement without it is
  `Dualizing.isIso_derivedHomBaseChange_app_of_isModulePseudoCoherent_of_finiteTorDimension`.
* `Dualizing.isIso_derivedHomBaseChange_app_of_flat` — the same with flatness of `R → R'` in
  place of finite Tor dimension, which is the example the source names.
* `Dualizing.isIso_derivedHomBaseChange_of_isPerfect` — **Stacks 0BZP**, as invertibility of the
  natural transformation, hence at every object of `D(R)` at once.
* `Dualizing.isIso_derivedHomBaseChange_of_isPerfect_of_kFlatAlgebraActionEq` — the same,
  derived instead from the hypothesis `hAct`, for the callers that supply it.

## Implementation notes

Derived extension of scalars along `R → R'` and along `A → A'` is not packaged in Mathlib for
unbounded complexes, so, exactly as in the construction of the morphism of Stacks 0E29, the two
derived base-change functors enter as arguments together with the comparison morphisms
exhibiting their universal properties. The two further models of derived extension of scalars
that the criterion of Stacks 0E2A mentions are pinned to the canonical ones.

The statements of the pseudo-coherent case carry one hypothesis beyond those of their source,
named `hAct`: the equality of the two `A`-actions `Dualizing.algebraActionLeftCanonical` and
`Dualizing.algebraActionRightCanonical` on the classes of K-flat complexes of `A`-modules. This
is the compatibility of the two projection formulas — one along `R → A`, one along `R' → A'` —
with the restriction/base-change identification of Stacks 0661, which is the step the source
proof of Stacks 0E2A performs by "unwinding the left and right hand side"; see
`Dualizing.ProjectionFormulaCompatibility`. It is a property of the Tor-independent square and
of the two derived base-change functors alone: it mentions neither the object `K`, nor any of
the finiteness hypotheses, nor the morphism whose invertibility is asserted. By
`Dualizing.algebraAction_eq_of_isZero_baseChangeAlgebra` it holds whenever `A ⊗ᴸ_R R'` vanishes.

The finiteness hypotheses are the source's, in the library's spellings: pseudo-coherence of `A`
as an `R`-module is `StacksDraft.PseudoCoherence.IsModulePseudoCoherent`, finite Tor dimension of
`R'` as an `R`-module is `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension` read off a
certified derived tensor product as in Stacks 0652, perfectness of `A` as an `R`-module is
`StacksDraft.Perfect.IsPerfectModule`, and `D⁺(R)` is the `plus` part of the standard
t-structure. Finite Tor dimension and the universe lift of the modules interact: it is read at
the module universe that the three rings force, which is stronger than reading it at the module
universe of `R'` alone.

Perfectness of `A` as an `R`-module lives at the module universe of `A`, while the criterion asks
for perfectness of the degree-zero complex on `ULift A` over `R` at the larger module universe;
`StacksDraft.Perfect.isPerfectModule_ulift` raises the universe and
`Dualizing.uliftAlgebraRestrictScalarsIso` identifies the lift of `A` as an `R`-module with the
restriction of the lift of `A` as a module over itself.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

universe uR uA uRp v w

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

/-- Perfectness of `A` as an `R`-module, in the spelling the criterion of Stacks 0A6A uses for the
algebra: the degree-zero complex on the universe lift of `A`, restricted along `R → A`, is a
perfect object of `D(R)` at a larger module universe. -/
theorem isPerfect_singleULiftAlgebra {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    [Algebra R A] (hA : StacksDraft.Perfect.IsPerfectModule (R := R) A) :
    StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max w uR uA} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max w uR uA, uA} A)))) := by
  have h : StacksDraft.Perfect.IsPerfectModule (R := R) (ULift.{max w uR uA, uA} A) :=
    StacksDraft.Perfect.isPerfectModule_ulift A hA
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{max w uR uA} R) 0).mapIso
      uliftAlgebraRestrictScalarsIso.{uR, uA, w}).symm h

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

/-- Stacks 0BZM under the compatibility `hAct` of the two projection formulas discussed in the
module documentation: if `A` is pseudo-coherent as an `R`-module, `R'` has finite Tor dimension as
an `R`-module, and `A` and `R'` are Tor independent over `R`, then the base-change morphism of
Stacks 0E29 is invertible at every object of `D⁺(R)`. The statement without `hAct` is
`Dualizing.isIso_derivedHomBaseChange_app_of_isModulePseudoCoherent_of_finiteTorDimension`. -/
theorem isIso_derivedHomBaseChange_app_of_finiteTorDimension
    (hAct : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeftCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X) =
        (algebraActionRightCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X))
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
  isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_canonicalCompatibility hTor baseChangeR
    comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA D hFinite hA K hK
    (projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction hTor baseChangeR comparisonR
      isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hAct K)

/-- **The flat case of Stacks 0BZM**, which is the example the source names: if `R → R'` is flat,
`A` is pseudo-coherent as an `R`-module and `A` and `R'` are Tor independent over `R`, the
base-change morphism of Stacks 0E29 is invertible at every bounded-below object of `D(R)`.

Boundedness below is given as an explicit bound rather than as membership in `D⁺(R)`, which is
the form `Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_canonicalCompatibility` takes. -/
theorem isIso_derivedHomBaseChange_app_of_flat
    (hAct : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeftCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X) =
        (algebraActionRightCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X))
    (hFlat : (algebraMap R R').Flat)
    (hA : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_flat_of_canonicalCompatibility hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hFlat
    (isPseudoCoherent_singleULiftAlgebra.{uR, uA, max v uRp} hA) K b hK
    (projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction hTor baseChangeR comparisonR
      isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hAct K)

/-- The invertibility of the base-change morphism of Stacks 0E29 for `A` perfect over `R`,
derived from the equality `hAct` of the two canonical algebra actions on K-flat complexes.
`Dualizing.isIso_derivedHomBaseChange_of_isPerfect` is the same statement with no such
hypothesis; this form is kept for the callers that still supply `hAct`. -/
theorem isIso_derivedHomBaseChange_of_isPerfect_of_kFlatAlgebraActionEq
    (hAct : ∀ X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp} X →
      (algebraActionLeftCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X) =
        (algebraActionRightCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app (DerivedCategory.Q.obj X))
    (hA : StacksDraft.Perfect.IsPerfectModule (R := R) A) :
    IsIso (derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact isIso_derivedHomBaseChange_app_of_isPerfect_of_canonicalCompatibility hTor baseChangeR
    comparisonR isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (isPerfect_singleULiftAlgebra.{uR, uA, max v uRp} hA) K
    (projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction hTor baseChangeR comparisonR
      isLeftDerivedR baseChangeA comparisonA isLeftDerivedA hAct K)


/-- **Stacks 0BZP.** Let `R → A` and `R → R'` be homomorphisms of commutative rings and
`A' = A ⊗_R R'`. If `A` is perfect as an `R`-module and `A` and `R'` are Tor independent over
`R`, then the base-change morphism of Stacks 0E29 is invertible — as a natural transformation,
hence at every object of `D(R)` and with no boundedness hypothesis.

The proof is that of the source. By Stacks 0E2A the restriction of the morphism along
`R' → A'` is, up to isomorphisms of source and target, the derived-Hom base-change morphism of
Stacks 0E1X at the algebra `A`; this is
`Dualizing.exists_restrictScalars_map_derivedHomBaseChange_app_eq`. That morphism is
invertible because `A` is perfect, by Stacks 0ATK (1), and restriction of scalars reflects
isomorphisms. -/
@[stacks 0BZP]
theorem isIso_derivedHomBaseChange_of_isPerfect
    (hA : StacksDraft.Perfect.IsPerfectModule (R := R) A) :
    IsIso (derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA) := by
  have := isLeftDerivedR
  have := isLeftDerivedA
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨sourceIso, targetIso, h⟩ :=
    exists_restrictScalars_map_derivedHomBaseChange_app_eq hTor baseChangeR comparisonR
      baseChangeA comparisonA K
  exact isIso_derivedHomBaseChange_app_of_isPerfect_of_comparison hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (isPerfect_singleULiftAlgebra.{uR, uA, max v uRp} hA) K sourceIso targetIso h

end Dualizing

end
