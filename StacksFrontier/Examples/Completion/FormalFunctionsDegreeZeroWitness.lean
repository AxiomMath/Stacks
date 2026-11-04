module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.Homology.DerivedComplete.PrincipalFormalFunctionsDegreeZero
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.Vanishing

/-!
# A non-zero witness for the hypotheses of the degree-zero formal-functions theorem

`Stacks.FormalFunctions.exists_iso_limit_tensorHomology_zero` concludes that
`H⁰(K) ≅ lim_n H⁰(K ⊗ᴸ_A A/fⁿ)` from two hypotheses: that `H⁰(K)` is `f`-adically complete, and
that the `f`-adic Tate module of `H¹(K)` vanishes. A comparison-is-an-isomorphism statement is
exactly where a degenerate reading passes every check, so this file exhibits an object at which the
two hypotheses hold **simultaneously and with non-zero degree-zero cohomology**: the ring of
formal power series `ℤ⟦X⟧`, the element `X`, and the free module of rank one placed in degree zero.

Completeness comes from Mathlib's instance `IsAdicComplete (Ideal.span {X}) (PowerSeries R)`,
transported along the identification of `H⁰` of a module placed in degree zero with the module
itself. The Tate module vanishes because `H¹` of a module placed in degree zero is a zero object.
`witness_nontrivial` records that `H⁰` is *not* a zero object, so the conclusion is not the
trivial isomorphism between two zero objects.

## Main results

* `Stacks.Examples.FormalFunctionsWitness.witness` — both hypotheses hold at `K = ℤ⟦X⟧[0]`.
* `Stacks.Examples.FormalFunctionsWitness.witness_nontrivial` — the degree-zero cohomology there
  is not a zero object.
* `Stacks.Examples.FormalFunctionsWitness.witness_conclusion` — the degree-zero formal-functions
  isomorphism at that object.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory PrincipalTorsionTower

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Examples.FormalFunctionsWitness

/-- The ring of formal power series over the integers. -/
public abbrev A : Type := PowerSeries ℤ

/-- The free module of rank one over `ℤ⟦X⟧`. -/
public abbrev M : ModuleCat.{0} A := ModuleCat.of A A

/-- `ℤ⟦X⟧` placed in degree zero. -/
public abbrev K : DerivedCategory (ModuleCat.{0} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{0} A) 0).obj M

/-- The degree-zero cohomology of a module placed in degree zero is the module. -/
public def e0 : (homologyFunctor (ModuleCat.{0} A) 0).obj K ≅ M :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{0} A) 0).app M

/-- The degree-one cohomology of a module placed in degree zero vanishes. -/
public theorem isZero_h1 : IsZero ((homologyFunctor (ModuleCat.{0} A) 1).obj K) :=
  K.isZero_of_isLE 0 1 (by omega)

/-- **Both hypotheses of the degree-zero formal-functions theorem hold** for `A = ℤ⟦X⟧`,
`f = X` and `K = A` placed in degree zero. -/
public theorem witness :
    IsAdicComplete (Ideal.span {(PowerSeries.X : A)})
        ((homologyFunctor (ModuleCat.{0} A) 0).obj K) ∧
      IsZero (CompletionSequences.adicTateModule A
        ((homologyFunctor (ModuleCat.{0} A) 1).obj K) PowerSeries.X) := by
  refine ⟨Stacks.Examples.isAdicComplete_of_linearEquiv e0.toLinearEquiv inferInstance, ?_⟩
  refine Stacks.TateModule.isZero_adicTateModule_of_pow_smul_eq_zero A _ PowerSeries.X 1
    fun x ↦ ?_
  have := ModuleCat.subsingleton_of_isZero isZero_h1
  rw [Subsingleton.elim x 0, smul_zero]

/-- **The witness is not degenerate**: its degree-zero cohomology is not a zero object. -/
public theorem witness_nontrivial : ¬ IsZero ((homologyFunctor (ModuleCat.{0} A) 0).obj K) := by
  intro h
  have := ModuleCat.subsingleton_of_isZero (h.of_iso e0.symm)
  exact not_subsingleton A this

/-- **The degree-zero formal-functions isomorphism at the witness.** -/
public theorem witness_conclusion :
    ∃ e : (homologyFunctor (ModuleCat.{0} A) 0).obj K ≅
        limit (Stacks.FormalFunctions.tensorHomologySystem A PowerSeries.X K 0),
      ∀ n : ℕ, e.hom ≫ limit.π (Stacks.FormalFunctions.tensorHomologySystem A
          PowerSeries.X K 0) ⟨n⟩ =
        (homologyFunctor (ModuleCat.{0} A) 0).map
          (Stacks.FormalFunctions.derivedTensorUnit A PowerSeries.X K n) :=
  Stacks.FormalFunctions.exists_iso_limit_tensorHomology_zero A PowerSeries.X K
    witness.1 witness.2

end Stacks.Examples.FormalFunctionsWitness

end
