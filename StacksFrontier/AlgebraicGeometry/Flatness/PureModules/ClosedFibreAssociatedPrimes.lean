module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.UniversalInjectivity
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated primes of fibres of a projective module over a local ring

Let `R` be a local ring, `S` an `R`-algebra and `N` an `S`-module which is projective over `R`
and whose closed fibre is finite over the Noetherian closed-fibre ring. Then every associated
prime of a fibre of `N` meets the closed fibre of `R`.

The proof localizes `N` at the elements of `S` which are regular on the closed fibre. That
localization map is universally injective over `R`, so the associated prime survives in the
localized fibre; the description of the contractions of the primes of the localization then
places it below an associated prime of the closed-fibre module, which contains the extended
maximal ideal.

## Main results

* `Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top`: an associated prime of a
  fibre cannot be comaximal with the extension of the maximal ideal of the base.

## Implementation notes

The associated-prime hypothesis is written as equality with the annihilator of an element, as in
the Stacks Project definition. The fibre at the contraction of `q` is the tensor product with
its residue field, and the closed-fibre module is the quotient by the action of the extended
maximal ideal. Both `N` and the residue field are lifted by `ULift` into a common universe, in
which the universal-injectivity statement for the localization map is available.

## References

* [Stacks Project, Tag 05FV](https://stacks.math.columbia.edu/tag/05FV)
-/

@[expose] public section

namespace Stacks.PureModules

universe u v w

open scoped _root_.TensorProduct

/-- An element annihilates a vector exactly when it lies in the colon ideal of the zero
submodule by the span of that vector. -/
private lemma mem_bot_colon_span_singleton_iff {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) (x : M) :
    r ∈ (⊥ : Submodule R M).colon (Submodule.span R {x}) ↔ r • x = 0 := by
  simp

/-- An injective linear map transports associated primes forward. -/
private lemma associated_map_injective {S M M' : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (f : M →ₗ[S] M') (hf : Function.Injective f) {q : Ideal S}
    (hq : IsAssociatedPrimeStacks S M q) : IsAssociatedPrimeStacks S M' q := by
  rcases hq with ⟨hp, x, hx⟩
  refine ⟨hp, f x, Submodule.ext fun r => ?_⟩
  rw [mem_bot_colon_span_singleton_iff, ← hx, mem_bot_colon_span_singleton_iff]
  exact ⟨fun hr => hf (by simpa only [map_smul, map_zero] using hr),
    fun hr => by simpa only [map_smul, map_zero] using congrArg f hr⟩

/-- **Stacks Project, Tag 05FV.** Under the finite Noetherian closed-fibre hypotheses, an
associated prime of any fibre of a projective module meets the closed fibre of a local base. -/
@[stacks 05FV]
lemma associatedPrime_add_map_maximalIdeal_ne_top
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N]
    [IsNoetherianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    [Module.Finite (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N)))]
    (q : PrimeSpectrum S)
    (hq : IsAssociatedPrimeStacks S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) q.asIdeal) :
    q.asIdeal + (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≠ ⊤ := by
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let N' := ULift.{max u (max v w)} N
  let P' : Submodule S N' := I • (⊤ : Submodule S N')
  let eN : N ≃ₗ[S] N' := (ULift.moduleEquiv (R := S) (M := N)).symm
  have hP : (I • (⊤ : Submodule S N)).map eN.toLinearMap = P' := by
    ext x
    simp [P', eN, I]
  let eQ : (N ⧸ I • (⊤ : Submodule S N)) ≃ₗ[S] N' ⧸ P' := Submodule.Quotient.equiv _ P' eN hP
  have _ : Module.Finite (S ⧸ I) (N' ⧸ P') := by
    let eQA : (N ⧸ I • (⊤ : Submodule S N)) ≃ₗ[S ⧸ I] N' ⧸ P' :=
      { toEquiv := eQ.toEquiv
        map_add' := eQ.map_add
        map_smul' := fun a x => by
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact eQ.map_smul s x }
    exact Module.Finite.equiv eQA
  have _ : Module.Projective R N' := Module.Projective.of_equiv (eN.restrictScalars R)
  let sigma := nonZeroSMulDivisors S (N' ⧸ P')
  let k := (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
  let k' := ULift.{max u (max v w)} k
  let eFiber : (N ⊗[R] k) ≃ₗ[S] (N' ⊗[R] k') :=
    TensorProduct.AlgebraTensorModule.congr eN (ULift.moduleEquiv (R := R) (M := k)).symm
  let gS : (N' ⊗[R] k') →ₗ[S] (LocalizedModule sigma N' ⊗[R] k') :=
    TensorProduct.AlgebraTensorModule.rTensor R k' (LocalizedModule.mkLinearMap sigma N')
  have hqL : IsAssociatedPrimeStacks S (LocalizedModule sigma N' ⊗[R] k') q.asIdeal :=
    associated_map_injective gS
      (Stacks.UniversalInjectivity.universallyInjective_localizedModule_mkLinearMap.{u, v, max u w}
        k')
      (associated_map_injective eFiber.toLinearMap eFiber.injective hq)
  let T := Localization sigma
  have hdisj : Disjoint (sigma : Set S) (q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    intro s hsigma hsq
    rcases hqL with ⟨hqprime, y, hy⟩
    rw [← hy] at hsq
    replace hsq := (mem_bot_colon_span_singleton_iff s y).1 hsq
    refine hqprime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [← hy, mem_bot_colon_span_singleton_iff, one_smul]
    have hsmul : Function.Injective
        (fun z : LocalizedModule sigma N' ⊗[R] k' => s • z) := fun z z' h =>
      (IsLocalization.map_units T ⟨s, hsigma⟩).smul_bijective.injective (by simpa using h)
    exact hsmul (hsq.trans (smul_zero s).symm)
  have hqRange : q.asIdeal ∈ Set.range (fun z : PrimeSpectrum T => z.asIdeal.under S) :=
    ⟨⟨Ideal.map (algebraMap S T) q.asIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint sigma T q.asIdeal q.2 hdisj⟩,
      IsLocalization.under_map_of_isPrime_disjoint (M := sigma) (S := T)
        (I := q.asIdeal) q.2 hdisj⟩
  rw [Stacks.UniversalInjectivity.range_under_localization_nonZeroSMulDivisors
    (R := R) (S := S) (N := N') (T := T)] at hqRange
  rcases hqRange with ⟨_, p, hp, hqp⟩
  have hIp : I ≤ p := by
    rcases hp with ⟨_, z, hz⟩
    intro s hs
    rw [← hz, mem_bot_colon_span_singleton_iff]
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective P' z
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hs Submodule.mem_top
  intro htop
  exact hp.1.ne_top (top_le_iff.mp (htop ▸ sup_le hqp hIp))

end Stacks.PureModules
