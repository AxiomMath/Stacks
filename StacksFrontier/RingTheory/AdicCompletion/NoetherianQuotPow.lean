module

public import StacksFrontier.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

/-!
# The three assertions of Stacks 031C

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` an `R`-module, and write `M^∧` for the
`I`-adic completion of `M`. Then `M^∧` is `I`-adically complete, `IⁿM^∧ = (IⁿM)^∧` and
`M^∧/IⁿM^∧ = M/IⁿM`. Each assertion is the corresponding part of Lemma 05GG, which needs `I` to be
finitely generated; over a Noetherian ring that is `IsNoetherian.noetherian I`.

## Main results

* `AdicCompletion.isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval`:
  Stacks 031C.

## Implementation notes

`IⁿM` is `I ^ n • ⊤`. The completion `(IⁿM)^∧` is identified with a submodule of `M^∧` through
`AdicCompletion.ofPowSMul I M n`, the completion of the inclusion `IⁿM ⊆ M`; the statement records
that this map is injective, so that the identification is legitimate, and that its image is
`IⁿM^∧`. The identification `M^∧/IⁿM^∧ = M/IⁿM` is through the map induced by the projection
`M^∧ → M/IⁿM`, which is bijective; the resulting isomorphism is
`AdicCompletion.quotPowSMulTopEquiv`. Both are stated for every `n : ℕ`, as in the source.

Faithfulness. The hypotheses are the source's: `IsNoetherianRing R`, an ideal `I` and an arbitrary
`R`-module `M` (no finiteness of `M` is assumed). The Noetherian hypothesis is live: over
`k[x₁, x₂, …]` with `I = (x₁, x₂, …)` the completion is not `I`-adically complete (Stacks 05JA).
At `R = M = ℤ`, `I = (p)` the statement says `ℤ_p` is `p`-adically complete,
`pⁿℤ_p = (pⁿℤ)^∧` and `ℤ_p/pⁿℤ_p = ℤ/pⁿ`.

## References

* [StackProject 031C](https://stacks.math.columbia.edu/tag/031C)
* [StackProject 05GG](https://stacks.math.columbia.edu/tag/05GG)

## Tags

adic completion, complete, Noetherian ring
-/

@[expose] public section

namespace AdicCompletion

/-- **Stacks 031C**. Let `R` be a Noetherian ring, `I` an ideal of `R` and `M` an `R`-module, and
write `M^∧` for the `I`-adic completion of `M`. Then
1. `M^∧` is `I`-adically complete;
2. `IⁿM^∧ = (IⁿM)^∧` for every `n`: the completion `(IⁿM)^∧ → M^∧` of the inclusion `IⁿM ⊆ M` is
   injective and its image is the submodule `IⁿM^∧` of `M^∧`;
3. `M^∧/IⁿM^∧ = M/IⁿM` for every `n`: the map `M^∧/IⁿM^∧ → M/IⁿM` induced by the projection
   `M^∧ → M/IⁿM` is bijective.

Here `IⁿM` is written Mathlib's way as `I ^ n • ⊤`. -/
@[stacks 031C "All three assertions. Completeness is Mathlib's `AdicCompletion.isAdicComplete`
(Stacks 05GG (1)); injectivity of `(IⁿM)^∧ → M^∧` is Mathlib's `AdicCompletion.ofPowSMul_injective`;
`IⁿM^∧ = (IⁿM)^∧` combines Mathlib's `AdicCompletion.pow_smul_top_eq_ker_eval` and
`AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval`; `M^∧/IⁿM^∧ = M/IⁿM` is
`AdicCompletion.bijective_liftQ_eval`. Each is fed `IsNoetherian.noetherian I : I.FG`, the
source's reduction to Lemma 05GG. Every `n : ℕ` is allowed, as in the source."]
public theorem isAdicComplete_and_pow_smul_top_eq_range_ofPowSMul_and_bijective_liftQ_eval
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (AdicCompletion I M) ∧
      (∀ n : ℕ, Function.Injective (ofPowSMul I M n) ∧
        (I ^ n • ⊤ : Submodule R (AdicCompletion I M))
          = ((ofPowSMul I M n).range).restrictScalars R) ∧
      ∀ n : ℕ, Function.Bijective
        ((I ^ n • ⊤ : Submodule R (AdicCompletion I M)).liftQ (eval I M n)
          (pow_smul_top_le_ker_eval I n)) :=
  ⟨inferInstance, fun n ↦ ⟨ofPowSMul_injective I n,
    pow_smul_top_eq_restrictScalars_range_ofPowSMul (IsNoetherian.noetherian I) n⟩,
    fun n ↦ bijective_liftQ_eval (IsNoetherian.noetherian I) M n⟩

end AdicCompletion

end
