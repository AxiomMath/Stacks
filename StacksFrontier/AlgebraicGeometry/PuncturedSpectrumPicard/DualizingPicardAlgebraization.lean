module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardAlgebraizationOfEssSurj
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.LocalPrincipalEquivalence

/-!
# [Stacks, Tag 0F2E]: invertible modules on `U₀` extend, over a ring with a dualizing complex

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. [Stacks, Tag 0F2E] says that the conclusion
of [Stacks, Tag 0F2D] — `colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective, where `U`,
resp. `U₀`, is the punctured spectrum of `A`, resp. of `A/fA` — holds if

1. `A` has a dualizing complex,
2. `A` is `f`-adically complete,
3. `f` is a nonzerodivisor,
4. one of the following is true
   * (a) `A_f` is `(S₂)` and for `𝔭 ⊂ A`, `f ∉ 𝔭` minimal we have `dim(A/𝔭) ≥ 4`, or
   * (b) if `𝔭 ∉ V(f)` and `V(𝔭) ∩ V(f) ≠ {𝔪}`, then `depth(A_𝔭) + dim(A/𝔭) > 3`,
5. `H³_𝔪(A/fA) = 0`.

The proof is exactly that of [Stacks, Tag 0F2D], with [Stacks, Tag 0EKY] in place of
[Stacks, Tag 0EKZ]: the argument of [Stacks, Tag 0F2D] from an essential-surjectivity input is
`Stacks.PuncturedSpectrumPicard.picardColimitSurjective_of_forall_isCompletionNearClosed`, and the
input is the essential-surjectivity half of [Stacks, Tag 0EKY],
`Stacks.Algebraization.isCompletionNearClosedFiniteLocallyFree_of_isLocalRing_of_eq_span_singleton`
applied in the situation `(f) ⊆ 𝔪` of [Stacks, Tag 0EHC].

## Main results

* `Stacks.PuncturedSpectrumPicard.picardColimitSurjective_of_isDualizingComplex`:
  **[Stacks, Tag 0F2E]**.

## References

* [Stacks Project, Tag 0F2E](https://stacks.math.columbia.edu/tag/0F2E)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0EKY](https://stacks.math.columbia.edu/tag/0EKY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u w

namespace Stacks.PuncturedSpectrumPicard

variable (A : Type u) [CommRing A] [IsLocalRing A] (f : A)

/-- **[Stacks, Tag 0F2E].** Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Assume

1. `A` has a dualizing complex,
2. `A` is `f`-adically complete,
3. `f` is a nonzerodivisor,
4. one of the following is true
   * (a) `A_f` is `(S₂)` and for `𝔭 ⊂ A`, `f ∉ 𝔭` minimal we have `dim(A/𝔭) ≥ 4`, or
   * (b) if `𝔭 ∉ V(f)` and `V(𝔭) ∩ V(f) ≠ {𝔪}`, then `depth(A_𝔭) + dim(A/𝔭) > 3`,
5. `H³_𝔪(A/fA) = 0`.

Then the conclusion of [Stacks, Tag 0F2D] holds: with `U`, resp. `U₀`, the punctured spectrum of
`A`, resp. of `A/fA`, the map `colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective. As
for [Stacks, Tag 0F2D] (`Stacks.PuncturedSpectrumPicard.picardColimitSurjective`), the conclusion
is `Stacks.PuncturedSpectrumPicard.PicardColimitSurjective`, the elementwise form of surjectivity
out of the filtered colimit: every invertible module on `U₀` is the restriction of an invertible
module on an open `U'` of `U` containing `U₀`.

Hypothesis (4a) reads "`A_f` is `(S₂)`" as `PropertySkRing (Localization.Away f) 2`, Serre's
condition of [Stacks, Tag 031P] for the ring `A_f`; in (4b), `V(f)` is the set of primes
containing `f`. Hypothesis (1) is read in any model `[HasDerivedCategory (ModuleCat A)]` of the
derived category; whether a dualizing complex exists does not depend on the model. These are the
spellings of [Stacks, Tag 0EKY]
(`Stacks.Algebraization.completionEquivalence_local_principal_finiteLocallyFree`). Hypothesis (5)
is written, as in [Stacks, Tag 0F2D], in the library's default model, before the model of (1) is
introduced, so that the two do not interfere.

The proof is the source's: that of [Stacks, Tag 0F2D] with [Stacks, Tag 0EKY] in place of
[Stacks, Tag 0EKZ]. A class on `U₀` extends along the infinitesimal neighbourhoods of `U₀` by
[Stacks, Tag 0C6R] and `H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`, giving an invertible object of
`Coh(U, f𝒪_U)`; by the essential surjectivity of [Stacks, Tag 0EKY] it is the completion of a
finite locally free module on an open `V ⊇ U₀`, which is invertible near `U₀`
(`Stacks.PuncturedSpectrumPicard.picardColimitSurjective_of_forall_isCompletionNearClosed`). -/
@[stacks 0F2E "the whole remark: under (1)-(5) the conclusion of 0F2D holds; points (a) and (b) \
are commentary with no mathematical claim"]
theorem picardColimitSurjective_of_isDualizingComplex [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hreg : IsSMulRegular A f)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcond :
      (PropertySkRing (Localization.Away f) 2 ∧
        ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
          (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
        ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
          {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
          {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩} →
        (3 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
            ringKrullDim (A ⧸ p.asIdeal))) :
    PicardColimitSurjective A f :=
  picardColimitSurjective_of_forall_isCompletionNearClosed A f hf hreg hvanish3 fun F hfree =>
    Algebraization.isCompletionNearClosedFiniteLocallyFree_of_isLocalRing_of_eq_span_singleton
      (principalLocalSituation A f hf) hdual hcomplete rfl rfl hcond F hfree

end Stacks.PuncturedSpectrumPicard

end
