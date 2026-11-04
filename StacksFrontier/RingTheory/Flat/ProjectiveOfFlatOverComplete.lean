module

public import Mathlib.Data.Finsupp.Encodable
public import StacksFrontier.Algebra.MittagLeffler.Projective
public import StacksFrontier.Algebra.MittagLeffler.ShortExact
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.ProjectiveAdicCompletionInjectivity
public import StacksFrontier.RingTheory.Flat.ProjectiveQuotientAdicCompletion

/-!
# Projectivity from flatness over an adically complete ring

Let `R` be a Noetherian ring which is `I`-adically complete, let `S` be a finite type `R`-algebra
and let `N` be a finite `S`-module which is flat over `R`. This file proves Stacks 05DP: if `N/IN`
is projective over `R/I` and, for every prime `𝔮` of `S` which is an associated prime of the fibre
`N ⊗[R] κ(𝔭)` with `𝔭 = R ∩ 𝔮`, the ideal `IS + 𝔮` is proper, then `N` is projective as an
`R`-module.

The argument is the source's. The hypothesis on the associated primes makes `N → N^∧`
universally injective (Stacks 05DM) and the hypothesis on `N/IN` makes `N^∧` Mittag-Leffler
(Stacks 05DK); the Mittag-Leffler property therefore descends from `N^∧` to `N` along the
universally exact sequence `0 → N → N^∧ → N^∧/N → 0` (Stacks 059N). Being finite over a finite
type `R`-algebra, `N` is countably generated over `R`, so it is flat, countably generated and
Mittag-Leffler, hence projective by Stacks 059X.

## Main results

* `Module.projective_of_flat_of_projective_quotient_of_associatedPrimes`: Stacks 05DP.

## Implementation notes

Stacks 059N and the Mittag-Leffler API are stated for a ring and modules in a single universe,
while the statement here keeps the universes of `R`, `S` and `N` independent; the proof therefore
runs on `ULift N` in the universe `max u w` and transports the conclusion back.

The contraction `𝔭 = R ∩ 𝔮` is `PrimeSpectrum.comap (algebraMap R S) 𝔮`, the condition `IS + 𝔮 ≠ S`
is the corresponding supremum of ideals being different from `⊤`, and `N/IN` is
`N ⧸ I • (⊤ : Submodule R N)` with its canonical `R ⧸ I`-module structure.

## References

* [Stacks Project, Tag 05DP](https://stacks.math.columbia.edu/tag/05DP)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module

/-- `N` is countably generated over `R` when it is finite over a finite type `R`-algebra `S`:
the products of a monomial in finitely many algebra generators with one of finitely many module
generators form a countable generating set. -/
private theorem countablyGenerated_of_finite_of_finiteType (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (N : Type w)
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N] :
    Module.CountablyGenerated R N := by
  classical
  obtain ⟨t, ht⟩ := (inferInstance : Algebra.FiniteType R S).1
  let mon (d : t →₀ ℕ) : S := ∏ i ∈ d.support, (i : S) ^ d i
  have hφ : Function.Surjective (MvPolynomial.aeval (R := R) ((↑) : t → S)) := by
    intro x
    have hx : x ∈ (Algebra.adjoin R (↑t : Set S) : Set S) := ht ▸ trivial
    rwa [Algebra.adjoin_eq_range] at hx
  have hmon : Submodule.span R (Set.range mon) = ⊤ := by
    refine top_unique fun s _ => ?_
    obtain ⟨p, rfl⟩ := hφ s
    rw [MvPolynomial.as_sum p, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)
  obtain ⟨gs, hgs⟩ := (Module.finite_def (R := S) (M := N)).mp inferInstance
  refine ⟨Set.image2 (· • ·) (Set.range mon) (gs : Set N),
    (Set.countable_range mon).image2 gs.countable_toSet _, ?_⟩
  rw [Set.image2_smul, Submodule.span_smul_of_span_eq_top hmon, hgs,
    Submodule.restrictScalars_top]

/-- **Stacks Project, Tag 05DP.** Let `R` be a Noetherian ring, `I`-adically complete, let `S` be
a finite type `R`-algebra and let `N` be a finite `S`-module which is flat over `R`. If `N/IN` is
projective over `R/I` and `IS + 𝔮 ≠ S` for every prime `𝔮` of `S` which is an associated prime of
the fibre `N ⊗[R] κ(𝔭)` with `𝔭 = R ∩ 𝔮`, then `N` is projective as an `R`-module. -/
@[stacks 05DP "`N/IN` is `N ⧸ I • ⊤`; the contraction `𝔭 = R ∩ 𝔮` is
`PrimeSpectrum.comap (algebraMap R S) 𝔮` and `κ(𝔭)` its `ResidueField`; the condition `IS + 𝔮 ≠ S`
is the join of ideals being different from `⊤`."]
theorem projective_of_flat_of_projective_quotient_of_associatedPrimes (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (N : Type w) [AddCommGroup N]
    [Module S N] [Module R N] [IsScalarTower R S N] [IsNoetherianRing R] [IsAdicComplete I R]
    [Algebra.FiniteType R S] [Module.Finite S N] [Module.Flat R N]
    (hprojective : Module.Projective (R ⧸ I) (N ⧸ I • (⊤ : Submodule R N)))
    (hassociated : ∀ q : PrimeSpectrum S, q.asIdeal ∈ associatedPrimes S
        (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) →
      I.map (algebraMap R S) ⊔ q.asIdeal ≠ ⊤) :
    Module.Projective R N := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let M := ULift.{max u w} N
  let e : M ≃ₗ[R] N := ULift.moduleEquiv
  let eS : M ≃ₗ[S] N := ULift.moduleEquiv
  have hprojective' : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    .of_equiv' (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (Submodule.Quotient.equiv (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) e
        (by simp))).symm
  have hassociated' : ∀ q : PrimeSpectrum S, q.asIdeal ∈ associatedPrimes S
      (M ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) →
      I.map (algebraMap R S) ⊔ q.asIdeal ≠ ⊤ := by
    intro q hq
    exact hassociated q (AssociatedPrimes.mem_iff.2
      ((TensorProduct.AlgebraTensorModule.congr eS (LinearEquiv.refl R _)).isAssociatedPrime_iff.1
        (AssociatedPrimes.mem_iff.1 hq)))
  have hUI : UniversallyInjective (AdicCompletion.of I M) :=
    AdicCompletion.universallyInjective_of_flat_of_fibre_associatedPrimes I M hassociated'
  have hMLC : IsMittagLeffler.{u, max u w, max u w, max u w, max u w} R (AdicCompletion I M) :=
    AdicCompletion.isMittagLeffler_of_projective_quotient_smul_top M I hprojective'
  have hMLM : IsMittagLeffler.{u, max u w, max u w, max u w, max u w} R M := by
    rw [isMittagLeffler_def_iff]
    refine (Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
      (M₃ := AdicCompletion I M ⧸ LinearMap.range (AdicCompletion.of I M))
      (LinearMap.exact_map_mkQ_range _) (Submodule.mkQ_surjective _) hUI).1
      ((isMittagLeffler_def_iff R (AdicCompletion I M)).mp hMLC)
  have : Module.Projective R M :=
    Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated R M hMLM
      (Module.CountablyGenerated.of_linearEquiv e.symm
        (countablyGenerated_of_finite_of_finiteType R S N))
  exact Module.Projective.of_equiv' e

end Module

end
