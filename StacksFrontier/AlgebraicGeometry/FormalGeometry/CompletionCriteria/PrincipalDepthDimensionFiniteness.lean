module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisorWhole
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.Depth.PrincipalDivisorDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension

/-!
# Hypothesis (5) of Stacks 0DXU is condition (c) of Stacks 0EHH

Fix an algebraization situation (Stacks 0EHC) whose ring `A` is Noetherian local with `𝔞 = 𝔪`
and which has a dualizing complex, and let `(F_n)` be a coherent `I`-adic system on
`U = X ∖ V(𝔪)` with `I = (f)` for a nonzerodivisor `f`, each term finite locally free over the
infinitesimal neighbourhood it is annihilated by.  [Stacks, Tag 0DXU] assumes in addition

* (5) `depth((A/fA)_𝔭) + dim(A/𝔭) > 1` for every prime `𝔭 ∈ V(f)` other than `𝔪`, and
* (6) `depth(A_𝔭) + dim(A/𝔭) > 3` for every `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`,

and concludes that `(F_n)` extends canonically to `X`, and is the completion of a coherent
`𝒪_U`-module when `A` is complete.  Its proof verifies conditions (a), (b) and (c) of the
Mittag-Leffler criterion [Stacks, Tag 0EHH].

This file discharges condition (c) from hypothesis (5), and then assembles the two conclusions
from the three conditions, leaving condition (a) as the single explicit input.

## Main results

* `Stacks.Algebraization.finite_localCohomologyBaseQuotient_of_depthDimOnDivisor` — hypothesis
  (5) makes `H^i_𝔞(A/fA)` a finite `A`-module for `i ≤ 1`.
* `Stacks.Algebraization.finite_globalSectionsSystem_zero_of_depthDimOnDivisor` — **condition
  (c) of [Stacks, Tag 0EHH]**: `H⁰(U, F_1)` is a finite `A`-module.
* `Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_isFiniteLength_range` — both
  conclusions of [Stacks, Tag 0DXU] from its hypotheses (1), (2), (3), (4), (5) together with
  condition (a) in the weak form [Stacks, Tag 0DXG] asks for.

## Implementation notes

Hypothesis (5) is [Stacks, Tag 0EFD] at `s = 1`, `T = V(𝔪)` and `M = A/fA`, on the nose.  That
tag asks for `depth(M_𝔭) + dim((A/𝔭)_𝔮) > s` at every pair `𝔭 ∉ T`, `𝔮 ∈ T` with `𝔭 ⊆ 𝔮`.  At
`T = V(𝔪)` the outer prime `𝔮` can only be `𝔪`, so the dimension term is
`dim(A_𝔪/𝔭A_𝔪) = dim(A/𝔭)` (`Stacks.FlatLocalCatenary.fibre_height_eq` through
`Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime`), and `𝔭 ∉ T` says
`𝔭 ≠ 𝔪`.  On `V(f)` the resulting inequality is hypothesis (5) verbatim; off `V(f)` the module
`(A/fA)_𝔭` is zero, so its depth is `⊤` and nothing is required.  So no appeal to
[Stacks, Tag 0BK3] is needed for condition (c).

Hypothesis (6) is **not** used here.  What the source does with it, and with hypothesis (2) and
the local structure of hypothesis (4), is produce condition (a): the finite length of the image
of `H¹(U, F_{n+1}) ⟶ H¹(U, F_1)` for some `n`, by local duality and Matlis duality over the
localizations `A_𝔮` at the primes `𝔮 ∈ V(f) ∖ {𝔪}`.  That derivation is not carried out in this
library, and the main result below takes the finite length as an explicit input; it is therefore
not a registration of the tag.  The pieces of that derivation which *are* in the library are
listed in the module docstring of
`StacksFrontier.RingTheory.Depth.PrincipalDivisorDepthDimension`; in particular
`Stacks.Algebraization.isFiniteLength_range_openCohomology_of_isFiniteLength_range_localCohomology`
(`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologyGlobalSections`)
reduces `harange` to the finite length of the image of `H²_𝔪(Mₙ) ⟶ H²_𝔪(M₁)` for
`Mₙ = H⁰(U, ℱₙ)`, which is where the source applies local duality and Matlis duality.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0DXG](https://stacks.math.columbia.edu/tag/0DXG)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing
open Stacks.RingTheory.PrincipalDivisorDepth

universe u

namespace Stacks.Algebraization

/-- Localizing `A/fA` at a prime that does not contain `f` gives the zero module: `f` is a unit
there, and `f` annihilates `A/fA`. -/
theorem subsingleton_localizedModule_baseQuotient {A : Type u} [CommRing A] {f : A}
    {p : Ideal A} [p.IsPrime] (hfp : f ∉ p) :
    Subsingleton (LocalizedModule p.primeCompl (A ⧸ Ideal.span {f})) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  refine ⟨f, hfp, ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {f}) m
  change (Submodule.Quotient.mk (f • x) : A ⧸ Ideal.span {f}) = 0
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [smul_eq_mul]
  exact Ideal.mem_span_singleton.mpr ⟨x, rfl⟩

/-- **Hypothesis (5) of [Stacks, Tag 0DXU] makes `H^i_𝔪(A/fA)` finite for `i ≤ 1`.** Let `S` be
an algebraization situation whose ring `A` is local with `𝔞 = 𝔪` and which has a dualizing
complex, and let `f ∈ A`.  If `depth((A/fA)_𝔭) + dim(A/𝔭) > 1` for every prime `𝔭 ∈ V(f)` other
than `𝔪`, then the local cohomology `H^i_𝔞(A/fA)` is a finite `A`-module for every `i ≤ 1`.

This is [Stacks, Tag 0EFD] at `s = 1`, `T = V(𝔪)` and `M = A/fA`.  The inequality that tag asks
for is `depth((A/fA)_𝔭) + dim((A/𝔭)_𝔮) > 1` for every pair `𝔭 ∉ T`, `𝔮 ∈ T` with `𝔭 ⊆ 𝔮`.  Here
`T = V(𝔪) = {𝔪}`, so `𝔮 = 𝔪` and `dim((A/𝔭)_𝔪) = dim(A/𝔭)`
(`Stacks.FlatLocalCatenary.fibre_height_eq`), and `𝔭 ∉ T` says exactly `𝔭 ≠ 𝔪`.  At the primes
of `V(f)` the inequality is hypothesis (5) verbatim; off `V(f)` the module `(A/fA)_𝔭` vanishes,
so its depth is `⊤` and the inequality is automatic.  The source cites Local Cohomology,
Proposition 51.8.7 for the same step.

Hypothesis (5) therefore needs no separate appeal to [Stacks, Tag 0BK3]: the ring-theoretic form
of that criterion is [Stacks, Tag 0EFD], and the inequality it asks for *is* the hypothesis. -/
theorem finite_localCohomologyBaseQuotient_of_depthDimOnDivisor
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = maximalIdeal S.A) (f : S.A)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (h5 : DepthDimOnDivisor f) (i : ℕ) (hi : i ≤ 1) :
    Module.Finite S.A (localCohomologyBaseQuotient S f i) := by
  have key := (Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim
    S.A (PrimeSpectrum.zeroLocus (S.a : Set S.A))
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization 1
    (S.A ⧸ Ideal.span {f}) omega homega).mpr ?_ (i : ℤ) (by exact_mod_cast hi)
  · exact key
  intro p q hp hq hpq
  have : p.asIdeal.IsPrime := p.2
  have : q.asIdeal.IsPrime := q.2
  -- `𝔮 = 𝔪`, because `𝔮 ⊇ 𝔞 = 𝔪` and `𝔮` is prime
  have hqmax : q.asIdeal = maximalIdeal S.A := by
    refine ((maximalIdeal.isMaximal S.A).eq_of_le q.2.ne_top ?_).symm
    rw [← ha]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hq
  -- `𝔭 ≠ 𝔪`, because `𝔭 ∉ V(𝔞) = V(𝔪)`
  have hpm : ¬ maximalIdeal S.A ≤ p.asIdeal := by
    intro hle
    exact hp ((PrimeSpectrum.mem_zeroLocus _ _).mpr (by rw [ha]; exact hle))
  -- the dimension term is `dim(A/𝔭)`, as a coerced `ℕ∞`
  set h : ℕ∞ := ((maximalIdeal S.A).map (Ideal.Quotient.mk p.asIdeal)).height with hh
  have hdimq : ringKrullDim (Localization.AtPrime q.asIdeal ⧸
      p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal))) = (h : WithBot ℕ∞) := by
    rw [Stacks.AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime
      p.asIdeal q.asIdeal hpq, hh]
    exact congrArg (fun J : Ideal S.A =>
      (((J.map (Ideal.Quotient.mk p.asIdeal)).height : ℕ∞) : WithBot ℕ∞)) hqmax
  have hdimp : (h : WithBot ℕ∞) = ringKrullDim (S.A ⧸ p.asIdeal) :=
    FlatLocalCatenary.fibre_height_eq p.asIdeal (le_maximalIdeal p.2.ne_top)
  rw [hdimq, ← Stacks.LocalCohomology.natCast_lt_add_iff_eint 1 _ h]
  -- the depth term: hypothesis (5) on `V(f)`, and the zero module off it
  by_cases hfp : f ∈ p.asIdeal
  · have h5p := h5 p hfp (fun hc => hpm (by rw [hc]; exact le_rfl))
    rw [← hdimp, ← WithBot.coe_add] at h5p
    exact_mod_cast h5p
  · have := subsingleton_localizedModule_baseQuotient (f := f) (p := p.asIdeal) hfp
    rw [Module.depth_eq_top_of_subsingleton, top_add]
    exact lt_top_iff_ne_top.mpr (by simp)

/-! ### Condition (c) of Stacks 0EHH from hypothesis (5) -/

/-- **Condition (c) of [Stacks, Tag 0EHH] from hypotheses (1), (3), (4) and (5) of
[Stacks, Tag 0DXU].**  `H⁰(U, F_1)` is a finite `A`-module.

The source says "we conclude that `M_n = H^0(U, ℱ_n)` is a finite `A`-module by (5) and Local
Cohomology, Proposition 51.8.7", and
`Stacks.Algebraization.finite_globalSections_of_shortExactSequences` propagates the finiteness
from `F_1` to every `F_n`.  Here hypothesis (5) is turned into the degree-`≤ 1` finiteness of
`H^i_𝔞(A/fA)` by [Stacks, Tag 0EFD]
(`Stacks.Algebraization.finite_localCohomologyBaseQuotient_of_depthDimOnDivisor`), hypotheses
(3) and (4) make a power of every `g ∈ 𝔞` on the module algebraizing `F_1` factor through a
finite free `A/fA`-module
(`Stacks.Algebraization.exists_pow_smul_factor_firstTerm`), and those two together give the
finiteness of `H^0(U, F_1)` by Local Cohomology 0BPY and 0BK0
(`Stacks.Algebraization.finite_complementCohomologyBase_firstTerm` at `s = 1`). -/
theorem finite_globalSectionsSystem_zero_of_depthDimOnDivisor
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = maximalIdeal S.A)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hI : S.I = Ideal.span {f}) (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (h5 : DepthDimOnDivisor f) :
    Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) := by
  obtain ⟨M, hMfin, hfM, ⟨eM⟩⟩ :=
    exists_finiteModule_smul_eq_zero_tilde_restrict_iso S F f hI
  have := hMfin
  have hcomp := finite_complementCohomologyBase_firstTerm S f M 1
    (fun i _ hi2 =>
      finite_localCohomologyBaseQuotient_of_depthDimOnDivisor S ha f omega homega h5 i hi2)
    (exists_pow_smul_factor_firstTerm S F f hI hfree M hfM eM)
  have hqc : (systemObj S F 0).IsQuasicoherent := F.property.isQuasicoherent 0
  exact finite_globalSectionsSystem_zero_of_finite_openCohomology S F
    (finite_openCohomology_of_finite_complementCohomologyBase S (systemObj S F 0) M eM 0
      (hcomp 0 (by omega)))

/-! ### Stacks 0DXU up to condition (a) -/

/-- **[Stacks, Tag 0DXU] with condition (a) of [Stacks, Tag 0EHH] as the only remaining input.**
Let `S` be an algebraization situation whose ring `A` is local with `𝔞 = 𝔪` and which has a
dualizing complex — hypotheses (1) and (2) of the source — let `I = (f)` be generated by a
nonzerodivisor `f` — hypothesis (3) — let every term of the system be finite locally free over
the infinitesimal neighbourhood it is annihilated by — hypothesis (4) — and let
`depth((A/fA)_𝔭) + dim(A/𝔭) > 1` for every `𝔭 ∈ V(f)` other than `𝔪` — hypothesis (5).  If
moreover the image of `H¹(U, F_{n+1}) ⟶ H¹(U, F_1)` has finite length as an `A`-module for some
`n`, then `(F_n)` extends canonically to `X = Spec(A)`, and if `A` is `I`-adically complete then
`(F_n)` is the completion of a coherent `𝒪_U`-module.

The three conditions of the Mittag-Leffler criterion [Stacks, Tag 0EHH] that the source verifies
are discharged here as follows.  Condition (b), the limit topology on `limₙ H⁰(U, F_n)` being the
`I`-adic topology, comes from the short exact sequences `0 → F_n → F_{n+1} → F_1 → 0` that
hypotheses (3) and (4) produce
(`Stacks.Algebraization.hasPrincipalShortExactSequences_of_locallyFree`).  Condition (c),
finiteness of every `H⁰(U, F_n)`, comes from hypothesis (5) through
`Stacks.Algebraization.finite_globalSectionsSystem_zero_of_depthDimOnDivisor` and the induction
`Stacks.Algebraization.finite_globalSections_of_shortExactSequences`.  Condition (a) is
[Stacks, Tag 0DXG] at the finite-length image, which is the hypothesis `harange` — the point the
source's proof reaches when it writes "to finish the proof it suffices to show that there exists
an `n > 1` such that the image of `H¹(U, ℱₙ) → H¹(U, ℱ₁)` has finite length as an `A`-module".

What the source does with hypotheses (2) and (6), and with the local structure of hypothesis (4),
is exactly to produce `harange`, by local duality and Matlis duality; that derivation is not
carried out here, and `omega` enters below only through hypothesis (5)'s route to condition (c).
So this declaration is **not** a registration of the tag: it is the tag with its last step left
as an explicit input. -/
theorem canonicallyExtends_and_isCompletion_of_isFiniteLength_range
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = maximalIdeal S.A)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hI : S.I = Ideal.span {f}) (hf : f ∈ nonZeroDivisors S.A)
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (h5 : DepthDimOnDivisor f)
    (harange : ∃ n : ℕ, IsFiniteLength S.A
      (LinearMap.range ((openCohomologyFunctor S 1).map
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
          (systemObj S F) (systemMapSucc S F) n)).hom)) :
    CanonicallyExtends S F ∧
      (IsAdicComplete (Ideal.span {f}) S.A →
        (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage
          (kerComapSystem S F)) := by
  have h : HasPrincipalShortExactSequences S F f :=
    hasPrincipalShortExactSequences_of_locallyFree S F f hI hf hfree
  have h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) :=
    finite_globalSectionsSystem_zero_of_depthDimOnDivisor S ha F f hI hfree omega homega h5
  refine ⟨canonicallyExtends_of_isFiniteLength_range S F f hI h h0 harange,
    fun hcomplete => (isCompletion_iff_nearClosed S (kerComapSystem S F)).mpr
      (isCompletionNearClosed_of_isFiniteLength_range S F f hI hcomplete h h0 harange)⟩

end Stacks.Algebraization

end
