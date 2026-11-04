module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalLocusConnected
public import StacksFrontier.RingTheory.Dualizing.IsDualizingComplexModels
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds

/-!
# A hypersurface minus a closed subset of codimension at least three is connected: Stacks 0EG3

Let `A` be a Noetherian domain which has a dualizing complex and which is complete with respect
to a nonzero `f ∈ A`, and let `f ∈ 𝔞 ⊆ A` be an ideal. Write `X = Spec(A)`, `Y = V(f)` and
`Z = V(𝔞)`. Stacks 0EG3 says that if every irreducible component of `Z` has codimension `> 2`
in `X`, then `Y ∖ Z` is connected (in particular nonempty).

## Main results

* `Stacks.Algebraization.isConnected_zeroLocus_singleton_sdiff_of_isDomain` — **Stacks 0EG3**.

## Formulation

The irreducible components of `Z = V(𝔞)` are the closures `V(𝔮)` of the minimal primes `𝔮` of
`𝔞`, and the codimension of `V(𝔮)` in `Spec(A)` is the height of `𝔮`; so the hypothesis reads
`2 < 𝔮.height` for every `𝔮 ∈ 𝔞.minimalPrimes`. The dualizing complex lives in an arbitrary model
`[HasDerivedCategory (ModuleCat A)]` of `D(A)`; `Dualizing.exists_isDualizingComplex_iff_of_models`
moves it to the model in which Stacks 0EG5 is stated.

## The proof

The source observes that 0EG3 is a special case of Stacks 0EG5
(`Stacks.Algebraization.eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex`) with
`I = (f)`, and this is the route taken here.

* Condition (1) of 0EG5 is the hypothesis.
* Condition (2): the only minimal prime of the domain `A` is `(0)`, which does not contain `f`.
  For `𝔮 ⊇ 𝔞` the ring `(A/(0))_𝔮 = A_𝔮` has dimension `ht(𝔮) ≥ ht(𝔮') > 2` for a minimal prime
  `𝔮'` of `𝔞` below `𝔮`, while `cd(A, (f)) + 1 ≤ 2` because `(f)` has one generator
  (Stacks 0DX9).
* Condition (3): `Spec(A)` is irreducible, so every nonempty open subset is irreducible, hence
  connected.

0EG5 then says `Y ∖ Z` is empty or connected. It is not empty: `f` is not a unit (`A ≠ 0` is
`(f)`-adically complete), so some minimal prime `𝔭` of `(f)` exists, of height `≤ 1` by Krull's
principal ideal theorem; were `𝔞 ⊆ 𝔭`, a minimal prime of `𝔞` below `𝔭` would have height `≤ 1`,
against the hypothesis. So `𝔭 ∈ Y ∖ Z`.

## References

* [Stacks Project, Tag 0EG3](https://stacks.math.columbia.edu/tag/0EG3)
* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- An integer at most `1`, increased by one, is strictly below the Krull-dimension value of
any height `> 2`, compared in the extended integers. -/
private lemma intCast_lt_krullDimToEInt_of_two_lt {c : ℤ} (hc : c ≤ 1) {h : ℕ∞} (hh : 2 < h) :
    ((c + 1 : ℤ) : EInt) < krullDimToEInt (h : WithBot ℕ∞) := by
  cases h with
  | top => exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  | coe n =>
    have hn : 2 < n := by exact_mod_cast hh
    show ((c + 1 : ℤ) : EInt) < ((n : ℤ) : EInt)
    exact WithBotTop.coe_lt_coe.mpr (by omega)

/-- **Stacks Project, Tag 0EG3.** Let `A` be a Noetherian domain which has a dualizing complex
and which is complete with respect to a nonzero `f ∈ A`. Let `f ∈ 𝔞 ⊆ A` be an ideal. Assume
every irreducible component of `Z = V(𝔞)` has codimension `> 2` in `X = Spec(A)`, that is,
`2 < ht(𝔮)` for every minimal prime `𝔮` of `𝔞`. Then `Y ∖ Z` is connected, where `Y = V(f)`.

The dualizing complex may be taken in any model of `D(A)`. The hypothesis `f ≠ 0` is the
source's; the argument does not use it. -/
@[stacks 0EG3 "the whole statement: Y minus Z is connected, at the source's hypotheses"]
public theorem isConnected_zeroLocus_singleton_sdiff_of_isDomain (A : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (f : A) (_hf : f ≠ 0) [IsAdicComplete (Ideal.span {f}) A] (a : Ideal A) (hfa : f ∈ a)
    (hcodim : ∀ q ∈ a.minimalPrimes, 2 < q.height) :
    _root_.IsConnected
      (PrimeSpectrum.zeroLocus ({f} : Set A) \ PrimeSpectrum.zeroLocus (a : Set A)) := by
  classical
  set I : Ideal A := Ideal.span {f} with hIdef
  have hIa : I ≤ a := (Ideal.span_singleton_le_iff_mem a).mpr hfa
  have hzl : PrimeSpectrum.zeroLocus ({f} : Set A) = PrimeSpectrum.zeroLocus (I : Set A) :=
    (PrimeSpectrum.zeroLocus_span _).symm
  have hdual' := (Dualizing.exists_isDualizingComplex_iff_of_models (A := A) inferInstance
    (HasDerivedCategory.standard (ModuleCat.{u} A))).mp hdualizing
  have hItop : I ≠ ⊤ := by
    intro hI
    have hc : IsAdicComplete (⊤ : Ideal A) A := hI ▸ (inferInstance : IsAdicComplete I A)
    have := hc.subsingleton
    exact not_subsingleton A this
  have hcd : cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ 1 := by
    have := cohomologicalDimension_le_card_generators A I I.fg_of_isNoetherianRing ![f]
      (by simp [hIdef])
    simpa using this
  have hheight : ∀ q : PrimeSpectrum A, a ≤ q.asIdeal → 2 < q.asIdeal.height := by
    intro q hq
    obtain ⟨q', hq', hq'q⟩ := Ideal.exists_minimalPrimes_le hq
    exact (hcodim q' hq').trans_le (Ideal.height_mono hq'q)
  have hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a ≤ q.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) := by
    intro p q hp _ _ haq
    have hp0 : p.asIdeal = ⊥ := by
      rw [IsDomain.minimalPrimes_eq_singleton_bot] at hp
      exact hp
    rw [hp0, Ideal.map_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal]
    exact intCast_lt_krullDimToEInt_of_two_lt hcd (hheight q haq)
  have hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
      _root_.IsConnected V := fun V hV hne _ =>
    IsIrreducible.isConnected ⟨hne,
      (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum A)).isPreirreducible.open_subset hV
        (Set.subset_univ V)⟩
  rw [hzl]
  rcases eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex A I a hIa hdual' hdim
    hconn with hempty | hconnected
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hItop
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hIM
    have : I.IsPrincipal := ⟨⟨f, rfl⟩⟩
    have hp1 : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp
    have hpP : p.IsPrime := hp.1.1
    have hmem : (⟨p, hpP⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) := by
      refine ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr hp.1.2, fun hap => ?_⟩
      have h2 := hheight ⟨p, hpP⟩ ((PrimeSpectrum.mem_zeroLocus _ _).mp hap)
      exact absurd (h2.trans_le hp1) (by norm_num)
    rw [hempty] at hmem
    exact hmem
  · exact hconnected

end Stacks.Algebraization

end
