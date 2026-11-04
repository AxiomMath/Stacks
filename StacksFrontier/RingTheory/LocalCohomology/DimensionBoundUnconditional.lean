module

public import StacksFrontier.RingTheory.LocalCohomology.ArithmeticRank
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenVanishing
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.DimensionBound

/-!
# The cohomological dimension is bounded by the Krull dimension

Stacks 0DXC has two assertions: the cohomological dimension of a finitely generated ideal of a
ring is at most the Krull dimension of the ring, and the local cohomology of a finite module
vanishes above the dimension of its support. The file
`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/DimensionBound.lean` carries out every step
of the source's proof except one, and reduces both assertions to the single statement

`B local Noetherian, J finitely generated, dim B ≤ e ⟹ cd(B, J) ≤ e`,

taking it as an explicit hypothesis. This file discharges that hypothesis and so proves both
assertions outright.

The missing input was Kronecker's bound on the arithmetic rank, proved as
`Stacks.ArithmeticRank.exists_zeroLocus_range_eq_of_isLocalRing`: over a local ring of
dimension at most `e`, a proper ideal has the same zero locus as `e` of its elements. The
generator bound of Stacks 0DX9 (2) then bounds the cohomological dimension by `e`. The unit ideal
needs separate treatment — its zero locus is empty, hence clopen, and the cohomological dimension
of an ideal with clopen zero locus is at most zero.

This route replaces the one the source takes, which goes through the vanishing of sheaf
cohomology above the dimension of a spectral space (Stacks 0A3G) and the implication (3) ⇒ (1) of
Stacks 0DX7, neither of which is available in this library.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_le_of_isLocalRing` — the local case: over a
  Noetherian local ring of Krull dimension at most `e`, every finitely generated ideal has
  cohomological dimension at most `e`.
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim` — the second assertion of
  Stacks 0DXC: `cd(A, I) ≤ dim A` for every finitely generated ideal of a Noetherian ring.
* `Stacks.LocalCohomology.localCohomologyModule_isZero_of_supportDim_lt` — the first assertion of
  Stacks 0DXC: `H^i_{V(I)}(M) = 0` for `i` above the dimension of the support of a finite module
  `M`.

## Implementation notes

The globalization is Stacks 0DXB, already available as
`Stacks.LocalCohomology.cohomologicalDimension_le_of_forall_localization_le`: the cohomological
dimension is the supremum over the localizations `A_𝔭`, each local of dimension `ht 𝔭 ≤ dim A`,
and each Noetherian because `A` is.

The existing reduction `cohomologicalDimension_le_ringKrullDim_of_isLocalRing` is *not* used,
because its hypothesis quantifies over all local rings without assuming them Noetherian, and the
bound proved here needs Noetherianity (through the finiteness of the set of minimal primes).
Localizing by hand through `cohomologicalDimension_le_of_forall_localization_le` keeps the
hypothesis where it belongs.

No `@[stacks 0DXC]` attribute is placed: the results below carry a Noetherian hypothesis that
the source does not make, so they are a special case of the tag. The tag itself, without that
hypothesis, is in
`StacksFrontier/RingTheory/LocalCohomology/CohomologicalDimension/KrullDimension.lean`.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

/-- **The local case of the second assertion of Stacks 0DXC.** Over a Noetherian local ring of
Krull dimension at most `e`, the cohomological dimension of a finitely generated ideal is at most
`e`.

For a proper ideal this is Kronecker's sharp local bound followed by the generator bound of
Stacks 0DX9 (2). The unit ideal has empty, hence clopen, zero locus, so its cohomological
dimension is at most zero. -/
theorem cohomologicalDimension_le_of_isLocalRing (B : Type u) [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] (J : Ideal B) (hJ : J.FG) (e : ℕ)
    (he : ringKrullDim B ≤ (e : WithBot ℕ∞)) :
    cohomologicalDimension B J hJ ≤ (e : ℤ) := by
  by_cases htop : J = ⊤
  · subst htop
    refine (cohomologicalDimension_le_zero_of_isClopen_zeroLocus B ⊤ hJ ?_).trans
      (Int.natCast_nonneg e)
    simpa using isClopen_empty
  · obtain ⟨n, f, hn, hf⟩ :=
      Stacks.ArithmeticRank.exists_zeroLocus_range_eq_of_isLocalRing J htop e he
    exact (cohomologicalDimension_le_card_zeroLocus_generators B J hJ f hf).trans
      (by exact_mod_cast hn)

/-- **The second assertion of Stacks Project, Tag 0DXC.** The cohomological dimension of a
finitely generated ideal of a Noetherian ring is bounded by the Krull dimension of the ring.

By Stacks 0DXB the cohomological dimension is the supremum of those of the localizations `A_𝔭`.
Each `A_𝔭` is Noetherian and local of Krull dimension `ht 𝔭 ≤ dim A`, so
`cohomologicalDimension_le_of_isLocalRing` applies to each. -/
theorem cohomologicalDimension_le_ringKrullDim (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) := by
  refine cohomologicalDimension_le_of_forall_localization_le A I hI (d : ℤ) (by omega) fun p => ?_
  have : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  exact cohomologicalDimension_le_of_isLocalRing _ _ _ d
    ((ringKrullDim_localizationAtPrime_le A p).trans hd)

/-- In `WithBot ℕ∞`, being strictly below the cast of `m + 1` means being at most the cast of `m`.
The three cases are `⊥`, `⊤` and a natural number. -/
theorem withBotENat_le_of_lt_succ (x : WithBot ℕ∞) (m : ℕ)
    (hx : x < ((m + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((m : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => simp at hx
    | coe k =>
      have hk : k < m + 1 := by exact_mod_cast hx
      exact_mod_cast Nat.lt_succ_iff.mp hk

/-- **The first assertion of Stacks Project, Tag 0DXC.** For a finite module `M` over a Noetherian
ring and a finitely generated ideal `I`, the local cohomology `H^i_{V(I)}(M)` vanishes in every
degree `i` above the dimension of the support of `M`.

The subsingleton case is separate, because an empty support has dimension `⊥`. Otherwise
`dim Supp M = dim (A / ann M)` is at most `i - 1`, so the second assertion bounds the
cohomological dimension of `I (A / ann M)` by `i - 1`, which is the hypothesis of
`localCohomologyModule_isZero_of_supportDim_lt_of_quotient_bound`. -/
theorem localCohomologyModule_isZero_of_supportDim_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] (i : ℤ)
    (hi : Module.supportDim A M < (i.toNat : WithBot ℕ∞)) :
    IsZero (localCohomologyModule A I hI M i) := by
  by_cases hsub : Subsingleton M
  · have : Subsingleton M := hsub
    exact isZero_homology_localCohomology_of_subsingleton.{u, v} A I hI M i
  · have hM : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    refine localCohomologyModule_isZero_of_supportDim_lt_of_quotient_bound A I hI M i hi ?_
    have hne : Module.supportDim A M ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial A M
    have hpos : 1 ≤ i.toNat := by
      rcases Nat.eq_zero_or_pos i.toNat with h | h
      · rw [h] at hi
        exact absurd ((WithBot.lt_zero_iff_eq_bot _).mp (by simpa using hi)) hne
      · omega
    have hdim : ringKrullDim (A ⧸ Module.annihilator A M) ≤ ((i.toNat - 1 : ℕ) : WithBot ℕ∞) := by
      refine withBotENat_le_of_lt_succ _ _ ?_
      rw [← Module.supportDim_eq_ringKrullDim_quotient_annihilator,
        show (i.toNat - 1 + 1 : ℕ) = i.toNat by omega]
      exact hi
    refine (cohomologicalDimension_le_ringKrullDim (A ⧸ Module.annihilator A M)
      (I.map (Ideal.Quotient.mk (Module.annihilator A M)))
      (hI.map (Ideal.Quotient.mk (Module.annihilator A M))) (i.toNat - 1) hdim).trans ?_
    rw [show ((i.toNat - 1 : ℕ) : ℤ) = (i.toNat : ℤ) - 1 by omega]

end Stacks.LocalCohomology

end
