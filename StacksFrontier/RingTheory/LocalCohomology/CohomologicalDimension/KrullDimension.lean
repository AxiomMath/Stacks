module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.AffineComplement
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.LocalDimensionBound
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Local cohomology vanishes above the dimension

Let `I` be a finitely generated ideal of a commutative ring `A`. The cohomological dimension
`cd(A, I)` of Stacks 0DX8 is at most the Krull dimension of `A`, and the local cohomology
`H^i_{V(I)}(M)` of a finite `A`-module `M` vanishes in every degree `i` above the dimension of
the support of `M`.

Both statements reduce, by Stacks 0DXB and Stacks 0BJB, to the bound `cd(A, I) ≤ dim A` for a
*local* ring `A`, and that is what is proved here. If `V(I)` is empty or `dim A = 0` there is
nothing to do. Otherwise `V(I)` contains the closed point, so the open `U = Spec A ∖ V(I)` has
Krull dimension strictly below `dim A`; being a quasi-compact open of a spectral space it is
itself spectral, so Stacks 0A3G makes the cohomology of every abelian sheaf on `U` vanish in
degrees at least `dim A`. That is the third of the equivalent conditions of Stacks 0DX7 for the
bound `dim A`, whose first condition is the vanishing of `H^i_{V(I)}(A)` for `i > dim A`.

## Main results

* `Stacks.LocalCohomology.spectralSpace_complZeroLocusOpen` — the complement of the zero locus
  of a finitely generated ideal is a spectral space.
* `Stacks.LocalCohomology.cohomologicalDimension_le_of_isLocalRing_of_ringKrullDim_le` — the
  local case of the bound.
* `Stacks.LocalCohomology.cohomologicalDimension_le_of_ringKrullDim_le` — **Stacks 0DXC**, the
  bound `cd(A, I) ≤ dim A` for an arbitrary ring.
* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_supportDim_lt` — **Stacks 0DXC**, the
  vanishing of `H^i_{V(I)}(M)` for `i > dim (Supp M)`.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0902](https://stacks.math.columbia.edu/tag/0902)
* [Stacks Project, Tag 090M](https://stacks.math.columbia.edu/tag/090M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-- The complement of the zero locus of a finitely generated ideal is a spectral space: it is a
quasi-compact open of the spectrum of the ring, which is spectral. -/
theorem spectralSpace_complZeroLocusOpen
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    SpectralSpace (complZeroLocusOpen A I).toScheme :=
  have : SpectralSpace (Spec (CommRingCat.of A)) :=
    inferInstanceAs (SpectralSpace (PrimeSpectrum A))
  have : CompactSpace (complZeroLocusOpen A I).toScheme :=
    compactSpace_complZeroLocusOpen A I hI
  Topology.IsOpenEmbedding.spectralSpace (complZeroLocusOpen A I).ι.isOpenEmbedding

/-- An ideal of a local ring with nonempty zero locus is contained in the maximal ideal: a prime
containing it is contained in the maximal ideal. -/
theorem le_maximalIdeal_of_zeroLocus_nonempty
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hne : (PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) :
    I ≤ IsLocalRing.maximalIdeal A := by
  obtain ⟨p, hp⟩ := hne
  exact ((PrimeSpectrum.mem_zeroLocus _ _).mp hp).trans
    (IsLocalRing.le_maximalIdeal p.2.ne_top)

/-- Over a local ring of Krull dimension at most `m + 1`, the cohomology of any module on
`Spec A ∖ V(I)` vanishes in every degree at least `m + 1`, for an ideal `I` contained in the
maximal ideal: that open is a spectral space of Krull dimension at most `m`, and the cohomology
of an abelian sheaf on a spectral space vanishes above its dimension. -/
theorem isZero_hgroup_complZeroLocusOpen_of_ringKrullDim_le
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I.FG)
    (hIm : I ≤ IsLocalRing.maximalIdeal A) (m : ℕ)
    (hd : ringKrullDim A ≤ ((m + 1 : ℕ) : WithBot ℕ∞))
    (F : ((complZeroLocusOpen A I) : Scheme).Modules)
    (n : ℕ) (hn : m + 1 ≤ n) :
    IsZero (Hgroup ((complZeroLocusOpen A I) : Scheme).ringCatSheaf ⊤ n F) := by
  have hsp : SpectralSpace (complZeroLocusOpen A I).toScheme :=
    spectralSpace_complZeroLocusOpen A I hI
  have hdim : topologicalKrullDim (complZeroLocusOpen A I).toScheme ≤ (m : WithBot ℕ∞) :=
    withBotENat_le_of_lt_succ _ m (specOpenComplement_toScheme_dim_lt A I hIm (m + 1) hd)
  have hext : HasExt.{u} (Sheaf
      (Opens.grothendieckTopology (complZeroLocusOpen A I).toScheme) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  refine isZero_Hgroup_of_subsingleton_sheafCohomology F n (by omega) ?_
  exact CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le m
    (complZeroLocusOpen A I).toScheme inferInstance hext _ n hdim (by omega)

/-- **The local case of Stacks Project, Tag 0DXC.** Over a local ring of Krull dimension at most
`e ≥ 1`, a finitely generated ideal with nonempty zero locus has cohomological dimension at
most `e`.

The complement of the zero locus misses the closed point, so it is a spectral space of dimension
below `e`; its cohomological vanishing in degrees at least `e` is the third condition of
Stacks 0DX7 for the bound `e`, and the first condition of that tag is the assertion. -/
theorem cohomologicalDimension_le_of_isLocalRing_of_ringKrullDim_le
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I.FG)
    (hne : (PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) (e : ℕ) (he : 1 ≤ e)
    (hd : ringKrullDim A ≤ (e : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (e : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, e = m + 1 := ⟨e - 1, by omega⟩
  have hIm := le_maximalIdeal_of_zeroLocus_nonempty A I hne
  refine cohomologicalDimension_le A I hI _ ⟨by omega, ?_⟩
  have h := (localCohomology_vanishing_tfae.{u, u} A I hI ((m + 1 : ℕ) : ℤ) (by omega)).out 3 1
  refine h.mp ⟨fun hneg => absurd hneg (by omega), fun hzero => absurd hzero (by omega), ?_⟩
  intro _ _ F _ n hn
  exact isZero_hgroup_complZeroLocusOpen_of_ringKrullDim_le A I hI hIm m hd F n
    (by exact_mod_cast hn)

/-- **Stacks Project, Tag 0DXC.** The cohomological dimension of a finitely generated ideal of a
commutative ring is at most the Krull dimension of the ring.

By Stacks 0DXB the cohomological dimension is the supremum of the cohomological dimensions of
the localizations `A_𝔭`, each local of dimension `ht 𝔭 ≤ dim A`. -/
@[stacks 0DXC "the bound of the cohomological dimension by the Krull dimension"]
theorem cohomologicalDimension_le_of_ringKrullDim_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    cohomologicalDimension A I hI ≤ (d : ℤ) :=
  cohomologicalDimension_le_ringKrullDim_of_isLocalRing_of_one_le
    (fun B _ _ J hJ hne e he1 he =>
      cohomologicalDimension_le_of_isLocalRing_of_ringKrullDim_le B J hJ hne e he1 he)
    A I hI d hd

/-- **Stacks Project, Tag 0DXC.** For a finite module `M` over a commutative ring `A` and a
finitely generated ideal `I ⊆ A`, the local cohomology `H^i_{V(I)}(M)` vanishes in every degree
`i` above the dimension of the support of `M`.

With `𝔞 = ann(M)` and `B = A/𝔞` one has `Spec B = Supp M`, so `dim B = dim Supp M < i`; the
bound `cd(B, IB) ≤ i - 1` then gives the vanishing through Stacks 0BJB and the implication
(1) ⇒ (2) of Stacks 0DX7. A subsingleton module is treated separately, the dimension of an empty
support being `⊥`. -/
@[stacks 0DXC "the vanishing above the dimension of the support", sga "2 V 3.1" "(i)"]
theorem isZero_localCohomologyModule_of_supportDim_lt
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
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
    refine (cohomologicalDimension_le_of_ringKrullDim_le (A ⧸ Module.annihilator A M)
      (I.map (Ideal.Quotient.mk (Module.annihilator A M)))
      (hI.map (Ideal.Quotient.mk (Module.annihilator A M))) (i.toNat - 1) hdim).trans ?_
    rw [show ((i.toNat - 1 : ℕ) : ℤ) = (i.toNat : ℤ) - 1 by omega]

end Stacks.LocalCohomology

end
