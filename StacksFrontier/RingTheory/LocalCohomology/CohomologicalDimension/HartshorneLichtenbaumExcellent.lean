module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.AffineComplement
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaumCompletion
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom

/-!
# Hartshorne–Lichtenbaum vanishing over an excellent normal local ring

Let `A` be an excellent normal Noetherian local ring of dimension `d` and let `I ⊆ A` be an ideal
with `dim V(I) ≥ 1`. Then the cohomological dimension of `I` in `A` is strictly less than `d`,
and when `d = 2` the open `Spec A ∖ V(I)` is affine.

Excellence makes the completion `A^∧` normal (Stacks 0C23, through the regularity of the formal
fibres of a G-ring), hence a domain, so `(0)` is its only minimal prime and
`dim V(I A^∧ + (0)) = dim V(I A^∧) ≥ 1`: a chain of two primes containing `I` lifts along the
faithfully flat map `A → A^∧` by going down. That is the hypothesis of Stacks 0EB6. In dimension
two the resulting bound reads `cd(A, I) ≤ 1`, so the cohomology of every quasi-coherent module on
`U = Spec A ∖ V(I)` vanishes in all degrees `≥ 1` by (1) ⟹ (3) of Stacks 0DX7; since `U` is
quasi-compact, Serre's criterion (Stacks 01XF) makes it affine.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_isExcellent_of_isNormalRing` —
  **[Stacks Project, Tag 0EB7]**, the cohomological dimension bound.
* `Stacks.LocalCohomology.isAffineOpen_complZeroLocusOpen_of_isExcellent_of_isNormalRing` —
  **[Stacks Project, Tag 0EB7]**, affineness of the complement in dimension two.

## Implementation notes

`dim V(I)` is the Krull dimension of `A ⧸ I`, the spelling the hypothesis of Stacks 0EB6 uses,
and the dimension of `A` is carried as a natural number `d` together with
`ringKrullDim A = (d : WithBot ℕ∞)`, as in the neighbouring statements. Normality is the
library's `IsNormalRing`: every localization at a prime is an integrally closed domain.

The affineness half uses Serre's criterion in the form stated for the repository's own
cohomology, `Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal`, because that is
the spelling in which (1) ⟹ (3) of Stacks 0DX7 delivers the vanishing.

## References

* [Stacks Project, Tag 0EB7](https://stacks.math.columbia.edu/tag/0EB7)
* [Stacks Project, Tag 0EB6](https://stacks.math.columbia.edu/tag/0EB6)
* [Stacks Project, Tag 0C23](https://stacks.math.columbia.edu/tag/0C23)
* [Stacks Project, Tag 0DXD](https://stacks.math.columbia.edu/tag/0DXD)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 0AH2](https://stacks.math.columbia.edu/tag/0AH2)
* [Stacks Project, Tag 0BFK](https://stacks.math.columbia.edu/tag/0BFK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Normality of the completion -/

/-- The completion at the maximal ideal of an excellent normal Noetherian local ring is normal:
an excellent ring is a G-ring, so the map to the completion is a regular ring map (Stacks 0AH2),
and normality ascends along a regular ring map (Stacks 0BFK). -/
@[ega "IV 7.8.3" "(v)"]
private theorem isNormalRing_adicCompletion_maximalIdeal_of_isExcellent
    (A : Type u) [CommRing A] [IsLocalRing A] (hnormal : IsNormalRing A) (hA : IsExcellent A) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  have : IsNoetherianRing A := hA.1.1
  have hreg : IsRegularRingHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :=
    isRegularRingHom_algebraMap_adicCompletion hA.1.2.1 (IsLocalRing.maximalIdeal A)
  rw [isRegularRingHom_iff_of_eq_algebraMap _ rfl] at hreg
  exact isNormalRing_of_flat_of_isGeometricallyRegular_fiber A
    (AdicCompletion (IsLocalRing.maximalIdeal A) A) hnormal fun q _ => (hreg.2 q).2

/-! ### Positivity of the dimension of a quotient after a faithfully flat base change -/

/-- Along a faithfully flat ring map, positivity of the dimension of `R ⧸ K` is inherited by
`S ⧸ KS`: the top prime of a chain of two primes containing `K` has a prime of `S` over it, going
down produces a prime of `S` below that one over the bottom of the chain, and both contain the
image ideal. -/
private theorem one_le_ringKrullDim_quotient_map_of_faithfullyFlat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (K : Ideal R)
    (hK : (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ K)) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ K.map (algebraMap R S)) := by
  rw [ringKrullDim_quotient, Order.one_le_krullDim_iff] at hK
  rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, hpq⟩ := hK
  have hKp : K ≤ p.asIdeal := PrimeSpectrum.mem_zeroLocus _ _ |>.mp hp
  have hpq' : p.asIdeal < q.asIdeal := hpq
  have hqp : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨Q, hQprime, hQover⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := S) q.asIdeal
  have hpp : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨P, hPQ, hPprime, hPover⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (p := p.asIdeal) (q := q.asIdeal)
      Q hpq'
  have hKP : K.map (algebraMap R S) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (hKp.trans hPover.over.le)
  refine ⟨⟨⟨P, hPprime⟩, ?_⟩, ⟨⟨Q, hQprime⟩, ?_⟩, ?_⟩
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hKP
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hKP.trans hPQ.le)
  · exact hPQ

/-! ### Hartshorne–Lichtenbaum vanishing for an excellent normal local ring -/

/-- **[Stacks Project, Tag 0EB7].** Let `A` be an excellent normal Noetherian local ring of
dimension `d` and let `I ⊆ A` be an ideal with `dim V(I) ≥ 1`. Then the cohomological dimension
of `I` in `A` is strictly less than `d`. -/
@[stacks 0EB7 "cd(A, I) < dim(A)"]
theorem cohomologicalDimension_lt_of_isExcellent_of_isNormalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsExcellent A) (hnormal : IsNormalRing A)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (I : Ideal A)
    (hI : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I)) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  have hff : Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (IsLocalRing.maximalIdeal A)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hC : IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    isNormalRing_adicCompletion_maximalIdeal_of_isExcellent A hnormal hA
  have hdom : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A) := hC.of_isLocalRing.1
  refine cohomologicalDimension_lt_of_minimalPrimes_adicCompletion A d hd I ?_
  intro q hqmin _
  have hqbot : q.asIdeal = ⊥ := (hqmin.eq_of_le ⟨Ideal.isPrime_bot, bot_le⟩ bot_le).symm
  rw [hqbot, Ideal.add_eq_sup, sup_bot_eq]
  exact one_le_ringKrullDim_quotient_map_of_faithfullyFlat A
    (AdicCompletion (IsLocalRing.maximalIdeal A) A) I hI

/-- **[Stacks Project, Tag 0EB7].** For an excellent normal Noetherian local ring `A` of
dimension two and an ideal `I ⊆ A` with `dim V(I) ≥ 1`, the open `Spec A ∖ V(I)` is affine.

The cohomological dimension bound gives `cd(A, I) ≤ 1`, hence the vanishing of the cohomology of
every quasi-coherent module on the complement in degrees `≥ 1` by Stacks 0DX7; the complement is
quasi-compact, so Serre's criterion applies. This is the route of Stacks 0DXD. -/
@[stacks 0EB7 "Spec(A) ∖ V(I) is affine when dim(A) = 2"]
theorem isAffineOpen_complZeroLocusOpen_of_isExcellent_of_isNormalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsExcellent A) (hnormal : IsNormalRing A)
    (hd : ringKrullDim A = (2 : WithBot ℕ∞)) (I : Ideal A)
    (hI : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I)) :
    IsAffineOpen (complZeroLocusOpen A I) := by
  have hfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hd2 : ringKrullDim A = ((2 : ℕ) : WithBot ℕ∞) := by rw [hd]; norm_num
  have hcd : cohomologicalDimension A I hfg < ((2 : ℕ) : ℤ) :=
    cohomologicalDimension_lt_of_isExcellent_of_isNormalRing A hA hnormal 2 hd2 I hI
  have hcd2 : cohomologicalDimension A I hfg < 2 := by exact_mod_cast hcd
  have hcdle : cohomologicalDimension A I hfg ≤ 1 := by omega
  have h₁ : ∀ i : ℤ, (1 : ℤ) < i →
      IsZero (localCohomologyModule A I hfg (ModuleCat.of A A) i) := fun i hi =>
    (isLocalCohomologyBound_cohomologicalDimension A I hfg).2 i (lt_of_le_of_lt hcdle hi)
  have h₃ := ((localCohomology_vanishing_tfae.{u, u} A I hfg 1 (by norm_num)).out 1 3).mp h₁
  have hvan := h₃.2.2 (by norm_num : (0 : ℤ) < 1)
  have : CompactSpace (complZeroLocusOpen A I).toScheme :=
    compactSpace_complZeroLocusOpen A I hfg
  exact Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal
    (complZeroLocusOpen A I) fun J hJ => hvan _ hJ 1 (by norm_num)

end Stacks.LocalCohomology

end
