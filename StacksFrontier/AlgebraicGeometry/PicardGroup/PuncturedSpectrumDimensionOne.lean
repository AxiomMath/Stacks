module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# The Picard group of the punctured spectrum of a Noetherian local ring of dimension one

Let `A` be a Noetherian local ring of Krull dimension at most one. Then the punctured spectrum
`Spec A ∖ {𝔪}` is a *discrete* space — each of its points is a prime other than the maximal
ideal, hence not maximal, hence minimal, and there are finitely many minimal primes, no two of
which specialize to each other — and an invertible module on a scheme with discrete space is
trivial. So the Picard group of the punctured spectrum vanishes.

This is the dimension-one companion of
`Stacks.PicardUFD.subsingleton_picardGroup_puncturedSpectrum`, which is the regular case
([Stacks, Tag 0F2H]) and goes through unique factorization instead. Neither implies the other: a
Noetherian local ring of dimension one need not be regular or even reduced, and a regular local
ring need not have dimension at most one.

The statement is the hypothesis of the one-point extension of an invertible module,
`Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_puncturedOpen`, and so it is the
form in which "the Picard group is trivial on the punctured neighbourhood of a point" enters
clause (2) of [Stacks, Tag 09NA]: there the local rings along the complement of the retrocompact
open are Noetherian of dimension at most one, which is exactly this hypothesis.

## Main results

* `Stacks.PuncturedSpectrumArtinian.subsingleton_picardGroup_of_discreteTopology`: a scheme with
  discrete underlying space has trivial Picard group.
* `Stacks.PuncturedSpectrumArtinian.discreteTopology_of_notMem_closedPoint`: an open of the
  spectrum of a Noetherian local ring of Krull dimension at most one missing the closed point is
  discrete.
* `Stacks.PuncturedSpectrumArtinian.subsingleton_picardGroup_puncturedSpectrum`: **the Picard
  group of the punctured spectrum vanishes.**

## Implementation notes

The discreteness argument already occurs, inline, inside
`AlgebraicGeometry.isAffineOpen_of_krullDimLE_one`
(`StacksFrontier/AlgebraicGeometry/OneDimensionalLocal/Basic.lean`), where it is used to see that
such an open is a finite discrete scheme and hence affine. It is stated separately here because
affineness is not what the Picard statement needs: triviality comes from
`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`, which takes the discreteness
directly.

The ring-theoretic companion is
`StacksFrontier/RingTheory/LocalRing/PuncturedSpectrumArtinian.lean`, which says that inverting an
element of the maximal ideal makes such a ring Artinian; the two are the same fact in the two
languages, and the geometric one is stated for an arbitrary open missing the closed point rather
than for one basic open.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.SheafOfModules

universe u

namespace Stacks.PuncturedSpectrumArtinian

/-- **A scheme with discrete underlying space has trivial Picard group.** -/
theorem subsingleton_picardGroup_of_discreteTopology (Z : Scheme.{u})
    [DiscreteTopology (Z : Type u)] : Subsingleton Z.picardGroup := by
  refine Z.subsingleton_picardGroup fun L hL => ?_
  exact Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology Z L

/-- **An open of the spectrum of a Noetherian local ring of Krull dimension at most one missing
the closed point is discrete.** Every prime in it is not maximal, hence minimal; there are
finitely many minimal primes, and no two of them specialize to each other. -/
theorem discreteTopology_of_notMem_closedPoint (R : CommRingCat.{u}) [IsLocalRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (V : (Spec R).Opens)
    (hV : IsLocalRing.closedPoint R ∉ V) : DiscreteTopology V := by
  classical
  have hnotmax (p : V) : ¬ p.1.asIdeal.IsMaximal := by
    intro hp
    have hp' : p.1 = IsLocalRing.closedPoint R :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hp)
    exact hV (hp' ▸ p.2)
  have hmin (p : V) : p.1.asIdeal ∈ minimalPrimes R :=
    (Ring.krullDimLE_one_iff.mp ‹_› p.1.asIdeal p.1.2).resolve_right (hnotmax p)
  have hinj : Function.Injective
      (fun p : V ↦ (⟨p.1.asIdeal, hmin p⟩ : {I : Ideal R // I ∈ minimalPrimes R})) :=
    fun a b hab ↦ Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val hab))
  have : Finite {I : Ideal R // I ∈ minimalPrimes R} :=
    (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  have : Finite V := Finite.of_injective _ hinj
  have : T1Space V := t1Space_iff_specializes_imp_eq.mpr fun a b hab ↦
    Subtype.ext (PrimeSpectrum.ext
      (((IsMinimalPrime.iff_minimal _).mp (hmin b)).eq_of_le a.1.2
        ((PrimeSpectrum.le_iff_specializes a.1 b.1).mpr
          (hab.map continuous_subtype_val))))
  exact Finite.instDiscreteTopology

/-- **The Picard group of the punctured spectrum of a Noetherian local ring of Krull dimension
at most one is trivial.** -/
theorem subsingleton_picardGroup_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] :
    Subsingleton (Stacks.Divisors.puncturedSpectrum A).toScheme.picardGroup := by
  have : DiscreteTopology ((Stacks.Divisors.puncturedSpectrum A : (Spec (.of A)).Opens) :
      Type u) :=
    discreteTopology_of_notMem_closedPoint (.of A) _ (fun h => h rfl)
  exact subsingleton_picardGroup_of_discreteTopology _

end Stacks.PuncturedSpectrumArtinian

end
