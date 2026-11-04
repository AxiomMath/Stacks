module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# The Picard group of the punctured spectrum of a regular local ring

Let `(A, 𝔪)` be a regular local ring and let `U = Spec A ∖ {𝔪}` be its punctured spectrum. Then
`Pic(U)` is trivial: a regular local ring is a unique factorization domain, and the Picard group
of every open subscheme of the spectrum of a unique factorization domain vanishes.

## Main results

* `Stacks.PicardUFD.subsingleton_picardGroup_puncturedSpectrum`: **Tag 0F2H.** The Picard group
  of the punctured spectrum of a regular local ring is trivial.
* `Stacks.PicardUFD.isTrivial_of_isInvertible_puncturedSpectrum`: consequently every invertible
  module on the punctured spectrum of a regular local ring is isomorphic to the structure sheaf.

## Implementation notes

The punctured spectrum is `Stacks.Divisors.puncturedSpectrum`, the open complement of the closed
point of `Spec A`, which is the spelling the surrounding section uses.

Unique factorization comes from `IsRegularLocalRing.uniqueFactorizationMonoid`
([Stacks, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)) and the domain hypothesis from
`IsRegularLocalRing.isDomain` ([Stacks, Tag 00NP](https://stacks.math.columbia.edu/tag/00NP));
neither is an instance, by design, so both are supplied by hand. The triviality input is
`Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum`
([Stacks, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA), part (1)), which is the source's
own lemma covering the extension step
[Stacks, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9) that the proof of Tag 0F2H cites;
it carries no Noetherian hypothesis, so no hypothesis beyond regularity is used.

## References

* [Stacks Project, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.PicardUFD

/-- **Stacks Project, Tag 0F2H.** Let `(A, 𝔪)` be a regular local ring. Then the Picard group of
the punctured spectrum `Spec A ∖ {𝔪}` of `A` is trivial. -/
@[stacks 0F2H, sga "2 XI 3.13" "XI.3.13(i)"]
theorem subsingleton_picardGroup_puncturedSpectrum (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    Subsingleton (Stacks.Divisors.puncturedSpectrum A).toScheme.picardGroup := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : UniqueFactorizationMonoid A := IsRegularLocalRing.uniqueFactorizationMonoid A
  exact subsingleton_picardGroup_open_spectrum A (Stacks.Divisors.puncturedSpectrum A)

/-- Every invertible module on the punctured spectrum of a regular local ring is trivial, since
the Picard group of the punctured spectrum vanishes. -/
@[sga "2 XI 3.13" "XI.3.13(i)"]
theorem isTrivial_of_isInvertible_puncturedSpectrum (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatIsSheaf L) :
    Stacks.SheafOfModules.IsTrivial
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatIsSheaf L := by
  have := subsingleton_picardGroup_puncturedSpectrum A
  exact (Scheme.picardClass_eq_zero_iff _ L hL).1 (Subsingleton.elim _ _)

end Stacks.PicardUFD

end
