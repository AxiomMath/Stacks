module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceLocallyQuasiFinite
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# A locally quasi-finite morphism over a normal base with no positive weighting

Stacks 0GKJ says that a locally quasi-finite morphism onto a geometrically unibranch locally
Noetherian scheme carries a *positive* weighting, and cites Stacks 0F3E for it; but 0F3E produces
a weighting with values in the nonnegative integers, and a positive weighting — one with values
in the strictly positive integers, as More on Morphisms, Section 37.75 defines the word — does not
exist in that generality. This file exhibits the morphism that shows it: the closed immersion of
the closed point `(2)` into `Spec ℤ`.

The base `Spec ℤ` is normal, hence geometrically unibranch, and Noetherian, so Stacks 0GKJ applies
to this morphism verbatim. It carries the nonnegative weighting of
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch` and no
positive one, because a locally quasi-finite morphism with a positive weighting is universally
open by Stacks 0F3C while this one is not even open: its range misses the generic point of
`Spec ℤ`, which every open set meeting the closed point contains.

## Main results

* `AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` — there is
  a locally quasi-finite morphism locally of finite type onto a scheme which is normal,
  geometrically unibranch and locally Noetherian, carrying a nonnegative weighting and no
  positive weighting.

## Implementation notes

The witness is `Spec` of the reduction `ℤ → ℤ/2`, a surjective ring map, so the morphism is a
closed immersion and therefore finite, locally of finite type and locally quasi-finite.
Non-openness is checked without computing the range: every point of the source is carried to a
prime of `ℤ` containing `2`, so the generic point `(0)` is not in the range, while an open set
containing a point contains everything that point is a specialization of
(`Specializes.mem_open`), and `(0) ≤ p` makes every `p` a specialization of `(0)`.

The statement is at `Scheme.{0}`, the universe `ℤ` lives in; it is an existence statement about
one morphism, so nothing is gained by lifting it.

## References

* [Stacks Project, Tag 0GKJ](https://stacks.math.columbia.edu/tag/0GKJ)
* [Stacks Project, Tag 0F3C](https://stacks.math.columbia.edu/tag/0F3C)
* [Stacks Project, Tag 0F3E](https://stacks.math.columbia.edu/tag/0F3E)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- The reduction `ℤ → ℤ/2`, as a morphism of `CommRingCat`. -/
private def intToZModTwo : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (Int.castRingHom (ZMod 2))

/-- The closed immersion of the closed point `(2)` into `Spec ℤ`. -/
private noncomputable def specZModTwoToSpecInt :
    Spec (CommRingCat.of (ZMod 2)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map intToZModTwo

private theorem isClosedImmersion_specZModTwoToSpecInt :
    IsClosedImmersion specZModTwoToSpecInt :=
  IsClosedImmersion.spec_of_surjective intToZModTwo
    fun a => ZMod.intCast_surjective (n := 2) (show ZMod 2 from a)

/-- Every point of the source is carried to a prime ideal of `ℤ` containing `2`. -/
private theorem two_mem_specZModTwoToSpecInt (x : Spec (CommRingCat.of (ZMod 2))) :
    (2 : ℤ) ∈ (specZModTwoToSpecInt x).asIdeal := by
  show ((2 : ℤ) : ZMod 2) ∈ x.asIdeal
  rw [show ((2 : ℤ) : ZMod 2) = 0 by decide]
  exact x.asIdeal.zero_mem

/-- The closed immersion of the closed point `(2)` into `Spec ℤ` is not an open map: the generic
point of `Spec ℤ` is not in its range, while an open range would have to contain it. -/
private theorem not_isOpenMap_specZModTwoToSpecInt :
    ¬ IsOpenMap specZModTwoToSpecInt.base := by
  intro hopen
  let source : Spec (CommRingCat.of (ZMod 2)) := ⟨⊥, Ideal.isPrime_bot⟩
  let generic : Spec (CommRingCat.of ℤ) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨preimage, hpreimage⟩ : generic ∈ Set.range specZModTwoToSpecInt.base :=
    ((PrimeSpectrum.le_iff_specializes generic (specZModTwoToSpecInt source)).mp
      bot_le).mem_open hopen.isOpen_range ⟨source, rfl⟩
  have htwo := two_mem_specZModTwoToSpecInt preimage
  rw [hpreimage] at htwo
  exact absurd (Ideal.mem_bot.mp htwo) (by norm_num)

/-- **The word *positive* in Stacks 0GKJ asks for more than its hypotheses give.** There is a
locally quasi-finite morphism locally of finite type onto a scheme which is normal, hence
geometrically unibranch, and locally Noetherian, which carries a nonnegative weighting — the
generic-separable-degree weighting of Stacks 0F3E, as
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch` produces
it — and which carries no weighting with strictly positive values.

The witness is the closed immersion of the closed point `(2)` into `Spec ℤ`. It is locally
quasi-finite because it is a closed immersion, and it is not universally open because it is not
open: the generic point of `Spec ℤ` is not in its range. So Stacks 0F3C, in the contrapositive
form `AlgebraicGeometry.not_exists_positive_weighting_of_not_universallyOpen`, forbids a positive
weighting for it.

This is why the statements of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceLocallyQuasiFinite`
assert `0 ≤ w x` and not `0 < w x`: the latter is false at the hypotheses of Stacks 0GKJ. The
nonnegative weighting is what Stacks 0F3E, the lemma Stacks 0GKJ cites for its weighting, in fact
produces, and everything the example asserts about the weighting other than that one word is
carried in full. -/
public theorem exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting :
    ∃ (X Y : Scheme.{0}) (f : X ⟶ Y),
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f ∧ IsLocallyNoetherian Y ∧ IsNormal Y ∧
        IsGeometricallyUnibranch Y ∧
        (∃ w : X → ℤ, IsWeighting f w ∧ ∀ x : X, 0 ≤ w x) ∧
        ¬ ∃ w : X → ℤ, IsWeighting f w ∧ ∀ x : X, 0 < w x := by
  have := isClosedImmersion_specZModTwoToSpecInt
  have hnormal : IsNormal (Spec (CommRingCat.of ℤ)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed ℤ)
  exact ⟨_, _, specZModTwoToSpecInt, inferInstance, inferInstance, inferInstance, hnormal,
    isGeometricallyUnibranch_of_isNormal,
    exists_nonneg_weighting_of_isGeometricallyUnibranch specZModTwoToSpecInt
      isGeometricallyUnibranch_of_isNormal,
    not_exists_positive_weighting_of_not_universallyOpen specZModTwoToSpecInt
      fun huniversallyOpen => not_isOpenMap_specZModTwoToSpecInt
        (Scheme.Hom.isOpenMap specZModTwoToSpecInt)⟩

end AlgebraicGeometry

end
