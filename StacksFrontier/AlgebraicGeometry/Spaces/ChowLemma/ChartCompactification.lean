module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechCharts
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# The projective compactification of an affine chart over `Spec R`

The proof of Stacks 089J, Chow's lemma for algebraic spaces over `Spec A`, begins by choosing
an affine scheme `W` with a surjective étale morphism to the algebraic space `X`, and then
embeds `W` as an *open* subscheme of a scheme `Y` which is H-projective over `Spec A`. This
file proves that second step, which is a statement about schemes alone: an affine scheme
locally of finite type over the spectrum of a ring is H-quasi-projective over it, and
therefore — by Stacks 01WA — an open subscheme of a scheme projective over it.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isHQuasiProjective_of_isAffine_toSpec`: an affine scheme locally of
  finite type over `Spec R` is H-quasi-projective over `Spec R`.
* `AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec`: such an
  affine scheme is an open subscheme of a scheme projective over `Spec R`, compatibly with the
  structure morphisms.

## What is and is not proved

Stacks 089J itself is not proved; see
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/Basic.lean` for its statement and for the gap.
Neither result here carries a Stacks attribute: the first is an unlabelled step of the proof
of Stacks 089J, and the second is an application of Stacks 01WA, which is already carried by
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`.

The immersion into projective space is
`AlgebraicGeometry.exists_isImmersion_projectiveSpaceOver_of_isAffine`, a closed immersion
into an affine space over the base followed by a standard chart of a projective space over
it. What H-quasi-projectivity adds to that immersion is quasi-compactness, which holds
because the source is a compact space and projective space over the spectrum of a ring is a
quasi-separated space — the latter being
`Stacks.ProjectiveCohomology.quasiSeparatedSpace_projectiveSpaceOverRing`, which is why the
base is written as a spectrum rather than as an arbitrary affine scheme.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **An affine scheme locally of finite type over `Spec R` is H-quasi-projective over
`Spec R`.** The immersion into a projective space over the base is
`AlgebraicGeometry.exists_isImmersion_projectiveSpaceOver_of_isAffine`; it is quasi-compact
because its source is a compact space and its target is a quasi-separated space.

This is the input of the step of the proof of Stacks 089J which replaces the affine étale
chart `W` of the algebraic space by an open subscheme of a scheme projective over the
base. -/
theorem isHQuasiProjective_of_isAffine_toSpec {R : CommRingCat.{u}} {W : Scheme.{u}}
    [IsAffine W] (g : W ⟶ Spec R) [LocallyOfFiniteType g] : IsHQuasiProjective g := by
  obtain ⟨m, j, hj, hjS⟩ := exists_isImmersion_projectiveSpaceOver_of_isAffine g
  have hqs : QuasiSeparatedSpace (projectiveSpaceOver m (Spec R)) :=
    Stacks.ProjectiveCohomology.quasiSeparatedSpace_projectiveSpaceOverRing m R
  exact ⟨m, j, hj, quasiCompact_of_compactSpace j, hjS⟩

/-- **An affine scheme locally of finite type over `Spec R` is an open subscheme of a scheme
projective over `Spec R`.** This is
`AlgebraicGeometry.isHQuasiProjective_of_isAffine_toSpec` followed by Stacks 01WA in the form
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`.

It is the choice of the scheme `Y`, H-projective over the base with `W ⊆ Y` open, with which
the proof of Stacks 089J forms the `d`-fold product in which the cover is cut out. -/
@[ega "III 5.2.6" "special case"]
theorem exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec {R : CommRingCat.{u}}
    {W : Scheme.{u}} [IsAffine W] (g : W ⟶ Spec R) [LocallyOfFiniteType g] :
    ∃ (Y : Scheme.{u}) (j : W ⟶ Y) (p : Y ⟶ Spec R),
      IsOpenImmersion j ∧ IsProjectiveMorphism p ∧ j ≫ p = g :=
  exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective
    (isHQuasiProjective_of_isAffine_toSpec g)

end AlgebraicGeometry

end
