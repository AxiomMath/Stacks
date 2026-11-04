module

public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup

/-!
# The strict transform of a composite

Let `g : W ⟶ X` and `f : X ⟶ A` be morphisms of algebraic spaces over `S` and let `b : A' ⟶ A`
be the blowing up of `A` in a closed subspace `Z`.  There are two ways to strictly transform `W`
down to a blowing up of `W`:

* in one step, as the strict transform of `g ≫ f : W ⟶ A` with respect to `b` and the inverse
  image of `Z` in `A'`;
* in two steps, first the strict transform `X' ⟶ X` of `f`, which by Stacks 0864 part (1) is the
  blowing up of `X` in `f⁻¹Z`, and then the strict transform of `g` with respect to *that*
  blowing up and the inverse image of `f⁻¹Z` in `X'`.

**This file proves the two agree**, canonically and compatibly with the morphisms to `W`.  The
library had nothing relating `strictTransform` of a composite to `strictTransform` of a factor at
the level of spaces: the comparisons it has are either for a composite of *blowing ups* (Stacks
0868, 080I) or for an étale restriction of the transformed morphism (Stacks 0863 part (2),
`AlgebraicGeometry.Space.strictTransformSubfunctor_le_preimage_of_isEtale`, whose proof needs a
chart of the source to be a chart of the target and so does not cover a general `g`).

## Main results

* `AlgebraicGeometry.Space.exists_iso_strictTransformSpace_comp_iterated`: the two strict
  transforms above are isomorphic over `W`.

## Implementation notes

**The proof is the universal property, not a chartwise computation.**  Stacks 0864 part (1),
`AlgebraicGeometry.Space.isBlowupAlong_strictTransform`, identifies each of the two spaces as a
blowing up of `W`: the one-step transform in `(g ≫ f)⁻¹Z`, the two-step one in `g⁻¹(f⁻¹Z)`.
Inverse images compose (`CategoryTheory.Subfunctor.preimage_comp`), so these are blowing ups of
`W` in the *same* closed subspace, and a blowing up in a given centre is unique up to unique
isomorphism over the base — `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`.  So no hypothesis
is needed on `g`; in particular the affineness that Step 1 of Stacks 0GV6 has available is not
used.

**This is not what Step 1 of Stacks 0GV6 needs.**  It is natural to expect this comparison to be
the step that identifies "the strict transform of a stratum's blowing up" with "the blowing up of
the pulled-back centre" in Step 1.  It is not: Stacks 0864 part (1) gives that identification
directly, and
`AlgebraicGeometry.Space.IsResolutionBlowupStratified.pullback_of_isAffineHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyStep1Pullback.lean` uses it
without any composite comparison.  The result here is recorded for its own sake.

**Relation to the nearest existing result.**  The uniqueness argument used here is the one of
`AlgebraicGeometry.Space.exists_iso_strictTransformSpace_comp_eq_strictTransformBlowUpComparison`
in `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformIsBlowup.lean`, which compares *one*
blowing up of `X` in `f⁻¹Z` with the strict transform of `f` in a fixed situation.  What is new
here is the situation, not the argument: the two sides live over different blowing ups (`b` and
the strict transform of `f` along `b`) and are blowing ups of `W` in centres that are only equal
*because inverse images compose*.  That identification of the two centres is the content, and it
is what is absent from the library.

**No hypothesis is carried.**  The only hypothesis is that `b` is a blowing up of `A` in `Z`,
which is what makes both sides blowing ups at all.

## References

* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A X W A' : AlgebraicSpaces B S hS} (g : W ⟶ X) (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1)

/-- **The strict transform of a composite agrees with the iterated strict transform.**  Let
`b : A' ⟶ A` be the blowing up of `A` in a closed subspace `Z`, let `f : X ⟶ A` and
`g : W ⟶ X`.  Write `bX : X' ⟶ X` for the strict transform of `f` with respect to `b` and the
inverse image of `Z` in `A'`, which by Stacks 0864 part (1) is the blowing up of `X` in `f⁻¹Z`.
Then the strict transform of `g ≫ f` with respect to `(b, b⁻¹Z)` and the strict transform of `g`
with respect to `(bX, bX⁻¹(f⁻¹Z))` are isomorphic, compatibly with their morphisms to `W`.

Both are blowing ups of `W` — the first in `(g ≫ f)⁻¹Z`, the second in `g⁻¹(f⁻¹Z)` — by Stacks
0864 part (1), and those two centres are equal because inverse images of subfunctors compose.  A
blowing up in a given centre is unique up to isomorphism over the base, which is the
isomorphism produced. -/
theorem exists_iso_strictTransformSpace_comp_iterated (hb : IsBlowupAlong B S hS Z b) :
    ∃ e : strictTransformSpace B S hS (g ≫ f) b (preimageClosedSubspace b Z).1 ≅
        strictTransformSpace B S hS g
          (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
            strictTransformPullbackToSource B S hS f b)
          (preimageClosedSubspace
            (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
              strictTransformPullbackToSource B S hS f b)
            (preimageClosedSubspace f Z)).1,
      e.hom ≫ (strictTransformSpaceι B S hS g
            (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
              strictTransformPullbackToSource B S hS f b)
            (preimageClosedSubspace
              (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
                strictTransformPullbackToSource B S hS f b)
              (preimageClosedSubspace f Z)).1 ≫
          strictTransformPullbackToSource B S hS g
            (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
              strictTransformPullbackToSource B S hS f b)) =
        strictTransformSpaceι B S hS (g ≫ f) b (preimageClosedSubspace b Z).1 ≫
          strictTransformPullbackToSource B S hS (g ≫ f) b := by
  -- the strict transform of `f`, which is the blowing up of `X` in `f⁻¹Z`
  have hbX : IsBlowupAlong B S hS (preimageClosedSubspace f Z)
      (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
        strictTransformPullbackToSource B S hS f b) :=
    isBlowupAlong_strictTransform B S hS f b Z hb
  -- the two blowing ups of `W`
  have h₁ : IsBlowupAlong B S hS (preimageClosedSubspace (g ≫ f) Z)
      (strictTransformSpaceι B S hS (g ≫ f) b (preimageClosedSubspace b Z).1 ≫
        strictTransformPullbackToSource B S hS (g ≫ f) b) :=
    isBlowupAlong_strictTransform B S hS (g ≫ f) b Z hb
  have h₂ := isBlowupAlong_strictTransform B S hS g
    (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
      strictTransformPullbackToSource B S hS f b) (preimageClosedSubspace f Z) hbX
  -- the two centres are the same closed subspace of `W`
  have hcentre : preimageClosedSubspace (g ≫ f) Z =
      preimageClosedSubspace g (preimageClosedSubspace f Z) :=
    Subtype.ext (Subfunctor.preimage_comp Z.1 g.hom f.hom)
  rw [hcentre] at h₁
  obtain ⟨e, he⟩ := IsBlowupAlong.exists_iso h₁ h₂
  exact ⟨e, he⟩

end AlgebraicGeometry.Space

end
