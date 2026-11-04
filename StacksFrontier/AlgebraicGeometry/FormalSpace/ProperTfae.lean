module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperAffineCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperAffineLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperFormalAtlas

/-!
# The equivalent characterisations of a proper morphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
fppf sheaves over `S`. **Stacks 0ART** lists five equivalent conditions on `f`:

1. `f` is proper (**Stacks 0AM6**);
2. every base change of `f` along a scheme over `S` in the site is proper;
3. every base change of `f` along an *affine* scheme over `S` in the site is proper;
4. every base change of `f` along an affine scheme `Z` over `S` in the site is an algebraic
   space over `S` whose projection to `Z` is proper as a morphism of algebraic spaces;
5. there is a covering `{Y_i ⟶ Y}` of the target as in Definition 0AIM all of whose base
   changes of `f` are proper.

The first four are assembled here into one equivalence, and all five into another, the latter
under the standing hypothesis of Stacks 0ART that the target be a formal algebraic space, which
is what condition (5) needs to follow from the others.

## Main results

* `AlgebraicGeometry.FormalSpace.isProper_tfae`: conditions (1), (2), (3) and (4) of
  **Stacks 0ART** are equivalent.
* `AlgebraicGeometry.FormalSpace.isProper_tfae_of_isFormalAlgebraicSpace`: all five conditions
  of **Stacks 0ART** are equivalent, for a morphism whose target is a formal algebraic space.

## Implementation notes

The cycle on the first four conditions is closed by (3) ⇒ (1),
`AlgebraicGeometry.FormalSpace.IsProperOnAffineBaseChanges.isProper`, which is the only
implication of that list needing Stacks 02WQ in the value universe of a formal algebraic space.
The remaining arrows are in `StacksFrontier.AlgebraicGeometry.FormalSpace.Proper` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.ProperAffineCriterion`.

Condition (5) is attached to the cycle by the two arrows
`AlgebraicGeometry.FormalSpace.IsProper.hasProperFormalAtlas` and
`AlgebraicGeometry.FormalSpace.HasProperFormalAtlas.isProper`. Only the first of them uses that
`Y` is a formal algebraic space — the covering it produces is an atlas of `Y` — so
(5) ⇒ (1) is available with no hypothesis on `X` or `Y` beyond the sheaf condition and is
stated that way in `StacksFrontier.AlgebraicGeometry.FormalSpace.ProperFormalAtlas`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0ART](https://stacks.math.columbia.edu/tag/0ART)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ART, conditions (1), (2), (3) and (4) are equivalent.** For a morphism of fppf
sheaves on the big fppf site of `S`: being proper, having every base change along a scheme of
the site proper, having every base change along an affine scheme of the site proper, and having
every base change along an affine scheme `Z` of the site be an algebraic space over `S` proper
over `Z`, are the same condition.

The cycle is closed by (3) ⇒ (1). Condition (5) of the source asks nothing of `X` or `Y` in
`AlgebraicGeometry.FormalSpace.HasProperFormalAtlas.isProper` but needs `Y` to be a formal
algebraic space to follow from the others, so it is added to the list separately in
`AlgebraicGeometry.FormalSpace.isProper_tfae_of_isFormalAlgebraicSpace`. -/
@[stacks 0ART "(1), (2), (3) and (4) are equivalent"]
theorem isProper_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    List.TFAE
      [IsProper B S hS f,
        IsProperOnSchemeBaseChanges B S hS f,
        IsProperOnAffineBaseChanges B S hS f,
        IsAlgebraicAndProperOnAffineBaseChanges B S hS f] := by
  tfae_have 1 ↔ 2 := isProper_iff_isProperOnSchemeBaseChanges B S hS f
  tfae_have 2 → 3 := fun h ↦ h.isProperOnAffineBaseChanges B S hS
  tfae_have 3 ↔ 4 := isProperOnAffineBaseChanges_iff_isAlgebraicAndProper B S hS f
  tfae_have 3 → 1 := IsProperOnAffineBaseChanges.isProper B S hS
  tfae_finish

/-- **Stacks 0ART.** For a morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S`
whose target is a formal algebraic space over `S`, the five conditions of the source are
equivalent: `f` is proper; every base change of `f` along a scheme of the site is proper; every
base change of `f` along an affine scheme of the site is proper; every base change of `f` along
an affine scheme `Z` of the site is an algebraic space over `S` proper over `Z`; and there is
one covering of `Y` as in Definition 0AIM all of whose base changes of `f` are proper.

The first four are `AlgebraicGeometry.FormalSpace.isProper_tfae`, which needs no hypothesis on
`Y`; the fifth is attached by `AlgebraicGeometry.FormalSpace.IsProper.hasProperFormalAtlas`,
which reads an atlas of `Y` off the hypothesis, and by
`AlgebraicGeometry.FormalSpace.HasProperFormalAtlas.isProper`. -/
@[stacks 0ART "all five conditions are equivalent"]
theorem isProper_tfae_of_isFormalAlgebraicSpace {X Y : FppfSheaf B S hS}
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsProper B S hS f,
        IsProperOnSchemeBaseChanges B S hS f,
        IsProperOnAffineBaseChanges B S hS f,
        IsAlgebraicAndProperOnAffineBaseChanges B S hS f,
        HasProperFormalAtlas B S hS f] := by
  have h := isProper_tfae B S hS f
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 1 ↔ 4 := h.out 1 4
  tfae_have 1 ↔ 3 := h.out 1 3
  tfae_have 1 → 5 := IsProper.hasProperFormalAtlas B S hS hY
  tfae_have 5 → 1 := HasProperFormalAtlas.isProper B S hS
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
