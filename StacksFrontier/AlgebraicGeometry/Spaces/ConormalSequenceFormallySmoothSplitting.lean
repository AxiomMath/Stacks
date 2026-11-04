module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitting
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified morphism with formally smooth source

Let `B` be a big fppf site over a scheme `S`, let `Y` be an algebraic space (the base `B` of the
source; the letter `B` is taken here by the site, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramified.lean`), let
`h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `Y` and assume `Z` is
formally smooth over `Y`.  Stacks 06BJ asserts that the canonical sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of Stacks 060F is **split**, and so short exact.  The tag is proved, in the namespace
`AlgebraicGeometry.Space`, as
`IsUniversalFirstOrderThickening.conormalSequence_shortExact_of_formallySmooth` in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallySmoothShortExact.lean`.

The source's proof is three lines.  Let `Z ⊂ Z'` be the universal first order thickening of `Z`
over `X`; the sequence is identified with the sequence of Stacks 05ZA for the immersion
`ι : Z ⟶ Z'`, which is the content of Stacks 060F; formal smoothness of `Z` over `Y` produces,
étale locally on `Z'`, a left inverse `Z' ⟶ Z` over `Y` of `ι`; and a left inverse splits the
second arrow of that sequence, which is Stacks 05ZB.  This file records the identification of
the second arrow of the sequence of Stacks 060F with the second arrow of the sequence of
Stacks 05ZA, through which a splitting of the latter transports to the former.

## How the situation is presented

Exactly as in `ConormalSequenceFormallyUnramified.lean`: the datum is a universal first order
thickening `hZ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Z h'` of a
subfunctor `Z` of an algebraic space `Z'` over a structure morphism `h' : Z' ⟶ X`, the morphism
`h` of the source is the composite `ι ≫ h'` of the inclusion
`AlgebraicGeometry.Space.universalThickeningInclusion` with `h'`, and the middle term of the
sequence is read as the double inverse image `ι^*(h')^*Ω_{X/Y}`.

The two arrows of the sequence are the ones that file constructs,
`AlgebraicGeometry.Space.thickeningConormalFirstMap` and
`AlgebraicGeometry.Space.thickeningConormalSecondMap`, and no new arrow is built here.

## Main results

* `AlgebraicGeometry.Space.thickeningConormalSecondMap_eq`: the second arrow of the sequence of
  Stacks 060F is the isomorphism of Stacks 060E followed by the second arrow
  `AlgebraicGeometry.Space.pullbackDifferentialsMap` of the sequence of Stacks 05ZA for
  `Z ⊂ Z'` over `Y`.  This holds by construction.

## References

* [Stacks Project, Tag 06BJ](https://stacks.math.columbia.edu/tag/06BJ)
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F), the sequence.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the splitting criterion
  — Lemma 76.7.11 of the source's proof.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence of
  an immersion, which the sequence of Stacks 060F is transported from.
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E), the identification of the
  middle term.
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607), the universal first order
  neighbourhood and the conormal sheaf `𝒞_{Z/X}`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-! ### The second arrow of the sequence of Stacks 060F, as a composite -/

/-- The second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` of the sequence of Stacks 060F is the isomorphism
`AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` of Stacks 060E followed by the second
arrow `AlgebraicGeometry.Space.pullbackDifferentialsMap` of the sequence of Stacks 05ZA for the
closed subspace `Z ⊂ Z'` over `Y`.

This holds by construction — it is the defining equation of
`AlgebraicGeometry.Space.thickeningConormalSecondMap` — and is recorded so that a splitting of
the sequence of Stacks 05ZA may be transported by rewriting with it rather than unfolding the
definition. -/
theorem thickeningConormalSecondMap_eq (hZ : IsUniversalFirstOrderThickening B S hS Z h')
    (p : X ⟶ Y) :
    thickeningConormalSecondMap B S hS hZ p =
      thickeningSheafOfDifferentialsMap B S hS hZ p ≫
        pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) :=
  rfl

end AlgebraicGeometry.Space

end
