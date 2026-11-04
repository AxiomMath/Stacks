module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# A surjective open immersion of presheaves is an isomorphism

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of presheaves on
the big fppf site of `S` which is an open immersion in the sense of part (1) of
[Stacks Project, Tag 02YU] and whose induced map on the point sets of
[Stacks Project, Tag 03BU] is surjective is an isomorphism.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isOpenImmersion_of_surjective_pointsMap`: a surjective
  open immersion is an isomorphism.

## Implementation notes

An open immersion is in particular relatively representable, so surjectivity on points
transfers to surjectivity of every represented base change by the available direction of
[Stacks Project, Tag 03MD], `AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`; and
a relative open immersion which is surjective after every represented base change is an
isomorphism, which is
`AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`.

Neither input needs the source or the target to be an algebraic space, so no algebraicity
hypothesis is carried: representability of `f` is part of the open-immersion property itself.

There is no Lean-side substrate in the Stacks project for this statement — it is the
unbundling of a step used inside several of its proofs — so the result carries no `@[stacks]`
attribute.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves on the big fppf site of `S` which is an open immersion and whose
map on points is surjective is an isomorphism. -/
theorem isIso_of_isOpenImmersion_of_surjective_pointsMap (f : X ⟶ Y)
    (hf : IsOpenImmersion B S hS f)
    (hs : Function.Surjective (pointsMap B S hS X f)) :
    IsIso f :=
  isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS f hf
    (presheafSurjective_of_isSurjective B S hS f hf.rep hs)

end AlgebraicGeometry.Space

end
