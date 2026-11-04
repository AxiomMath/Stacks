module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# The small étale topos of an algebraic space

The *small étale topos* of an algebraic space is the category of sheaves of sets on its
small étale site. The site itself is `AlgebraicGeometry.Space.SmallEtale`, built in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSite.lean` for an arbitrary presheaf `F` on
the big fppf site of `S`, and the topos is named here at the same generality.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTopos`: the category of sheaves of sets on the small
  étale site of `F`.

## Implementation notes

This is an abbreviation for a `CategoryTheory.Sheaf` category, so the whole sheaf API —
limits, colimits, sheafification, the morphisms of topoi — applies to it unchanged. The
coefficients are `Type (u + 1)`, the universe in which the small étale site has its
morphisms; the site is essentially small at `u`, so this category is equivalent to one with
coefficients in `Type u`.

No algebraic-space hypothesis on `F` enters the definition: the small étale site of a
presheaf is defined without one, and the topos is the sheaf category over it. For an
algebraic space in the sense of `AlgebraicGeometry.IsAlgebraicSpace` this is the small étale
topos of the Stacks project.

## References

* [Stacks Project, Tag 04JT](https://stacks.math.columbia.edu/tag/04JT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04JT.** The category of sheaves of sets on the small étale site of a presheaf
`F` on the big fppf site of `S`; for an algebraic space, its small étale topos. -/
@[stacks 04JT]
abbrev smallEtaleTopos (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Sheaf (SmallEtale.topology B S hS F) (Type (u + 1))

end AlgebraicGeometry.Space

end
