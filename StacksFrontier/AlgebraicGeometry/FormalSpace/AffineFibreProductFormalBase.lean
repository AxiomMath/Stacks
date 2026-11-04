module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable

/-!
# Clause (1) of Stacks 0AN3 over a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X ⟶ Z` and `Y ⟶ Z` be morphisms of
fppf sheaves on the big fppf site of `S`. **Stacks 0AN3, clause (1)** says that if `Z` is a
separated formal algebraic space and `X` and `Y` are affine formal algebraic spaces, then so is
the fibre product `X ×_Z Y`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`:
  **Stacks 0AN3, clause (1)**, under the hypotheses the source states.

## Implementation notes

`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback` carries representability of
the relative products of representables over `Z`
(`AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts`) rather than asking that `Z` be
a formal algebraic space: that is the generality in which its proof runs, and it is the form
Stacks 0AJ2 consumes. The source's own hypothesis is that `Z` is a formal algebraic space over
`S`, and for such a `Z` the representability hypothesis is a theorem — the representability
assertion of **Stacks 0AIP**, available here as
`AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace`. So the
statement below is the one the source makes, and it is deduced by discharging that hypothesis.

Separatedness of `Z` is `AlgebraicGeometry.FormalSpace.IsSeparated`, clause (2) of Stacks 0AJ6 in
the reduction-free form which clause (2) of Stacks 0AJ7 names; it is the clause the proof of
Stacks 0AN3 uses. That it implies separatedness of the reduction, which is clause (1) of
Stacks 0AJ6, is `StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparated`; the converse is
not proved in this library.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AN3, clause (1).** The fibre product of two affine formal algebraic spaces over a
separated formal algebraic space is an affine formal algebraic space. -/
@[stacks 0AN3 "clause (1): the fibre product of two affine formal algebraic spaces over a \
separated formal algebraic space, at the hypotheses of the source"]
theorem isAffineFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hZsep : IsSeparated B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS (pullback p q) :=
  isAffineFormalAlgebraicSpace_pullback B S hS p q
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ) hZsep hX hY

end AlgebraicGeometry.FormalSpace

end
