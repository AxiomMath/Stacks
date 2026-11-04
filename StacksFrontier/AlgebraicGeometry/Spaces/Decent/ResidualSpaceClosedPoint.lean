module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceUniqueness

/-!
# Residual spaces at closed points (Stacks 0H1U)

Let `X` be a locally Noetherian algebraic space over a scheme `S`, let `x` be a point of `|X|`
and let `f : Z ⟶ X` be a residual space of `X` at `x` in the sense of **Stacks 06R0**. Then
`x` is a closed point of `|X|` exactly when `f` is a closed immersion.

## Main results

* `AlgebraicGeometry.Space.IsResidualSpaceAt.isClosed_singleton_iff_isClosedImmersion` is
  **Stacks 0H1U**, for any residual space of `X` at `x`.

## Implementation notes

The source attaches `Z_x` to `x` as a given, justified by **Stacks 06QZ**; here it is the
hypothesis `IsResidualSpaceAt B S hS X x f` on a morphism `f : Z ⟶ X`. That predicate is
inhabited at every point of every algebraic space by the existence half of Stacks 06QZ,
`AlgebraicGeometry.Space.exists_isResidualSpaceAt`, and determined up to a unique isomorphism
over `X` by the uniqueness half, `AlgebraicGeometry.Space.existsUnique_iso_of_isResidualSpaceAt`,
so quantifying over all such `f` is the source's statement about `Z_x`.

The easy implication is
`AlgebraicGeometry.Space.isClosed_singleton_of_isClosedImmersion_of_isResidualSpaceAt`, which
needs no local Noetherianity: the image on points of a residual space at `x` is `{x}`, and the
image on points of a closed immersion is closed (Stacks 04CD).

The other implication compares the given residual space with the reduced closed subspace of
Stacks 03IQ on `{x}`, which is a residual space at `x` by
`AlgebraicGeometry.Space.isResidualSpaceAt_ι_reducedClosedSubspace` (this is where local
Noetherianity enters, through Stacks 06ED and 04ZK) and whose inclusion is a closed immersion.
The uniqueness half of Stacks 06QZ identifies the two up to an isomorphism over `X`, and being a
closed immersion is invariant under precomposition with an isomorphism.

`AlgebraicGeometry.Space.isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton` states the same equivalence with
that uniqueness carried as a hypothesis, because uniqueness is proved downstream of that file;
the statement here discharges it.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 0H1U](https://stacks.math.columbia.edu/tag/0H1U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

attribute [local instance] pointTopology

/-- **Stacks Project, Tag 0H1U.** Let `S` be a scheme, let `X` be an algebraic space over `S`
which is locally Noetherian, let `x` be a point of `|X|`, and let `f : Z ⟶ X` be a residual
space of `X` at `x`. Then `x` is a closed point of `|X|` if and only if `f` is a closed
immersion.

One implication is
`AlgebraicGeometry.Space.isClosed_singleton_of_isClosedImmersion_of_isResidualSpaceAt`. For the
other, the reduced closed subspace of `X` on the closed point `{x}` is a residual space of `X`
at `x` and its inclusion is a closed immersion; the uniqueness half of Stacks 06QZ identifies
`f` with that inclusion up to an isomorphism of its source over `X`, and being a closed
immersion is invariant under such an isomorphism. -/
@[stacks 0H1U "stated for any residual space of `X` at `x`"]
theorem IsResidualSpaceAt.isClosed_singleton_iff_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {x : points B S hS X} {f : Z ⟶ X} (hf : IsResidualSpaceAt B S hS X x f) :
    _root_.IsClosed ({x} : Set (points B S hS X)) ↔ IsClosedImmersion B S hS f :=
  isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt B S hS hX hN x f hf
    fun _ g hg => (existsUnique_iso_of_isResidualSpaceAt B S hS hX f g hf hg).exists

end AlgebraicGeometry.Space

end
