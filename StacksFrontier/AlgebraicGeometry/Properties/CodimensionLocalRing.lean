module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Codimension of an irreducible closed subset of a scheme and the local ring at its generic point

Let `X` be a scheme and let `Y ⊆ X` be an irreducible closed subset. The underlying space of a
scheme is sober, so `Y` has a generic point `ξ`, and

    codim (Y, X) = dim 𝒪_{X, ξ}.

This is **Stacks 02IZ**, with the codimension of Stacks 02I3 on the left and the Krull dimension
of the local ring of `X` at `ξ` on the right.

## Main results

* `AlgebraicGeometry.codimension_eq_ringKrullDim_stalk`: **Stacks 02IZ**.
* `AlgebraicGeometry.codimension_eq_ringKrullDim_stalk_genericPoint`: the same statement with the
  generic point produced by sobriety rather than supplied.

## Implementation notes

The codimension of Stacks 02I3 is `codimension`, the coheight of `Y` in the poset
`TopologicalSpace.IrreducibleCloseds X` of irreducible closed subsets ordered by inclusion. On a
sober Kolmogorov space that poset is order-isomorphic to the space itself with the specialization
order, by `TopologicalSpace.irreducibleSetEquivPoints`, and the isomorphism carries `Y` to its
generic point; so the left-hand side is the coheight of `ξ` in `X`. The right-hand side is that
same coheight by `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`. Both identifications are
invariances of coheight, so no finiteness, separation or Noetherian hypothesis on `X` is needed.

Stacks reduces to an affine open neighbourhood of `ξ` by Stacks 02I4 and then computes with
Algebra, Lemma 00ET. That reduction and that computation are what
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` already performs: it passes to an affine open
by `AlgebraicGeometry.coheight_eq_of_isOpenImmersion`, which also carries the tag 02I4, and on an
affine scheme it identifies the dimension of the localization at a prime with the height of that
prime, which is the content of 00ET.

The two sides have different value types — `codimension` takes values in `ℕ∞` and `ringKrullDim`
in `WithBot ℕ∞` — so the equality is stated with the coercion on the left. The generic point is
not an argument of the codimension, so the statement quantifies over `ξ` with the hypothesis
`IsGenericPoint ξ Y` of Stacks 004X; in a Kolmogorov space such a `ξ` is unique.

## References

* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks 02IZ**.
Let `X` be a scheme, let `Y ⊆ X` be an irreducible closed subset and let `ξ` be the generic
point of `Y`. Then the codimension of `Y` in `X`, in the sense of Stacks 02I3, is the Krull
dimension of the local ring `𝒪_{X, ξ}`. -/
@[stacks 02IZ, ega "IV 21.6.2" "partial", ega "IV 5.1.2", ega "IV 5.1.3" "special case"]
theorem codimension_eq_ringKrullDim_stalk {X : Scheme.{u}} (Y : IrreducibleCloseds X) (ξ : X)
    (hξ : IsGenericPoint ξ (Y : Set X)) :
    (codimension Y : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk ξ) := by
  have hY : (irreducibleSetEquivPoints.symm ξ : IrreducibleCloseds X) = Y :=
    IrreducibleCloseds.ext hξ
  rw [ringKrullDim_stalk_eq_coheight, codimension_eq_coheight, ← hY,
    Order.coheight_orderIso]

/-- Stacks 02IZ with the generic point produced by sobriety of the underlying space of a scheme:
the codimension of an irreducible closed subset `Y ⊆ X` is the Krull dimension of the local ring
of `X` at the generic point of `Y`. -/
@[ega "IV 21.6.2" "partial", ega "IV 5.1.2", ega "IV 5.1.3" "special case"]
theorem codimension_eq_ringKrullDim_stalk_genericPoint {X : Scheme.{u}}
    (Y : IrreducibleCloseds X) :
    (codimension Y : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk Y.isIrreducible.genericPoint) :=
  codimension_eq_ringKrullDim_stalk Y _
    (Y.isIrreducible.isGenericPoint_genericPoint Y.isClosed)

end AlgebraicGeometry

end
