module

public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# The fundamental class of a locally equidimensional scheme

Let `X` be locally of finite type over the base scheme of a Chow situation and suppose its
relative dimension function has a dimension decomposition `X = ⨿_n X_n`, every irreducible
component of `X_n` having relative dimension `n`. Chapter 42 of the Stacks Project writes the
Chow group of codimension-`p` cycles as the product `CH^p(X) = ∏_n CH_{n - p}(X_n)`. In
codimension zero this reads `CH^0(X) = ∏_n CH_n(X_n)`, and the *fundamental class* of `X` is the
family whose `n`th coordinate is the class of the cycle of `X_n` itself in dimension `n`.

## Main definitions

* `Stacks.Chow.degreeZeroChowGroup` — the group `CH^0(X)` in this product description.
* `Stacks.Chow.fundamentalClass` — the fundamental class `[X] = ∑_n [X_n]_n ∈ CH^0(X)`.

## Main results

* `Stacks.Chow.fundamentalClass_apply` — the `n`th coordinate is the class of the cycle
  associated to the `n`th piece.

## Implementation notes

A dimension decomposition is a proposition, so choosing a witnessing family of pieces with
`Classical.choose` adds no mathematical data; both the group and the class are stated relative to
that choice. Each piece `X_n` enters as the identity closed immersion of the open subscheme
`X_n`, whose associated `n`-cycle is `[X_n]_n`; the cycle lives in the cycle group of `X_n` over
the base, which is why the morphism to the base used in the `n`th factor is `X_n → X → S`.

## References

* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The Chow group `CH^0(X)` of codimension-zero cycles, described as the product of the Chow
groups `CH_n(X_n)` over the pieces of a dimension decomposition of the relative dimension
function of `X` over the base of a Chow situation. -/
abbrev degreeZeroChowGroup (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f]
    (h : HasDimensionDecomposition (relativeDimension C.dimensionFunction f)) : Type u :=
  ∀ n : ℤ, chowGroup C ((Classical.choose h n).ι ≫ f) n

/-- **Stacks 0FE4.** The fundamental class `[X] = ∑_n [X_n]_n` of a scheme whose relative
dimension function has a dimension decomposition: the family whose `n`th coordinate is the class
in `CH_n(X_n)` of the cycle associated to the piece `X_n` itself. -/
@[stacks 0FE4 "fundamental_class"]
def fundamentalClass (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f]
    (h : HasDimensionDecomposition (relativeDimension C.dimensionFunction f)) :
    degreeZeroChowGroup C f h :=
  fun n ↦ QuotientAddGroup.mk
    (cycleAssociatedToClosedSubscheme C ((Classical.choose h n).ι ≫ f) (𝟙 _) n)

/-- The `n`th coordinate of the fundamental class is the class of the cycle associated to the
`n`th piece of the decomposition. -/
@[simp]
theorem fundamentalClass_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f]
    (h : HasDimensionDecomposition (relativeDimension C.dimensionFunction f)) (n : ℤ) :
    fundamentalClass C f h n =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C ((Classical.choose h n).ι ≫ f) (𝟙 _) n) :=
  rfl

end Stacks.Chow

end
