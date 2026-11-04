module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative effective Cartier divisors

Let `f : X ⟶ S` be a morphism of schemes. A closed subscheme `D ⊆ X`, presented by its
quasi-coherent sheaf of ideals, is a *relative effective Cartier divisor* over `S` when it is an
effective Cartier divisor on `X` — that is, its ideal sheaf is an invertible `𝒪_X`-module — and
its structure morphism `D ⟶ S` is flat. The flatness over the base is what makes the notion
behave well under base change: a relative effective Cartier divisor pulls back to a relative
effective Cartier divisor, which an absolute effective Cartier divisor need not do.

## Main definitions

* `Stacks.Divisors.IsRelativeEffectiveCartierDivisor` — the predicate above.

## Implementation notes

The closed subscheme is represented by `Scheme.IdealSheafData`, and its structure morphism to
the base is the composite `I.subschemeι ≫ f` of the closed immersion with `f`. The predicate is
an abbreviation, so both of its conjuncts are directly available to clients; the effective
Cartier condition is `Stacks.Divisors.IsEffectiveCartierDivisor` (Tag 01WR) and the flatness
condition is Mathlib's `AlgebraicGeometry.Flat`.

## References

* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **Stacks Project, Tag 062T.** A closed subscheme of `X` is a *relative effective Cartier
divisor* over `S` when it is an effective Cartier divisor on `X` and its structure morphism to
`S` is flat. -/
@[stacks 062T]
abbrev IsRelativeEffectiveCartierDivisor {X S : Scheme.{u}}
    (f : X ⟶ S) (I : X.IdealSheafData) : Prop :=
  IsEffectiveCartierDivisor I ∧ Flat (I.subschemeι ≫ f)

end Stacks.Divisors

end
