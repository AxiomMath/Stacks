module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Syntomic morphisms of algebraic spaces

Being syntomic — flat and locally of finite presentation with local complete intersection
fibres — is étale local on the source and target, stable under base change and fppf local on
the target, so by Tag 03MJ it transfers to morphisms of algebraic spaces: a morphism of
algebraic spaces over `S` is *syntomic* when the scheme morphism it induces in every
commuting square of étale charts is syntomic. It is *syntomic at a point* of its source when
it is syntomic on some open subspace containing that point.

## Main definitions

* `AlgebraicGeometry.Space.IsSyntomic`: **Stacks 03Z7**, part (1).
* `AlgebraicGeometry.Space.IsSyntomicAt`: **Stacks 03Z7**, part (2).

## Main results

There are no propositional results. Both definitions are abbreviations, so the chart API of
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applies to them directly.

## Implementation notes

The every-chart condition `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` is condition (1)
of Tag 03MJ; its equivalence with the some-chart condition is the content of that tag and is
not available, so the every-chart form is the definition, exactly as in the source. The
scheme-level predicate tested on charts is `AlgebraicGeometry.Syntomic` of Tag 01UC.

Part (2) quantifies over open subspaces of the source in the sense of Tag 02YU, and records
the point as the image of a point of that subspace; the source of a morphism of algebraic
spaces need not be a scheme, so this is the form the source's reduction to charts takes.

## References

* [Stacks Project, Tag 03Z7](https://stacks.math.columbia.edu/tag/03Z7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03Z7, part (1).** A morphism of algebraic spaces over `S` is *syntomic* when
the scheme morphism underlying every commuting square of étale scheme charts of it is
syntomic. -/
@[stacks 03Z7 "part (1): syntomic morphisms"]
abbrev IsSyntomic (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u}) f

/-- **Stacks 03Z7, part (2).** A morphism of algebraic spaces over `S` is *syntomic at* a
point `x` of its source when it is syntomic on some open subspace of the source having a
point over `x`. -/
@[stacks 03Z7 "part (2): syntomic at a point"]
abbrev IsSyntomicAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsSyntomic B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
