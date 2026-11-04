module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Morphisms of finite presentation of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *locally of finite presentation* when
the scheme morphism it induces in every commuting square of étale charts is locally of
finite presentation, *of finite presentation at* a point of its source when some open
neighbourhood of that point restricts it to one which is locally of finite presentation,
and *of finite presentation* when it is locally of finite presentation, quasi-compact and
quasi-separated.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` is local finite presentation:
  **Stacks 03XP**, part (1).
* `AlgebraicGeometry.Space.IsFinitePresentationAt` is finite presentation at a point of
  the source: **Stacks 03XP**, part (2).
* `AlgebraicGeometry.Space.IsFinitePresentation` is finite presentation: **Stacks 03XP**,
  part (3).

## Main results

There are no propositional results. All three definitions are abbreviations, so the chart
API of `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applies to them directly.

## Implementation notes

These are the three parts of Stacks 03XP, and they follow the three parts of Stacks 03XF
in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteType` exactly.

Part (1) is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to Mathlib's
scheme-morphism property `AlgebraicGeometry.LocallyOfFinitePresentation`; its equivalence
with the condition on one surjective chart is Stacks 03MJ and follows from étale locality
of that property on source and target. Being locally of finite presentation is indeed étale
local on the source and target, stable under base change and fppf local on the target, which
is what makes the transfer of Stacks 03MJ apply. The equivalence itself is not available
here, so the every-chart form is the definition, exactly as in the source. That chartwise
condition is also the defining condition of Stacks 04RD for an arbitrary property étale
local on source and target, so the tag for that definition is recorded here on the chartwise
predicate rather than on a duplicate of it.

In part (2) an open neighbourhood `X' ⊂ X` of `x` is a subfunctor of the source which is
an open subspace in the sense of `AlgebraicGeometry.Space.IsOpenSubspace` (Stacks 02YU,
part (2)) together with the requirement that `x` lie in the image of `|X'| → |X|`; the
points of an algebraic space and the map they induce are
`AlgebraicGeometry.Space.points` and `AlgebraicGeometry.Space.pointsMap` of Stacks 03BU,
so the containment `x ∈ |X'|` is membership in the range of that map rather than a
containment of subsets of a single type, and the restriction `f|_{X'}` is the composite
`X'.ι ≫ f`. Quantifying over open subspaces of the source rather than over open subschemes
of a chart is what lets the source be an arbitrary presheaf; the two formulations agree for
an algebraic space, because the open subspaces containing a point are cofinal among the
images of open subschemes of charts.

Note that part (3) is *not* local finite presentation together with quasi-compactness: the
quasi-separatedness condition `AlgebraicGeometry.Space.IsQuasiSeparated` of Stacks 03HL,
part (3) is a separate conjunct, exactly as in the source definition.

All three are abbreviations, which exposes the chart condition, the existential and the
conjunction directly to clients. None of them imposes algebraicity of the source or
target; as with the conditions of `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that
is imposed by clients, exactly as in the source definitions.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 04RD](https://stacks.math.columbia.edu/tag/04RD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03XP, part (1).** A morphism of algebraic spaces over `S` is *locally of
finite presentation* when every commuting square of étale scheme charts induces a scheme
morphism which is locally of finite presentation. -/
@[stacks 03XP "part (1): locally of finite presentation"]
abbrev IsLocallyOfFinitePresentation (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) f

/-- **Stacks 03XP, part (2).** A morphism of algebraic spaces over `S` is *of finite
presentation at* a point `x` of its source when it is locally of finite presentation on an
open subspace of the source containing `x`.

Ten predicates of this library share this signature, among them
`AlgebraicGeometry.Space.IsFiniteTypeAt` and `AlgebraicGeometry.Space.IsSmoothAt`: each applies
the same "holds on an open subspace through `x`" schema to a different property of morphisms of
schemes, and each is a different part of a different tag of the source. The shape is shared, the
content is not. -/
@[stacks 03XP "part (2): finite presentation at a point"]
abbrev IsFinitePresentationAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X,
    IsOpenSubspace B S hS U ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      IsLocallyOfFinitePresentation B S hS (U.ι ≫ f)

/-- **Stacks 03XP, part (3).** A morphism of algebraic spaces over `S` is *of finite
presentation* when it is locally of finite presentation, quasi-compact and
quasi-separated. -/
@[stacks 03XP "part (3): finite presentation"]
abbrev IsFinitePresentation (f : X ⟶ Y) : Prop :=
  IsLocallyOfFinitePresentation B S hS f ∧
    IsQuasiCompact B S hS f ∧ IsQuasiSeparated B S hS f

/- **Stacks 04RD.** The chartwise condition of Stacks 03MJ is the definition of what it
means for a morphism of algebraic spaces to have a property of scheme morphisms which is
étale local on the source-and-target. -/
add_to_stacks 04RD AlgebraicGeometry.Space.HoldsOnEveryEtaleChart

end AlgebraicGeometry.Space

end
