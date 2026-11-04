module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Pseudo-coherent morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *pseudo-coherent* when the scheme
morphism it induces in every commuting square of étale charts is pseudo-coherent, and
*pseudo-coherent at* a point of its source when some open neighbourhood of that point
restricts it to a pseudo-coherent morphism.

## Main definitions

* `AlgebraicGeometry.Space.IsPseudoCoherent` is pseudo-coherence of a morphism of
  algebraic spaces: **Stacks 06BR**, part (1).
* `AlgebraicGeometry.Space.IsPseudoCoherentAt` is pseudo-coherence at a point of the
  source: **Stacks 06BR**, part (2).

## Main results

There are no propositional results. Both definitions are abbreviations, so the chart API
of `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applies to them directly.

## Implementation notes

Part (1) is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the
scheme-morphism property `AlgebraicGeometry.PseudoCoherent` of Stacks 067Z; its
equivalence with the condition on one surjective chart is Stacks 03MJ and rests on étale
locality of pseudo-coherence on source and target. That equivalence is not available here,
so the every-chart form is the definition, exactly as in the source.

Part (2) follows `AlgebraicGeometry.Space.IsFinitePresentationAt` of Stacks 03XP, part
(2): an open neighbourhood `X' ⊂ X` of `x` is a subfunctor of the source which is an open
subspace in the sense of `AlgebraicGeometry.Space.IsOpenSubspace` (Stacks 02YU, part (2))
together with the requirement that `x` lie in the image of `|X'| → |X|`, so the
containment `x ∈ |X'|` is membership in the range of
`AlgebraicGeometry.Space.pointsMap` (Stacks 03BU) rather than a containment of subsets of
a single type, and the restriction `f|_{X'}` is the composite `X'.ι ≫ f`.

Neither definition imposes algebraicity of the source or target; as with the conditions of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that is imposed by clients, exactly as
in the source definition.

## References

* [Stacks Project, Tag 06BR](https://stacks.math.columbia.edu/tag/06BR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06BR, part (1).** A morphism of algebraic spaces over `S` is
*pseudo-coherent* when every commuting square of étale scheme charts induces a
pseudo-coherent scheme morphism. -/
@[stacks 06BR "part (1): pseudo-coherent morphism"]
abbrev IsPseudoCoherent (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.PseudoCoherent.{u} : MorphismProperty Scheme.{u}) f

/-- **Stacks 06BR, part (2).** A morphism of algebraic spaces over `S` is
*pseudo-coherent at* a point `x` of its source when it is pseudo-coherent on an open
subspace of the source containing `x`. -/
@[stacks 06BR "part (2): pseudo-coherent at a point"]
abbrev IsPseudoCoherentAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X,
    IsOpenSubspace B S hS U ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      IsPseudoCoherent B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
