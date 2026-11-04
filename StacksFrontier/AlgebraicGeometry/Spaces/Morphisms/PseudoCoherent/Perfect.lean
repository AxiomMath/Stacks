module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Perfect morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *perfect* when the scheme morphism it
induces in every commuting square of étale charts is perfect, and *perfect at* a point of
its source when some open neighbourhood of that point restricts it to a perfect morphism.

## Main definitions

* `AlgebraicGeometry.Space.IsPerfect` is perfection of a morphism of algebraic spaces:
  **Stacks 06BZ**, part (1).
* `AlgebraicGeometry.Space.IsPerfectAt` is perfection at a point of the source:
  **Stacks 06BZ**, part (2).

## Main results

There are no propositional results. Both definitions are abbreviations, so the chart API
of `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applies to them directly.

## Implementation notes

Part (1) is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the
scheme-morphism property `AlgebraicGeometry.Perfect` of Stacks 0687; its equivalence with
the condition on one surjective chart is Stacks 03MJ and rests on étale locality of
perfection on source and target. That equivalence is not available here, so the
every-chart form is the definition, exactly as in the source.

Part (2) follows `AlgebraicGeometry.Space.IsPseudoCoherentAt` of Stacks 06BR, part (2):
an open neighbourhood `X' ⊂ X` of `x` is a subfunctor of the source which is an open
subspace in the sense of `AlgebraicGeometry.Space.IsOpenSubspace` (Stacks 02YU, part (2))
together with the requirement that `x` lie in the image of `|X'| → |X|`, and the
restriction `f|_{X'}` is the composite `X'.ι ≫ f`.

Neither definition imposes algebraicity of the source or target; as with the conditions of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that is imposed by clients, exactly as
in the source definition.

## References

* [Stacks Project, Tag 06BZ](https://stacks.math.columbia.edu/tag/06BZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06BZ, part (1).** A morphism of algebraic spaces over `S` is *perfect* when
every commuting square of étale scheme charts induces a perfect scheme morphism. -/
@[stacks 06BZ "part (1): perfect morphism"]
abbrev IsPerfect (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.Perfect.{u} : MorphismProperty Scheme.{u}) f

/-- **Stacks 06BZ, part (2).** A morphism of algebraic spaces over `S` is *perfect at* a
point `x` of its source when it is perfect on an open subspace of the source containing
`x`. -/
@[stacks 06BZ "part (2): perfect at a point"]
abbrev IsPerfectAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X,
    IsOpenSubspace B S hS U ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
      IsPerfect B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
