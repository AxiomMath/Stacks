module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Local complete intersection morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a *local complete intersection
morphism*, or a *Koszul morphism*, when the scheme morphism it induces in every commuting
square of étale charts is a local complete intersection morphism, and *Koszul at* a point
of its source when some open neighbourhood of that point restricts it to a local complete
intersection morphism.

## Main definitions

* `AlgebraicGeometry.Space.IsLocalCompleteIntersection` is the Koszul property of a
  morphism of algebraic spaces: **Stacks 06C4**, part (1).
* `AlgebraicGeometry.Space.KoszulAt` is the Koszul property at a point of the source:
  **Stacks 06C4**, part (2).

## Main results

There are no propositional results. Both definitions are abbreviations, so the chart API
of `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` applies to them directly.

## Implementation notes

Part (1) is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to the
scheme-morphism property `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism` of Stacks
069F, part (2); its equivalence with the condition on one surjective chart is Stacks 03MJ and
rests on étale locality of the Koszul property on source and target. That locality is not
available at this point in the import order — it is established downstream, in the submodule
`LocalCompleteIntersection.FlatBaseChange` of this module,
as `AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism` — so the
every-chart form is the definition here, exactly as in the source.

Part (2) follows `AlgebraicGeometry.Space.IsPseudoCoherentAt` of Stacks 06BR, part (2):
an open neighbourhood `X' ⊂ X` of `x` is a subfunctor of the source which is an open
subspace in the sense of `AlgebraicGeometry.Space.IsOpenSubspace` (Stacks 02YU, part (2))
together with a point of `|X'|` mapping to `x` under `AlgebraicGeometry.Space.pointsMap`
(Stacks 03BU), and the restriction `f|_{X'}` is the composite `X'.ι ≫ f`.

The scheme-level `AlgebraicGeometry.KoszulAt` is the pointwise condition whose universal
quantification is `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism`, whereas the
space-level `AlgebraicGeometry.Space.KoszulAt` below is a genuinely weaker, local
condition on a morphism of algebraic spaces: it asks for the full Koszul property only
after restriction to an open neighbourhood. The two notions therefore stay apart.

Neither definition imposes algebraicity of the source or target; as with the conditions of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms`, that is imposed by clients, exactly as
in the source definition.

## References

* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06C4, part (1).** A morphism of algebraic spaces over `S` is a *local complete
intersection morphism*, or a *Koszul morphism*, when every commuting square of étale scheme
charts induces a local complete intersection morphism of schemes. -/
@[stacks 06C4 "part (1): local complete intersection morphisms"]
abbrev IsLocalCompleteIntersection (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u}) f

/-- **Stacks 06C4, part (2).** A morphism of algebraic spaces over `S` is *Koszul at* a
point `x` of its source when it is a local complete intersection morphism on an open
subspace of the source containing `x`. -/
@[stacks 06C4 "part (2): Koszul at a point"]
abbrev KoszulAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X,
    IsOpenSubspace B S hS U ∧
      ∃ x' : points B S hS U.toFunctor,
        pointsMap B S hS U.toFunctor U.ι x' = x ∧
          IsLocalCompleteIntersection B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
