module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces

/-!
# Limits of directed systems of Noetherian algebraic spaces

A Noetherian limit system over a scheme `S` is a nonempty directed preorder `I` together with
an inverse system `(B_i)_{i ∈ I}` of Noetherian algebraic spaces over `S` whose transition
morphisms `B_{i'} ⟶ B_i` for `i ≤ i'` are affine, and a chosen limit `B = lim_i B_i` of that
system which is again an algebraic space. It is the standing setup for descending an algebraic
space of finite type over `B` to a finite stage, and is the algebraic-space analogue of
`AlgebraicGeometry.LimitNoetherianSituation`.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianLimitSystem` bundles the directed inverse system of
  Noetherian algebraic spaces with its chosen limiting cone.

## Implementation notes

Algebraic spaces over `S` are presheaves on the big fppf site over `S`, so the inverse system
is a functor out of the opposite `Iᵒᵖ` of the indexing preorder and the transition morphism
`B_{i'} ⟶ B_i` for `i ≤ i'` is the image of the corresponding morphism of `Iᵒᵖ`. The limit
space together with all of its projections and their naturality is packaged as a
`CategoryTheory.Limits.Cone`, whose universal property is recorded by
`CategoryTheory.Limits.IsLimit`; algebraicity of the limit is not automatic for a cone in
presheaves and is therefore part of the data.

Noetherian means `AlgebraicGeometry.Space.IsNoetherian`, which uses the absolute
quasi-separatedness of Stacks 03BS, part (3); that is why the containment `hZ` of the terminal
scheme in the site is a parameter.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-- **Stacks 0CP6.** A directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms, equipped with a chosen limiting cone whose
point is again an algebraic space. -/
@[stacks 0CP6]
structure NoetherianLimitSystem (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type v) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  system : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Every member of the system is an algebraic space over `S`. -/
  system_isAlgebraicSpace :
    ∀ i : I, IsAlgebraicSpace B S hS (system.obj (op i))
  /-- Every member of the system is Noetherian. -/
  noetherian : ∀ i : I, IsNoetherian B S hS hZ (system.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (system.map f)
  /-- The chosen cone, whose point is the limit space `B`. -/
  limitCone : Cone system
  /-- The chosen cone is a limit cone. -/
  isLimit : IsLimit limitCone
  /-- The limit of the system is an algebraic space over `S`. -/
  limit_isAlgebraicSpace : IsAlgebraicSpace B S hS limitCone.pt

end AlgebraicGeometry.Space

end
