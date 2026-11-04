module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism

/-!
# 1-morphisms of algebraic stacks of finite type

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is locally of finite type* when, for every
2-commutative square of algebraic spaces over `f` whose two vertical 1-morphisms are smooth and
whose every comparison 1-morphism to a 2-fibre product is smooth, the top horizontal morphism of
algebraic spaces is locally of finite type. It *is of finite type* when it is locally of finite
type and quasi-compact.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType`: a 1-morphism of algebraic
  stacks is locally of finite type.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFiniteType`: a 1-morphism of algebraic stacks is of
  finite type.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation`:
  a 1-morphism locally of finite presentation is locally of finite type.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism `f` of algebraic stacks over `S` is *locally of finite type* when every
2-commutative square of algebraic spaces over `f` whose two vertical 1-morphisms are smooth and
whose every comparison 1-morphism to a 2-fibre product is smooth has its top horizontal morphism
locally of finite type. -/
@[stacks 06FS "part (1): locally of finite type"]
abbrev IsLocallyOfFiniteType {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.HasPropertyOnEverySmoothDiagram B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h) f.hom

/-- A 1-morphism of algebraic stacks over `S` is *of finite type* when it is locally of finite
type and quasi-compact. -/
@[stacks 06FS "part (2): finite type"]
abbrev IsFiniteType {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsLocallyOfFiniteType B S hS f ∧ Stack.IsQuasiCompactMorphism B S hS f

/-- A 1-morphism of algebraic stacks over `S` which is locally of finite presentation is locally
of finite type. -/
@[stacks 06Q5 "first assertion"]
theorem isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  fun U V hU hV a b h η ha hb hk =>
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (hf U V hU hV a b h η ha hb hk)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
