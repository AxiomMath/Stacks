module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# The universal smooth-diagram criterion for a representable morphism

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target and which is moreover stable under base change and local at the target for the
fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable
by algebraic spaces. Then `f` satisfies the universal smooth-diagram test for `P` if and only if
`f` has the relative property `P`.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty`: the relative
  property implies the universal smooth-diagram test.
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_relative`: the two agree.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For `P` smooth local on the source-and-target, stable under base change and local
at the target for the fppf precoverage, and `f : 𝒳 ⟶ 𝒴` a 1-morphism of algebraic stacks over `S`
representable by algebraic spaces: if every algebraic space representing a base change of `f`
along a scheme-valued point of `𝒴` has structural morphism with `P`, then every 2-commutative
square of algebraic spaces over `f` with smooth vertical 1-morphisms and smooth comparison to a
2-fibre product has `P` on its top horizontal morphism. -/
theorem hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hrel : HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P) f hf) :
    HasPropertyOnEverySmoothDiagram B S hS P f :=
  (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP h𝒳 h𝒴 f).2
    (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS P h𝒴 f hf hrel)

/-- For `P` smooth local on the source-and-target, stable under base change and local at the
target for the fppf precoverage, and `f : 𝒳 ⟶ 𝒴` a 1-morphism of algebraic stacks over `S`
representable by algebraic spaces, the universal smooth-diagram test for `P` holds exactly when
`f` has the relative property `P`. -/
theorem hasPropertyOnEverySmoothDiagram_iff_relative
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasPropertyOnEverySmoothDiagram B S hS P f ↔
      HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P) f hf :=
  ⟨fun h => hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS P hP f hf
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP h𝒳 h𝒴 f).1 h),
    hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty B S hS P hP h𝒳 h𝒴 f hf⟩

end AlgebraicGeometry.Stack

end
