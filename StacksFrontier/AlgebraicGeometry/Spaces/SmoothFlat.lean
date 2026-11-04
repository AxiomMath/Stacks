module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# A smooth morphism of algebraic spaces is flat (Stacks 04TA)

Both smoothness (Stacks 03ZC part (1)) and flatness (Stacks 03ML part (1)) of a morphism of
algebraic spaces over `S` are, by Stacks 03MJ, the condition that the scheme morphism underlying
every commuting square of étale scheme charts has the corresponding property of morphisms of
schemes. Since a smooth morphism of schemes is flat, the implication is chartwise, and it needs
no algebraic-space hypothesis on either side: the two conditions are stated for an arbitrary
morphism of set-valued presheaves on the big fppf site.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_isSmooth`: **Stacks 04TA**.

## Implementation notes

`AlgebraicGeometry.Smooth` and `AlgebraicGeometry.Flat` are classes on morphisms of schemes, so
the chartwise hypothesis can be put into the instance cache and the conclusion obtained by
instance search, which is what supplies the scheme-level implication.

Stacks 04TA lies in Chapter 67, Morphisms of Algebraic Spaces. It is a *theorem* and coins no
notion — both `AlgebraicGeometry.Space.IsSmooth` and `AlgebraicGeometry.Space.IsFlat` are
already defined. It is wanted by the uniqueness half of Stacks 04XL, where the atlas of an
algebraic stack is smooth and must be recognised as flat and locally of finite presentation.

## References

* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 04TA.** A smooth morphism of algebraic spaces over `S` is flat: on each commuting
square of étale scheme charts the underlying scheme morphism is smooth, hence flat. -/
@[stacks 04TA]
theorem isFlat_of_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    IsFlat B S hS f := by
  intro U V a b h ha hb comm
  let := hf U V a b h ha hb comm
  infer_instance

end AlgebraicGeometry.Space

end
