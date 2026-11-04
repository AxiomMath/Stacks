module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of categories fibred in groupoids representable by algebraic spaces

A 1-morphism of categories fibred in groupoids over the big fppf site of a scheme `S` is
*representable by algebraic spaces* when, for every scheme `U` over `S` and every
scheme-valued point of the target over `U`, the 2-fibre product is representable by an
algebraic space over `U`.

## Main definitions

* `AlgebraicGeometry.IsRepresentableByAlgebraicSpaces`: this representability property.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

universe u v₁ v₂ w₁ w₂

/-- A morphism of categories fibred in groupoids is representable by algebraic spaces if, for every
scheme `U` over `S` and every scheme-valued point of its target over `U`, the first projection of
the 2-fibre product is equivalent, over the big fppf site of `U`, to the category of elements of
an algebraic space over `U`. -/
public abbrev IsRepresentableByAlgebraicSpaces (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v₁, w₁} (AlgebraicGeometry.BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, w₂} (AlgebraicGeometry.BigFppfOver B S hS)}
    (f : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (U : AlgebraicGeometry.BigFppfOver B S hS),
    let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2;
    let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom;
    ∀ (y : 𝒰 ⥤ 𝒴.obj) (_hy : y ⋙ 𝒴.p = p𝒰), ∃ F : 𝒰ᵒᵖ ⥤ Type u,
      AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst p𝒰 𝒳.p 𝒴.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p)

end AlgebraicGeometry

end
