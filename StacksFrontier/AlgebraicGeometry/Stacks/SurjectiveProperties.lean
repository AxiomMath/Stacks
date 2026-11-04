module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Permanence properties of surjective morphisms of algebraic stacks

Surjectivity of a 1-morphism of algebraic stacks over `S`, that is, surjectivity of the induced
map on points, is preserved by composition, descends along a surjective morphism of targets, and
passes from a composite to its second factor.

## Main results

* `AlgebraicGeometry.Stack.isSurjective_comp`: a composite of surjective 1-morphisms is
  surjective.
* `AlgebraicGeometry.Stack.isSurjective_of_isSurjective_twoCommSq_fst`: surjectivity descends
  along a surjective 1-morphism of targets.
* `AlgebraicGeometry.Stack.isSurjective_of_isSurjective_comp`: if `f ≫ g` is surjective, so is
  `g`.

## References

* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 06PM](https://stacks.math.columbia.edu/tag/06PM)
* [Stacks Project, Tag 06PN](https://stacks.math.columbia.edu/tag/06PN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- The composite of two surjective 1-morphisms of algebraic stacks over `S` is surjective. -/
@[stacks 04ZT]
theorem isSurjective_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsSurjective B S hS f) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS (f ≫ g) := by
  rw [IsSurjective, AlgebraicStacks.pointsMap_comp]
  exact hg.comp hf

/-- If a composite of 1-morphisms of algebraic stacks over `S` is surjective, then so is its
second factor. -/
@[stacks 06PN]
theorem isSurjective_of_isSurjective_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsSurjective B S hS (f ≫ g)) : IsSurjective B S hS g :=
  Function.Surjective.of_comp (g := AlgebraicStacks.pointsMap B S hS f)
    (AlgebraicStacks.pointsMap_comp B S hS f g ▸ hfg)

/-- Surjectivity of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` descends along a
surjective 1-morphism `g : 𝒵 ⟶ 𝒴`: if some 2-commutative square over the cospan `(g, f)` has
surjective first projection, then `f` is surjective. -/
@[stacks 06PM, sga "1 VIII 3.1" "f' surj => f surj"]
theorem isSurjective_of_isSurjective_twoCommSq_fst {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hg : IsSurjective B S hS g)
    (hfst : IsSurjective B S hS P.fst) : IsSurjective B S hS f := by
  intro y
  obtain ⟨z, hz⟩ := hg y
  obtain ⟨p, hp⟩ := hfst z
  refine ⟨AlgebraicStacks.pointsMap B S hS P.snd p, ?_⟩
  have key := congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS P.iso.hom) p
  rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp] at key
  rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS f), ← key,
    Function.comp_apply, hp, hz]

end AlgebraicGeometry.Stack

end
