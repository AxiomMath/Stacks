module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase

/-!
# The 2-fibre product of stacks in setoids: the fibre conditions

Fix a site `(𝒞, J)` and categories `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴 : 𝒴 ⥤ 𝒞`, `p𝒮 : 𝒮 ⥤ 𝒞` over `𝒞` with
1-morphisms `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮`. Stacks 0434 says that the 2-category of stacks in setoids
over `𝒞` has 2-fibre products and that they are the ones of Categories, Stacks 0040 — which, as for
Stacks 0041 and 04SB, means that the construction of 0040 does not leave the sub-2-category: the
structure functor of `𝒳 ×_𝒮 𝒴` is again a stack in setoids.

Being a stack in setoids (`CategoryTheory.Functor.IsStackInSetoids`, Stacks 042Z) is three
conditions: being a stack, having groupoid fibres and having thin fibres. This file supplies the
two fibre conditions for the 2-fibre product `CategoryTheory.TwoFibreProductOver`:

* groupoid fibres are already Stacks 0041, `CategoryTheory.TwoFibreProductOver.fiber_isGroupoid`;
* thin fibres are `CategoryTheory.TwoFibreProductOver.fiber_isThin`, proved below.

## Main results

* `CategoryTheory.TwoFibreProductOver.fiber_isThin`: the fibres of the 2-fibre product are thin as
  soon as those of `𝒳` and of `𝒴` are. Nothing is asked of `𝒮`.
* `CategoryTheory.TwoFibreProductOver.isStackInSetoids_of_isStack`: the assembly of Stacks 0434
  from those two conditions and the stack condition on the 2-fibre product.

## Implementation notes

Thinness is immediate from `CategoryTheory.TwoFibreProductOver.Hom.ext'`, which says that a
morphism of the 2-fibre product is determined by its two components: the components of two
morphisms of a fibre both lie over `𝟙 U` (`CategoryTheory.TwoFibreProductOver.isHomLift_a` and
`.isHomLift_b`), so they are morphisms of the fibres of `𝒳` and `𝒴` over `U` and thinness there
identifies them pairwise. This is the same argument that
`StacksFrontier/CategoryTheory/FiberedInSetoids/TwoFibreProduct.lean` makes for
`CategoryTheory.TwoFibreProd`, the repository's other model of the 2-fibre product; it is
redone here for `CategoryTheory.TwoFibreProductOver` because that is the model the stack
conditions are proved for — condition (1) is Stacks 02XQ,
`CategoryTheory.TwoFibreProductOver.isFibered_structureFunctor`, and condition (2) is
`CategoryTheory.TwoFibreProductOver.isMorSheaf_structureFunctor`.

`isStackInSetoids_of_isStack` takes the stack condition on the 2-fibre product as a hypothesis;
Stacks 0434 itself is that lemma applied to Stacks 026G,
`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`, whose condition (3) is
`CategoryTheory.TwoFibreProductOver.hasEffectiveDescent_structureFunctor`. Stacks 02ZL is the same
assembly for stacks in groupoids, where the fibre condition is Stacks 0041 rather than Stacks 042Z.

As for Stacks 0041 and 04SB, "the 2-category of stacks in setoids has 2-fibre products, and they
are described as in Categories, Lemma 0040" is read as: the construction of Stacks 0040 does not
leave the sub-2-category. Mathlib has no 2-limits in a bicategory, so the literal statement is not
available; and per the precedent of Stacks 0041 and 04SB no separate universal property is needed,
the 2-category of stacks in setoids being a full sub-2-category of the 2-category of categories
over `𝒞`.
-/

@[expose] public section

namespace CategoryTheory

namespace TwoFibreProductOver

universe v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴] {𝒮 : Type u₄} [Category.{v} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- Two morphisms lying over `𝟙 U` between objects over `U` are equal if the fibre over `U` is
thin. -/
private theorem eq_of_isThin_fiber {𝒵 : Type*} [Category.{v} 𝒵] {p : 𝒵 ⥤ 𝒞}
    (h : ∀ V : 𝒞, Quiver.IsThin (p.Fiber V)) {U : 𝒞} {x y : 𝒵} (hx : p.obj x = U)
    (hy : p.obj y = U) {f g : x ⟶ y} (hf : p.IsHomLift (𝟙 U) f) (hg : p.IsHomLift (𝟙 U) g) :
    f = g :=
  congrArg Subtype.val ((h U (Functor.Fiber.mk hx) (Functor.Fiber.mk hy)).elim
    (⟨f, hf⟩ : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hy) ⟨g, hg⟩)

/-- The fibres of the 2-fibre product are thin as soon as the fibres of `𝒳` and of `𝒴` are: a
morphism of the 2-fibre product is determined by its two components, and the components of a
morphism of the fibre over `U` are morphisms of the fibres of `𝒳` and of `𝒴` over `U`.

This is the fibre condition that Stacks 042Z (1) adds to Stacks 0041 for the 2-fibre product; no
condition on the fibres of `𝒮` is needed, the comparison square being an equation between
morphisms of `𝒮` that both components already satisfy. -/
lemma fiber_isThin (h𝒳 : ∀ V : 𝒞, Quiver.IsThin (p𝒳.Fiber V))
    (h𝒴 : ∀ V : 𝒞, Quiver.IsThin (p𝒴.Fiber V)) (U : 𝒞) :
    Quiver.IsThin ((structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) := by
  intro P Q
  refine ⟨fun m m' ↦ Functor.Fiber.hom_ext (Hom.ext' ?_ ?_)⟩
  · exact eq_of_isThin_fiber h𝒳 (P.1.hx.trans P.2) (Q.1.hx.trans Q.2)
      (isHomLift_a m.1 (𝟙 U) m.2) (isHomLift_a m'.1 (𝟙 U) m'.2)
  · exact eq_of_isThin_fiber h𝒴 (P.1.hy.trans P.2) (Q.1.hy.trans Q.2)
      (isHomLift_b m.1 (𝟙 U) m.2) (isHomLift_b m'.1 (𝟙 U) m'.2)

/-- The assembly of Stacks 0434 from its three conditions: if `𝒳` and `𝒴` are fibred in groupoids
with thin fibres and the 2-fibre product is a stack over `(𝒞, J)`, then the 2-fibre product is a
stack in setoids.

The stack condition on the 2-fibre product is a hypothesis here, not a consequence: condition (1)
of Stacks 026F for it is Stacks 02XQ and condition (2) is
`CategoryTheory.TwoFibreProductOver.isMorSheaf_structureFunctor`, but condition (3), effectivity of
descent, is the part of Stacks 026G that the library does not have. So this lemma is not tagged
0434; supplying that hypothesis is all that 0434 still needs. -/
lemma isStackInSetoids_of_isStack {J : GrothendieckTopology 𝒞}
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (t𝒳 : ∀ V : 𝒞, Quiver.IsThin (p𝒳.Fiber V)) (t𝒴 : ∀ V : 𝒞, Quiver.IsThin (p𝒴.Fiber V))
    (hstack : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStack J) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStackInSetoids J where
  isStack := hstack
  fiber_isGroupoid := fiber_isGroupoid h𝒳 h𝒴
  fiber_isThin := fiber_isThin t𝒳 t𝒴

/-- **Stacks 02ZL.** The 2-fibre product of stacks in groupoids over a site `(𝒞, J)` is a stack in
groupoids: the construction of Stacks 0040 does not leave the 2-category of stacks in groupoids.

"Stack in groupoids" is spelled out as its two conditions, being a stack over `(𝒞, J)` and being
fibred in groupoids, because the library's `CategoryTheory.Functor.IsStackInGroupoids` is a second,
unrelated rendering of the notion (see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Stack.Setoid`). The first condition is Stacks 026G and the second
is Stacks 0041; the hypotheses on `F` and `G` are only that they are strictly over `𝒞`, since a
functor over `𝒞` into a category fibred in groupoids automatically preserves strongly cartesian
morphisms. -/
@[stacks 02ZL]
theorem isStack_isFiberedInGroupoids_structureFunctor {J : GrothendieckTopology 𝒞}
    (h𝒳 : Functor.IsStack p𝒳 J) (h𝒴 : Functor.IsStack p𝒴 J) (h𝒮 : Functor.IsStack p𝒮 J)
    (g𝒳 : p𝒳.IsFiberedInGroupoids) (g𝒴 : p𝒴.IsFiberedInGroupoids)
    (g𝒮 : p𝒮.IsFiberedInGroupoids) (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    Functor.IsStack (structureFunctor p𝒳 p𝒴 p𝒮 F G) J ∧
      (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFiberedInGroupoids :=
  ⟨isStack_structureFunctor p𝒳 p𝒴 p𝒮 F G J h𝒳 h𝒴 h𝒮 (g𝒮.isFibredOneMorphism hF)
      (g𝒮.isFibredOneMorphism hG),
    isFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G g𝒳 g𝒴 g𝒮 hF hG⟩

/-- **Stacks 0434.** The 2-fibre product of stacks in setoids over a site `(𝒞, J)` is a stack in
setoids: the construction of Stacks 0040 does not leave the 2-category of stacks in setoids.

Its three conditions are Stacks 026G (`isStack_structureFunctor`), Stacks 0041
(`fiber_isGroupoid`) and thinness of the fibres (`fiber_isThin`). Nothing is asked of `F` and `G`
beyond being strictly over `𝒞`, since a functor over `𝒞` into a category fibred in groupoids
automatically preserves strongly cartesian morphisms. -/
@[stacks 0434]
theorem isStackInSetoids {J : GrothendieckTopology 𝒞} (h𝒳 : p𝒳.IsStackInSetoids J)
    (h𝒴 : p𝒴.IsStackInSetoids J) (h𝒮 : p𝒮.IsStackInSetoids J)
    (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStackInSetoids J :=
  isStackInSetoids_of_isStack h𝒳.isFiberedInGroupoids h𝒴.isFiberedInGroupoids h𝒳.fiber_isThin
    h𝒴.fiber_isThin
    (isStack_structureFunctor p𝒳 p𝒴 p𝒮 F G J h𝒳.isStack h𝒴.isStack h𝒮.isStack
      (h𝒮.isFiberedInGroupoids.isFibredOneMorphism hF)
      (h𝒮.isFiberedInGroupoids.isFibredOneMorphism hG))

end TwoFibreProductOver

end CategoryTheory
