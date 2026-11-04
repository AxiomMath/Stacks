module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase
import StacksCore.Tactic.EgaSgaAttribute

/-! # The 2-fibre product over a faithful 1-morphism has thin fibres

Fix a base category `𝒞` and categories `𝒯`, `ℛ`, `𝒮` over `𝒞` with 1-morphisms `f : 𝒯 ⥤ 𝒮` and
`g : ℛ ⥤ 𝒮`. If `f` is faithful and the fibres of `ℛ` are thin, then the fibres of the 2-fibre
product `𝒯 ×_𝒮 ℛ` are thin as well. Consequently, over a site, the 2-fibre product of a stack in
groupoids and a stack in setoids along a faithful 1-morphism, and the 2-fibre product of two stacks
in setoids, are stacks in setoids.

## Main results

* `CategoryTheory.TwoFibreProductOver.fiber_isThin_of_faithful`: thinness of the fibres;
* `CategoryTheory.Functor.faithful_of_fiber_isThin`: a 1-morphism out of a fibred category with
  thin fibres is faithful;
* `CategoryTheory.Functor.isStackInSetoids_structureFunctor` and
  `CategoryTheory.Functor.isStackInSetoids_structureFunctor_of_isStackInSetoids`: the 2-fibre
  product is a stack in setoids, given that it is a stack;
* `CategoryTheory.Functor.isStackInSetoids_twoFibreProduct` and
  `CategoryTheory.Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids`: the same without
  that hypothesis.
-/

@[expose] public section

namespace CategoryTheory

universe v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒯 : Type u₂} [Category.{v} 𝒯]
  {ℛ : Type u₃} [Category.{v} ℛ] {𝒮 : Type u₄} [Category.{v} 𝒮]
variable {p𝒯 : 𝒯 ⥤ 𝒞} {pℛ : ℛ ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {f : 𝒯 ⥤ 𝒮} {g : ℛ ⥤ 𝒮}

-- The components of a morphism of a fibre of the 2-fibre product are read through the fibre
-- inclusion, which is semireducible, so the endpoints of the composites below agree only once it
-- unfolds.
set_option backward.isDefEq.respectTransparency false in
/-- If `f` is faithful and the fibres of `pℛ` are thin, then the fibres of the 2-fibre product
`𝒯 ×_𝒮 ℛ` are thin. -/
lemma TwoFibreProductOver.fiber_isThin_of_faithful [f.Faithful]
    (hthin : ∀ V : 𝒞, Quiver.IsThin (pℛ.Fiber V)) (U : 𝒞) :
    Quiver.IsThin ((TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).Fiber U) := by
  intro P Q
  refine ⟨fun Φ Ψ => ?_⟩
  have hb : (Functor.Fiber.fiberInclusion.map Φ).b = (Functor.Fiber.fiberInclusion.map Ψ).b := by
    have h := (hthin U (TwoFibreProductOver.fibSnd P) (TwoFibreProductOver.fibSnd Q)).allEq
      (TwoFibreProductOver.fibSndHom Φ) (TwoFibreProductOver.fibSndHom Ψ)
    simpa using congrArg Functor.Fiber.fiberInclusion.map h
  have ha : (Functor.Fiber.fiberInclusion.map Φ).a = (Functor.Fiber.fiberInclusion.map Ψ).a := by
    refine f.map_injective ?_
    rw [← cancel_mono (Functor.Fiber.fiberInclusion.obj Q).iso.hom,
      (Functor.Fiber.fiberInclusion.map Φ).w, (Functor.Fiber.fiberInclusion.map Ψ).w, hb]
  exact Functor.Fiber.hom_ext (TwoFibreProductOver.Hom.ext' ha hb)

/-- A 1-morphism over `𝒞` out of a fibred category all of whose fibres are thin is faithful. -/
@[sga "4 I 6.5.2" "(ii), sufficiency"]
lemma Functor.faithful_of_fiber_isThin [p𝒯.IsFibered]
    (hthin : ∀ V : 𝒞, Quiver.IsThin (p𝒯.Fiber V)) (hf : f ⋙ p𝒮 = p𝒯) : f.Faithful where
  map_injective {a b} φ₁ φ₂ h := by
    have hbase : p𝒯.map φ₁ = p𝒯.map φ₂ := by
      subst hf
      simp [Functor.comp_map, h]
    refine Functor.hom_unique_of_fiber_isThin p𝒯 (p𝒯.map φ₁) (hthin _) φ₁ φ₂ inferInstance ?_
    rw [hbase]
    infer_instance

/-- Let `𝒯` be fibred in groupoids over `𝒞`, let `ℛ` be a stack in setoids over the site `(𝒞, J)`,
and let `f : 𝒯 ⥤ 𝒮`, `g : ℛ ⥤ 𝒮` be functors over `𝒞` with `f` faithful. If the 2-fibre product
`𝒯 ×_𝒮 ℛ` is a stack over `(𝒞, J)`, then it is a stack in setoids. -/
theorem Functor.isStackInSetoids_structureFunctor (J : GrothendieckTopology 𝒞)
    (hg𝒯 : p𝒯.IsFiberedInGroupoids) (hℛ : pℛ.IsStackInSetoids J) [f.Faithful]
    (hstack : (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStack J) :
    (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStackInSetoids J where
  isStack := hstack
  fiber_isGroupoid := TwoFibreProductOver.fiber_isGroupoid hg𝒯 hℛ.isFiberedInGroupoids
  fiber_isThin := TwoFibreProductOver.fiber_isThin_of_faithful hℛ.fiber_isThin

/-- The 2-fibre product of two stacks in setoids over a category over `𝒞` is a stack in setoids,
given that it is a stack. -/
theorem Functor.isStackInSetoids_structureFunctor_of_isStackInSetoids (J : GrothendieckTopology 𝒞)
    (h𝒯 : p𝒯.IsStackInSetoids J) (hℛ : pℛ.IsStackInSetoids J) (hf : f ⋙ p𝒮 = p𝒯)
    (hstack : (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStack J) :
    (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStackInSetoids J :=
  have : p𝒯.IsFibered := h𝒯.isStack.isFibered
  have : f.Faithful := Functor.faithful_of_fiber_isThin h𝒯.fiber_isThin hf
  Functor.isStackInSetoids_structureFunctor J h𝒯.isFiberedInGroupoids hℛ hstack

/-- Let `𝒯` be a stack in groupoids and `𝒮` a stack over the site `(𝒞, J)`, and let `ℛ` be a
stack in setoids. Let `f : 𝒯 ⥤ 𝒮` and `g : ℛ ⥤ 𝒮` be 1-morphisms with `f` faithful. Then the
2-fibre product `𝒯 ×_{f, 𝒮, g} ℛ` is a stack in setoids. -/
@[stacks 05UI]
theorem Functor.isStackInSetoids_twoFibreProduct (J : GrothendieckTopology 𝒞)
    (h𝒯 : Functor.IsStack p𝒯 J) (g𝒯 : p𝒯.IsFiberedInGroupoids)
    (hℛ : pℛ.IsStackInSetoids J) (h𝒮 : Functor.IsStack p𝒮 J)
    (hF : p𝒯.IsFibredOneMorphism p𝒮 f) (hG : pℛ.IsFibredOneMorphism p𝒮 g) [f.Faithful] :
    (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStackInSetoids J :=
  Functor.isStackInSetoids_structureFunctor J g𝒯 hℛ
    (TwoFibreProductOver.isStack_structureFunctor p𝒯 pℛ p𝒮 f g J h𝒯 hℛ.isStack h𝒮 hF hG)

/-- Let `𝒮` be a stack over the site `(𝒞, J)` and let `𝒮₁`, `𝒮₂` be stacks in setoids, with
1-morphisms `f_i : 𝒮_i ⥤ 𝒮`. Then `𝒮₁ ×_{f₁, 𝒮, f₂} 𝒮₂` is a stack in setoids. -/
@[stacks 05UJ]
theorem Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids
    (J : GrothendieckTopology 𝒞)
    (h𝒯 : p𝒯.IsStackInSetoids J) (hℛ : pℛ.IsStackInSetoids J)
    (h𝒮 : Functor.IsStack p𝒮 J)
    (hF : p𝒯.IsFibredOneMorphism p𝒮 f) (hG : pℛ.IsFibredOneMorphism p𝒮 g) :
    (TwoFibreProductOver.structureFunctor p𝒯 pℛ p𝒮 f g).IsStackInSetoids J :=
  Functor.isStackInSetoids_structureFunctor_of_isStackInSetoids J h𝒯 hℛ hF.comp_eq
    (TwoFibreProductOver.isStack_structureFunctor p𝒯 pℛ p𝒮 f g J h𝒯.isStack hℛ.isStack h𝒮 hF hG)

end CategoryTheory
