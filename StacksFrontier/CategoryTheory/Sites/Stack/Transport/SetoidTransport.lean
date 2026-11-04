module

public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport

/-!
# The stack-in-setoids condition transports along an equivalence over the base

A *stack in setoids* is a stack whose fibre categories are thin groupoids
(`CategoryTheory.Functor.IsStackInSetoids`). If `𝒳` and `𝒴` are equivalent over `𝒞` and `𝒳` is a
stack in setoids, then so is `𝒴`.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.fiber_isGroupoid`: groupoid fibres transport along an
  equivalence over `𝒞`.
* `CategoryTheory.BasedCategory.Equivalence.fiber_isThin`: thin fibres transport along an
  equivalence over `𝒞`.
* `CategoryTheory.BasedCategory.Equivalence.isStackInSetoids`: the stack-in-setoids condition
  transports along an equivalence over `𝒞`.

## References

* [Stacks Project, Tag 0431](https://stacks.math.columbia.edu/tag/0431)
-/

@[expose] public section

-- The transports below relate `p` and `𝒴.p` through `BasedFunctor.comp`, whose instance
-- arguments are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

include e

/-- The inverse of an equivalence over `𝒞` sends fibre morphisms to fibre morphisms. -/
private theorem inverse_map_isHomLift {U : 𝒞} {x y : 𝒴.p.Fiber U} (m : x ⟶ y) :
    𝒳.p.IsHomLift (𝟙 U) (e.inverse.map (Functor.Fiber.fiberInclusion.map m)) :=
  BasedFunctor.preserves_isHomLift (F := e.inverse) (𝟙 U) _

/-- If `𝒳` and `𝒴` are equivalent over `𝒞` and every fibre of `𝒳` is a groupoid, then every fibre
of `𝒴` is a groupoid. -/
lemma fiber_isGroupoid (h : ∀ U : 𝒞, IsGroupoid (𝒳.p.Fiber U)) (U : 𝒞) :
    IsGroupoid (𝒴.p.Fiber U) where
  all_isIso {x y} m := by
    have hFF := e.fullyFaithfulInverse
    have := hFF.full
    have := hFF.faithful
    have hm : 𝒴.p.IsHomLift (𝟙 U) (Functor.Fiber.fiberInclusion.map m) := m.2
    have hiso : IsIso (e.inverse.map (Functor.Fiber.fiberInclusion.map m)) := by
      have := h U
      exact Functor.Fiber.fiberInclusion.map_isIso
        (X := e.symm.fiberMap x) (Y := e.symm.fiberMap y)
        ⟨e.inverse.map (Functor.Fiber.fiberInclusion.map m), e.inverse_map_isHomLift m⟩
    have : IsIso (Functor.Fiber.fiberInclusion.map m) :=
      isIso_of_fully_faithful e.inverse.toFunctor _
    refine ⟨⟨⟨inv (Functor.Fiber.fiberInclusion.map m), inferInstance⟩, ?_, ?_⟩⟩ <;>
      apply Functor.Fiber.hom_ext <;> simp [Functor.Fiber.fiberInclusion]

/-- If `𝒳` and `𝒴` are equivalent over `𝒞` and every fibre of `𝒳` is thin, then every fibre of
`𝒴` is thin. -/
lemma fiber_isThin (h : ∀ U : 𝒞, Quiver.IsThin (𝒳.p.Fiber U)) (U : 𝒞) :
    Quiver.IsThin (𝒴.p.Fiber U) := by
  intro x y
  refine ⟨fun m m' ↦ ?_⟩
  have hFF := e.fullyFaithfulInverse
  have heq : (⟨e.inverse.map (Functor.Fiber.fiberInclusion.map m),
        e.inverse_map_isHomLift m⟩ : e.symm.fiberMap x ⟶ e.symm.fiberMap y) =
      ⟨e.inverse.map (Functor.Fiber.fiberInclusion.map m'), e.inverse_map_isHomLift m'⟩ :=
    (h U _ _).allEq _ _
  exact Functor.Fiber.hom_ext (hFF.map_injective (congrArg Functor.Fiber.fiberInclusion.map heq))

/-- The stack-in-setoids condition transports along an equivalence over `𝒞`. -/
theorem isStackInSetoids (J : GrothendieckTopology 𝒞) (h : 𝒳.p.IsStackInSetoids J) :
    𝒴.p.IsStackInSetoids J where
  isStack := e.isStack J h.isStack
  fiber_isGroupoid := e.fiber_isGroupoid h.fiber_isGroupoid
  fiber_isThin := e.fiber_isThin h.fiber_isThin

end BasedCategory.Equivalence

end CategoryTheory
