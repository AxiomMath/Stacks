module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance

/-!
# An equivalence over the base, read fibrewise

Let `𝒞` be a category and let `e : BasedCategory.Equivalence 𝒳 𝒴` be an equivalence of
categories over `𝒞`. Since the two functors of `e` are functors over `𝒞`, each carries the fibre
of one side over `U` into the fibre of the other over `U`. This file defines that fibrewise
reading and records the full faithfulness of the two functors.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.fiberMap` and
  `CategoryTheory.BasedCategory.Equivalence.fiberMapFunctor`, the induced map on fibres and the
  forward functor read fibrewise.
* `CategoryTheory.BasedCategory.Equivalence.fullyFaithfulFunctor` and
  `CategoryTheory.BasedCategory.Equivalence.fullyFaithfulInverse`, full faithfulness of the two
  functors of an equivalence over `𝒞`.
-/

@[expose] public section

-- The declarations below relate `p` and `𝒴.p` through `BasedFunctor.comp`, whose instance
-- arguments are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

-- Every declaration below is a statement about `e`, but several mention it only in their proofs.
include e

/-- The map from the fibre of `𝒳` over `U` to the fibre of `𝒴` over `U` induced by the forward
functor of an equivalence over `𝒞`. -/
@[implicit_reducible]
def fiberMap {U : 𝒞} (x : 𝒳.p.Fiber U) : 𝒴.p.Fiber U :=
  ⟨e.functor.obj x.1, (e.functor.w_obj x.1).trans x.2⟩

/-- The underlying object of `𝒴` of `e.fiberMap x` is the image of `x` under `e.functor`. -/
@[simp]
lemma fiberMap_val {U : 𝒞} (x : 𝒳.p.Fiber U) : (e.fiberMap x).1 = e.functor.obj x.1 := rfl

/-- The forward functor of an equivalence over `𝒞` read fibrewise: the functor from the fibre of
`𝒳` over `U` to the fibre of `𝒴` over `U` given on objects by `fiberMap`. -/
@[implicit_reducible]
def fiberMapFunctor (U : 𝒞) : 𝒳.p.Fiber U ⥤ 𝒴.p.Fiber U where
  obj x := e.fiberMap x
  map φ := ⟨e.functor.map (Functor.Fiber.fiberInclusion.map φ),
    BasedFunctor.preserves_isHomLift (F := e.functor) (𝟙 U) _⟩
  map_id _ := Functor.Fiber.hom_ext (e.functor.map_id _)
  map_comp _ _ := Functor.Fiber.hom_ext (e.functor.map_comp _ _)

/-- `CategoryTheory.BasedCategory.Equivalence.fiberMapFunctor` acts on morphisms by applying
`e.functor` to the underlying morphism of `𝒳`. -/
@[simp]
lemma fiberInclusion_map_fiberMapFunctor_map {U : 𝒞} {x y : 𝒳.p.Fiber U} (φ : x ⟶ y) :
    Functor.Fiber.fiberInclusion.map ((e.fiberMapFunctor U).map φ) =
      e.functor.map (Functor.Fiber.fiberInclusion.map φ) := rfl

/-- The forward functor of the inverse equivalence is the inverse functor. -/
@[simp] lemma symm_functor : e.symm.functor = e.inverse := rfl

/-- The inverse functor of the inverse equivalence is the forward functor. -/
@[simp] lemma symm_inverse : e.symm.inverse = e.functor := rfl

/-- The forward functor of an equivalence over `𝒞` is fully faithful. -/
noncomputable def fullyFaithfulFunctor : e.functor.toFunctor.FullyFaithful :=
  e.equiv.fullyFaithfulFunctor

/-- The inverse functor of an equivalence over `𝒞` is fully faithful. -/
noncomputable def fullyFaithfulInverse : e.inverse.toFunctor.FullyFaithful :=
  e.equiv.fullyFaithfulInverse

end BasedCategory.Equivalence

end CategoryTheory
