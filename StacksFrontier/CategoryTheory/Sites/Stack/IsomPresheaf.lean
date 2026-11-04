module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The presheaf of isomorphisms `Isom(x, y)` (Stacks 02ZB)

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, let `U` be an object of `𝒮` and let `x`, `y` be objects of
the fibre category over `U`. Stacks 02ZB introduces two presheaves on `𝒮/U`: the *presheaf of
morphisms* `Mor(x, y)`, whose sections over `f : V ⟶ U` are the morphisms `f^* x ⟶ f^* y` of the
fibre over `V`, and its *subpresheaf of isomorphisms* `Isom(x, y)`, whose sections over `f` are the
morphisms `f^* x ⟶ f^* y` that are isomorphisms.

`Mor(x, y)` is `CategoryTheory.Functor.morPresheaf`. This file adds `Isom(x, y)`. That the
isomorphisms really do form a subpresheaf is the substance: it says that restricting an isomorphism
of a fibre to a smaller object of `𝒮/U` again gives an isomorphism, which is not formal, because
the restriction map `CategoryTheory.Functor.morRestrict` is defined by a universal property and not
as the action of a functor on morphisms. What makes it true is that restriction along a fixed
`h : f₁ ⟶ f₂` is compatible with composition and identities in the fibre, and that in turn comes
from a naturality square relating `morRestrict` to the restriction map
`CategoryTheory.Functor.pullbackFiberMap` of a single object.

## Main definitions

* `CategoryTheory.Functor.isomSubpresheaf`, the subpresheaf `Isom(x, y) ⊆ Mor(x, y)` of
  Stacks 02ZB;
* `CategoryTheory.Functor.isomPresheaf`, the same thing read as a presheaf on `𝒮/U` in its own
  right. Its inclusion into `Mor(x, y)` is `CategoryTheory.Subfunctor.ι`, which Mathlib already
  knows to be a monomorphism.

## Main results

* `CategoryTheory.Functor.fiberInclusion_map_morRestrict_comp_pullbackFiberMap`, the naturality
  square: restricting a section and then pushing the result back up agrees with pushing up first
  and then applying the section;
* `CategoryTheory.Functor.morRestrict_id_hom` and `CategoryTheory.Functor.morRestrict_comp_hom`,
  restriction along a fixed morphism of `𝒮/U` preserves identities and composition of the fibre;
* `CategoryTheory.Functor.isIso_morRestrict`, restriction of an isomorphism is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Functor

-- `Fiber` and its inclusion must unfold for the endpoints of the composites below to be seen
-- as equal at `implicit` transparency, as in
-- `StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks`.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- The naturality square for the restriction maps of `Mor(x, y)`: for `h : f₁ ⟶ f₂` in `𝒮/U` and a
section `m : f₂^* x ⟶ f₂^* y`, restricting `m` along `h` and then following the restriction map
`f₁^* y ⟶ f₂^* y` of `y` is the same as first following the restriction map `f₁^* x ⟶ f₂^* x` of
`x` and then applying `m`.

Both sides lie over `h.left` and become equal after composing with the chosen cartesian lift of
`f₂` at `y`, which is strongly cartesian, so they agree. -/
lemma fiberInclusion_map_morRestrict_comp_pullbackFiberMap (x y : p.Fiber U) {g₁ g₂ : Over U}
    (h : g₁ ⟶ g₂) (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    Fiber.fiberInclusion.map (morRestrict p x y h m) ≫ pullbackFiberMap p y h =
      pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m := by
  have hl : p.IsHomLift h.left
      (Fiber.fiberInclusion.map (morRestrict p x y h m) ≫ pullbackFiberMap p y h) := by
    have h0 : p.IsHomLift (𝟙 g₁.left ≫ h.left)
        (Fiber.fiberInclusion.map (morRestrict p x y h m) ≫ pullbackFiberMap p y h) :=
      inferInstance
    rwa [Category.id_comp] at h0
  have hr : p.IsHomLift h.left
      (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m) := by
    have h0 : p.IsHomLift (h.left ≫ 𝟙 g₂.left)
        (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m) := inferInstance
    rwa [Category.comp_id] at h0
  refine IsStronglyCartesian.ext p g₂.hom (IsPreFibered.pullbackMap y.2 g₂.hom) h.left ?_
  rw [Category.assoc, pullbackFiberMap_fac, morRestrict_fac, Category.assoc]

/-- Restriction along `h : f₁ ⟶ f₂` sends the identity section of `Mor(x, x)` to the identity. -/
lemma morRestrict_id_hom (x : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    morRestrict p x x h (𝟙 (pullbackFiber p x g₂.hom)) = 𝟙 (pullbackFiber p x g₁.hom) := by
  refine (morRestrict_uniq p x x h _ _ ?_).symm
  have e₁ : Fiber.fiberInclusion.map (𝟙 (pullbackFiber p x g₁.hom)) ≫
      IsPreFibered.pullbackMap x.2 g₁.hom = IsPreFibered.pullbackMap x.2 g₁.hom := by
    rw [Functor.map_id]; exact Category.id_comp _
  have e₂ : Fiber.fiberInclusion.map (𝟙 (pullbackFiber p x g₂.hom)) ≫
      IsPreFibered.pullbackMap x.2 g₂.hom = IsPreFibered.pullbackMap x.2 g₂.hom := by
    rw [Functor.map_id]; exact Category.id_comp _
  rw [e₁, e₂, pullbackFiberMap_fac]

/-- Restriction along `h : f₁ ⟶ f₂` respects composition in the fibre over `f₂.left`. -/
lemma morRestrict_comp_hom (x y z : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom)
    (n : pullbackFiber p y g₂.hom ⟶ pullbackFiber p z g₂.hom) :
    morRestrict p x z h (m ≫ n) = morRestrict p x y h m ≫ morRestrict p y z h n := by
  refine (morRestrict_uniq p x z h (m ≫ n) _ ?_).symm
  rw [Functor.map_comp, Category.assoc, morRestrict_fac, ← Category.assoc,
    fiberInclusion_map_morRestrict_comp_pullbackFiberMap, Category.assoc, Functor.map_comp,
    Category.assoc]

/-- Restriction along `h : f₁ ⟶ f₂` carries an isomorphism `f₂^* x ≅ f₂^* y` of the fibre to an
isomorphism `f₁^* x ≅ f₁^* y`: the restriction of the inverse is an inverse, by
`CategoryTheory.Functor.morRestrict_comp_hom` and `CategoryTheory.Functor.morRestrict_id_hom`. -/
lemma isIso_morRestrict (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) [IsIso m] :
    IsIso (morRestrict p x y h m) :=
  ⟨morRestrict p y x h (CategoryTheory.inv m), by
    rw [← morRestrict_comp_hom, IsIso.hom_inv_id, morRestrict_id_hom], by
    rw [← morRestrict_comp_hom, IsIso.inv_hom_id, morRestrict_id_hom]⟩

/-- **Stacks 02ZB**, the subpresheaf `Isom(x, y)` of `Mor(x, y)`: over `f : V ⟶ U` its sections are
the morphisms `f^* x ⟶ f^* y` of the fibre over `V` that are isomorphisms. This is a subpresheaf
because restriction preserves isomorphisms, `CategoryTheory.Functor.isIso_morRestrict`. -/
@[stacks 02ZB "The subpresheaf `Isom(x, y)` of `Mor(x, y)`; the presheaf `Mor(x, y)` itself is
  `CategoryTheory.Functor.morPresheaf`."]
noncomputable def isomSubpresheaf (x y : p.Fiber U) : Subfunctor (morPresheaf p x y) where
  obj g := {m | IsIso m}
  map i m hm := by
    have : IsIso m := hm
    exact isIso_morRestrict p x y i.unop m

/-- A section of `Mor(x, y)` lies in `Isom(x, y)` exactly when it is an isomorphism. -/
lemma mem_isomSubpresheaf_obj (x y : p.Fiber U) {g : (Over U)ᵒᵖ} (m : (morPresheaf p x y).obj g) :
    m ∈ (isomSubpresheaf p x y).obj g ↔
      IsIso (show pullbackFiber p x g.unop.hom ⟶ pullbackFiber p y g.unop.hom from m) :=
  Iff.rfl

/-- **Stacks 02ZB**, the *presheaf of isomorphisms from `x` to `y`* on `𝒮/U`. Its inclusion into
the presheaf of morphisms `CategoryTheory.Functor.morPresheaf` is `CategoryTheory.Subfunctor.ι`. -/
@[sga "3 I 1.7.2" "more general"]
noncomputable def isomPresheaf (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type v₂ :=
  (isomSubpresheaf p x y).toFunctor

end Functor

end CategoryTheory
