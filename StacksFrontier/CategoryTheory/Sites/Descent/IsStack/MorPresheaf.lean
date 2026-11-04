module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp

/-!
# The presheaf `Mor(x, y)` of Stacks 02ZB

For a fibred category `p` and two objects `x`, `y` of the fibre over `U`, the presheaf
`Mor(x, y)` on `𝒮/U` has as its sections over `f : V ⟶ U` the morphisms `f^* x ⟶ f^* y` of the
fibre over `V`, taken between the *chosen* pullbacks, and its restriction map along `h : f₁ ⟶ f₂`
of `𝒮/U` is the one determined by the universal property of the chosen cartesian lift of `f₁` at
`y`. Chosen pullbacks exist by `CategoryTheory.Functor.IsPreFibered`, so no extra data beyond
condition (1) of Stacks 026F is needed.

Condition (2) of Stacks 026F is then `CategoryTheory.Functor.IsMorSheaf`: that this presheaf is a
sheaf for the topology induced on `𝒮/U`.

## Main definitions

* `CategoryTheory.Functor.morPresheaf`, the presheaf `Mor(x, y)` of Stacks 02ZB;
* `CategoryTheory.Functor.IsMorSheaf`, condition (2) of Stacks 026F.
-/

@[expose] public section

-- Needed throughout: the transfer lemmas below relate `p` and `P.ι ⋙ p`, and the instance
-- arguments of `IsHomLift` and `IsCartesian` are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮}

/-- The morphism `f₁^* x ⟶ f₂^* x` over `h.left` induced by the universal property of the chosen
cartesian lift of `f₂` at `x`, for `h : f₁ ⟶ f₂` in `𝒮/U`. This is the restriction map of the
pullbacks of a single object. -/
noncomputable def pullbackFiberMap (x : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (pullbackFiber p x g₁.hom).1 ⟶ (pullbackFiber p x g₂.hom).1 :=
  IsStronglyCartesian.map p g₂.hom (IsPreFibered.pullbackMap x.2 g₂.hom)
    (g := h.left) (Over.w h).symm (IsPreFibered.pullbackMap x.2 g₁.hom)

/-- `pullbackFiberMap p x h` lies over `h.left`. -/
instance pullbackFiberMap_isHomLift (x : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    p.IsHomLift h.left (pullbackFiberMap p x h) := by
  unfold pullbackFiberMap; infer_instance

/-- The equation that determines `pullbackFiberMap p x h`: composed with the chosen cartesian lift
of `f₂` at `x` it is the chosen cartesian lift of `f₁` at `x`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberMap_fac (x : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    pullbackFiberMap p x h ≫ IsPreFibered.pullbackMap x.2 g₂.hom =
      IsPreFibered.pullbackMap x.2 g₁.hom :=
  IsStronglyCartesian.fac p g₂.hom _ _ _

/-- The restriction map of the chosen pullbacks of `x` along an identity of `𝒮/U` is the
identity. -/
lemma pullbackFiberMap_id (x : p.Fiber U) (g : Over U) :
    pullbackFiberMap p x (𝟙 g) = 𝟙 _ := by
  have : p.IsHomLift (Over.Hom.left (𝟙 g)) (𝟙 (pullbackFiber p x g.hom).1) :=
    IsHomLift.id (pullbackFiber p x g.hom).2
  exact (IsStronglyCartesian.map_uniq p g.hom _ _ _ _ (by simp)).symm

/-- The restriction maps of the chosen pullbacks of `x` compose. -/
lemma pullbackFiberMap_comp (x : p.Fiber U) {g₁ g₂ g₃ : Over U} (h₁ : g₁ ⟶ g₂) (h₂ : g₂ ⟶ g₃) :
    pullbackFiberMap p x h₁ ≫ pullbackFiberMap p x h₂ = pullbackFiberMap p x (h₁ ≫ h₂) := by
  unfold pullbackFiberMap
  exact IsStronglyCartesian.map_comp_map p g₃.hom _ _ _ _ _

/-- The composite `f₁^* x ⟶ f₂^* x ⟶ f₂^* y ⟶ y` lies over `f₁`. -/
lemma isHomLift_pullbackFiberMap_comp (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    p.IsHomLift g₁.hom (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
      IsPreFibered.pullbackMap y.2 g₂.hom) := by
  have h1 : p.IsHomLift (h.left ≫ 𝟙 g₂.left ≫ g₂.hom)
      (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 g₂.hom) := inferInstance
  rwa [Category.id_comp, Over.w h] at h1

/-- Makes `isHomLift_pullbackFiberMap_comp` available to instance search. -/
private instance isHomLift_pullbackFiberMap_comp_aux (x y : p.Fiber U) {g₁ g₂ : Over U}
    (h : g₁ ⟶ g₂) (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    p.IsHomLift g₁.hom (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
      IsPreFibered.pullbackMap y.2 g₂.hom) :=
  isHomLift_pullbackFiberMap_comp p x y h m

/-- The restriction along `h : f₁ ⟶ f₂` of a section `m : f₂^* x ⟶ f₂^* y` of `Mor(x, y)`: the
unique morphism `f₁^* x ⟶ f₁^* y` in the fibre whose composite with the chosen cartesian lift of
`f₁` at `y` is `f₁^* x ⟶ f₂^* x ⟶ f₂^* y ⟶ y`. -/
noncomputable def morRestrict (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    pullbackFiber p x g₁.hom ⟶ pullbackFiber p y g₁.hom :=
  have := isHomLift_pullbackFiberMap_comp p x y h m
  ⟨IsCartesian.map p g₁.hom (IsPreFibered.pullbackMap y.2 g₁.hom)
      (pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 g₂.hom),
    IsCartesian.map_isHomLift p g₁.hom _ _⟩

/-- The equation that determines `morRestrict p x y h m`: composed with the chosen cartesian lift
of `f₁` at `y` it is `f₁^* x ⟶ f₂^* x ⟶ f₂^* y ⟶ y`. -/
@[reassoc]
lemma morRestrict_fac (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom) :
    Fiber.fiberInclusion.map (morRestrict p x y h m) ≫
        IsPreFibered.pullbackMap y.2 g₁.hom =
      pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 g₂.hom :=
  IsCartesian.fac p g₁.hom (IsPreFibered.pullbackMap y.2 g₁.hom) _

/-- `morRestrict p x y h m` is the only morphism of the fibre over `f₁.left` satisfying
`morRestrict_fac`. -/
lemma morRestrict_uniq (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom)
    (n : pullbackFiber p x g₁.hom ⟶ pullbackFiber p y g₁.hom)
    (hn : Fiber.fiberInclusion.map n ≫ IsPreFibered.pullbackMap y.2 g₁.hom =
      pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 g₂.hom) :
    n = morRestrict p x y h m := by
  exact Fiber.hom_ext
    (IsCartesian.map_uniq p g₁.hom (IsPreFibered.pullbackMap y.2 g₁.hom) _ _ hn)

/-- Restricting a section of `Mor(x, y)` along an identity of `𝒮/U` leaves it unchanged. -/
@[stacks 026A "restriction along the identity"]
lemma morRestrict_id (x y : p.Fiber U) (g : Over U)
    (m : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom) :
    morRestrict p x y (𝟙 g) m = m :=
  (morRestrict_uniq p x y (𝟙 g) m m (by simp [pullbackFiberMap_id])).symm

/-- Restricting a section of `Mor(x, y)` along a composite is restricting along the two factors in
turn. -/
@[stacks 026A "compatibility with composition: φ|_{V″} = (φ|_{V′})|_{V″}"]
lemma morRestrict_comp (x y : p.Fiber U) {g₁ g₂ g₃ : Over U} (h₁ : g₁ ⟶ g₂) (h₂ : g₂ ⟶ g₃)
    (m : pullbackFiber p x g₃.hom ⟶ pullbackFiber p y g₃.hom) :
    morRestrict p x y (h₁ ≫ h₂) m = morRestrict p x y h₁ (morRestrict p x y h₂ m) := by
  refine (morRestrict_uniq p x y (h₁ ≫ h₂) m _ ?_).symm
  rw [morRestrict_fac, morRestrict_fac, ← pullbackFiberMap_comp]
  simp

/-- The presheaf `Mor(x, y)` on `𝒮/U` of a fibred category `p`: its sections over `f : V ⟶ U` are
the morphisms `f^* x ⟶ f^* y` of the fibre over `V`, and its restriction maps are
`CategoryTheory.Functor.morRestrict`. -/
@[stacks 02ZB, implicit_reducible]
noncomputable def morPresheaf (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type v₂ where
  obj g := pullbackFiber p x g.unop.hom ⟶ pullbackFiber p y g.unop.hom
  map h := ↾fun s ↦ morRestrict p x y h.unop s
  map_id g := by
    ext m
    exact congrArg Fiber.fiberInclusion.map (morRestrict_id p x y g.unop m)
  map_comp {g₃ g₂ g₁} q₁ q₂ := by
    ext m
    exact congrArg Fiber.fiberInclusion.map (morRestrict_comp p x y q₂.unop q₁.unop m)

/-- The sections of `CategoryTheory.Functor.morPresheaf` over `g` are the morphisms between the
chosen pullbacks along `g`. -/
lemma morPresheaf_obj (x y : p.Fiber U) (g : (Over U)ᵒᵖ) :
    (morPresheaf p x y).obj g = (pullbackFiber p x g.unop.hom ⟶ pullbackFiber p y g.unop.hom) :=
  rfl

/-- The restriction maps of `CategoryTheory.Functor.morPresheaf` are
`CategoryTheory.Functor.morRestrict`. -/
@[simp]
lemma morPresheaf_map_apply (x y : p.Fiber U) {g₁ g₂ : (Over U)ᵒᵖ} (h : g₁ ⟶ g₂)
    (m : (morPresheaf p x y).obj g₁) :
    (morPresheaf p x y).map h m = morRestrict p x y h.unop m :=
  rfl

/-- Stacks 026F (2) for a fibred category `p`: the presheaf `Mor(x, y)` of Stacks 02ZB on `𝒮/U`
is a sheaf for the topology induced on `𝒮/U` by `J`. -/
def IsMorSheaf (J : GrothendieckTopology 𝒮) (U : 𝒮) (x y : p.Fiber U) : Prop :=
  Presheaf.IsSheaf (J.over U) (morPresheaf p x y)

end Functor

end CategoryTheory
