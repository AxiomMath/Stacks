module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# Base change of a morphism of a fibre

A morphism `α : y ⟶ y'` of the fibre over `W` induces a morphism `b^* y ⟶ b^* y'` of the fibre
over `Z` for every `b : Z ⟶ W`, namely the one determined by the universal property of the chosen
cartesian lift of `b` at `y'`. This is functorial, so an isomorphism of the fibre over `W` induces
an isomorphism of the fibre over `Z`.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberHom`, the induced morphism of chosen pullbacks;
* `CategoryTheory.Functor.pullbackFiberIso`, its isomorphism form;
* `CategoryTheory.Functor.pullbackFiberHomEquiv`, the universal property of the chosen pullback
  read as a bijection: morphisms of the fibre over `Z` into `ε^* x` are the morphisms into `x`
  lying over `ε`;
* `CategoryTheory.Functor.transportHomOver`, the action of an isomorphism `ε^* x ≅ ε'^* x'` of
  chosen pullbacks on those morphisms.
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

variable {p : 𝒳 ⥤ 𝒮} [p.IsPreFibered] {W : 𝒮} {y y' y'' : p.Fiber W} {Z : 𝒮}

/-- The morphism `b^* y ⟶ b^* y'` of the fibre over `Z` induced by `α : y ⟶ y'`. -/
noncomputable def pullbackFiberHom (α : y ⟶ y') (b : Z ⟶ W) :
    pullbackFiber p y b ⟶ pullbackFiber p y' b :=
  have : p.IsCartesian b (IsPreFibered.pullbackMap y.2 b) :=
    IsPreFibered.pullbackMap.IsCartesian y.2 b
  have : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map α) := α.2
  have : p.IsCartesian b (IsPreFibered.pullbackMap y'.2 b) :=
    IsPreFibered.pullbackMap.IsCartesian y'.2 b
  have : p.IsHomLift b (IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α) :=
    inferInstance
  ⟨IsCartesian.map p b (IsPreFibered.pullbackMap y'.2 b)
    (IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α), inferInstance⟩

/-- A morphism `β` of the fibre over `Z` is `pullbackFiberHom α b` exactly when it satisfies the
defining equation of `pullbackFiberHom_fac`. -/
private lemma eq_pullbackFiberHom_iff (α : y ⟶ y') (b : Z ⟶ W)
    (β : pullbackFiber p y b ⟶ pullbackFiber p y' b) :
    β = pullbackFiberHom α b ↔ Fiber.fiberInclusion.map β ≫ IsPreFibered.pullbackMap y'.2 b =
      IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α := by
  have : p.IsCartesian b (IsPreFibered.pullbackMap y.2 b) :=
    IsPreFibered.pullbackMap.IsCartesian y.2 b
  have : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map α) := α.2
  have : p.IsCartesian b (IsPreFibered.pullbackMap y'.2 b) :=
    IsPreFibered.pullbackMap.IsCartesian y'.2 b
  have : p.IsHomLift b (IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α) :=
    inferInstance
  refine ⟨fun h => h ▸ IsCartesian.fac p b (IsPreFibered.pullbackMap y'.2 b)
    (IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α), fun hβ => ?_⟩
  exact Fiber.hom_ext (IsCartesian.map_uniq p b (IsPreFibered.pullbackMap y'.2 b)
    (IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α) _ hβ)

/-- The equation that determines `pullbackFiberHom α b`: composed with the chosen cartesian lift
of `b` at `y'` it is the chosen cartesian lift of `b` at `y` followed by `α`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberHom_fac (α : y ⟶ y') (b : Z ⟶ W) :
    Fiber.fiberInclusion.map (pullbackFiberHom α b) ≫ IsPreFibered.pullbackMap y'.2 b =
      IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α :=
  (eq_pullbackFiberHom_iff α b _).1 rfl

/-- `pullbackFiberHom α b` is the only morphism of the fibre over `Z` satisfying
`pullbackFiberHom_fac`. -/
lemma pullbackFiberHom_uniq (α : y ⟶ y') (b : Z ⟶ W)
    (β : pullbackFiber p y b ⟶ pullbackFiber p y' b)
    (hβ : Fiber.fiberInclusion.map β ≫ IsPreFibered.pullbackMap y'.2 b =
      IsPreFibered.pullbackMap y.2 b ≫ Fiber.fiberInclusion.map α) :
    β = pullbackFiberHom α b :=
  (eq_pullbackFiberHom_iff α b β).2 hβ

/-- Base change of an identity is the identity. -/
@[simp] lemma pullbackFiberHom_id (b : Z ⟶ W) : pullbackFiberHom (𝟙 y) b = 𝟙 _ :=
  (pullbackFiberHom_uniq (𝟙 y) b (𝟙 _) (by simp [Fiber.fiberInclusion])).symm

/-- Base change along `b` is functorial in the morphism of the fibre. -/
@[reassoc]
lemma pullbackFiberHom_comp (α : y ⟶ y') (β : y' ⟶ y'') (b : Z ⟶ W) :
    pullbackFiberHom (α ≫ β) b = pullbackFiberHom α b ≫ pullbackFiberHom β b :=
  (pullbackFiberHom_uniq _ b _ (by
    simp [Functor.map_comp, Category.assoc, pullbackFiberHom_fac,
      pullbackFiberHom_fac_assoc])).symm

/-- The isomorphism `b^* y ≅ b^* y'` of the fibre over `Z` induced by `α : y ≅ y'`. -/
@[simps]
noncomputable def pullbackFiberIso (α : y ≅ y') (b : Z ⟶ W) :
    pullbackFiber p y b ≅ pullbackFiber p y' b where
  hom := pullbackFiberHom α.hom b
  inv := pullbackFiberHom α.inv b
  hom_inv_id := by rw [← pullbackFiberHom_comp, α.hom_inv_id, pullbackFiberHom_id]
  inv_hom_id := by rw [← pullbackFiberHom_comp, α.inv_hom_id, pullbackFiberHom_id]

/-- Base change along `b` carries the two composites of an isomorphism of a fibre to identities. -/
@[reassoc (attr := simp)]
lemma pullbackFiberHom_hom_inv_id (α : y ≅ y') (b : Z ⟶ W) :
    pullbackFiberHom α.hom b ≫ pullbackFiberHom α.inv b = 𝟙 _ :=
  (pullbackFiberIso α b).hom_inv_id

/-- Base change along `b` of `α.inv` followed by base change of `α.hom` is the identity. -/
@[reassoc (attr := simp)]
lemma pullbackFiberHom_inv_hom_id (α : y ≅ y') (b : Z ⟶ W) :
    pullbackFiberHom α.inv b ≫ pullbackFiberHom α.hom b = 𝟙 _ :=
  (pullbackFiberIso α b).inv_hom_id

/-- Morphisms of the fibre over `Z` from `u` into the chosen pullback of `x` along `ε : Z ⟶ V`
are the morphisms `u.1 ⟶ x.1` of `𝒳` lying over `ε`. -/
noncomputable def pullbackFiberHomEquiv {V Z : 𝒮} (u : p.Fiber Z) (x : p.Fiber V) (ε : Z ⟶ V) :
    (u ⟶ pullbackFiber p x ε) ≃ {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ} where
  toFun χ :=
    ⟨Fiber.fiberInclusion.map χ ≫ IsPreFibered.pullbackMap x.2 ε, by
      have h₁ : p.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map χ) := χ.2
      have h₂ : p.IsHomLift ε (IsPreFibered.pullbackMap x.2 ε) :=
        (IsPreFibered.pullbackMap.IsCartesian x.2 ε).toIsHomLift
      infer_instance⟩
  invFun σ :=
    have : p.IsCartesian ε (IsPreFibered.pullbackMap x.2 ε) :=
      IsPreFibered.pullbackMap.IsCartesian x.2 ε
    have : p.IsHomLift ε σ.1 := σ.2
    ⟨IsCartesian.map p ε (IsPreFibered.pullbackMap x.2 ε) σ.1, inferInstance⟩
  left_inv χ := by
    have hcart : p.IsCartesian ε (IsPreFibered.pullbackMap x.2 ε) :=
      IsPreFibered.pullbackMap.IsCartesian x.2 ε
    have h₁ : p.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map χ) := χ.2
    have h₂ : p.IsHomLift ε (IsPreFibered.pullbackMap x.2 ε) := hcart.toIsHomLift
    have h₃ : p.IsHomLift ε
        (Fiber.fiberInclusion.map χ ≫ IsPreFibered.pullbackMap x.2 ε) := inferInstance
    exact Fiber.hom_ext (IsCartesian.map_uniq p ε (IsPreFibered.pullbackMap x.2 ε)
      (Fiber.fiberInclusion.map χ ≫ IsPreFibered.pullbackMap x.2 ε)
      (Fiber.fiberInclusion.map χ) rfl).symm
  right_inv σ := by
    have hcart : p.IsCartesian ε (IsPreFibered.pullbackMap x.2 ε) :=
      IsPreFibered.pullbackMap.IsCartesian x.2 ε
    have : p.IsHomLift ε σ.1 := σ.2
    exact Subtype.ext (IsCartesian.fac p ε (IsPreFibered.pullbackMap x.2 ε) σ.1)

/-- The morphism over `ε` attached to `χ` is `χ` followed by the chosen cartesian lift of `ε`. -/
@[simp]
lemma pullbackFiberHomEquiv_apply_coe {V Z : 𝒮} (u : p.Fiber Z) (x : p.Fiber V) (ε : Z ⟶ V)
    (χ : u ⟶ pullbackFiber p x ε) :
    (pullbackFiberHomEquiv u x ε χ).1 =
      Fiber.fiberInclusion.map χ ≫ IsPreFibered.pullbackMap x.2 ε := rfl

/-- The defining property of the inverse bijection: the morphism of the fibre it produces,
composed with the chosen cartesian lift, is the given morphism over `ε`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberHomEquiv_symm_fac {V Z : 𝒮} (u : p.Fiber Z) (x : p.Fiber V) (ε : Z ⟶ V)
    (σ : {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ}) :
    Fiber.fiberInclusion.map ((pullbackFiberHomEquiv u x ε).symm σ) ≫
        IsPreFibered.pullbackMap x.2 ε = σ.1 :=
  congrArg Subtype.val ((pullbackFiberHomEquiv u x ε).apply_symm_apply σ)

/-- Transport a morphism lying over `ε` to a morphism lying over `ε'` along an isomorphism of
the two chosen pullbacks. -/
noncomputable def transportHomOver {V W Z : 𝒮} (u : p.Fiber Z) {x : p.Fiber V} {x' : p.Fiber W}
    {ε : Z ⟶ V} {ε' : Z ⟶ W} (θ : pullbackFiber p x ε ≅ pullbackFiber p x' ε')
    (σ : {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ}) : {τ : u.1 ⟶ x'.1 // p.IsHomLift ε' τ} :=
  pullbackFiberHomEquiv u x' ε' ((pullbackFiberHomEquiv u x ε).symm σ ≫ θ.hom)

/-- The transported morphism is the morphism of the fibre corresponding to `σ`, followed by
`θ.hom` and the chosen cartesian lift of `ε'`. -/
@[simp]
lemma transportHomOver_coe {V W Z : 𝒮} (u : p.Fiber Z) {x : p.Fiber V} {x' : p.Fiber W}
    {ε : Z ⟶ V} {ε' : Z ⟶ W} (θ : pullbackFiber p x ε ≅ pullbackFiber p x' ε')
    (σ : {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ}) :
    (transportHomOver u θ σ).1 =
      Fiber.fiberInclusion.map ((pullbackFiberHomEquiv u x ε).symm σ) ≫
        Fiber.fiberInclusion.map θ.hom ≫ IsPreFibered.pullbackMap x'.2 ε' := by
  simp [transportHomOver, Category.assoc]

/-- Transporting along the identity does nothing. -/
@[simp]
lemma transportHomOver_refl {V Z : 𝒮} (u : p.Fiber Z) {x : p.Fiber V} {ε : Z ⟶ V}
    (σ : {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ}) :
    transportHomOver u (Iso.refl (pullbackFiber p x ε)) σ = σ := by
  simp [transportHomOver]

/-- Transporting along a composite of two isomorphisms of chosen pullbacks is transporting
twice. -/
lemma transportHomOver_trans {V W X Z : 𝒮} (u : p.Fiber Z) {x : p.Fiber V} {x' : p.Fiber W}
    {x'' : p.Fiber X} {ε : Z ⟶ V} {ε' : Z ⟶ W} {ε'' : Z ⟶ X}
    (θ : pullbackFiber p x ε ≅ pullbackFiber p x' ε')
    (θ' : pullbackFiber p x' ε' ≅ pullbackFiber p x'' ε'')
    (σ : {σ : u.1 ⟶ x.1 // p.IsHomLift ε σ}) :
    transportHomOver u (θ ≪≫ θ') σ = transportHomOver u θ' (transportHomOver u θ σ) := by
  simp only [transportHomOver, Equiv.symm_apply_apply, Iso.trans_hom, Category.assoc]

/-- Transport commutes with precomposition by a morphism of the fibre over `Z`. -/
lemma transportHomOver_comp {V W Z : 𝒮} {u u' : p.Fiber Z} (m : u ⟶ u') {x : p.Fiber V}
    {x' : p.Fiber W} {ε : Z ⟶ V} {ε' : Z ⟶ W}
    (θ : pullbackFiber p x ε ≅ pullbackFiber p x' ε')
    (σ : {σ : u'.1 ⟶ x.1 // p.IsHomLift ε σ}) (τ : {τ : u.1 ⟶ x.1 // p.IsHomLift ε τ})
    (hτ : τ.1 = Fiber.fiberInclusion.map m ≫ σ.1) :
    (transportHomOver u θ τ).1 =
      Fiber.fiberInclusion.map m ≫ (transportHomOver u' θ σ).1 := by
  have hcart : p.IsCartesian ε (IsPreFibered.pullbackMap x.2 ε) :=
    IsPreFibered.pullbackMap.IsCartesian x.2 ε
  have hm : p.IsHomLift (𝟙 Z) (Fiber.fiberInclusion.map m) := m.2
  have key : (pullbackFiberHomEquiv u x ε).symm τ =
      m ≫ (pullbackFiberHomEquiv u' x ε).symm σ := by
    refine Fiber.hom_ext (IsCartesian.ext p ε (IsPreFibered.pullbackMap x.2 ε) _ _ ?_)
    rw [pullbackFiberHomEquiv_symm_fac, Functor.map_comp, Category.assoc,
      pullbackFiberHomEquiv_symm_fac, hτ]
  rw [transportHomOver_coe, transportHomOver_coe, key, Functor.map_comp, Category.assoc]

end Functor

end CategoryTheory
