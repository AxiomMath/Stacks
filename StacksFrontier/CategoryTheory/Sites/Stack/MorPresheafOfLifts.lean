module

public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The presheaf `Mor(x, y)` computed from any system of cartesian lifts

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, let `U` be an object of `𝒮` and let `x`, `y` be objects
of the fibre over `U`.  The presheaf `Mor(x, y)` of Stacks 02ZB,
`CategoryTheory.Functor.morPresheaf`, is formed with the *chosen* pullbacks `f^* x`, `f^* y`:
its sections over `f : V ⟶ U` are the morphisms `f^* x ⟶ f^* y` of the fibre over `V`, and its
restriction maps are defined by the universal property of the chosen cartesian lifts.

In practice a fibred category comes with its own, explicit, cartesian lifts, and one wants to
compute `Mor(x, y)` with those.  This file does so, for an arbitrary system of strongly cartesian
lifts `x_f ⟶ x` of the objects `f` of `𝒮/U` with transition morphisms `x_{f₁} ⟶ x_{f₂}` over
the morphisms of `𝒮/U`, `CategoryTheory.Functor.CartesianLiftSystem`.  The point of the
statement is that `y` need not be pulled back at all: a section of `Mor(x, y)` over `f` is the
same thing as a morphism `x_f ⟶ y` lying over `f`, and restriction along `h : f₁ ⟶ f₂` is
precomposition with the transition morphism `x_{f₁} ⟶ x_{f₂}`.

## Main definitions

* `CategoryTheory.Functor.CartesianLiftSystem`: a system of strongly cartesian lifts of an object
  of the fibre over `U` along the objects of `𝒮/U`, with transition morphisms.
* `CategoryTheory.Functor.CartesianLiftSystem.homOver`: the morphisms `x_f ⟶ y` lying over `f`.
* `CategoryTheory.Functor.CartesianLiftSystem.morPresheafEquiv`: the sections of `Mor(x, y)` over
  `f` are the morphisms `x_f ⟶ y` lying over `f`.
* `CategoryTheory.Functor.CartesianLiftSystem.morPresheafIso`: **a presheaf `Q` on `𝒮/U` whose
  sections over `f` are identified with the morphisms `x_f ⟶ y` over `f`, compatibly with
  precomposition by the transition morphisms, is isomorphic to `Mor(x, y)`.**
* `CategoryTheory.Functor.isomPresheafIsoMorPresheafOfGroupoid`: when the fibres are groupoids,
  `Isom(x, y) = Mor(x, y)`.

## Main results

* `CategoryTheory.Functor.CartesianLiftSystem.morPresheafEquiv_morRestrict`: restriction of
  sections of `Mor(x, y)` is precomposition with the transition morphisms.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite

universe w v₁ v₂ u₁ u₂

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable (p : 𝒳 ⥤ 𝒮) {U : 𝒮}

/-- **A system of cartesian lifts** of an object `x` of the fibre over `U`: for every object `f` of
`𝒮/U` an object `x_f` of `𝒳` with a strongly cartesian morphism `x_f ⟶ x` over `f`, and for every
morphism `h : f₁ ⟶ f₂` of `𝒮/U` a transition morphism `x_{f₁} ⟶ x_{f₂}` over `h` compatible with
the lifts. -/
structure CartesianLiftSystem (x : p.Fiber U) where
  /-- The source `x_f` of the lift along `f`. -/
  obj : Over U → 𝒳
  /-- The lift `x_f ⟶ x` along `f`. -/
  hom : ∀ f : Over U, obj f ⟶ x.1
  /-- The lift is strongly cartesian over `f`. -/
  isStronglyCartesian : ∀ f : Over U, p.IsStronglyCartesian f.hom (hom f)
  /-- The transition morphism `x_{f₁} ⟶ x_{f₂}` along a morphism of `𝒮/U`. -/
  trans : ∀ {f₁ f₂ : Over U}, (f₁ ⟶ f₂) → (obj f₁ ⟶ obj f₂)
  /-- The transition morphism lies over the morphism of `𝒮/U`. -/
  trans_isHomLift : ∀ {f₁ f₂ : Over U} (h : f₁ ⟶ f₂), p.IsHomLift h.left (trans h)
  /-- The transition morphisms are compatible with the lifts. -/
  trans_hom : ∀ {f₁ f₂ : Over U} (h : f₁ ⟶ f₂), trans h ≫ hom f₂ = hom f₁

namespace CartesianLiftSystem

attribute [instance] isStronglyCartesian trans_isHomLift

variable {p} [p.IsFibered] {x : p.Fiber U} (L : CartesianLiftSystem p x)

/-- The morphisms `x_f ⟶ y` lying over `f`. -/
abbrev homOver (y : 𝒳) (f : Over U) : Type v₂ :=
  {φ : L.obj f ⟶ y // p.IsHomLift f.hom φ}

/-- The comparison `x_f ⟶ f^* x` of the given lift with the chosen one, over the identity. -/
noncomputable def toChosen (f : Over U) : L.obj f ⟶ (pullbackFiber p x f.hom).1 :=
  IsStronglyCartesian.map p f.hom (IsPreFibered.pullbackMap x.2 f.hom)
    (Category.id_comp f.hom).symm (L.hom f)

/-- The comparison of the given lift with the chosen one lies over the identity. -/
instance toChosen_isHomLift (f : Over U) : p.IsHomLift (𝟙 f.left) (L.toChosen f) := by
  unfold toChosen; infer_instance

/-- The factorisation characterising `CategoryTheory.Functor.CartesianLiftSystem.toChosen`:
following it with the chosen lift along `f` is the given lift along `f`. -/
@[reassoc (attr := simp)]
lemma toChosen_fac (f : Over U) :
    L.toChosen f ≫ IsPreFibered.pullbackMap x.2 f.hom = L.hom f :=
  IsStronglyCartesian.fac p f.hom _ _ _

/-- The comparison `f^* x ⟶ x_f` of the chosen lift with the given one, over the identity. -/
noncomputable def ofChosen (f : Over U) : (pullbackFiber p x f.hom).1 ⟶ L.obj f :=
  IsStronglyCartesian.map p f.hom (L.hom f) (Category.id_comp f.hom).symm
    (IsPreFibered.pullbackMap x.2 f.hom)

/-- The comparison of the chosen lift with the given one lies over the identity. -/
instance ofChosen_isHomLift (f : Over U) : p.IsHomLift (𝟙 f.left) (L.ofChosen f) := by
  unfold ofChosen; infer_instance

/-- The factorisation characterising `CategoryTheory.Functor.CartesianLiftSystem.ofChosen`:
following it with the given lift along `f` is the chosen lift along `f`. -/
@[reassoc (attr := simp)]
lemma ofChosen_fac (f : Over U) :
    L.ofChosen f ≫ L.hom f = IsPreFibered.pullbackMap x.2 f.hom :=
  IsStronglyCartesian.fac p f.hom _ _ _

/-- The two comparisons are mutually inverse: `x_f ⟶ f^* x ⟶ x_f` is the identity. -/
@[reassoc (attr := simp)]
lemma toChosen_ofChosen (f : Over U) : L.toChosen f ≫ L.ofChosen f = 𝟙 _ := by
  have : p.IsHomLift (𝟙 f.left) (𝟙 (L.obj f)) :=
    IsHomLift.id (IsHomLift.domain_eq p (𝟙 f.left) (L.toChosen f))
  exact IsStronglyCartesian.ext p f.hom (L.hom f) (𝟙 f.left) (by simp)

/-- The two comparisons are mutually inverse: `f^* x ⟶ x_f ⟶ f^* x` is the identity. -/
@[reassoc (attr := simp)]
lemma ofChosen_toChosen (f : Over U) : L.ofChosen f ≫ L.toChosen f = 𝟙 _ := by
  have : p.IsHomLift (𝟙 f.left) (𝟙 (pullbackFiber p x f.hom).1) :=
    IsHomLift.id (pullbackFiber p x f.hom).2
  exact IsStronglyCartesian.ext p f.hom (IsPreFibered.pullbackMap x.2 f.hom) (𝟙 f.left)
    (by simp)

/-- The comparisons with the chosen lifts intertwine the transition morphisms with the restriction
maps of the chosen pullbacks. -/
@[reassoc]
lemma toChosen_pullbackFiberMap {f₁ f₂ : Over U} (h : f₁ ⟶ f₂) :
    L.toChosen f₁ ≫ pullbackFiberMap p x h = L.trans h ≫ L.toChosen f₂ := by
  exact IsStronglyCartesian.ext p f₂.hom (IsPreFibered.pullbackMap x.2 f₂.hom) h.left
    (by simp [L.trans_hom])

variable (y : p.Fiber U)

/-- The morphism `x_f ⟶ y` over `f` of a section `m : f^* x ⟶ f^* y` of `Mor(x, y)`. -/
noncomputable def ofSection (f : Over U)
    (m : pullbackFiber p x f.hom ⟶ pullbackFiber p y f.hom) : L.homOver y.1 f :=
  ⟨L.toChosen f ≫ Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 f.hom, by
    simpa using (inferInstance : p.IsHomLift (𝟙 f.left ≫ 𝟙 f.left ≫ f.hom)
      (L.toChosen f ≫ Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 f.hom))⟩

/-- The section of `Mor(x, y)` over `f` of a morphism `x_f ⟶ y` over `f`. -/
noncomputable def toSection (f : Over U) (φ : L.homOver y.1 f) :
    pullbackFiber p x f.hom ⟶ pullbackFiber p y f.hom :=
  haveI := φ.2
  ⟨L.ofChosen f ≫ IsStronglyCartesian.map p f.hom (IsPreFibered.pullbackMap y.2 f.hom)
      (Category.id_comp f.hom).symm φ.1, by
    simpa using (inferInstance : p.IsHomLift (𝟙 f.left ≫ 𝟙 f.left)
      (L.ofChosen f ≫ IsStronglyCartesian.map p f.hom (IsPreFibered.pullbackMap y.2 f.hom)
        (Category.id_comp f.hom).symm φ.1))⟩

/-- **The sections of `Mor(x, y)` over `f` are the morphisms `x_f ⟶ y` over `f`.** -/
noncomputable def morPresheafEquiv (f : Over U) :
    (pullbackFiber p x f.hom ⟶ pullbackFiber p y f.hom) ≃ L.homOver y.1 f where
  toFun m := L.ofSection y f m
  invFun φ := L.toSection y f φ
  left_inv m := by
    apply Fiber.hom_ext
    change L.ofChosen f ≫ IsStronglyCartesian.map p f.hom (IsPreFibered.pullbackMap y.2 f.hom)
      (Category.id_comp f.hom).symm (L.toChosen f ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 f.hom) = Fiber.fiberInclusion.map m
    have : p.IsHomLift (𝟙 f.left) (L.toChosen f ≫ Fiber.fiberInclusion.map m) := by
      simpa using (inferInstance : p.IsHomLift (𝟙 f.left ≫ 𝟙 f.left)
        (L.toChosen f ≫ Fiber.fiberInclusion.map m))
    rw [← IsStronglyCartesian.map_uniq p f.hom (IsPreFibered.pullbackMap y.2 f.hom)
      (Category.id_comp f.hom).symm _ (L.toChosen f ≫ Fiber.fiberInclusion.map m)
      (Category.assoc _ _ _), L.ofChosen_toChosen_assoc]
  right_inv φ := by
    have := φ.2
    apply Subtype.ext
    change L.toChosen f ≫ (L.ofChosen f ≫ IsStronglyCartesian.map p f.hom
      (IsPreFibered.pullbackMap y.2 f.hom) (Category.id_comp f.hom).symm φ.1) ≫
        IsPreFibered.pullbackMap y.2 f.hom = φ.1
    simp

/-- **Restriction of sections of `Mor(x, y)` is precomposition with the transition morphisms**:
the morphism `x_{f₁} ⟶ y` of the restriction along `h : f₁ ⟶ f₂` of a section `m` is the
transition morphism `x_{f₁} ⟶ x_{f₂}` followed by the morphism `x_{f₂} ⟶ y` of `m`. -/
lemma morPresheafEquiv_morRestrict {f₁ f₂ : Over U} (h : f₁ ⟶ f₂)
    (m : pullbackFiber p x f₂.hom ⟶ pullbackFiber p y f₂.hom) :
    (L.morPresheafEquiv y f₁ (morRestrict p x y h m)).1 =
      L.trans h ≫ (L.morPresheafEquiv y f₂ m).1 := by
  show L.toChosen f₁ ≫ Fiber.fiberInclusion.map (morRestrict p x y h m) ≫
      IsPreFibered.pullbackMap y.2 f₁.hom =
    L.trans h ≫ L.toChosen f₂ ≫ Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 f₂.hom
  rw [morRestrict_fac, L.toChosen_pullbackFiberMap_assoc]

/-- **`Mor(x, y)` computed from a system of cartesian lifts.**  A presheaf `Q` on `𝒮/U` whose
sections over `f` are identified with the morphisms `x_f ⟶ y` lying over `f`, in such a way that
restriction along `h : f₁ ⟶ f₂` is precomposition with the transition morphism
`x_{f₁} ⟶ x_{f₂}`, is isomorphic to `Mor(x, y)`. -/
noncomputable def morPresheafIso (Q : (Over U)ᵒᵖ ⥤ Type v₂)
    (e : ∀ f : Over U, Q.obj (op f) ≃ L.homOver y.1 f)
    (he : ∀ {f₁ f₂ : Over U} (h : f₁ ⟶ f₂) (q : Q.obj (op f₂)),
      (e f₁ (Q.map h.op q)).1 = L.trans h ≫ (e f₂ q).1) :
    Q ≅ morPresheaf p x y :=
  NatIso.ofComponents
    (fun f => Equiv.toIso ((e f.unop).trans (L.morPresheafEquiv y f.unop).symm))
    (fun {f₂ f₁} h => by
      ext q
      change (L.morPresheafEquiv y f₁.unop).symm (e f₁.unop (Q.map h q)) =
        morRestrict p x y h.unop ((L.morPresheafEquiv y f₂.unop).symm (e f₂.unop q))
      apply (L.morPresheafEquiv y f₁.unop).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      rw [L.morPresheafEquiv_morRestrict, Equiv.apply_symm_apply]
      exact he h.unop q)

end CartesianLiftSystem

/-- **When the fibres are groupoids, `Isom(x, y)` is all of `Mor(x, y)`**: every section of
`Mor(x, y)` is an isomorphism. -/
noncomputable def isomPresheafIsoMorPresheafOfGroupoid [p.IsFibered]
    (hg : ∀ S : 𝒮, IsGroupoid (p.Fiber S)) (x y : p.Fiber U) :
    p.isomPresheaf x y ≅ morPresheaf p x y :=
  NatIso.ofComponents
    (fun f => Equiv.toIso
      { toFun := fun m => m.1
        invFun := fun m => ⟨m, (hg f.unop.left).all_isIso m⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end CategoryTheory.Functor

end
