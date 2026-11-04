module

public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp

/-!
# The presheaf `Mor(x, y)` computed with any family of cartesian lifts

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and `x`, `y` objects of the fibre over `U`.  The presheaf
`Mor(x, y)` of Stacks 02ZB on `𝒮/U` is defined with the chosen pullbacks `g^* x`, `g^* y`: its
sections over `g : V ⟶ U` are the morphisms `g^* x ⟶ g^* y` of the fibre over `V`.  By the
universal property of the chosen cartesian lift `g^* y ⟶ y` these are the morphisms `g^* x ⟶ y`
of `𝒳` lying over `g`, and `g^* x` may be replaced by the domain of *any* strongly cartesian
morphism over `g` with target `x`.

This file proves that, for an arbitrary family of strongly cartesian lifts `w_g ⟶ x` with
compatible transition morphisms: `Mor(x, y)` is isomorphic to the presheaf
`g ↦ {φ : w_g ⟶ y lying over g}` whose restriction maps are precomposition with the transition
morphisms.  In concrete fibred categories the lifts `w_g` can be taken to be explicit pullbacks,
and the right-hand side is then computed without reference to the chosen cleavage.

## Main definitions

* `CategoryTheory.Functor.CartesianLiftFamily`: a family of strongly cartesian lifts of `x` along
  all the objects of `𝒮/U`, with transition morphisms over the morphisms of `𝒮/U`.
* `CategoryTheory.Functor.CartesianLiftFamily.homOverPresheaf`: the presheaf
  `g ↦ {φ : w_g ⟶ y lying over g}`.

## Main results

* `CategoryTheory.Functor.CartesianLiftFamily.morPresheafIso`: `Mor(x, y)` is isomorphic to
  `homOverPresheaf`.

## References

* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Opposite

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}

/-- **A family of cartesian lifts of `x`.**  For every object `g : V ⟶ U` of `𝒮/U` an object
`w_g` of the fibre over `V` with a strongly cartesian morphism `w_g ⟶ x` over `g`, and for every
morphism `h : g₁ ⟶ g₂` of `𝒮/U` a morphism `w_{g₁} ⟶ w_{g₂}` over `h` compatible with the lifts.
-/
structure CartesianLiftFamily (p : 𝒳 ⥤ 𝒮) {U : 𝒮} (x : p.Fiber U) where
  /-- The domain of the lift over `g`. -/
  obj : ∀ g : Over U, p.Fiber g.left
  /-- The lift over `g`. -/
  hom : ∀ g : Over U, (obj g).1 ⟶ x.1
  /-- The lift over `g` is strongly cartesian. -/
  isStronglyCartesian : ∀ g : Over U, p.IsStronglyCartesian g.hom (hom g)
  /-- The transition morphism over a morphism of `𝒮/U`. -/
  trans : ∀ {g₁ g₂ : Over U} (_ : g₁ ⟶ g₂), (obj g₁).1 ⟶ (obj g₂).1
  /-- The transition morphism lies over the morphism of `𝒮`. -/
  isHomLift_trans : ∀ {g₁ g₂ : Over U} (h : g₁ ⟶ g₂), p.IsHomLift h.left (trans h)
  /-- The transition morphisms are compatible with the lifts. -/
  trans_hom : ∀ {g₁ g₂ : Over U} (h : g₁ ⟶ g₂), trans h ≫ hom g₂ = hom g₁

namespace CartesianLiftFamily

/-- A family of cartesian lifts from the lifts alone: the transition morphisms are the ones the
universal property of the strongly cartesian lifts provides. -/
def ofStronglyCartesian {U : 𝒮} {x : p.Fiber U} (obj : ∀ g : Over U, p.Fiber g.left)
    (hom : ∀ g : Over U, (obj g).1 ⟶ x.1)
    (isStronglyCartesian : ∀ g : Over U, p.IsStronglyCartesian g.hom (hom g)) :
    CartesianLiftFamily p x where
  obj := obj
  hom := hom
  isStronglyCartesian := isStronglyCartesian
  trans {g₁ g₂} h :=
    haveI := isStronglyCartesian g₂
    haveI := isStronglyCartesian g₁
    IsStronglyCartesian.map p g₂.hom (hom g₂) (Over.w h).symm (hom g₁)
  isHomLift_trans {g₁ g₂} h := by
    have := isStronglyCartesian g₂
    have := isStronglyCartesian g₁
    exact IsStronglyCartesian.map_isHomLift p g₂.hom (hom g₂) (Over.w h).symm (hom g₁)
  trans_hom {g₁ g₂} h := by
    have := isStronglyCartesian g₂
    have := isStronglyCartesian g₁
    exact IsStronglyCartesian.fac p g₂.hom (hom g₂) (Over.w h).symm (hom g₁)

/-- In a family of cartesian lifts, the transition morphism over `h` is the only morphism over
`h.left` compatible with the lifts. -/
theorem trans_eq {U : 𝒮} {x : p.Fiber U} (L : CartesianLiftFamily p x) {g₁ g₂ : Over U}
    (h : g₁ ⟶ g₂) (τ : (L.obj g₁).1 ⟶ (L.obj g₂).1) [p.IsHomLift h.left τ]
    (hτ : τ ≫ L.hom g₂ = L.hom g₁) : L.trans h = τ := by
  have := L.isStronglyCartesian g₂
  have := L.isHomLift_trans h
  exact IsStronglyCartesian.ext p g₂.hom (L.hom g₂) h.left (by rw [L.trans_hom, hτ])


variable {U : 𝒮} {x : p.Fiber U} (L : CartesianLiftFamily p x)

attribute [instance] isStronglyCartesian isHomLift_trans

/-- The transition morphism along an identity is the identity. -/
theorem trans_id (g : Over U) : L.trans (𝟙 g) = 𝟙 (L.obj g).1 := by
  have : p.IsHomLift (𝟙 g.left) (𝟙 (L.obj g).1) := IsHomLift.id (L.obj g).2
  have : p.IsHomLift (𝟙 g.left) (L.trans (𝟙 g)) := by
    simpa using L.isHomLift_trans (𝟙 g)
  exact IsStronglyCartesian.ext p g.hom (L.hom g) (𝟙 g.left)
    (by rw [L.trans_hom, Category.id_comp])

/-- The transition morphisms compose. -/
theorem trans_comp {g₁ g₂ g₃ : Over U} (h₁ : g₁ ⟶ g₂) (h₂ : g₂ ⟶ g₃) :
    L.trans (h₁ ≫ h₂) = L.trans h₁ ≫ L.trans h₂ := by
  have : p.IsHomLift (h₁.left ≫ h₂.left) (L.trans (h₁ ≫ h₂)) := by
    simpa using L.isHomLift_trans (h₁ ≫ h₂)
  exact IsStronglyCartesian.ext p g₃.hom (L.hom g₃) (h₁.left ≫ h₂.left)
    (by rw [L.trans_hom, Category.assoc, L.trans_hom, L.trans_hom])

/-- **The presheaf of morphisms out of the lifts lying over the base.**  Its sections over
`g : V ⟶ U` are the morphisms `w_g ⟶ y` of `𝒳` lying over `g`, and its restriction along
`h : g₁ ⟶ g₂` is precomposition with the transition morphism `w_{g₁} ⟶ w_{g₂}`. -/
def homOverPresheaf (y : 𝒳) : (Over U)ᵒᵖ ⥤ Type v₂ where
  obj g := {φ : (L.obj g.unop).1 ⟶ y // p.IsHomLift g.unop.hom φ}
  map {g₁ g₂} h := ↾fun φ => ⟨L.trans h.unop ≫ φ.1, by
    have := φ.2
    have : p.IsHomLift (h.unop.left ≫ g₁.unop.hom) (L.trans h.unop ≫ φ.1) := inferInstance
    simpa [Over.w h.unop] using this⟩
  map_id g := by
    ext φ : 3
    refine Subtype.ext ?_
    change L.trans (𝟙 g.unop) ≫ φ.1 = φ.1
    rw [L.trans_id, Category.id_comp]
  map_comp {g₁ g₂ g₃} h₁ h₂ := by
    ext φ : 3
    refine Subtype.ext ?_
    change L.trans (h₂.unop ≫ h₁.unop) ≫ φ.1 = L.trans h₂.unop ≫ L.trans h₁.unop ≫ φ.1
    rw [L.trans_comp, Category.assoc]

/-- The restriction maps of `CategoryTheory.Functor.CartesianLiftFamily.homOverPresheaf`. -/
theorem homOverPresheaf_map_coe (y : 𝒳) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (φ : (L.homOverPresheaf y).obj (op g₂)) :
    ((L.homOverPresheaf y).map h.op φ).1 = L.trans h ≫ φ.1 :=
  rfl

variable [p.IsFibered]

/-- The comparison of the lift over `g` with the chosen pullback of `x` along `g`. -/
def pullbackFiberIso (g : Over U) : L.obj g ≅ pullbackFiber p x g.hom :=
  fiberIsoPullbackFiber p x g.hom (L.obj g) (L.hom g) (L.isStronglyCartesian g)

/-- The comparison with the chosen pullback, followed by the chosen pullback map, is the lift over
`g`. -/
@[reassoc]
theorem pullbackFiberIso_hom_comp (g : Over U) :
    (L.pullbackFiberIso g).hom.1 ≫ IsPreFibered.pullbackMap x.2 g.hom = L.hom g := by
  have hbase : g.hom = (Iso.refl g.left).hom ≫ g.hom := by simp
  exact IsStronglyCartesian.fac p g.hom (IsPreFibered.pullbackMap x.2 g.hom) hbase (L.hom g)

/-- The comparisons with the chosen pullbacks intertwine the transition morphisms with the
restriction maps of the chosen pullbacks. -/
theorem pullbackFiberIso_hom_comp_pullbackFiberMap {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (L.pullbackFiberIso g₁).hom.1 ≫ pullbackFiberMap p x h =
      L.trans h ≫ (L.pullbackFiberIso g₂).hom.1 := by
  have h₁ := (L.pullbackFiberIso g₁).hom.2
  have h₂ := (L.pullbackFiberIso g₂).hom.2
  have : p.IsHomLift h.left ((L.pullbackFiberIso g₁).hom.1 ≫ pullbackFiberMap p x h) := by
    have : p.IsHomLift (𝟙 g₁.left ≫ h.left)
        ((L.pullbackFiberIso g₁).hom.1 ≫ pullbackFiberMap p x h) := inferInstance
    simpa using this
  have : p.IsHomLift h.left (L.trans h ≫ (L.pullbackFiberIso g₂).hom.1) := by
    have : p.IsHomLift (h.left ≫ 𝟙 g₂.left) (L.trans h ≫ (L.pullbackFiberIso g₂).hom.1) :=
      inferInstance
    simpa using this
  refine IsStronglyCartesian.ext p g₂.hom (IsPreFibered.pullbackMap x.2 g₂.hom) h.left ?_
  rw [Category.assoc, pullbackFiberMap_fac, pullbackFiberIso_hom_comp, Category.assoc,
    pullbackFiberIso_hom_comp, L.trans_hom]

/-- The bijection, over one object `g` of `𝒮/U`, between the sections of `Mor(x, y)` and the
morphisms `w_g ⟶ y` lying over `g`. -/
def morEquiv (y : p.Fiber U) (g : Over U) :
    (pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom) ≃
      {φ : (L.obj g).1 ⟶ y.1 // p.IsHomLift g.hom φ} where
  toFun m := ⟨((L.pullbackFiberIso g).hom ≫ m).1 ≫ IsPreFibered.pullbackMap y.2 g.hom, by
    have := ((L.pullbackFiberIso g).hom ≫ m).2
    have : p.IsHomLift (𝟙 g.left ≫ g.hom)
        (((L.pullbackFiberIso g).hom ≫ m).1 ≫ IsPreFibered.pullbackMap y.2 g.hom) :=
      inferInstance
    simpa using this⟩
  invFun φ :=
    haveI := φ.2
    (L.pullbackFiberIso g).inv ≫
      (⟨IsCartesian.map p g.hom (IsPreFibered.pullbackMap y.2 g.hom) φ.1,
        IsCartesian.map_isHomLift p g.hom _ φ.1⟩ : L.obj g ⟶ pullbackFiber p y g.hom)
  left_inv m := by
    have := ((L.pullbackFiberIso g).hom ≫ m).2
    have e : (⟨IsCartesian.map p g.hom (IsPreFibered.pullbackMap y.2 g.hom)
        (((L.pullbackFiberIso g).hom ≫ m).1 ≫ IsPreFibered.pullbackMap y.2 g.hom),
        IsCartesian.map_isHomLift p g.hom _ _⟩ : L.obj g ⟶ pullbackFiber p y g.hom) =
        (L.pullbackFiberIso g).hom ≫ m :=
      Fiber.hom_ext (IsCartesian.map_uniq p g.hom _ _ _ rfl).symm
    simp only [e, Iso.inv_hom_id_assoc]
  right_inv φ := by
    have := φ.2
    refine Subtype.ext ?_
    simp only [Iso.hom_inv_id_assoc]
    exact IsCartesian.fac p g.hom _ _

/-- **`Mor(x, y)` computed with a family of cartesian lifts.**  The presheaf `Mor(x, y)` of
Stacks 02ZB is isomorphic to the presheaf of morphisms `w_g ⟶ y` lying over `g`, with
precomposition by the transition morphisms as restriction maps. -/
def morPresheafIso (y : p.Fiber U) : morPresheaf p x y ≅ L.homOverPresheaf y.1 :=
  NatIso.ofComponents (fun g => (L.morEquiv y g.unop).toIso) <| by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m : 3
    refine Subtype.ext ?_
    change ((L.pullbackFiberIso g₁).hom ≫ morRestrict p x y h m).1 ≫
        IsPreFibered.pullbackMap y.2 g₁.hom =
      L.trans h ≫ ((L.pullbackFiberIso g₂).hom ≫ m).1 ≫ IsPreFibered.pullbackMap y.2 g₂.hom
    have hf := morRestrict_fac p x y h m
    change (morRestrict p x y h m).1 ≫ IsPreFibered.pullbackMap y.2 g₁.hom =
      pullbackFiberMap p x h ≫ m.1 ≫ IsPreFibered.pullbackMap y.2 g₂.hom at hf
    change ((L.pullbackFiberIso g₁).hom.1 ≫ (morRestrict p x y h m).1) ≫
        IsPreFibered.pullbackMap y.2 g₁.hom =
      L.trans h ≫ ((L.pullbackFiberIso g₂).hom.1 ≫ m.1) ≫ IsPreFibered.pullbackMap y.2 g₂.hom
    rw [Category.assoc, hf, ← Category.assoc, L.pullbackFiberIso_hom_comp_pullbackFiberMap h]
    simp only [Category.assoc]

end CartesianLiftFamily

end CategoryTheory.Functor

end
