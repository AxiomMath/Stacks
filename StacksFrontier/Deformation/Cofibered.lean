module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories cofibered in groupoids

A functor is cofibered in groupoids when its opposite is fibered in groupoids. All of
Chapter 90 is phrased for cofibered, rather than fibered, categories.

## Main definitions

* `IsCofiberedInGroupoids` is the predicate that a functor is cofibered in groupoids.
* `Deformation.isoOfIsHomLiftId` is the isomorphism determined by a vertical morphism.
* `Deformation.pushforwardObj` is a chosen pushforward of an object along a morphism of the
  base, and `Deformation.chosenPushforwardMap` the arrow to it.
* `Deformation.pushforwardDesc` is the arrow out of a chosen pushforward descended from an
  arrow lying over a composite.

## Main results

* `Deformation.exists_pushforward`: a morphism of the base pushes an object forward.
* `Deformation.isCofiberedInGroupoids_op_of_isFiberedInGroupoids`: the opposite of a functor
  fibered in groupoids is cofibered in groupoids.
* `Deformation.isStronglyCocartesian_of_isCofiberedInGroupoids`: every morphism is strongly
  cocartesian over its image.
* `Deformation.isIso_of_isHomLift_id`: a morphism lying over an identity is an isomorphism.
* `Deformation.chosenPushforwardMap_lift` and `Deformation.pushforwardObj_eq`: the arrow to a
  chosen pushforward lies over the given morphism, so the pushforward lies over its target.
* `Deformation.pushforwardDesc_lift` and `Deformation.pushforwardDesc_fac`: the descended arrow
  lies over the second factor and factors the arrow it was descended from.

## Implementation notes

The definition is an abbreviation of `Functor.IsFiberedInGroupoids` applied to the opposite
functor, so the API for categories fibered in groupoids applies after passing to opposites.

## References

* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
-/

@[expose] public section

namespace Deformation

/-! ### Categories cofibered in groupoids -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

/-- A functor `p : F ⥤ C` is *cofibered in groupoids* when the opposite
functor `p.op : Fᵒᵖ ⥤ Cᵒᵖ` is fibered in groupoids. -/
@[stacks 06GJ]
public abbrev IsCofiberedInGroupoids {F : Type u₁} [Category.{v₁} F]
    {C : Type u₂} [Category.{v₂} C] (p : F ⥤ C) : Prop := p.op.IsFiberedInGroupoids

end

/-! ### Shared consequences of the cofibered condition -/

section
open CategoryTheory
universe u v u₁ v₁
/-- In a category cofibered in groupoids, a morphism out of an object can be
pushed forward along any morphism of the base. -/
public lemma exists_pushforward {F : Type u₁} [Category.{v₁} F]
    {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C} (g : A ⟶ B)
    (x : F) (hx : p.obj x = A) :
    ∃ (y : F) (φ : x ⟶ y), p.IsHomLift g φ := by
  obtain ⟨y, φ, hφ⟩ := hp.exists_lift g.op (Opposite.op x) (by cases hx; rfl)
  refine ⟨y.unop, φ.unop, ?_⟩
  cases hφ
  exact IsHomLift.map p φ.unop

/-- The opposite of a functor fibered in groupoids is cofibered in groupoids: passing to
opposites twice gives back a functor fibered in groupoids. -/
public lemma isCofiberedInGroupoids_op_of_isFiberedInGroupoids {F : Type u₁} [Category.{v₁} F]
    {C : Type u} [Category.{v} C] {p : F ⥤ C} (hp : p.IsFiberedInGroupoids) :
    IsCofiberedInGroupoids p.op := by
  refine ⟨fun {V U} f x hx ↦ ?_, fun {x y z} φ ψ f hf ↦ ?_⟩
  · subst hx
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f.unop.unop x.unop.unop rfl
    refine ⟨Opposite.op (Opposite.op y), φ.op.op, ?_⟩
    have hdom : p.op.op.obj (Opposite.op (Opposite.op y)) = V :=
      congrArg (fun c ↦ Opposite.op (Opposite.op c)) (IsHomLift.domain_eq p f.unop.unop φ)
    refine IsHomLift.of_fac p.op.op f φ.op.op hdom rfl ?_
    have hfac := congrArg (fun g ↦ g.op.op) (IsHomLift.fac p f.unop.unop φ)
    simpa [eqToHom_op] using hfac
  · obtain ⟨χ, ⟨hχ, hχφ⟩, huniq⟩ := hp.unique_lift φ.unop.unop ψ.unop.unop f.unop.unop
      (congrArg (fun g ↦ g.unop.unop) hf)
    refine ⟨χ.op.op, ⟨congrArg (fun g ↦ g.op.op) hχ, congrArg (fun g ↦ g.op.op) hχφ⟩, ?_⟩
    intro ω ⟨hω, hωφ⟩
    exact congrArg (fun g ↦ g.op.op)
      (huniq ω.unop.unop ⟨congrArg (fun g ↦ g.unop.unop) hω,
        congrArg (fun g ↦ g.unop.unop) hωφ⟩)

/-- In a category cofibered in groupoids, every morphism is strongly cocartesian
over its image. -/
public lemma isStronglyCocartesian_of_isCofiberedInGroupoids
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    {R S : C} {a b : F} (hp : IsCofiberedInGroupoids p)
    (g : R ⟶ S) (f : a ⟶ b) (hf : p.IsHomLift g f) :
    p.IsStronglyCocartesian g f := by
  cases hf
  refine ⟨fun {b'} g φ hφ ↦ ?_⟩
  have hcomm : g.op ≫ p.op.map f.op = p.op.map φ.op := by
    change (p.map f ≫ g).op = (p.map φ).op
    exact congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p _ φ)
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := hp.unique_lift f.op φ.op g.op hcomm
  refine ⟨χ.unop, ⟨?_, ?_⟩, ?_⟩
  · have heq : p.map χ.unop = g := congrArg Quiver.Hom.unop hχ
    rw [← heq]
    infer_instance
  · exact congrArg Quiver.Hom.unop hfac
  · intro ψ ⟨hψ, hψfac⟩
    have heq : p.op.map ψ.op = g.op :=
      congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p g ψ).symm
    exact congrArg Quiver.Hom.unop
      (huniq ψ.op ⟨heq, congrArg Quiver.Hom.op hψfac⟩)

/-- In a category cofibered in groupoids, a morphism lying over an identity of the base — a
vertical morphism — is an isomorphism. -/
public lemma isIso_of_isHomLift_id
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A : C} {a b : F} (f : a ⟶ b)
    (hf : p.IsHomLift (𝟙 A) f) : IsIso f := by
  let := hf
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp (𝟙 A) f hf
  exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p (𝟙 A) f

/-- The canonical isomorphism determined by a vertical morphism in a category cofibered in
groupoids. -/
public noncomputable def isoOfIsHomLiftId
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A : C} {a b : F} (f : a ⟶ b)
    (hf : p.IsHomLift (𝟙 A) f) : a ≅ b :=
  letI := isIso_of_isHomLift_id hp f hf
  asIso f

/-- The isomorphism determined by a vertical morphism has that morphism as its forward map. -/
@[simp]
public theorem isoOfIsHomLiftId_hom
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A : C} {a b : F} (f : a ⟶ b)
    (hf : p.IsHomLift (𝟙 A) f) : (isoOfIsHomLiftId hp f hf).hom = f := rfl

/-! ### A chosen pushforward -/

/-- A chosen pushforward of an object along a morphism of the base. -/
public noncomputable def pushforwardObj
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C}
    (g : A ⟶ B) (x : F) (hx : p.obj x = A) : F :=
  Classical.choose (exists_pushforward hp g x hx)

/-- The arrow to the chosen pushforward. -/
public noncomputable def chosenPushforwardMap
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C}
    (g : A ⟶ B) (x : F) (hx : p.obj x = A) : x ⟶ pushforwardObj hp g x hx :=
  Classical.choose (Classical.choose_spec (exists_pushforward hp g x hx))

/-- The arrow to the chosen pushforward lies over the morphism of the base it is taken along. -/
public lemma chosenPushforwardMap_lift
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C}
    (g : A ⟶ B) (x : F) (hx : p.obj x = A) :
    p.IsHomLift g (chosenPushforwardMap hp g x hx) :=
  Classical.choose_spec (Classical.choose_spec (exists_pushforward hp g x hx))

/-- The chosen pushforward along `g : A ⟶ B` of an object lying over `A` lies over `B`. -/
public lemma pushforwardObj_eq
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C}
    (g : A ⟶ B) (x : F) (hx : p.obj x = A) :
    p.obj (pushforwardObj hp g x hx) = B := by
  let := chosenPushforwardMap_lift hp g x hx
  exact IsHomLift.codomain_eq p g (chosenPushforwardMap hp g x hx)

/-- The arrow to the chosen pushforward is strongly cocartesian. -/
private lemma isStronglyCocartesian_chosenPushforwardMap
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B : C}
    (g : A ⟶ B) (x : F) (hx : p.obj x = A) :
    p.IsStronglyCocartesian g (chosenPushforwardMap hp g x hx) :=
  isStronglyCocartesian_of_isCofiberedInGroupoids hp g _ (chosenPushforwardMap_lift hp g x hx)

/-- The unique arrow out of a pushforward induced by an arrow over a composite. -/
public noncomputable def pushforwardDesc
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (x z : F) (hx : p.obj x = A)
    (ψ : x ⟶ z) (hψ : p.IsHomLift (f ≫ g) ψ) :
    pushforwardObj hp f x hx ⟶ z := by
  letI := chosenPushforwardMap_lift hp f x hx
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hp f
    (chosenPushforwardMap hp f x hx) (chosenPushforwardMap_lift hp f x hx)
  letI := hψ
  exact Functor.IsStronglyCocartesian.map p f (chosenPushforwardMap hp f x hx)
    (g := g) (f' := f ≫ g) rfl ψ

/-- The arrow descended through a pushforward lies over the second factor of the composite. -/
public lemma pushforwardDesc_lift
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (x z : F) (hx : p.obj x = A)
    (ψ : x ⟶ z) (hψ : p.IsHomLift (f ≫ g) ψ) :
    p.IsHomLift g (pushforwardDesc hp f g x z hx ψ hψ) := by
  let := isStronglyCocartesian_chosenPushforwardMap hp f x hx
  let := hψ
  unfold pushforwardDesc
  change p.IsHomLift g
    (Functor.IsStronglyCocartesian.map p f (chosenPushforwardMap hp f x hx)
      (g := g) (f' := f ≫ g) rfl ψ)
  infer_instance

/-- The arrow descended through a pushforward factors the arrow it was descended from. -/
public lemma pushforwardDesc_fac
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}
    (hp : IsCofiberedInGroupoids p) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (x z : F) (hx : p.obj x = A)
    (ψ : x ⟶ z) (hψ : p.IsHomLift (f ≫ g) ψ) :
    chosenPushforwardMap hp f x hx ≫ pushforwardDesc hp f g x z hx ψ hψ = ψ := by
  let := isStronglyCocartesian_chosenPushforwardMap hp f x hx
  let := hψ
  exact Functor.IsStronglyCocartesian.fac p f
    (chosenPushforwardMap hp f x hx) (g := g) (f' := f ≫ g) rfl ψ

end

end Deformation
