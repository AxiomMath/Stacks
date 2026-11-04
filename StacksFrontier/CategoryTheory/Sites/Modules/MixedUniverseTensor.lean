module

public import Mathlib.Algebra.Module.ULift
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor

/-!
# The objectwise tensor product of presheaves of modules in independent universes

Let `R : Cᵒᵖ ⥤ CommRingCat.{u}` be a presheaf of commutative rings on a category `C`.  The
tensor product of two modules over a commutative ring makes sense when the two factors lie in
independent universes, the result lying in their maximum, and the same is therefore true of the
objectwise tensor product of two presheaves of `R`-modules. The canonical construction is
`PresheafOfModules.tensorObj`, with its native curried `PresheafOfModules.tensorBifunctor`.
This file supplies ordinary-module tensor helpers, generic universe lifts of presheaves of
modules, and computations for the canonical tensor product.

## Main definitions

* `ModuleCat.MixedTensor.tensorObj` is the tensor product of two modules over a commutative
  ring whose carriers lie in independent universes.
* `ModuleCat.MixedTensor.tensorLift` constructs a morphism out of it from a bilinear family of
  values, `ModuleCat.MixedTensor.tensorHom` is the action on a pair of morphisms, and
  `ModuleCat.MixedTensor.tensorMapₛₗ` the action on a pair of semilinear maps along one ring
  homomorphism.
* `ModuleCat.MixedTensor.uliftTensorLift` and
  `ModuleCat.MixedTensor.uliftTensorBilinear` pass between bilinear families of values and
  morphisms out of the universe lift of a tensor product of modules.
* `PresheafOfModules.uliftSections` raises the universe of the sections of a presheaf of modules,
  and `PresheafOfModules.ulift` is the functor doing so.
* Applying `PresheafOfModules.uliftSections` directly to `PresheafOfModules.tensorObj`
  includes the coefficient universe in the universe of the sections. Whiskering the canonical
  bifunctor with `PresheafOfModules.ulift` gives the corresponding functorial construction.

## Main results

* `ModuleCat.MixedTensor.tensor_ext` and `ModuleCat.MixedTensor.uliftTensor_ext`: a morphism
  out of a tensor product of modules, or out of its universe lift, is determined by its values
  on pure tensors.
* `PresheafOfModules.MixedTensor.tensorObj_eq` and
  `PresheafOfModules.MixedTensor.tensorHom_eq`: when the factors have sections in the universe
  of the coefficient rings, the construction here is the tensor product of the monoidal
  structure on presheaves of modules, on the nose.

## Implementation notes

The monoidal structure on `ModuleCat R` for `R : Type u` is available in the library only on
`ModuleCat.{u} R`, that is, with the universe of the modules equal to the universe of the ring,
and consequently the monoidal structure on presheaves of modules is available only on
`PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)`.  The restriction comes from the
monoidal unit: the unit object is `R` itself, so it lives in `ModuleCat.{u} R` and nowhere else.
Tensor products of objects and of morphisms, by contrast, need no such hypothesis, and neither
does the associator.  So the constructions below carry no universe hypothesis at all, while a
monoidal structure with sections outside the universe of the coefficient rings is not to be
expected: there is no unit object.

A second constraint is worth stating, since it is easy to mistake for an accident of the
construction.  `ModuleCat.{v} S` is a category at one universe `v`, so a morphism whose source
is a module with carrier in `Type (max m n)` has its target there too.  Hence a morphism out of
a tensor product cannot land in an arbitrary third universe, and a universal property of the
tensor product is a statement about targets at `max m n` exactly.  To reach a larger universe
one applies `uliftSections` to the tensor product itself. The resulting sections in
`Type (max u m n)` are used by the mixed-universe quasi-coherent tensor constructions.

Naming the definitional equation between the construction here and the library's monoidal
tensor product as `tensorObj_eq` and `tensorHom_eq` is what lets results proved for one
spelling be applied to the other without a transparency override.

`PresheafOfModules.uliftSections` is the same construction as `PresheafOfModules.uliftObj` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/AssociatedSheafIsos.lean`, which raises the
sections of a presheaf of modules in the same way but takes the amount lifted as its last
universe argument rather than its first, and carries a different downstream API
(`uliftMap` and `uliftFunctor` there, `ulift` here).  The two differ only in their
implementation; they are kept apart under distinct names rather than merged, since merging them
means rewriting the universe applications of both APIs.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

universe m n t v v₁ u₁ u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat.MixedTensor

variable {R : Type u} [CommRing R]

/-- The tensor product of two modules over a commutative ring, as an object of `ModuleCat`.
The two factors may have carriers in independent universes, and the result lies in their
maximum. -/
public noncomputable abbrev tensorObj (M₁ : ModuleCat.{m} R) (M₂ : ModuleCat.{n} R) :
    ModuleCat.{max m n} R :=
  ModuleCat.of R (M₁ ⊗[R] M₂)

section

variable {M₁ : ModuleCat.{m} R} {M₂ : ModuleCat.{n} R} {M₃ : ModuleCat.{max m n} R}
  (f : M₁ → M₂ → M₃) (h₁ : ∀ x x' y, f (x + x') y = f x y + f x' y)
  (h₂ : ∀ (a : R) x y, f (a • x) y = a • f x y)
  (h₃ : ∀ x y y', f x (y + y') = f x y + f x y')
  (h₄ : ∀ (a : R) x y, f x (a • y) = a • f x y)

/-- A morphism out of the tensor product of two modules in independent universes, constructed
from a bilinear family of values on pure tensors. -/
public noncomputable def tensorLift : tensorObj M₁ M₂ ⟶ M₃ :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄))

@[simp] public theorem tensorLift_tmul (x : M₁) (y : M₂) :
    (tensorLift f h₁ h₂ h₃ h₄).hom (x ⊗ₜ y) = f x y := rfl

end

/-- A morphism out of the tensor product of two modules is determined by its values on pure
tensors. -/
public theorem tensor_ext {M₁ : ModuleCat.{m} R} {M₂ : ModuleCat.{n} R}
    {M₃ : ModuleCat.{max m n} R} {f g : tensorObj M₁ M₂ ⟶ M₃}
    (h : ∀ (x : M₁) (y : M₂), f.hom (x ⊗ₜ y) = g.hom (x ⊗ₜ y)) : f = g :=
  ModuleCat.hom_ext (TensorProduct.ext (by ext x y; exact h x y))

/-- Pure tensors with equal factors are equal. -/
public theorem tmul_congr {M₁ : ModuleCat.{m} R} {M₂ : ModuleCat.{n} R} {x x' : M₁} {y y' : M₂}
    (hx : x = x') (hy : y = y') :
    (x ⊗ₜ y : tensorObj M₁ M₂) = (x' ⊗ₜ y' : tensorObj M₁ M₂) := by
  rw [hx, hy]

/-- The tensor product of two morphisms of modules in independent universes. -/
public noncomputable def tensorHom {M₁ M₂ : ModuleCat.{m} R} {M₃ M₄ : ModuleCat.{n} R}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ :=
  ModuleCat.ofHom (TensorProduct.map f.hom g.hom)

@[simp] public theorem tensorHom_tmul {M₁ M₂ : ModuleCat.{m} R} {M₃ M₄ : ModuleCat.{n} R}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (x : M₁) (y : M₃) :
    (tensorHom f g).hom (x ⊗ₜ y) = f.hom x ⊗ₜ g.hom y := rfl

section ULift

variable {M₁ : ModuleCat.{m} R} {M₂ : ModuleCat.{n} R} {M₃ : ModuleCat.{max t m n} R}

section

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ x x' y, f (x + x') y = f x y + f x' y)
  (h₂ : ∀ (a : R) x y, f (a • x) y = a • f x y)
  (h₃ : ∀ x y y', f x (y + y') = f x y + f x y')
  (h₄ : ∀ (a : R) x y, f x (a • y) = a • f x y)

/-- A morphism out of the universe lift of the tensor product of two modules, constructed from
a bilinear family of values on pure tensors. -/
public noncomputable def uliftTensorLift :
    ModuleCat.of R (ULift.{t} (M₁ ⊗[R] M₂)) ⟶ M₃ :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄) ∘ₗ
    (ULift.moduleEquiv : ULift.{t} (M₁ ⊗[R] M₂) ≃ₗ[R] _).toLinearMap)

@[simp] public theorem uliftTensorLift_up (x : M₁) (y : M₂) :
    (uliftTensorLift f h₁ h₂ h₃ h₄ : ModuleCat.of R (ULift.{t} (M₁ ⊗[R] M₂)) ⟶ M₃).hom
      (ULift.up (x ⊗ₜ y)) = f x y := rfl

end

/-- The bilinear family of values on pure tensors of a morphism out of the universe lift of a
tensor product of two modules. -/
public noncomputable def uliftTensorBilinear
    (f : ModuleCat.of R (ULift.{t} (M₁ ⊗[R] M₂)) ⟶ M₃) : M₁ →ₗ[R] M₂ →ₗ[R] M₃ :=
  LinearMap.compr₂ (TensorProduct.mk R M₁ M₂)
    (f.hom ∘ₗ (ULift.moduleEquiv : ULift.{t} (M₁ ⊗[R] M₂) ≃ₗ[R] _).symm.toLinearMap)

@[simp] public theorem uliftTensorBilinear_apply
    (f : ModuleCat.of R (ULift.{t} (M₁ ⊗[R] M₂)) ⟶ M₃) (x : M₁) (y : M₂) :
    uliftTensorBilinear f x y = f.hom (ULift.up (x ⊗ₜ y)) := rfl

/-- A morphism out of the universe lift of a tensor product of two modules is determined by its
values on the lifts of pure tensors. -/
public theorem uliftTensor_ext {f g : ModuleCat.of R (ULift.{t} (M₁ ⊗[R] M₂)) ⟶ M₃}
    (h : ∀ (x : M₁) (y : M₂),
      f.hom (ULift.up (x ⊗ₜ y)) = g.hom (ULift.up (x ⊗ₜ y))) : f = g := by
  have key : f.hom ∘ₗ (ULift.moduleEquiv : ULift.{t} (M₁ ⊗[R] M₂) ≃ₗ[R] _).symm.toLinearMap =
      g.hom ∘ₗ (ULift.moduleEquiv : ULift.{t} (M₁ ⊗[R] M₂) ≃ₗ[R] _).symm.toLinearMap :=
    TensorProduct.ext (by ext x y; exact h x y)
  exact ModuleCat.hom_ext (LinearMap.ext fun z ↦ LinearMap.congr_fun key z.down)

end ULift

section Semilinear

variable {S : Type u} [CommRing S] (φ : R →+* S)

/-- The tensor product of two semilinear maps along one homomorphism of commutative rings: a
semilinear map between the tensor products of the sources and of the targets. -/
public noncomputable def tensorMapₛₗ {M₁ : ModuleCat.{m} R} {N₁ : ModuleCat.{m} S}
    {M₂ : ModuleCat.{n} R} {N₂ : ModuleCat.{n} S} (f₁ : M₁ →ₛₗ[φ] N₁) (f₂ : M₂ →ₛₗ[φ] N₂) :
    tensorObj M₁ M₂ →ₛₗ[φ] tensorObj N₁ N₂ :=
  TensorProduct.lift (LinearMap.mk₂'ₛₗ φ φ (fun x y ↦ f₁ x ⊗ₜ f₂ y)
    (fun x x' y ↦ by rw [map_add, TensorProduct.add_tmul])
    (fun c x y ↦ by rw [map_smulₛₗ, TensorProduct.smul_tmul'])
    (fun x y y' ↦ by rw [map_add, TensorProduct.tmul_add])
    (fun c x y ↦ by rw [map_smulₛₗ, TensorProduct.tmul_smul]))

@[simp] public theorem tensorMapₛₗ_tmul {M₁ : ModuleCat.{m} R} {N₁ : ModuleCat.{m} S}
    {M₂ : ModuleCat.{n} R} {N₂ : ModuleCat.{n} S} (f₁ : M₁ →ₛₗ[φ] N₁) (f₂ : M₂ →ₛₗ[φ] N₂)
    (x : M₁) (y : M₂) : tensorMapₛₗ φ f₁ f₂ (x ⊗ₜ y) = f₁ x ⊗ₜ f₂ y := rfl

end Semilinear

end ModuleCat.MixedTensor

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C]

/-- The restriction of a section along an identity morphism is the section itself. -/
public theorem restrictₛₗ_id {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R₀) (X : Cᵒᵖ)
    (x : M.obj X) : M.restrictₛₗ (𝟙 X) x = x := by
  rw [restrictₛₗ_apply, M.map_id]
  rfl

/-- Restriction of sections along a composite is the composite of the restrictions. -/
public theorem restrictₛₗ_comp {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R₀)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : M.obj X) :
    M.restrictₛₗ (f ≫ g) x = M.restrictₛₗ g (M.restrictₛₗ f x) :=
  M.map_comp_apply f g x

section ULift

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}}

/-- A presheaf of modules with the universe of its sections raised: the sections over an object
are the universe lift of the original ones. -/
public noncomputable def uliftSections (M : PresheafOfModules.{v} R₀) :
    PresheafOfModules.{max t v} R₀ where
  obj X := ModuleCat.of (R₀.obj X) (ULift.{t} (M.obj X))
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R₀.map f).hom).obj
      (ModuleCat.of (R₀.obj Y) (ULift.{t} (M.obj Y))))
    { toFun := fun x ↦ ULift.up (M.restrictₛₗ f x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (M.restrictₛₗ f) x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (map_smulₛₗ (M.restrictₛₗ f) a x.down) }
  map_id X := by ext x; exact congrArg ULift.up (M.restrictₛₗ_id X x.down)
  map_comp f g := by ext x; exact congrArg ULift.up (M.restrictₛₗ_comp f g x.down)

@[simp] public theorem uliftSections_map_up (M : PresheafOfModules.{v} R₀) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : M.obj X) :
    ((M.uliftSections.{t}).map f).hom (ULift.up x) = ULift.up (M.restrictₛₗ f x) := rfl

/-- A morphism out of a presheaf of modules with raised sections is determined by its values on
the lifts of the original sections. -/
public theorem uliftSections_hom_ext {M : PresheafOfModules.{v} R₀}
    {N : PresheafOfModules.{max t v} R₀} {f g : M.uliftSections.{t} ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X), (f.app X).hom (ULift.up x) = (g.app X).hom (ULift.up x)) :
    f = g :=
  hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ h X x.down)

/-- Raising the universe of the sections of a presheaf of modules is functorial. -/
public noncomputable def ulift :
    PresheafOfModules.{v} R₀ ⥤ PresheafOfModules.{max t v} R₀ where
  obj M := M.uliftSections
  map {_ _} φ :=
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ULift.up ((φ.app X).hom x.down)
          map_add' := fun x y ↦ congrArg ULift.up (map_add (φ.app X).hom x.down y.down)
          map_smul' := fun a x ↦ congrArg ULift.up (map_smul (φ.app X).hom a x.down) }
      naturality := fun {_ _} f ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
        congrArg ULift.up (naturality_apply φ f x.down)) }
  map_id _ := uliftSections_hom_ext fun _ _ ↦ rfl
  map_comp _ _ := uliftSections_hom_ext fun _ _ ↦ rfl

@[simp] public theorem ulift_map_app_up {M N : PresheafOfModules.{v} R₀} (φ : M ⟶ N) (X : Cᵒᵖ)
    (x : M.obj X) :
    ((ulift.{t}.map φ).app X).hom (ULift.up x) = ULift.up ((φ.app X).hom x) := rfl

@[simp] public theorem ulift_obj (M : PresheafOfModules.{v} R₀) :
    ulift.{t}.obj M = M.uliftSections.{t} := rfl

end ULift

namespace MixedTensor

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}}

section

variable (M₁ : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
  (M₂ : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat))

@[simp] public theorem tensorObj_obj (X : Cᵒᵖ) :
    (tensorObj M₁ M₂).obj X = ModuleCat.MixedTensor.tensorObj (M₁.obj X) (M₂.obj X) := rfl

@[simp] public theorem tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M₁.obj X) (y : M₂.obj X) :
    ((tensorObj M₁ M₂).map f).hom (x ⊗ₜ y) = M₁.restrictₛₗ f x ⊗ₜ M₂.restrictₛₗ f y := rfl

end

section

variable {M₁ M₂ : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
  {M₃ M₄ : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)}

@[simp] public theorem tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    (tensorHom f g).app X = ModuleCat.MixedTensor.tensorHom (f.app X) (g.app X) := rfl

end

@[simp] public theorem tensorObjUlift_map_up
    {M₁ : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
    {M₂ : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : M₁.obj X) (y : M₂.obj X) :
    (((tensorObj M₁ M₂).uliftSections.{u}).map f).hom (ULift.up (x ⊗ₜ y)) =
      ULift.up (M₁.restrictₛₗ f x ⊗ₜ M₂.restrictₛₗ f y) := rfl

section Compatibility

variable (M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- When both factors have sections in the universe of the coefficient rings, the canonical
objectwise tensor product is the tensor product of the monoidal structure on presheaves
of modules, on the nose. -/
public theorem tensorObj_eq : tensorObj M₁ M₂ = M₁ ⊗ M₂ := rfl

variable {M₁ M₂} {M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Likewise on morphisms: the canonical tensor product of two morphisms is the one of
the monoidal structure. -/
public theorem tensorHom_eq (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorHom f g = f ⊗ₘ g := rfl

end Compatibility

end MixedTensor

end PresheafOfModules

end
