module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos

/-!
# The universe lift of (pre)sheaves of modules is fully faithful

`PresheafOfModules.uliftObj` and `SheafOfModules.uliftObj` replace the sections by their universe
lift and change nothing else, so a morphism between two universe lifts is the universe lift of a
unique morphism: its component at an object is the one obtained by unwrapping and rewrapping
`ULift`.

## Main definitions

* `PresheafOfModules.fullyFaithfulUliftFunctor` and `SheafOfModules.fullyFaithfulUliftFunctor`:
  the universe-lifting functor is fully faithful.

## Main results

* `PresheafOfModules.uliftPreimage_app_apply` and `SheafOfModules.uliftPreimage_app_apply`: the
  component of the preimage of a morphism, on an element.
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ w z t

namespace PresheafOfModules

section ULift

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{z} R}

/-- The morphism of presheaves of modules whose universe lift is a given morphism between the
universe lifts: its component at an object unwraps the `ULift`, applies the component of the
given morphism to the wrapped element, and unwraps the result. -/
noncomputable def uliftPreimage
    (φ : uliftObj.{_, _, _, _, t} M ⟶ uliftObj.{_, _, _, _, t} N) : M ⟶ N where
  app U := ModuleCat.ofHom
    (R := R.obj U) (X := M.obj U) (Y := N.obj U)
    { toFun := fun m ↦ (Hom.app φ U (ULift.up m)).down
      map_add' := fun x y ↦ congrArg ULift.down ((Hom.app φ U).hom.map_add
        (ULift.up x) (ULift.up y))
      map_smul' := fun r m ↦ congrArg ULift.down ((Hom.app φ U).hom.map_smul r (ULift.up m)) }
  naturality {U V} f := by
    ext m
    exact congrArg ULift.down (naturality_apply φ f (ULift.up m))

/-- The component of `uliftPreimage φ` at `U` sends `m` to the unwrapping of the component of `φ`
at `U` applied to `ULift.up m`. -/
@[simp]
lemma uliftPreimage_app_apply (φ : uliftObj.{_, _, _, _, t} M ⟶ uliftObj.{_, _, _, _, t} N)
    (U : Cᵒᵖ) (m : M.obj U) :
    Hom.app (uliftPreimage.{_, _, _, _, t} φ) U m = (Hom.app φ U (ULift.up m)).down :=
  rfl

variable (R) in
/-- **The universe-lifting functor on presheaves of modules is fully faithful.** -/
noncomputable def fullyFaithfulUliftFunctor :
    (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).FullyFaithful where
  preimage φ := uliftPreimage.{_, _, _, _, t} φ
  map_preimage φ := by ext U m; rfl
  preimage_map φ := by ext U m; rfl

/-- The universe-lifting functor on presheaves of modules is full. -/
instance : (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).Full :=
  (fullyFaithfulUliftFunctor.{v₁, u₁, w, z, t} R).full

/-- The universe-lifting functor on presheaves of modules is faithful. -/
instance : (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).Faithful :=
  (fullyFaithfulUliftFunctor.{v₁, u₁, w, z, t} R).faithful

end ULift

end PresheafOfModules

namespace SheafOfModules

section ULift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{z} R}

/-- The morphism of sheaves of modules whose universe lift is a given morphism between the
universe lifts. -/
noncomputable def uliftPreimage
    (φ : uliftObj.{_, _, _, _, t} M ⟶ uliftObj.{_, _, _, _, t} N) : M ⟶ N where
  val := PresheafOfModules.uliftPreimage.{_, _, _, _, t} φ.val

/-- The component of `uliftPreimage φ` at `U` sends `m` to the unwrapping of the component of
`φ.val` at `U` applied to `ULift.up m`. -/
@[simp]
lemma uliftPreimage_app_apply (φ : uliftObj.{_, _, _, _, t} M ⟶ uliftObj.{_, _, _, _, t} N)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    PresheafOfModules.Hom.app (uliftPreimage.{_, _, _, _, t} φ).val U m =
      (PresheafOfModules.Hom.app φ.val U (ULift.up m)).down :=
  rfl

variable (R) in
/-- **The universe-lifting functor on sheaves of modules is fully faithful.** -/
noncomputable def fullyFaithfulUliftFunctor :
    (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).FullyFaithful where
  preimage φ := uliftPreimage.{_, _, _, _, t} φ
  map_preimage φ := by ext U m; rfl
  preimage_map φ := by ext U m; rfl

/-- The universe-lifting functor on sheaves of modules is full. -/
instance : (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).Full :=
  (fullyFaithfulUliftFunctor.{v₁, u₁, w, z, t} R).full

/-- The universe-lifting functor on sheaves of modules is faithful. -/
instance : (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).Faithful :=
  (fullyFaithfulUliftFunctor.{v₁, u₁, w, z, t} R).faithful

end ULift

end SheafOfModules

end
