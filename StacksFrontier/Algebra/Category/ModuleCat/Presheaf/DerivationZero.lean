module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# The zero derivation of a presheaf of modules

For a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R` and a presheaf of
`R`-modules `M`, the derivation which is zero on every object is a `φ`-derivation with values in
`M`. Postcomposing any derivation with the zero morphism gives it.

## Main definitions

* `PresheafOfModules.Derivation.instZero`: the zero derivation.

## Main results

* `PresheafOfModules.Derivation.zero_d`: the zero derivation vanishes on every section.
* `PresheafOfModules.Derivation.postcomp_zero`: postcomposing a derivation with the zero morphism
  gives the zero derivation.
-/

@[expose] public section

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules.Derivation

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} {φ : S ⟶ F.op ⋙ R}

/-- The zero derivation, vanishing on every section. -/
instance instZero : Zero (PresheafOfModulesOfCommRing.Derivation M φ) :=
  ⟨{ d := 0
     d_mul := fun _ _ => by simp
     d_map := fun _ _ => (map_zero _).symm
     d_app := fun _ => rfl }⟩

/-- The zero derivation sends every section `a` of `R` to `0`. -/
@[simp] theorem zero_d {X : Dᵒᵖ} (a : R.obj X) :
    (0 : PresheafOfModulesOfCommRing.Derivation M φ).d a = 0 := rfl

/-- Postcomposing a derivation with the zero morphism gives the zero derivation. -/
@[simp] theorem postcomp_zero (d : PresheafOfModulesOfCommRing.Derivation M φ) :
    d.postcomp (0 : M ⟶ N) = 0 := by
  ext X a
  simp

end PresheafOfModules.Derivation

end
