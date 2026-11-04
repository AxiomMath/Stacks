module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# A scalar annihilating a sheaf of modules annihilates its subobjects

If a section `a` of a sheaf of rings `R` kills every section of `P` over an object `U` of the
site, and `φ : N ⟶ P` is a monomorphism of sheaves of `R`-modules, then `a` kills every section
of `N` over `U`.

## Main results

* `Stacks.SheafOfModules.smul_eq_zero_of_mono`: the statement above.

## Implementation notes

Evaluation at an object of the site preserves monomorphisms, so `φ` is injective on sections
over `U`; the claim then follows from `a • φ m = φ (a • m)` and injectivity.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A scalar annihilating a sheaf of modules annihilates every subobject of it.** If `a` kills
every section of `P` over `U` and `φ : N ⟶ P` is a monomorphism, then `a` kills every section of
`N` over `U`. -/
theorem smul_eq_zero_of_mono {N P : _root_.SheafOfModules.{w} R} (φ : N ⟶ P) [Mono φ]
    (U : Cᵒᵖ) (a : R.obj.obj U) (hP : ∀ s : P.val.obj U, a • s = 0) (m : N.val.obj U) :
    a • m = 0 := by
  have hinj : Function.Injective (φ.val.app U) := (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((_root_.SheafOfModules.evaluation (R := R) U).map φ)))
  exact hinj (by rw [_root_.map_smul, _root_.map_zero, hP])

end Stacks.SheafOfModules

end
