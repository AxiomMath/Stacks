module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift

/-!
# Additions to `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift`

Further declarations about
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift`, kept in their own module.
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.SheafOfModules

/-! ### Raising the universe of the values of a presheaf of modules -/

/-- Raising the universe of the values of a sheaf of modules to the universe it already lives in
gives back an isomorphic sheaf. -/
noncomputable def moduleULiftSelfIso.{v, w, u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    (M : SheafOfModules.{v} R) : (moduleULift.{v} R).obj M ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun X => by
      change ModuleCat.of (R.obj.obj X) (ULift.{v} (M.val.obj X)) ≅ M.val.obj X
      exact ULift.moduleEquiv.toModuleIso)
      (fun {X Y} f => by ext ⟨x⟩; rfl))

universe u₁ v₁ w t

variable {C : Type u₁} [Category.{v₁} C]

/-! ### The second spelling of the extension by zero of the structure sheaf -/

section Base

variable (R : Cᵒᵖ ⥤ RingCat.{w})

end Base

/-! ### The comparison isomorphism -/

section Compare

variable (R : Cᵒᵖ ⥤ RingCat.{w})

end Compare

section Sheaf

variable {J : GrothendieckTopology C}

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

end Sheaf

end Stacks.SheafOfModules

end
