module

public import StacksFrontier.CategoryTheory.Adjunction.Quotient
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Quotient
import all StacksFrontier.CategoryTheory.Adjunction.Quotient

/-!
# Additions to `StacksFrontier.CategoryTheory.Adjunction.Quotient`

Declarations extending `StacksFrontier.CategoryTheory.Adjunction.Quotient`, kept in their own
module.
-/

@[expose] public section

namespace CategoryTheory.Quotient

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (r : HomRel C) (s : HomRel D) {L : C ⥤ D} {R : D ⥤ C}

/-- The counit of a descended adjunction is invertible at the image of an object at which the
counit downstairs is invertible. -/
theorem isIso_adjunctionOfSquares_counit_app {L' : Quotient r ⥤ Quotient s}
    {R' : Quotient s ⥤ Quotient r} (adj : L ⊣ R) (α : L ⋙ functor s ≅ functor r ⋙ L')
    (β : R ⋙ functor r ≅ functor s ⋙ R') (Y : D) [IsIso (adj.counit.app Y)] :
    IsIso ((adjunctionOfSquares r s adj α β).counit.app ((functor s).obj Y)) := by
  unfold adjunctionOfSquares
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app]
  have : IsIso ((functor s).map (adj.counit.app Y)) := inferInstance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance this)

end CategoryTheory.Quotient

end
