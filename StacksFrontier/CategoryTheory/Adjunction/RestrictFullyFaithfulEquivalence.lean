module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# An adjunction restricting to an equivalence

Let `L' ⊣ R'` be an adjunction between `C'` and `D'`, and let `C ⊆ C'`, `D ⊆ D'` be full
subcategories (more generally, fully faithful functors `iC`, `iD`) to which `L'` and `R'`
restrict as `L` and `R`.  If the unit of `L' ⊣ R'` is invertible at the objects of `C` and the
counit at the objects of `D`, then `L` is an equivalence: the restricted adjunction
`CategoryTheory.Adjunction.restrictFullyFaithful` has invertible unit and counit.

## Main results

* `CategoryTheory.Adjunction.isEquivalence_of_restrictFullyFaithful`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {C' : Type*} [Category C']
    {D' : Type*} [Category D'] {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L' ⊣ R') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) {L : C ⥤ D} {R : D ⥤ C}
    (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)

include hiC hiD comm1 comm2 in
/-- **An adjunction whose unit and counit are invertible on two full subcategories to which it
restricts restricts to an equivalence.** -/
theorem isEquivalence_of_restrictFullyFaithful
    (hunit : ∀ X, IsIso (adj.unit.app (iC.obj X)))
    (hcounit : ∀ Y, IsIso (adj.counit.app (iD.obj Y))) : L.IsEquivalence := by
  have := hiC.full
  have := hiC.faithful
  have := hiD.full
  have := hiD.faithful
  have : ∀ X, IsIso ((adj.restrictFullyFaithful hiC hiD comm1 comm2).unit.app X) := fun X => by
    have := hunit X
    have : IsIso (iC.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).unit.app X)) := by
      rw [map_restrictFullyFaithful_unit_app]
      infer_instance
    exact isIso_of_reflects_iso _ iC
  have : ∀ Y, IsIso ((adj.restrictFullyFaithful hiC hiD comm1 comm2).counit.app Y) := fun Y => by
    have := hcounit Y
    have : IsIso (iD.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).counit.app Y)) := by
      rw [map_restrictFullyFaithful_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ iD
  exact (adj.restrictFullyFaithful hiC hiD comm1 comm2).toEquivalence.isEquivalence_functor

end CategoryTheory.Adjunction

end
