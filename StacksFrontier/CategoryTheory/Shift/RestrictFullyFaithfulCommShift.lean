module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# Restricting an adjunction compatible with the shift

Let `L' ⊣ R'` be an adjunction between categories with a shift, compatible with the shift, and
let `L ⊣ R` be its restriction along fully faithful functors `iC`, `iD` commuting with the shift
(`CategoryTheory.Adjunction.restrictFullyFaithful`). If the two comparison isomorphisms
`iC ⋙ L' ≅ L ⋙ iD` and `iD ⋙ R' ≅ R ⋙ iC` commute with the shift, so does the restricted
adjunction: its unit, after the faithful functor `iC`, is the unit of `L' ⊣ R'` conjugated by
the two comparisons.

## Main results

* `CategoryTheory.Adjunction.commShift_restrictFullyFaithful_of_adjunction`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)

/-- The unit of the restricted adjunction, after the inclusion `iC`, is the unit of `L' ⊣ R'`
followed by the two comparison isomorphisms. -/
theorem whiskerRight_restrictFullyFaithful_unit :
    Functor.whiskerRight (adj.restrictFullyFaithful hiC hiD comm1 comm2).unit iC =
      (Functor.leftUnitor iC).hom ≫ (Functor.rightUnitor iC).inv ≫
        Functor.whiskerLeft iC adj.unit ≫ (Functor.associator iC L' R').inv ≫
          Functor.whiskerRight comm1.hom R' ≫ (Functor.associator L iD R').hom ≫
            Functor.whiskerLeft L comm2.hom ≫ (Functor.associator L R iC).inv := by
  ext X
  simp [map_restrictFullyFaithful_unit_app]

/-- **The restriction of an adjunction compatible with the shift is compatible with the
shift**, when the two comparison isomorphisms are. -/
theorem commShift_restrictFullyFaithful_of_adjunction (A : Type*) [AddMonoid A]
    [HasShift C A] [HasShift D A] [HasShift C' A] [HasShift D' A]
    [hiCs : iC.CommShift A] [hiDs : iD.CommShift A]
    [hLs : L.CommShift A] [hRs : R.CommShift A] [hL's : L'.CommShift A] [hR's : R'.CommShift A]
    [hadj : adj.CommShift A] [h1 : NatTrans.CommShift comm1.hom A]
    [h2 : NatTrans.CommShift comm2.hom A] :
    (adj.restrictFullyFaithful hiC hiD comm1 comm2).CommShift A := by
  have := hiC.faithful
  refine Adjunction.CommShift.mk' _ _ ?_
  refine NatTrans.commShift_of_whiskerRight _ iC ?_
  rw [whiskerRight_restrictFullyFaithful_unit]
  infer_instance

end CategoryTheory.Adjunction

end
