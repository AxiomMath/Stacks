module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Closure properties of the orthogonals of a property of objects

Let `P` be a property of objects of a category `C` with zero morphisms. Mathlib's
`CategoryTheory.ObjectProperty.rightOrthogonal` is the property of the objects `Y` such that
every morphism `X ⟶ Y` with `P X` vanishes, and `leftOrthogonal` is the dual. Mathlib records
that both are closed under isomorphisms and contain the zero object, and, when `C` is
pretriangulated and `P` is stable under the shift, that both are triangulated subcategories
(`CategoryTheory.ObjectProperty.rightOrthogonal.IsTriangulated`). This file adds two further
closure properties that an orthogonal enjoys for formal reasons.

The first is stability under retracts: a morphism out of a retract of an object of
`P.leftOrthogonal` factors through that object, and dually for `rightOrthogonal`.

The second is closure under colimits: if `X` is a colimit of a diagram all of whose values lie
in `P.leftOrthogonal`, then a morphism `X ⟶ Y` with `P Y` agrees with `0` after composing with
every leg of the colimit cocone, hence is `0`. No hypothesis is made on the shape of the
diagram, so in particular `P.leftOrthogonal` is closed under arbitrary coproducts. Dually
`P.rightOrthogonal` is closed under limits of any shape.

Both constructions are also antitone in `P`.

## Main results

* `CategoryTheory.ObjectProperty.rightOrthogonal.instIsStableUnderRetracts` and
  `CategoryTheory.ObjectProperty.leftOrthogonal.instIsStableUnderRetracts`.
* `CategoryTheory.ObjectProperty.leftOrthogonal.instIsClosedUnderColimitsOfShape` and
  `CategoryTheory.ObjectProperty.rightOrthogonal.instIsClosedUnderLimitsOfShape`.
* `CategoryTheory.ObjectProperty.rightOrthogonal_antitone` and
  `CategoryTheory.ObjectProperty.leftOrthogonal_antitone`.
-/

@[expose] public section

universe v' u' v u

namespace CategoryTheory.ObjectProperty

open Category Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-- The right orthogonal of a property of objects is stable under retracts. -/
instance rightOrthogonal.instIsStableUnderRetracts :
    P.rightOrthogonal.IsStableUnderRetracts where
  of_retract {Y Y'} h hY' X f hX := by
    have hf : (f ≫ h.i) ≫ h.r = f := by rw [assoc, h.retract, comp_id]
    rw [← hf, hY' (f ≫ h.i) hX, zero_comp]

/-- The left orthogonal of a property of objects is stable under retracts. -/
instance leftOrthogonal.instIsStableUnderRetracts :
    P.leftOrthogonal.IsStableUnderRetracts where
  of_retract {X X'} h hX' Y f hY := by
    have hf : h.i ≫ h.r ≫ f = f := by rw [← assoc, h.retract, id_comp]
    rw [← hf, hX' (h.r ≫ f) hY, comp_zero]

/-- The left orthogonal of a property of objects is closed under colimits of any shape: a
morphism out of a colimit which vanishes on every leg of the colimit cocone is zero. In
particular `P.leftOrthogonal` is closed under arbitrary coproducts. -/
instance leftOrthogonal.instIsClosedUnderColimitsOfShape (J : Type u') [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩ Y f hY
    refine h.isColimit.hom_ext fun j ↦ ?_
    rw [comp_zero]
    exact h.prop_diag_obj j _ hY

/-- The right orthogonal of a property of objects is closed under limits of any shape: a
morphism into a limit which vanishes on every leg of the limit cone is zero. In particular
`P.rightOrthogonal` is closed under arbitrary products. -/
instance rightOrthogonal.instIsClosedUnderLimitsOfShape (J : Type u') [Category.{v'} J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨h⟩ Y f hY
    refine h.isLimit.hom_ext fun j ↦ ?_
    rw [zero_comp]
    exact h.prop_diag_obj j _ hY

variable {P}

/-- Taking right orthogonals reverses the order: if `P ≤ Q`, then
`Q.rightOrthogonal ≤ P.rightOrthogonal`. -/
lemma rightOrthogonal_antitone {Q : ObjectProperty C} (h : P ≤ Q) :
    Q.rightOrthogonal ≤ P.rightOrthogonal :=
  fun _ hY _ f hX ↦ hY f (h _ hX)

/-- Taking left orthogonals reverses the order: if `P ≤ Q`, then
`Q.leftOrthogonal ≤ P.leftOrthogonal`. -/
lemma leftOrthogonal_antitone {Q : ObjectProperty C} (h : P ≤ Q) :
    Q.leftOrthogonal ≤ P.leftOrthogonal :=
  fun _ hX _ f hY ↦ hX f (h _ hY)

end CategoryTheory.ObjectProperty
