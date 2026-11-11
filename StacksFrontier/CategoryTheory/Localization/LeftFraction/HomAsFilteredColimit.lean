module

public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Localization.LeftFraction.HomAsColimitShift
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of `S⁻¹𝒞` as a filtered colimit over `Y/S`

Let `W` be a left multiplicative system on a category `C` (Mathlib's
`MorphismProperty.HasLeftCalculusOfFractions`, which is the conjunction of the axioms LMS1, LMS2
and LMS3 of Stacks), and let `Y` be an object of `C`. The category `Y/S` of Stacks, whose objects
are the morphisms `s : Y ⟶ Y'` lying in `W` and whose morphisms `s ⟶ t` are the arbitrary
morphisms `a : Y' ⟶ Y''` of `C` with `s ≫ a = t`, is Mathlib's `W.Under ⊤ Y`.

Stacks 05Q0 makes two claims: the category `Y/S` is filtered, and for every object `X` the
morphisms `X ⟶ Y` of `S⁻¹C` are the colimit of the sets `Mor_C(X, Y')` over
`(s : Y ⟶ Y') ∈ Y/S` (the displayed formula 05Q1). This file states both together, for an
arbitrary localization functor `L : C ⥤ D` of `C` at `W`, with no constraint on the universe of
the morphisms of `D`: the second claim is taken in the form
`MorphismProperty.isColimitUnderHomCoconeULift`, where the diagram `X/S ⥤ Type v` is composed
with `uliftFunctor` so that it lands in the universe of the (lifted) morphisms of `D`, and the
colimit cocone is the tautological one whose leg at `s` sends `f` to the left fraction `s⁻¹ f`
(`MorphismProperty.underHomCoconeULift_ι_app_apply`). The first claim is
`MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions`.

## Main results

* `CategoryTheory.MorphismProperty.isFiltered_under_and_nonempty_isColimit_underHomCoconeULift`:
  Stacks 05Q0 in full.

## References

* [Stacks, Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0), whose displayed formula is
  [Stacks, Tag 05Q1].
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
  {D : Type u₂} [Category.{v₂} D] (L : C ⥤ D) [L.IsLocalization W]

/-- **Stacks 05Q0**: let `W` be a left multiplicative system on `C`, let `L : C ⥤ D` be a
localization functor of `C` at `W`, and let `X`, `Y` be objects of `C`. Then the category `Y/S`
(Mathlib's `W.Under ⊤ Y`) of the morphisms `s : Y ⟶ Y'` of `W`, with morphisms the commutative
triangles `s ≫ a = t` for arbitrary `a`, is filtered, and the morphisms `L.obj X ⟶ L.obj Y` of
`W⁻¹C` are the filtered colimit `colim_{(s : Y ⟶ Y') ∈ Y/S} Mor_C(X, Y')` (formula 05Q1): the
cocone `underHomCoconeULift`, whose leg at `s` sends `f : X ⟶ Y'` to the left fraction `s⁻¹ f`,
is a colimit cocone. Both sides are lifted by `ULift` to a common universe, so no condition
relates the universe of the morphisms of `D` to that of the morphisms of `C`. -/
@[stacks 05Q0 "Mathlib's W.Under ⊤ Y is the category Y/S, and HasLeftCalculusOfFractions is \
LMS1-LMS3; the filteredness of Y/S is isFiltered_under_of_hasLeftCalculusOfFractions and formula \
05Q1 is isColimitUnderHomCoconeULift, for any localization L of C at W"]
theorem isFiltered_under_and_nonempty_isColimit_underHomCoconeULift (X Y : C) :
    IsFiltered (W.Under ⊤ Y) ∧ Nonempty (IsColimit (W.underHomCoconeULift L X Y)) :=
  ⟨W.isFiltered_under_of_hasLeftCalculusOfFractions Y,
    ⟨W.isColimitUnderHomCoconeULift L X Y⟩⟩

end CategoryTheory.MorphismProperty

end
