module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Existence of pointwise Kan extensions

Let `L : C ⥤ D` and `F : C ⥤ H` be functors. The pointwise right Kan extension of `F` along `L`
has value at an object `Y` of `D` the limit

`(Ran_L F)(Y) = lim_{(X, Y ⟶ L X)} F(X)`

indexed by the comma category `CategoryTheory.StructuredArrow Y L`, and dually the pointwise left
Kan extension is a colimit over `CategoryTheory.CostructuredArrow L Y`. This file records when
these (co)limits exist, so that the Kan extension exists for *every* `F`:

* if `C` has objects in `Type u₁` and morphisms in `Type v₁` and `D` has morphisms in `Type v₂`,
  the comma categories have objects in `Type (max u₁ v₂)` and morphisms in `Type v₁`, so it
  suffices that `H` have (co)limits of that size. For presheaves of sets on `C` (taking `C ⥤ D` to
  be `L.op : Cᵒᵖ ⥤ Dᵒᵖ`) with values in a universe containing those of `C` and `D`, this is the
  construction of the pushforward of presheaves `{}_pL` of Stacks 00XF and 06TK;
* if every comma category is essentially small for a universe `w` — for instance when `C` is
  essentially small and `D` is locally small for `w` — it suffices that `H` have `w`-small
  (co)limits.

The first criterion is found by typeclass inference unaided, through Mathlib's
`CategoryTheory.Limits.hasLimitOfHasLimitsOfShape`.

## Main results

* `CategoryTheory.Functor.hasPointwiseRightKanExtension_of_hasLimitsOfSize` and
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`: Kan extensions along
  `L` exist when the coefficients have (co)limits of the size of the comma categories.
* `CategoryTheory.Functor.hasPointwiseRightKanExtension_of_essentiallySmall` and
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_essentiallySmall`: Kan extensions along
  `L` exist when the comma categories are essentially `w`-small and the coefficients have
  `w`-small (co)limits.
* `CategoryTheory.Functor.hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall` and
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall`: the
  same when the source of `L` is essentially `w`-small and its target locally `w`-small.

## References

* [Stacks Project, Tag 00XF](https://stacks.math.columbia.edu/tag/00XF)
* [Stacks Project, Tag 06TK](https://stacks.math.columbia.edu/tag/06TK)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] (L : C ⥤ D) (F : C ⥤ H)

/-- Pointwise right Kan extensions along `L : C ⥤ D` exist as soon as the coefficient category has
limits indexed by the comma categories `StructuredArrow Y L`, whose objects form a
`Type (max u₁ v₂)` and whose morphisms a `Type v₁`. -/
theorem hasPointwiseRightKanExtension_of_hasLimitsOfSize [HasLimitsOfSize.{v₁, max u₁ v₂} H] :
    L.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- Pointwise left Kan extensions along `L : C ⥤ D` exist as soon as the coefficient category has
colimits indexed by the comma categories `CostructuredArrow L Y`, whose objects form a
`Type (max u₁ v₂)` and whose morphisms a `Type v₁`. -/
theorem hasPointwiseLeftKanExtension_of_hasColimitsOfSize [HasColimitsOfSize.{v₁, max u₁ v₂} H] :
    L.HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

/-- Pointwise right Kan extensions along `L` exist when every comma category `StructuredArrow Y L`
is essentially `w`-small and the coefficient category has `w`-small limits. -/
theorem hasPointwiseRightKanExtension_of_essentiallySmall
    [∀ Y : D, EssentiallySmall.{w} (StructuredArrow Y L)] [HasLimitsOfSize.{w, w} H] :
    L.HasPointwiseRightKanExtension F := fun Y ↦
  have := hasLimitsOfShape_of_essentiallySmall.{w} (StructuredArrow Y L) H
  inferInstance

/-- Pointwise left Kan extensions along `L` exist when every comma category `CostructuredArrow L Y`
is essentially `w`-small and the coefficient category has `w`-small colimits. -/
theorem hasPointwiseLeftKanExtension_of_essentiallySmall
    [∀ Y : D, EssentiallySmall.{w} (CostructuredArrow L Y)] [HasColimitsOfSize.{w, w} H] :
    L.HasPointwiseLeftKanExtension F := fun Y ↦
  have := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow L Y) H
  inferInstance

/-- Pointwise right Kan extensions along a functor `L` from an essentially `w`-small category to a
locally `w`-small category exist for coefficients with `w`-small limits: the comma categories
`StructuredArrow Y L` are then essentially `w`-small. -/
theorem hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall
    [EssentiallySmall.{w} C] [LocallySmall.{w} D] [HasLimitsOfSize.{w, w} H] :
    L.HasPointwiseRightKanExtension F :=
  hasPointwiseRightKanExtension_of_essentiallySmall.{w} L F

/-- Pointwise left Kan extensions along a functor `L` from an essentially `w`-small category to a
locally `w`-small category exist for coefficients with `w`-small colimits: the comma categories
`CostructuredArrow L Y` are then essentially `w`-small. -/
theorem hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall
    [EssentiallySmall.{w} C] [LocallySmall.{w} D] [HasColimitsOfSize.{w, w} H] :
    L.HasPointwiseLeftKanExtension F :=
  hasPointwiseLeftKanExtension_of_essentiallySmall.{w} L F

end CategoryTheory.Functor
