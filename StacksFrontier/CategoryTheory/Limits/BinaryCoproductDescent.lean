module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Descending morphisms along a binary coproduct in an extensive category

In a finitary extensive category the pullbacks of a morphism `f : T ⟶ X ⨿ Y` along the two
coproduct inclusions exhibit `T` as a binary coproduct. Consequently a morphism out of `T`
may be constructed, and two morphisms out of `T` may be compared, one summand at a time:
it suffices to work over a test object `W` equipped with `i : W ⟶ T` and a factorization of
`i ≫ f` through one of the two inclusions.

That is the form in which the construction is used, since the summand over which one works
is usually not the chosen pullback but some other object mapping to `T` compatibly — for
instance the diagonal or the graph summand of a relation.

## Main definitions

* `CategoryTheory.Limits.isColimitBinaryCofanPullbackCoprod`: the pullbacks of a morphism
  into a binary coproduct form a binary coproduct.

## Main results

* `CategoryTheory.Limits.hom_ext_of_pullback_coprod` and
  `CategoryTheory.Limits.hom_ext_of_coprod_cases`: two morphisms out of `T` agree as soon as
  they agree over each summand, in the chosen-pullback form and in the test-object form.
* `CategoryTheory.Limits.exists_lift_of_pullback_coprod` and
  `CategoryTheory.Limits.exists_lift_of_coprod_cases`: a pair of morphisms out of `T` factors
  through a given pair of morphisms out of `R` as soon as it does so over each summand.

## Implementation notes

The decomposition is the van Kampen property of the coproduct cofan, in the form
`CategoryTheory.BinaryCofan.isVanKampen_iff`, applied to the two chosen pullback squares.

The "case" forms are deduced from the chosen-pullback forms by taking for `W` the chosen
pullback itself and for the factorization `CategoryTheory.Limits.pullback.condition`;
conversely they imply them, so the two pairs are equivalent. Both are stated because the
hypothesis of the case form is what a caller can supply and the conclusion of the
chosen-pullback form is what is convenient to prove.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [FinitaryExtensive C]

/-- **The pullbacks of a morphism into a binary coproduct form a binary coproduct.** In a
finitary extensive category, base change along `f : T ⟶ X ⨿ Y` turns the coproduct cofan on
`X` and `Y` into a coproduct cofan on `T ×_{X ⨿ Y} X` and `T ×_{X ⨿ Y} Y`. -/
noncomputable def isColimitBinaryCofanPullbackCoprod [HasPullbacks C]
    {X Y T : C} (f : T ⟶ X ⨿ Y) :
    IsColimit (BinaryCofan.mk (pullback.fst f (coprod.inl : X ⟶ X ⨿ Y))
      (pullback.fst f (coprod.inr : Y ⟶ X ⨿ Y))) :=
  (((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.van_kampen' _ (coprodIsCoprod X Y)) _
    (pullback.snd _ _) (pullback.snd _ _) f
    pullback.condition.symm pullback.condition.symm).mpr
    ⟨IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩).some

/-- Two morphisms out of `T` agree as soon as they agree after base change along `f` to each
summand of a binary coproduct. -/
theorem hom_ext_of_pullback_coprod [HasPullbacks C]
    {X Y T Z : C} (f : T ⟶ X ⨿ Y) (a b : T ⟶ Z)
    (hl : pullback.fst f (coprod.inl : X ⟶ X ⨿ Y) ≫ a = pullback.fst _ _ ≫ b)
    (hr : pullback.fst f (coprod.inr : Y ⟶ X ⨿ Y) ≫ a = pullback.fst _ _ ≫ b) : a = b :=
  BinaryCofan.IsColimit.hom_ext (isColimitBinaryCofanPullbackCoprod f) hl hr

/-- **Two morphisms out of `T` agree as soon as they agree over each summand.** The test data
over a summand is an object `W` with a morphism `i` to `T` whose composite with `f` factors
through the inclusion of that summand. -/
theorem hom_ext_of_coprod_cases [HasPullbacks C]
    {X Y T Z : C} (f : T ⟶ X ⨿ Y) (a b : T ⟶ Z)
    (hl : ∀ (W : C) (i : W ⟶ T) (g : W ⟶ X),
      i ≫ f = g ≫ coprod.inl → i ≫ a = i ≫ b)
    (hr : ∀ (W : C) (i : W ⟶ T) (g : W ⟶ Y),
      i ≫ f = g ≫ coprod.inr → i ≫ a = i ≫ b) : a = b :=
  hom_ext_of_pullback_coprod f a b (hl _ _ _ pullback.condition) (hr _ _ _ pullback.condition)

/-- A pair of morphisms out of `T` factors through a pair of morphisms out of `R` as soon as
it does so after base change along `f` to each summand of a binary coproduct. -/
theorem exists_lift_of_pullback_coprod [HasPullbacks C] {X Y T R A B : C} (f : T ⟶ X ⨿ Y)
    (r : R ⟶ A) (s : R ⟶ B) (a : T ⟶ A) (b : T ⟶ B)
    (hl : ∃ l : pullback f (coprod.inl : X ⟶ X ⨿ Y) ⟶ R,
      l ≫ r = pullback.fst _ _ ≫ a ∧ l ≫ s = pullback.fst _ _ ≫ b)
    (hr : ∃ l : pullback f (coprod.inr : Y ⟶ X ⨿ Y) ⟶ R,
      l ≫ r = pullback.fst _ _ ≫ a ∧ l ≫ s = pullback.fst _ _ ≫ b) :
    ∃ l : T ⟶ R, l ≫ r = a ∧ l ≫ s = b := by
  obtain ⟨l, hlr, hls⟩ := hl
  obtain ⟨l', hlr', hls'⟩ := hr
  let c := isColimitBinaryCofanPullbackCoprod f
  refine ⟨BinaryCofan.IsColimit.desc c l l', ?_, ?_⟩ <;>
    refine hom_ext_of_pullback_coprod f _ _ ?_ ?_ <;>
    first
    | refine (BinaryCofan.IsColimit.inl_desc_assoc c l l' _).trans ?_
    | refine (BinaryCofan.IsColimit.inr_desc_assoc c l l' _).trans ?_
  all_goals assumption

/-- **A pair of morphisms out of `T` factors through a pair of morphisms out of `R` as soon
as it does so over each summand.** The test data over a summand is as in
`CategoryTheory.Limits.hom_ext_of_coprod_cases`. -/
theorem exists_lift_of_coprod_cases [HasPullbacks C] {X Y T R A B : C} (f : T ⟶ X ⨿ Y)
    (r : R ⟶ A) (s : R ⟶ B) (a : T ⟶ A) (b : T ⟶ B)
    (hl : ∀ (W : C) (i : W ⟶ T) (g : W ⟶ X), i ≫ f = g ≫ coprod.inl →
      ∃ l : W ⟶ R, l ≫ r = i ≫ a ∧ l ≫ s = i ≫ b)
    (hr : ∀ (W : C) (i : W ⟶ T) (g : W ⟶ Y), i ≫ f = g ≫ coprod.inr →
      ∃ l : W ⟶ R, l ≫ r = i ≫ a ∧ l ≫ s = i ≫ b) :
    ∃ l : T ⟶ R, l ≫ r = a ∧ l ≫ s = b :=
  exists_lift_of_pullback_coprod f r s a b (hl _ _ _ pullback.condition)
    (hr _ _ _ pullback.condition)

end CategoryTheory.Limits

end
