module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of `S⁻¹𝒞` as a colimit over `Y/S`

Let `W` be a left multiplicative system on a category `C` and let `Y` be an object of `C`. Let
`Y/S` be the category whose objects are the morphisms `s : Y ⟶ Y'` lying in `W` and whose
morphisms `s ⟶ t` are the morphisms `a : Y' ⟶ Y''` of `C` with `s ≫ a = t`. This is Mathlib's
`W.Under ⊤ Y`: the subcategory of `Under Y` whose objects are the `W`-morphisms out of `Y`, with
no condition on the morphisms. The category `Y/S` is filtered
(`MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions`), and for every object `X` the
morphisms `X ⟶ Y` of the localization `W⁻¹C` are the colimit of the sets `Mor_C(X, Y')` over
`(s : Y ⟶ Y') ∈ Y/S`.

Being a colimit is *data*, so `isColimitUnderHomCocone` is a `def`: the tautological cocone
`underHomCocone`, whose leg at `(s : Y ⟶ Y')` sends `f : X ⟶ Y'` to the left fraction `s⁻¹ f`,
is exhibited as a colimit cocone. Its legs are jointly surjective because every morphism of
`W⁻¹C` is a left fraction (`Localization.exists_leftFraction`), which is what defines the map out
of the cocone point, and they identify exactly the left fractions related by
`MorphismProperty.LeftFractionRel` (`MorphismProperty.LeftFraction.map_eq_iff`), which is what
makes that map well defined: the relation supplies a common numerator-and-denominator, i.e. an
object of `Y/S` receiving the two given ones, and the cocone relations at it do the rest.

The dual statement, for a right multiplicative system, is
`CategoryTheory.MorphismProperty.isColimitOverHomCocone`: there the colimit is over the
`W`-morphisms *into* the first variable.

The diagram takes values in `Type v`, the universe of the morphisms of `C`, so the localization
`L : C ⥤ D` is taken with `[Category.{v} D]`, i.e. with its morphisms in that same universe. This
holds for `W.Q'` under `MorphismProperty.HasLocalization.{v} W`, in particular (by
`HasLocalization.standard`) whenever `C` is a category in `Type v`.

## Main definitions

* `CategoryTheory.MorphismProperty.underHomDiagram`: the diagram `Y/S ⥤ Type v` sending
  `s : Y ⟶ Y'` to `Mor_C(X, Y')`.
* `CategoryTheory.MorphismProperty.underHomCocone`: the cocone on it with vertex
  `Mor_{W⁻¹C}(X, Y)` whose leg at `s` sends `f` to `s⁻¹ f`.
* `CategoryTheory.MorphismProperty.isColimitUnderHomCocone`: `underHomCocone` is a colimit cocone.

## References

* [Stacks, Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0), whose displayed formula is
  [Stacks, Tag 05Q1]; the dual statement is [Stacks, Tag 05Q4].
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u u₂

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

/-- The diagram `Y/S ⥤ Type v` of Stacks 05Q0: it sends an object `s : Y ⟶ Y'` of `Y/S` to the
set `Mor_C(X, Y')`, and a morphism `a : s ⟶ t` of `Y/S` to postcomposition with `a`, viewed as a
map `Mor_C(X, Y') ⟶ Mor_C(X, Y'')`. -/
def underHomDiagram (X Y : C) : W.Under ⊤ Y ⥤ Type v :=
  Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙ coyoneda.obj (Opposite.op X)

variable {D : Type u₂} [Category.{v} D] (L : C ⥤ D) [L.IsLocalization W]

/-- Postcomposing the numerator of a left fraction with a morphism `α : s ⟶ t` of `Y/S` does not
change the morphism of `W⁻¹C` it defines: `t⁻¹ (α ∘ f) = s⁻¹ f`. -/
private lemma map_leftFraction_comp {X Y : C} (A B : W.Under ⊤ Y) (α : A ⟶ B)
    (f : X ⟶ A.right) :
    (LeftFraction.mk (W := W) (X := X) (Y := Y) (f ≫ α.right) B.hom B.prop).map L
        (Localization.inverts L W) =
      (LeftFraction.mk (W := W) (X := X) (Y := Y) f A.hom A.prop).map L
        (Localization.inverts L W) :=
  (LeftFraction.map_eq_iff L W _ _).2
    ⟨B.right, 𝟙 B.right, α.right, by simp [MorphismProperty.Under.w α], by simp,
      by simpa using B.prop⟩

/-- The cocone on `underHomDiagram W X Y` with vertex `Mor_{W⁻¹C}(X, Y)` whose leg at an object
`s : Y ⟶ Y'` of `Y/S` sends `f : X ⟶ Y'` to the left fraction `s⁻¹ f`. -/
noncomputable def underHomCocone (X Y : C) : Cocone (W.underHomDiagram X Y) where
  pt := L.obj X ⟶ L.obj Y
  ι :=
    { app := fun A => ↾fun f =>
        (LeftFraction.mk (W := W) (X := X) (Y := Y) f A.hom A.prop).map L
          (Localization.inverts L W)
      naturality := fun A B α => by
        ext f
        exact map_leftFraction_comp W L A B α f }

/-- The leg of `underHomCocone` at `s : Y ⟶ Y'` sends `f : X ⟶ Y'` to `s⁻¹ f`. -/
@[simp]
lemma underHomCocone_ι_app_apply (X Y : C) (A : W.Under ⊤ Y) (f : X ⟶ A.right) :
    (W.underHomCocone L X Y).ι.app A f =
      (LeftFraction.mk (W := W) (X := X) (Y := Y) f A.hom A.prop).map L
        (Localization.inverts L W) :=
  rfl

omit [W.HasLeftCalculusOfFractions] in
/-- The legs of any cocone on `underHomDiagram W X Y` identify two left fractions that are
`LeftFractionRel`-related. -/
private lemma cocone_app_eq_of_rel {X Y : C} (c : Cocone (W.underHomDiagram X Y))
    (A B : W.Under ⊤ Y) (f : X ⟶ A.right) (g : X ⟶ B.right)
    (h : LeftFractionRel (LeftFraction.mk (W := W) (X := X) (Y := Y) f A.hom A.prop)
      (LeftFraction.mk (W := W) (X := X) (Y := Y) g B.hom B.prop)) :
    c.ι.app A f = c.ι.app B g := by
  obtain ⟨Z, t₁, t₂, hs, hf, hW⟩ := h
  have h₁ := types_congr_hom
    (c.w (Under.homMk (A := A) (B := Under.mk ⊤ (A.hom ≫ t₁) hW) t₁ rfl)) f
  have h₂ := types_congr_hom
    (c.w (Under.homMk (A := B) (B := Under.mk ⊤ (A.hom ≫ t₁) hW) t₂ hs.symm)) g
  rw [← h₁, ← h₂]
  exact congrArg _ hf

/-- **Morphisms of `W⁻¹C` as a colimit over `Y/S`**: for a left multiplicative system `W` on `C`,
a localization functor `L : C ⥤ D` of `C` at `W` and objects `X`, `Y` of `C`, the morphisms
`L.obj X ⟶ L.obj Y` of `W⁻¹C` are the colimit `colim_{(s : Y ⟶ Y') ∈ Y/S} Mor_C(X, Y')`, in the
sense that the tautological cocone `underHomCocone`, whose leg at `s` sends `f` to the left
fraction `s⁻¹ f`, is a colimit cocone.
The index category `Y/S` is filtered by
`MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions`, so this exhibits the morphisms
of `W⁻¹C` as a filtered colimit of morphisms of `C`. -/
@[stacks 05Q0 "the displayed formula 05Q1: the morphisms X ⟶ Y of the localization are the \
filtered colimit of the sets Mor_C(X, Y') over the objects (s : Y ⟶ Y') of Y/S, at the \
tautological cocone whose leg at s sends f to the left fraction s⁻¹ f", sga "4 VI 6.5"]
noncomputable def isColimitUnderHomCocone (X Y : C) : IsColimit (W.underHomCocone L X Y) where
  desc c := ↾fun g =>
    c.ι.app (Under.mk ⊤ (Localization.exists_leftFraction L W g).choose.s
      (Localization.exists_leftFraction L W g).choose.hs)
      (Localization.exists_leftFraction L W g).choose.f
  fac c A := by
    ext f
    refine cocone_app_eq_of_rel W c _ A _ f ((LeftFraction.map_eq_iff L W _ _).1 ?_)
    exact ((Localization.exists_leftFraction L W _).choose_spec).symm
  uniq c m hm := by
    ext g
    refine (congrArg m (Localization.exists_leftFraction L W g).choose_spec).trans ?_
    exact types_congr_hom (hm (Under.mk ⊤ (Localization.exists_leftFraction L W g).choose.s
      (Localization.exists_leftFraction L W g).choose.hs))
      (Localization.exists_leftFraction L W g).choose.f

end CategoryTheory.MorphismProperty

end
