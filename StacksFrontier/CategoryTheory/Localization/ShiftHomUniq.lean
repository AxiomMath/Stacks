module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# A Hom group between shifted images of a localization depends only on the localized class

Let `S` be a category with a shift by `ℤ`, let `W` be a class of morphisms of `S` and let
`q₁ : S ⥤ D₁` and `q₂ : S ⥤ D₂` be two localizations of `S` at `W`, each commuting with the
shift. Then for all objects `x`, `y` of `S` and every integer `n` there is a bijection

`Hom_{D₁}(q₁ x, (q₁ y)⟦n⟧) ≃ Hom_{D₂}(q₂ x, (q₂ y)⟦n⟧)`.

The statement is the Hom-group form of the uniqueness of a localization. Three steps make it:
the comparison equivalence `D₁ ≌ D₂` of `CategoryTheory.Localization.uniq` is fully faithful,
its characteristic isomorphism `q₁ ⋙ E ≅ q₂`
(`CategoryTheory.Localization.compUniqFunctor`) rewrites `E (q₁ x)` as `q₂ x`, and the
commutation of `E` with the shift — which it has because it is induced by a functor commuting
with the shift, `CategoryTheory.Functor.commShiftOfLocalization` — moves the shift out of the
argument of `E`.

The point of isolating it is that a Hom group of this shape is what a chain of identifications
through a derived category ends at, and the two sides of such a chain usually present the
derived category by two different localizations: one as the localization of a homotopy category
at the quasi-isomorphisms, the other as a Verdier quotient of a subcategory of something else.
Neither the equivalence nor its commutation with the shift occurs in the statement, so no
instance has to be arranged by the caller beyond the two `CommShift`s on the localizations
themselves.

## Main definitions

* `CategoryTheory.homShiftEquivOfIsLocalization`: the displayed bijection.
-/

@[expose] public section

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Category

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (W : MorphismProperty S)
  (q₁ : S ⥤ D₁) [q₁.IsLocalization W] [q₁.CommShift ℤ]
  (q₂ : S ⥤ D₂) [q₂.IsLocalization W] [q₂.CommShift ℤ]

/-- **A Hom group between shifted images of a localization depends only on the localized
class.** If `q₁ : S ⥤ D₁` and `q₂ : S ⥤ D₂` are two localizations of `S` at the same class `W`
of morphisms, both commuting with the shift by `ℤ`, then for all objects `x`, `y` of `S` and
every integer `n`

`Hom_{D₁}(q₁ x, (q₁ y)⟦n⟧) ≃ Hom_{D₂}(q₂ x, (q₂ y)⟦n⟧)`.

The comparison equivalence `CategoryTheory.Localization.uniq` has been contracted away by its
own full faithfulness, its characteristic isomorphism and its commutation with the shift. -/
noncomputable def homShiftEquivOfIsLocalization (x y : S) (n : ℤ) :
    (q₁.obj x ⟶ (q₁.obj y)⟦n⟧) ≃ (q₂.obj x ⟶ (q₂.obj y)⟦n⟧) :=
  letI := Functor.commShiftOfLocalization q₁ W ℤ q₂ (Localization.uniq q₁ q₂ W).functor
  (Functor.FullyFaithful.ofFullyFaithful (Localization.uniq q₁ q₂ W).functor).homEquiv.trans
    (Iso.homCongr ((Localization.compUniqFunctor q₁ q₂ W).app x)
      (((Localization.uniq q₁ q₂ W).functor.commShiftIso n).app (q₁.obj y) ≪≫
        (shiftFunctor D₂ n).mapIso ((Localization.compUniqFunctor q₁ q₂ W).app y)))

end CategoryTheory

end
