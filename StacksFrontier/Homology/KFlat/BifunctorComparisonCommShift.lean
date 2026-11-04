module

public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
import StacksCore.Tactic.StacksAttribute

/-!
# The two descents of the K-flat comparison commute with the shifts

The K-flat comparison `CochainComplex.KFlatBifunctor.comparison` of [Stacks, Tag 06YU] — the
statement that on (left) K-flat representatives the derived bifunctor is the total complex — is
a composite of five factors: three `DerivedCategory.quotientCompQhIso` bridges and the lifting
isomorphisms of the **two** localization descents out of which
`CochainComplex.KFlatBifunctor.derivedBifunctor` is built.  This file discharges the two lifting
isomorphisms, which are the factors carrying all the content.

## Main results

* `CochainComplex.KFlatBifunctor.homotopyBifunctorComparisonIso_commShift₂`: **the homotopy
  descent's lifting isomorphism commutes with the shifts in both variables.**
* `CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso_commShift₂`: **the derived
  descent's lifting isomorphism commutes with the shifts in both variables.**

## Implementation notes

Both are `CategoryTheory.Localization.lifting₂_iso_hom_commShift₂Int`, and that is the whole
content of the file: the two structures
`CochainComplex.KFlatBifunctor.homotopyBifunctor_commShift₂Int` and
`derivedBifunctor_commShift₂Int` are *defined* as
`CategoryTheory.Functor.CommShift₂.ofLocalizationInt` at exactly these two liftings, so the
general lemma applies at the spelling each instance already stores and nothing has to be
reconciled.

What each statement has to repeat is the seat for the source bifunctor, for the reason recorded
in `StacksFrontier/CategoryTheory/Localization/BifunctorCommShiftTwoLiftingIso.lean`:
`CategoryTheory.Functor.whiskeringLeft₂` is a plain `def`, so the source of a lifting isomorphism
is definitionally — but not syntactically — the double precomposition that
`CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` match, and instance search does not
unfold it.  The seat is `inferInstanceAs` at the unfolded spelling and it has to sit in the
*type*, since `CategoryTheory.NatTrans.CommShift₂` takes the two bifunctors' structures as
instance arguments.  This is the same step `kFlatToDerived_commShift₂Int` takes.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Localization

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **The lifting isomorphism of the homotopy-category descent commutes with the shifts in both
variables.**  `CochainComplex.KFlatBifunctor.homotopyBifunctor_commShift₂Int` is
`CategoryTheory.Functor.CommShift₂.ofLocalizationInt` at this very lifting, so this is
`CategoryTheory.Localization.lifting₂_iso_hom_commShift₂Int`. -/
theorem homotopyBifunctorComparisonIso_commShift₂ :
    letI : ((((Functor.whiskeringLeft₂ (HomotopyCategory D (ComplexShape.up ℤ))).obj
          (HomotopyCategory.quotient A (ComplexShape.up ℤ))).obj
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))).obj
          (homotopyBifunctor F)).CommShift₂Int :=
      inferInstanceAs ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (homotopyBifunctor F ⋙ (Functor.whiskeringLeft _ _ _).obj
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)))).CommShift₂Int)
    NatTrans.CommShift₂Int
      (Localization.Lifting₂.iso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (totalToHomotopy F) (homotopyBifunctor F)).hom :=
  Localization.lifting₂_iso_hom_commShift₂Int
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- **The lifting isomorphism of the derived descent commutes with the shifts in both
variables**, i.e. `CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso` is
shift-compatible.  `derivedBifunctor_commShift₂Int` is
`CategoryTheory.Functor.CommShift₂.ofLocalizationInt` at this very lifting, so this is
`CategoryTheory.Localization.lifting₂_iso_hom_commShift₂Int`. -/
theorem derivedBifunctorComparisonIso_commShift₂ :
    letI : ((((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatQLeft F)).obj
        (kFlatQ F)).obj (derivedBifunctor F)).CommShift₂Int :=
      inferInstanceAs (((kFlatQLeft F) ⋙ (derivedBifunctor F ⋙
        (Functor.whiskeringLeft _ _ _).obj (kFlatQ F))).CommShift₂Int)
    NatTrans.CommShift₂Int (derivedBifunctorComparisonIso F).hom :=
  Localization.lifting₂_iso_hom_commShift₂Int
    (kFlatQLeft F) (kFlatQ F) (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
    (kFlatToDerived F) (derivedBifunctor F)

end CochainComplex.KFlatBifunctor

end
