module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# The unitors of a localized monoidal structure at two choices of unit object

`CategoryTheory.LocalizedMonoidal L W ε` is the monoidal structure obtained by localizing a
monoidal category `C` along `L : C ⥤ D` at a class `W` of morphisms, with the extra datum
`ε : L.obj (𝟙_ C) ≅ unit` naming a preferred unit object. Two such structures on the same `L` and
`W` with different `ε` are *the same monoidal structure except for the two unitors*: the tensor
product, the whiskerings, the tensor product of two morphisms and the associator do not mention
`ε` at all, while `CategoryTheory.Localization.Monoidal.leftUnitor` and `rightUnitor` are each
`ε` whiskered into the appropriate factor, followed by a natural isomorphism that is independent
of `ε`.

**This file names that independent part and reads the two unitors against it**, so that a unitor
of one structure is a unitor of the other precomposed with the comparison of the two unit
objects:

  `ρ_{ε₁} X = (X ◁ (ε₁⁻¹ ≫ ε₂)) ≫ ρ_{ε₂} X`,  `λ_{ε₁} X = ((ε₁⁻¹ ≫ ε₂) ▷ X) ≫ λ_{ε₂} X`.

This is what a development carrying two unit conventions for one localization needs. In this
repository the two conventions are `Stacks.SheafInternalHom.monoidalCategory`, whose `ε` is
`CategoryTheory.Iso.refl` so that the unit object is the sheafification of the presheaf unit, and
`Stacks.SheafOfModules.monoidalCategory`, whose `ε` is `Stacks.SheafOfModules.sheafifyUnitIso` so
that the unit object is `SheafOfModules.unit`. Everything else about those two structures is
already identified by the `rfl` lemmas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections`; the unitors are what
was missing, and they are what an equation of morphisms of the first structure has to be read
through before it can be evaluated on a section.

## Main definitions

* `CategoryTheory.Localization.Monoidal.leftUnitorCore` and `rightUnitorCore`: the factor of the
  respective unitor that does not mention `ε`, namely the lift to the localization of the unitor
  of `C`.

## Main results

* `CategoryTheory.Localization.Monoidal.leftUnitorCore_eq` and `rightUnitorCore_eq`: those
  factors do not depend on the choice of unit object.
* `CategoryTheory.Localization.Monoidal.leftUnitor_hom_eq_of_unitIso` and
  `rightUnitor_hom_eq_of_unitIso`: **the comparison of the unitors at two choices of unit
  object.**

## Implementation notes

The two type synonyms `CategoryTheory.LocalizedMonoidal L W ε₁` and
`LocalizedMonoidal L W ε₂` are nominally distinct, so the statements supply the
`CategoryTheory.MonoidalCategoryStruct` instance explicitly and quantify over an object of `D`
itself; the notations `◁`, `▷`, `ρ_` and `λ_` cannot be used.

**No tactic occurs.** `dsimp` and `simp` both refuse to unfold
`CategoryTheory.Localization.Monoidal.monoidalCategoryStruct` here, reporting that the unfolded
goal is not type-correct: they work at `implicit` transparency, at which the type synonym does not
reduce to `D`, so an object of `D` is rejected where an object of `LocalizedMonoidal L W ε` is
expected. Mathlib's own proofs in that file turn the transparency check off with an elaboration
option. Term
mode has no such restriction — a `rfl` or an `Eq.trans` is checked at default transparency, where
the synonym reduces — so each unitor is split off against its core by `rfl` and the two cores are
identified by `rfl`, with `CategoryTheory.Functor.map_comp` doing the only actual work.

The cores are *stated* rather than derived from
`CategoryTheory.Localization.Monoidal.rightUnitor_hom_app`, which describes a unitor only at an
object in the image of `L`; the objects this development applies the result to are arbitrary
sheaves of modules, and recovering those from the image would need the essential surjectivity of
the localization and the naturality of both unitors.

## References

* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

universe v v' u u'

namespace CategoryTheory.Localization.Monoidal

open Category MonoidalCategory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (L : C ⥤ D) (W : MorphismProperty C) [MonoidalCategory C]
  [W.IsMonoidal] [L.IsLocalization W]

section Core

variable {unit : D}

/-- **The part of the right unitor of `CategoryTheory.LocalizedMonoidal L W ε` that does not
mention `ε`**: the lift to the localization of the right unitor of `C`, as a natural isomorphism
`- ⊗ L(𝟙_ C) ≅ -`.

`CategoryTheory.Localization.Monoidal.rightUnitor` is this isomorphism precomposed with `ε⁻¹`
whiskered into the second factor, which is
`CategoryTheory.Localization.Monoidal.rightUnitor_hom_app_eq_core`. -/
def rightUnitorCore (ε : L.obj (𝟙_ C) ≅ unit) :
    (tensorBifunctor L W ε).flip.obj ((toMonoidalCategory L W ε).obj (𝟙_ C)) ≅ 𝟭 _ :=
  Localization.liftNatIso (toMonoidalCategory L W ε) W
    (tensorRight (𝟙_ C) ⋙ toMonoidalCategory L W ε) (toMonoidalCategory L W ε)
    ((tensorBifunctor L W ε).flip.obj ((toMonoidalCategory L W ε).obj (𝟙_ C))) (𝟭 _)
    (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- **The part of the left unitor of `CategoryTheory.LocalizedMonoidal L W ε` that does not
mention `ε`**, the companion of `CategoryTheory.Localization.Monoidal.rightUnitorCore`. -/
def leftUnitorCore (ε : L.obj (𝟙_ C) ≅ unit) :
    (tensorBifunctor L W ε).obj ((toMonoidalCategory L W ε).obj (𝟙_ C)) ≅ 𝟭 _ :=
  Localization.liftNatIso (toMonoidalCategory L W ε) W
    (tensorLeft (𝟙_ C) ⋙ toMonoidalCategory L W ε) (toMonoidalCategory L W ε)
    ((tensorBifunctor L W ε).obj ((toMonoidalCategory L W ε).obj (𝟙_ C))) (𝟭 _)
    (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- **The right unitor split off against its core**: it is `ε⁻¹` whiskered into the second factor
followed by `CategoryTheory.Localization.Monoidal.rightUnitorCore`. This is the definition of
`CategoryTheory.Localization.Monoidal.rightUnitor`, read at an object. -/
theorem rightUnitor_hom_app_eq_core (ε : L.obj (𝟙_ C) ≅ unit) (X : D) :
    (@MonoidalCategoryStruct.rightUnitor _ _ (monoidalCategoryStruct L W ε) X).hom =
      ((tensorBifunctor L W ε).obj X).map ε.inv ≫ (rightUnitorCore L W ε).hom.app X :=
  rfl

/-- **The left unitor split off against its core**, the companion of
`CategoryTheory.Localization.Monoidal.rightUnitor_hom_app_eq_core`. -/
theorem leftUnitor_hom_app_eq_core (ε : L.obj (𝟙_ C) ≅ unit) (X : D) :
    (@MonoidalCategoryStruct.leftUnitor _ _ (monoidalCategoryStruct L W ε) X).hom =
      ((tensorBifunctor L W ε).map ε.inv).app X ≫ (leftUnitorCore L W ε).hom.app X :=
  rfl

end Core

variable {unit₁ unit₂ : D} (ε₁ : L.obj (𝟙_ C) ≅ unit₁) (ε₂ : L.obj (𝟙_ C) ≅ unit₂)

/-- **The core of the right unitor does not depend on the choice of unit object.** The choice
enters `CategoryTheory.Localization.Monoidal.rightUnitor` only through the whiskered `ε⁻¹`;
everything after it is the same term. -/
theorem rightUnitorCore_eq : rightUnitorCore L W ε₁ = rightUnitorCore L W ε₂ := rfl

/-- **The core of the left unitor does not depend on the choice of unit object.** -/
theorem leftUnitorCore_eq : leftUnitorCore L W ε₁ = leftUnitorCore L W ε₂ := rfl

/-- The comparison `ε₁⁻¹ ≫ ε₂` of two unit objects followed by `ε₂⁻¹` is `ε₁⁻¹`. -/
private theorem unitIso_comp_inv : (ε₁.inv ≫ ε₂.hom) ≫ ε₂.inv = ε₁.inv := by simp

/-- **The right unitors of a localized monoidal structure at two choices of unit object.** The
right unitor at `ε₁` is the comparison `ε₁⁻¹ ≫ ε₂` of the two unit objects, whiskered into the
second factor, followed by the right unitor at `ε₂`.

Both unitors are their common core precomposed with a whiskered inverse unit comparison
(`CategoryTheory.Localization.Monoidal.rightUnitor_hom_app_eq_core` and
`CategoryTheory.Localization.Monoidal.rightUnitorCore_eq`), so this is the functoriality of
`- ⊗ X` applied to `(ε₁⁻¹ ≫ ε₂) ≫ ε₂⁻¹ = ε₁⁻¹`. -/
theorem rightUnitor_hom_eq_of_unitIso (X : D) :
    (@MonoidalCategoryStruct.rightUnitor _ _ (monoidalCategoryStruct L W ε₁) X).hom =
      (@MonoidalCategoryStruct.whiskerLeft _ _ (monoidalCategoryStruct L W ε₂)
          X unit₁ unit₂ (ε₁.inv ≫ ε₂.hom)) ≫
        (@MonoidalCategoryStruct.rightUnitor _ _ (monoidalCategoryStruct L W ε₂) X).hom :=
  Eq.trans
    (congrArg (fun f => f ≫ (rightUnitorCore L W ε₁).hom.app X)
      ((congrArg (fun g => ((tensorBifunctor L W ε₁).obj X).map g)
            (unitIso_comp_inv L ε₁ ε₂)).symm.trans
        (((tensorBifunctor L W ε₁).obj X).map_comp (ε₁.inv ≫ ε₂.hom) ε₂.inv)))
    (assoc _ _ _)

/-- **The left unitors of a localized monoidal structure at two choices of unit object**, the
companion of `CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso`. -/
theorem leftUnitor_hom_eq_of_unitIso (X : D) :
    (@MonoidalCategoryStruct.leftUnitor _ _ (monoidalCategoryStruct L W ε₁) X).hom =
      (@MonoidalCategoryStruct.whiskerRight _ _ (monoidalCategoryStruct L W ε₂)
          unit₁ unit₂ (ε₁.inv ≫ ε₂.hom) X) ≫
        (@MonoidalCategoryStruct.leftUnitor _ _ (monoidalCategoryStruct L W ε₂) X).hom :=
  Eq.trans
    (congrArg (fun f => f ≫ (leftUnitorCore L W ε₁).hom.app X)
      ((congrArg (fun g => ((tensorBifunctor L W ε₁).map g).app X)
            (unitIso_comp_inv L ε₁ ε₂)).symm.trans
        (congrArg (fun θ => NatTrans.app θ X)
          ((tensorBifunctor L W ε₁).map_comp (ε₁.inv ≫ ε₂.hom) ε₂.inv))))
    (assoc _ _ _)

end CategoryTheory.Localization.Monoidal

end
