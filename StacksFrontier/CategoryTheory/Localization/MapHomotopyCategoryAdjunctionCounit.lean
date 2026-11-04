module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The induced adjunction on homotopy categories at the class of a complex

Let `adj : G ⊣ F` be an adjunction of additive functors between preadditive categories and let
`c` be a complex shape. At the class of a complex, the unit and counit of the induced adjunction
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction` on homotopy categories are the classes
of the unit and counit of the degreewise adjunction
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction`.

## Main results

* `CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient` and
  `CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_counit_app_quotient`: the unit and the
  counit of the induced adjunction, at the class of a complex, are the classes of the degreewise
  unit and counit.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {ι : Type*} {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]

/-- The unit of the adjunction induced on homotopy categories is, at the class of a complex, the
class of the degreewise unit. -/
lemma mapHomotopyCategoryAdjunction_unit_app_quotient (adj : G ⊣ F) (c : ComplexShape ι)
    (J : HomologicalComplex B c) :
    (mapHomotopyCategoryAdjunction adj c).unit.app ((HomotopyCategory.quotient B c).obj J) =
      (HomotopyCategory.quotient B c).map ((mapHomologicalComplexAdjunction adj c).unit.app J) :=
  rfl

/-- The counit of the adjunction induced on homotopy categories is, at the class of a complex,
the class of the degreewise counit. -/
lemma mapHomotopyCategoryAdjunction_counit_app_quotient (adj : G ⊣ F) (c : ComplexShape ι)
    (K : HomologicalComplex A c) :
    (mapHomotopyCategoryAdjunction adj c).counit.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient A c).map ((mapHomologicalComplexAdjunction adj c).counit.app K) :=
  rfl

end CategoryTheory.Adjunction

end
