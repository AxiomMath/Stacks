module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexCompShift
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparisonTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexTriangulated
public import StacksFrontier.CategoryTheory.Triangulated.HomologicalKernelRetracts

/-!
# A localization of `K(A)` at the acyclics is a localization of `K(Comp^dg(A))`

The chain `(*)` of [Stacks, Tag 09LK] is stated over `K(C)` for `C` a differential graded
category: its localization datum is a functor `q : K(C) ⥤ DA` which is a localization at the
morphisms whose cone lies in a thick subcategory `Ac` of `K(C)`. For `C` the differential graded
category `CochainComplex.dgCategory A` of Tag 09L9, the localization one actually has is
Mathlib's, on the *ordinary* homotopy category
`HomotopyCategory A (ComplexShape.up ℤ)` at `CategoryTheory.HomotopyCategory.subcategoryAcyclic A`
— for instance `CategoryTheory.DerivedCategory.Qh`. The two homotopy categories are the two sides
of `CochainComplex.homotopyCategoryEquivalence` of Tag 09L9, and this file carries the
localization across it.

Everything is the transported subcategory `CochainComplex.dgCategoryKAcyclic`, the inverse image
of the acyclics along the quasi-inverse of the comparison. Its morphisms-with-cone-in-it are the
inverse image of the acyclic-cone morphisms, by Mathlib's
`CategoryTheory.ObjectProperty.inverseImage_trW_iff`, which is what makes
`CategoryTheory.Functor.IsLocalization.of_equivalence_source` apply, and it is thick because the
acyclics are: closed under isomorphisms and triangulated by Mathlib, closed under retracts by
`CategoryTheory.HomotopyCategory.subcategoryAcyclic_isStableUnderRetracts`.

## Main definitions

* `CochainComplex.dgCategoryKAcyclic`: the acyclic objects of `K(Comp^dg(A))`, defined as the
  inverse image of the acyclics of `K(A)` along the quasi-inverse of the comparison. It is
  **thick**: the three instances are supplied here.

## Main results

* `CochainComplex.dgCategoryKAcyclic_trW_iff`: a morphism of `K(Comp^dg(A))` has acyclic cone
  exactly when its image in `K(A)` does.
* `CochainComplex.comparisonInverse_comp_isLocalization`: **the payload.** If
  `L : K(A) ⥤ D` is a localization at the acyclic-cone morphisms, then
  `E.inverse ⋙ L : K(Comp^dg(A)) ⥤ D` is a localization at
  `(CochainComplex.dgCategoryKAcyclic A).trW`, and it commutes with the translations. This is the
  `q` of Tag 09LK's chain.
* `CochainComplex.comparisonInverse_comp_Qh_isLocalization`: the same for
  `CategoryTheory.DerivedCategory.Qh`, which is step 3's localization.

## Implementation notes

Nothing here is hypothetical. What Mathlib's three `inverseImage` lemmas need of the
quasi-inverse of the comparison is that it commute with the translations and be exact, and both
are instances: `CochainComplex.homotopyCategoryEquivalence_inverse_commShift` and
`CochainComplex.homotopyCategoryEquivalence_inverse_isTriangulated`. The second is the content of
`StacksFrontier/CategoryTheory/DifferentialGraded/CochainComplexComparisonTriangulated.lean`, which
matches the two independently built pretriangulated structures — Mathlib's on
`HomotopyCategory A (ComplexShape.up ℤ)` and `CochainComplex.dgCategoryKPretriangulated` on
`(CochainComplex.dgCategory A).K` — against each other.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the comparison of the two homotopy
  categories; [Tag 09LJ](https://stacks.math.columbia.edu/tag/09LJ), the abelian setting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

namespace CochainComplex

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- **The acyclic objects of `K(Comp^dg(A))`**: the objects whose image under the quasi-inverse
of the comparison equivalence of Tag 09L9 is an acyclic object of the ordinary homotopy category.

Since the comparison is the identity on objects, these are the acyclic complexes, read in
`K(Comp^dg(A))`. -/
def dgCategoryKAcyclic : ObjectProperty (dgCategory A).K :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage
    (homotopyCategoryEquivalence A).inverse

/-- The acyclic objects of `K(Comp^dg(A))` are closed under isomorphisms. -/
instance dgCategoryKAcyclic_isClosedUnderIsomorphisms :
    (dgCategoryKAcyclic A).IsClosedUnderIsomorphisms := by
  dsimp only [dgCategoryKAcyclic]
  infer_instance

/-- **The acyclic objects of `K(Comp^dg(A))` are closed under retracts.** A retract is carried to
a retract by the quasi-inverse, and the acyclics of the ordinary homotopy category are closed
under retracts. -/
instance dgCategoryKAcyclic_isStableUnderRetracts :
    (dgCategoryKAcyclic A).IsStableUnderRetracts where
  of_retract h hY :=
    HomotopyCategory.subcategoryAcyclic_isStableUnderRetracts A |>.of_retract
      (h.map (homotopyCategoryEquivalence A).inverse) hY

/-- **The acyclic objects of `K(Comp^dg(A))` form a triangulated subcategory**, the quasi-inverse
of the comparison being exact. -/
instance dgCategoryKAcyclic_isTriangulated : (dgCategoryKAcyclic A).IsTriangulated := by
  dsimp only [dgCategoryKAcyclic]
  infer_instance

/-- **A morphism of `K(Comp^dg(A))` has acyclic cone exactly when its image in the ordinary
homotopy category does.** -/
theorem dgCategoryKAcyclic_trW_iff {X Y : (dgCategory A).K} (f : X ⟶ Y) :
    (dgCategoryKAcyclic A).trW f ↔ (HomotopyCategory.subcategoryAcyclic A).trW
      ((homotopyCategoryEquivalence A).inverse.map f) :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage_trW_iff _ f

variable {D : Type*} [Category D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
  [L.IsLocalization (HomotopyCategory.subcategoryAcyclic A).trW]

/-- **A localization of the ordinary homotopy category at the acyclics is a localization of
`K(Comp^dg(A))` at the transported acyclics.** This is the `q` of the chain `(*)` of
[Stacks, Tag 09LK]: precomposing a localization `L` of `K(A)` with the quasi-inverse of the
comparison of Tag 09L9 gives a localization of `K(Comp^dg(A))` at
`(CochainComplex.dgCategoryKAcyclic A).trW`.

It is Mathlib's `CategoryTheory.Functor.IsLocalization.of_equivalence_source` along the
comparison: the class of morphisms to invert on the other side is an inverse image, so the two
hypotheses it asks for are `CategoryTheory.ObjectProperty.inverseImage_trW_iff` and
`CategoryTheory.ObjectProperty.inverseImage_trW_isInverted`. -/
instance comparisonInverse_comp_isLocalization :
    ((homotopyCategoryEquivalence A).inverse ⋙ L).IsLocalization
      (dgCategoryKAcyclic A).trW := by
  refine Functor.IsLocalization.of_equivalence_source L
    (HomotopyCategory.subcategoryAcyclic A).trW _ _ (homotopyCategoryEquivalence A)
    (fun X Y f hf => ?_)
    ((HomotopyCategory.subcategoryAcyclic A).inverseImage_trW_isInverted _ L)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homotopyCategoryEquivalence A).unitIso.symm L ≪≫
      L.leftUnitor)
  refine MorphismProperty.le_isoClosure _ _ ?_
  rw [dgCategoryKAcyclic_trW_iff]
  exact ((HomotopyCategory.subcategoryAcyclic A).trW.arrow_mk_iso_iff
    (Arrow.isoMk ((homotopyCategoryEquivalence A).unitIso.app X)
      ((homotopyCategoryEquivalence A).unitIso.app Y) (by simp))).1 hf

/-- **The derived category of `A` is a localization of `K(Comp^dg(A))` at the acyclics.** This is
`CochainComplex.comparisonInverse_comp_isLocalization` at
`CategoryTheory.DerivedCategory.Qh`, the localization of step 3 of [Stacks, Tag 09LK]. -/
theorem comparisonInverse_comp_Qh_isLocalization [HasDerivedCategory.{v} A] :
    ((homotopyCategoryEquivalence A).inverse ⋙ DerivedCategory.Qh (C := A)).IsLocalization
      (dgCategoryKAcyclic A).trW :=
  inferInstance

end CochainComplex
