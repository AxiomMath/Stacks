module

public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions

/-!
# The total left derived functor at an object of a left orthogonal

Let `𝒩` be a triangulated subcategory of a triangulated category `C`, let `L : C ⥤ D` be a
localization functor for `𝒩.trW` and let `F : C ⥤ H` be any functor. If every object of `C`
receives a morphism of `𝒩.trW` from an object of the left orthogonal of `𝒩`, then `F` has a total
left derived functor `LF : D ⥤ H`
(`CategoryTheory.ObjectProperty.hasLeftDerivedFunctor_of_leftOrthogonal_resolutions`). Its counit
`LF(L P) ⟶ F(P)` is an isomorphism at every object `P` of the left orthogonal of `𝒩`.

## Main results

* `CategoryTheory.ObjectProperty.isIso_totalLeftDerivedCounit_app_of_leftOrthogonal`: the counit
  of the total left derived functor is an isomorphism at an object of the left orthogonal.

## References

* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C D H : Type*} [Category* C] [Category* D] [Category* H] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (𝒩 : ObjectProperty C) [𝒩.IsTriangulated]

/-- If `F` has a pointwise left derived functor `LF` with respect to `𝒩.trW`, the counit
`(L ⋙ LF).obj P ⟶ F.obj P` is an isomorphism at every object `P` of the left orthogonal of `𝒩`. -/
theorem isIso_totalLeftDerivedCounit_app_of_leftOrthogonal (L : C ⥤ D)
    [L.IsLocalization 𝒩.trW] (F : C ⥤ H) [F.HasPointwiseLeftDerivedFunctor 𝒩.trW]
    {P : C} (hP : 𝒩.leftOrthogonal P) :
    have := F.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor 𝒩.trW
    IsIso ((F.totalLeftDerivedCounit L 𝒩.trW).app P) := by
  have := F.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor 𝒩.trW
  simpa using (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
    (F.totalLeftDerived L 𝒩.trW) (F.totalLeftDerivedCounit L 𝒩.trW) (W := 𝒩.trW)
      (L.obj P)).isIso_π_app_of_isInitial _
    (structuredArrowMkIdIsInitial L P (leftOrthogonal.map_bijective_of_isTriangulated hP L))

end CategoryTheory.ObjectProperty
