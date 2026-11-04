module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage

/-!
# Exact functors carrying bounded objects into `D_B`

Let `R : D(A) ⥤ D(A')` be an exact functor between derived categories of abelian categories and
let `B ⊆ A`, `B' ⊆ A'` be weak Serre subcategories. If `R` carries every object of `B`, placed in
degree zero, into the subcategory `D_{B'}(A')` of objects all of whose cohomology objects lie in
`B'`, then it carries every bounded object of `D_B(A)` into `D_{B'}(A')`.

## Main results

* `DerivedCategoryB.derivedCategoryB_inverseImage_isTriangulatedClosed₂`: the objects carried by
  an exact functor into `D_{B'}(A')` form a strictly full subcategory stable under the shift and
  closed under extensions.
* `DerivedCategoryB.derivedCategoryB_map_obj_of_isGE_of_isLE`: **the dévissage**.

## Implementation notes

The objects carried by `R` into `D_{B'}(A')` are the preimage `(derivedCategoryB B').inverseImage
R`, a strictly full subcategory of `D(A)` stable under the shift and containing the middle vertex
of a distinguished triangle whose two other vertices it contains, because `R` is exact and
`D_{B'}(A')` is a triangulated subcategory (Stacks 06UQ). The window induction
`CategoryTheory.ObjectProperty.prop_of_isGE_of_isLE` then reduces the statement to objects
concentrated in one degree.

## References

* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u v' u'

namespace DerivedCategoryB

open DerivedCategory ObjectProperty WeakSerre

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {A' : Type u'} [Category.{v'} A'] [Abelian A'] [HasDerivedCategory A']
  (R : DerivedCategory A ⥤ DerivedCategory A') (B' : ObjectProperty A') (hB' : IsWeakSerre B')

include hB'

/-- The objects carried by `R` into `D_{B'}` form a strictly full subcategory. -/
theorem derivedCategoryB_inverseImage_isClosedUnderIsomorphisms :
    ((derivedCategoryB B').inverseImage R).IsClosedUnderIsomorphisms := by
  have := derivedCategoryB_isClosedUnderIsomorphisms B' hB'
  infer_instance

/-- The objects carried by `R` into `D_{B'}` are stable under the shift. -/
theorem derivedCategoryB_inverseImage_isStableUnderShift [R.CommShift ℤ] :
    ((derivedCategoryB B').inverseImage R).IsStableUnderShift ℤ := by
  have := derivedCategoryB_isStableUnderShift B' hB'
  refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
  exact (derivedCategoryB_isClosedUnderIsomorphisms B' hB').of_iso
    ((R.commShiftIso a).app K).symm ((derivedCategoryB B').le_shift a _ hK)

/-- The objects carried by `R` into `D_{B'}` contain the middle vertex of a distinguished triangle
whose other two vertices they contain. -/
theorem derivedCategoryB_inverseImage_isTriangulatedClosed₂ [R.CommShift ℤ] [R.IsTriangulated] :
    ((derivedCategoryB B').inverseImage R).IsTriangulatedClosed₂ := by
  have := derivedCategoryB_isClosedUnderIsomorphisms B' hB'
  have := derivedCategoryB_isTriangulated B' hB'
  have := derivedCategoryB_inverseImage_isClosedUnderIsomorphisms R B' hB'
  refine IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ ↦ ?_)
  exact (derivedCategoryB B').ext_of_isTriangulatedClosed₂ (R.mapTriangle.obj T)
    (R.map_distinguished T hT) h₁ h₃

/-- **An exact functor carries a bounded object of `D_B(A)` into `D_{B'}(A')` as soon as it
carries every object of `B`, placed in degree zero, there.** -/
theorem derivedCategoryB_map_obj_of_isGE_of_isLE [R.CommShift ℤ] [R.IsTriangulated]
    (B : ObjectProperty A)
    (hR : ∀ M : A, B M → derivedCategoryB B' (R.obj ((singleFunctor A 0).obj M)))
    (K : DerivedCategory A) (a b : ℤ) [K.IsGE a] [K.IsLE b] (hK : derivedCategoryB B K) :
    derivedCategoryB B' (R.obj K) := by
  have := derivedCategoryB_inverseImage_isClosedUnderIsomorphisms R B' hB'
  have := derivedCategoryB_inverseImage_isStableUnderShift R B' hB'
  have := derivedCategoryB_inverseImage_isTriangulatedClosed₂ R B' hB'
  have : K.IsLE (a + ((b - a).toNat : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_le K b _ (by omega)
  exact prop_of_isGE_of_isLE ((derivedCategoryB B').inverseImage R) a (b - a).toNat K
    inferInstance this (fun q _ _ ↦ hR _ (hK q))

end DerivedCategoryB
