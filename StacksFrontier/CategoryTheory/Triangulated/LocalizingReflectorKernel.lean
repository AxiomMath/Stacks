module

public import StacksFrontier.CategoryTheory.Triangulated.LocalizingReflector

/-!
# A reflector annihilates the subcategory it reflects away

Let `C` be a pretriangulated category, let `N : ObjectProperty C` and let `L : C ⥤ C` be an
endofunctor with a unit `η : 𝟭 C ⟶ L` such that every value `L X` is local — lies in `N^⊥` —
and such that precomposition with `η.app X` is a bijection onto the morphisms into a local
object. That is the package step 1 of [Stacks, Tag 09LK] produces, as
`CategoryTheory.ObjectProperty.exists_isTriangulated_reflector_localizingClosure`.

For an object `X` of `N` the value `L X` is then a zero object. The reason is in one line: the
unit `η.app X : X ⟶ L X` goes from an object of `N` into a local object, so it vanishes; hence
`η.app X ≫ 𝟙 = η.app X ≫ 0`, and the injectivity half of the universal property forces
`𝟙 (L X) = 0`.

This is the fact that lets an exact functor built out of `L` descend through a Verdier
quotient: `CategoryTheory.ObjectProperty.trW_isInvertedBy_of_isZero` asks precisely that the
objects being quotiented away go to zero objects.

## Main results

* `CategoryTheory.ObjectProperty.isZero_of_bijective_precomp_unit`: `L X` is a zero object for
  `X` in `N`, from the two properties of the unit at `X` alone.
* `CategoryTheory.ObjectProperty.isZero_reflector_obj`: the same for the reflector
  `N^⊥.reflector` of `StacksFrontier/CategoryTheory/Triangulated/LocalizingReflector.lean`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Category Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **A reflector annihilates the subcategory it reflects away.** Let `N : ObjectProperty C`,
let `L : C ⥤ C` carry a unit `η : 𝟭 C ⟶ L`, and let `X` be an object of `N` whose value `L X`
is local and at which precomposition with `η.app X` is injective on the morphisms into `L X`.
Then `L X` is a zero object. -/
lemma isZero_of_bijective_precomp_unit (N : ObjectProperty C) {L : C ⥤ C} {η : 𝟭 C ⟶ L} {X : C}
    (hLX : N.rightOrthogonal (L.obj X))
    (hbij : Function.Injective fun φ : L.obj X ⟶ L.obj X ↦ η.app X ≫ φ)
    (hX : N X) : IsZero (L.obj X) := by
  refine (IsZero.iff_id_eq_zero _).2 (hbij ?_)
  change η.app X ≫ 𝟙 _ = η.app X ≫ 0
  rw [comp_id, comp_zero]
  exact hLX (η.app X) hX

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **The reflector onto `N^⊥` annihilates `N`.** -/
lemma isZero_reflector_obj (N : ObjectProperty C) [N.rightOrthogonal.ι.IsRightAdjoint] {X : C}
    (hX : N X) : IsZero (N.rightOrthogonal.reflector.obj X) :=
  isZero_of_bijective_precomp_unit N (N.rightOrthogonal.prop_reflector_obj X)
    (N.rightOrthogonal.bijective_precomp_reflectorUnit
      (N.rightOrthogonal.prop_reflector_obj X) X).1 hX

end CategoryTheory.ObjectProperty

end
