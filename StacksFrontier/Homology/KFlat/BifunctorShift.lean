module

public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# The category of K-flat models carries a shift

Let `F : A ⥤ B ⥤ D` be an additive bifunctor between abelian categories whose total complexes
exist, and let `kFlatObjects F` be the object property of `K(B)` cutting out the complexes which
are K-flat for `F` (`CochainComplex.KFlatBifunctor.kFlatObjects`).  The functor `kFlatQ F` from
the full subcategory of K-flat models to `D(B)` is a localization at the quasi-isomorphisms between
K-flat objects (Stacks Tag 06YS).

This file registers `CategoryTheory.ObjectProperty.IsStableUnderShift ℤ` for `kFlatObjects F`, in
both variables, so that Mathlib's `CategoryTheory.ObjectProperty.hasShift` puts a shift on the
categories of K-flat models, and records the consequences that then follow by instance search
alone.

## Main results

* `CochainComplex.KFlatBifunctor.kFlatObjects_isStableUnderShift`: **a shift of a complex which
  is K-flat for `F` is again K-flat for `F`**, as an instance of
  `CategoryTheory.ObjectProperty.IsStableUnderShift ℤ`.
* `CochainComplex.KFlatBifunctor.kFlatObjectsLeft_isStableUnderShift`: the same in the left
  variable.

## Implementation notes

Shift stability is one of the parents of `CategoryTheory.ObjectProperty.IsTriangulated`, so the
instance is the projection out of `kFlatObjects_isTriangulated`. As that is a theorem, not an
instance, the projection is taken by instance search after a `have`, rather than by naming
`IsTriangulated.toIsStableUnderShift`, so it does not depend on the order of the parents.

The instances live in a separate module: `kFlatObjects` is an `abbrev` unfolding to a lambda, so an
instance whose subject is `kFlatObjects F` is keyed in the discrimination tree no more precisely
than `IsStableUnderShift _ ℤ` and is tried for *every* object property with a shift. Keeping them
out of `StacksFrontier.Homology.KFlat.BifunctorLocalization` confines that cost to the modules that
need a shift on the models category.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **A shift of a complex which is K-flat for `F` is again K-flat for `F`.**  This is the
`CategoryTheory.ObjectProperty.IsStableUnderShift ℤ` parent of `kFlatObjects_isTriangulated`. -/
instance kFlatObjects_isStableUnderShift :
    (kFlatObjects F).IsStableUnderShift ℤ := by
  have := kFlatObjects_isTriangulated F
  infer_instance

/-- **A shift of a complex which is left K-flat for `F` is again left K-flat for `F`**, the
mirror of `kFlatObjects_isStableUnderShift` in the first variable of `F`. -/
instance kFlatObjectsLeft_isStableUnderShift :
    (kFlatObjectsLeft F).IsStableUnderShift ℤ := by
  have := kFlatObjectsLeft_isTriangulated F
  infer_instance

/-! ### The shift package that Mathlib then supplies

The `example`s record that nothing beyond the two instances above is needed: the shift on the
models category, the commutation of the inclusion with it, and the commutation of the K-flat
localization functor with it are all found by instance search. -/

example : HasShift (kFlatObjects F).FullSubcategory ℤ := inferInstance

example : (kFlatObjects F).ι.CommShift ℤ := inferInstance

example : HasShift (kFlatObjectsLeft F).FullSubcategory ℤ := inferInstance

example : (kFlatObjectsLeft F).ι.CommShift ℤ := inferInstance

example [HasDerivedCategory B] : (kFlatQ F).CommShift ℤ := inferInstance

example [HasDerivedCategory A] : (kFlatQLeft F).CommShift ℤ := inferInstance

end CochainComplex.KFlatBifunctor

end
