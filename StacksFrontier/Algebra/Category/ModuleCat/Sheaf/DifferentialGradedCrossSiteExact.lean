module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.RestrictScalars

/-!
# A differential graded functor across two ringed sites is exact on homotopy categories

Let `X` and `Y` be ringed sites, let `A` be a sheaf of differential graded algebras on `X` and
`B` one on `Y`. [Stacks, Tag 0FQF] says that a functor of differential graded categories
commuting with the shift induces an exact functor of the homotopy categories, and
`CategoryTheory.DGCategory.DGFunctor.CommShiftB.isTriangulated` is that statement. It cannot be
applied to a functor relating `Mod^dg(A, d)` and `Mod^dg(B, d)` as they stand: a
`CategoryTheory.DGCategory.DGFunctor` relates two differential graded categories over *one*
commutative ring, and these two are linear over the global sections of the two different
structure sheaves.

This file reads both of them over `ℤ`, where they do live over one ring, by
`CategoryTheory.DGCategory.restrictScalars` along `Int.castRingHom`. Restriction of scalars
leaves the objects, the homogeneous morphisms, the differential, the composition and the
identities untouched, so the homotopy category, the cones, the admissible short exact sequences
and the triangulated structure are the ones `Mod^dg(A, d)` already has — and a functor between
the `ℤ`-readings induces a functor between the original homotopy categories, on the nose.

The result is `isTriangulated_onK`: a differential graded functor across the two sites which
satisfies `F(x[1]) = F(x)[1]` induces an **exact** functor
`K(Mod(A, d)) ⥤ K(Mod(B, d))` of triangulated categories, for the triangulated structures of
Tag 0FS7 that this development already puts on those homotopy categories.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.dgCategoryOverInt` is the differential graded category
  of right differential graded `A`-modules, read over `ℤ`.
* `SheafOfModules.DifferentialGradedModule.coneSituationOverInt` is its cone situation.

## Main results

* `SheafOfModules.DifferentialGradedModule.isStrictKShift_coneSituationOverInt`: the translation
  of the homotopy category carried by that cone situation is strict, which is what Tag 0FQF asks
  of it.
* `SheafOfModules.DifferentialGradedModule.isTriangulated_onK`: **a differential graded functor
  across two ringed sites commuting with the shift is exact on the homotopy categories.**
* `SheafOfModules.DifferentialGradedModule.commShift_onK`: and it commutes with the
  translations.

## Implementation notes

Reading over `ℤ` rather than along a ring homomorphism between the two global-section rings is
deliberate: it needs no comparison of the two rings at all, and `ℤ`-linearity of a differential
graded functor is additivity, which it has by its own axiom. The restriction is only ever used
to *state* the functor; nothing about the differential graded categories changes, which is why
the conclusion below is about the original homotopy categories and their original instances.

The strictness hypothesis is discharged from
`SheafOfModules.DifferentialGradedModule.isStrictKShift_shiftAxiomB` through
`CategoryTheory.DGCategory.ShiftAxiomB.isStrictKShift_restrictScalars`, so the cheap form of
Tag 0FQF applies and no strictification step intervenes: the translation in the conclusion is
the one `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instHasShift` is lifted from.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The ring homomorphism `ℤ ⟶ Γ(O_X)` through which the differential graded category of right
differential graded `A`-modules is read over `ℤ`. -/
noncomputable abbrev intToGlobalSections : ℤ →+* (limit X.O.obj : CommRingCat.{u}) :=
  Int.castRingHom _

/-- **The differential graded category of right differential graded `A`-modules, read over
`ℤ`.** Nothing but the module structure on the homogeneous morphisms changes, so its homotopy
category, its cocycles and its cones are those of
`SheafOfModules.DifferentialGradedModule.dgCategoryData`.

Marked `instance_reducible` so that the preadditive, shift and pretriangulated instances already
attached to `K(Mod(A, d))` are found for it. -/
@[instance_reducible]
noncomputable def dgCategoryOverInt : DGCategory.{max u w, max u v (w + 1)} ℤ :=
  DGCategory.restrictScalars (intToGlobalSections (X := X))
    (dgCategoryData.{u, v, w} A).category

/-- The homotopy category of the `ℤ`-reading is the homotopy category of right differential
graded `A`-modules. -/
theorem dgCategoryOverInt_K :
    (dgCategoryOverInt.{u, v, w} A).K = (dgCategoryData.{u, v, w} A).category.K :=
  rfl

/-- **The cone situation of the `ℤ`-reading**: the cones, their admissible short exact sequences
and their connecting arrows are those of
`SheafOfModules.DifferentialGradedModule.dgConeSituation`. -/
noncomputable def coneSituationOverInt : DGCategory.ConeSituation (dgCategoryOverInt.{u, v, w} A) :=
  (dgConeSituation.{u, v, w} A).restrictScalars (intToGlobalSections (X := X))

/-- **The translation of the homotopy category carried by the `ℤ`-reading is strict**, which is
the hypothesis Tag 0FQF puts on the two axiom (B) data. It is the strictness of the sheaf axiom
(B) datum, restriction of scalars leaving the translation untouched. -/
theorem isStrictKShift_coneSituationOverInt :
    (coneSituationOverInt.{u, v, w} A).shift.IsStrictKShift := by
  refine DGCategory.ShiftAxiomB.isStrictKShift_restrictScalars _ ?_
  rw [dgConeSituation_shift.{u, v, w} A]
  exact isStrictKShift_shiftAxiomB A

variable {Y : AlgebraicGeometry.RingedSite.{u, u, u}}
  (B : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **Tag 0FQF across two ringed sites.** A functor of differential graded categories from right
differential graded `A`-modules on `X` to right differential graded `B`-modules on `Y` — stated
between their `ℤ`-readings, which is the only way a `DGFunctor` can relate them — which
satisfies `F(x[1]) = F(x)[1]` induces a functor commuting with the translations of the two
homotopy categories.

The translations are the ones axiom (B) carries, which are those of
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instHasShift` by
`SheafOfModules.DifferentialGradedModule.dgConeSituation_shift`. -/
@[instance_reducible]
noncomputable def commShift_onK
    {F : DGCategory.DGFunctor (dgCategoryOverInt.{u, v, w} A) (dgCategoryOverInt.{u, v, w} B)}
    (hF : F.CommShiftB (coneSituationOverInt.{u, v, w} A).shift
      (coneSituationOverInt.{u, v, w} B).shift) :
    letI : HasShift (dgCategoryOverInt.{u, v, w} A).K ℤ :=
      (coneSituationOverInt.{u, v, w} A).shift.kShift
    letI : HasShift (dgCategoryOverInt.{u, v, w} B).K ℤ :=
      (coneSituationOverInt.{u, v, w} B).shift.kShift
    F.onK.CommShift ℤ :=
  (DGCategory.DGFunctor.CommShiftK.ofCommShiftB hF
    (isStrictKShift_coneSituationOverInt.{u, v, w} A)
    (isStrictKShift_coneSituationOverInt.{u, v, w} B)).commShift

/-- **A differential graded functor across two ringed sites commuting with the shift is exact on
the homotopy categories**, which is [Stacks, Tag 0FQF] in the generality the derived pullback
and the derived pushforward of a sheaf of differential graded modules need. The triangulated
structures are the ones of [Stacks, Tag 0FS7]: restriction of scalars to `ℤ` changes neither the
homotopy categories, nor their cones, nor their admissible short exact sequences, so the cone
situation here is the one that puts the triangulated structure on `K(Mod(A, d))`. -/
@[stacks 0FQF "the induced functor on homotopy categories is exact, across two ringed sites"]
theorem isTriangulated_onK
    {F : DGCategory.DGFunctor (dgCategoryOverInt.{u, v, w} A) (dgCategoryOverInt.{u, v, w} B)}
    (hF : F.CommShiftB (coneSituationOverInt.{u, v, w} A).shift
      (coneSituationOverInt.{u, v, w} B).shift) :
    letI : Preadditive (dgCategoryOverInt.{u, v, w} A).K :=
      DGCategory.homotopyPreadditive _
    letI : HasZeroObject (dgCategoryOverInt.{u, v, w} A).K :=
      DGCategory.homotopyHasZeroObject _ (coneSituationOverInt.{u, v, w} A)
    letI : HasShift (dgCategoryOverInt.{u, v, w} A).K ℤ :=
      (coneSituationOverInt.{u, v, w} A).shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor (dgCategoryOverInt.{u, v, w} A).K n).Additive := fun n =>
      DGCategory.homotopyShiftAdditive _ (coneSituationOverInt.{u, v, w} A) n
    letI : Pretriangulated (dgCategoryOverInt.{u, v, w} A).K :=
      DGCategory.homotopyPretriangulated _ (coneSituationOverInt.{u, v, w} A)
    letI : Preadditive (dgCategoryOverInt.{u, v, w} B).K :=
      DGCategory.homotopyPreadditive _
    letI : HasZeroObject (dgCategoryOverInt.{u, v, w} B).K :=
      DGCategory.homotopyHasZeroObject _ (coneSituationOverInt.{u, v, w} B)
    letI : HasShift (dgCategoryOverInt.{u, v, w} B).K ℤ :=
      (coneSituationOverInt.{u, v, w} B).shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor (dgCategoryOverInt.{u, v, w} B).K n).Additive := fun n =>
      DGCategory.homotopyShiftAdditive _ (coneSituationOverInt.{u, v, w} B) n
    letI : Pretriangulated (dgCategoryOverInt.{u, v, w} B).K :=
      DGCategory.homotopyPretriangulated _ (coneSituationOverInt.{u, v, w} B)
    letI : F.onK.CommShift ℤ := commShift_onK A B hF
    F.onK.IsTriangulated :=
  DGCategory.DGFunctor.CommShiftB.isTriangulated _ _
    (isStrictKShift_coneSituationOverInt.{u, v, w} A)
    (isStrictKShift_coneSituationOverInt.{u, v, w} B) hF

end SheafOfModules.DifferentialGradedModule

end
