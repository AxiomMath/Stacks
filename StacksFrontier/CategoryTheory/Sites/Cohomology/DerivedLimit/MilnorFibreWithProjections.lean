module

public import StacksFrontier.CategoryTheory.Triangulated.MilnorFibreBaseChange
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The strict Milnor fibre as a derived limit with projections

`Stacks.MilnorTower.exists_distTriang_Q_milnorObj` of
`CategoryTheory/Triangulated/MilnorFibreDerivedLimit.lean` states the Milnor triangle of a tower
of cochain complexes with its structural map written out as the product of the images of the
projections. This file records that this is exactly
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` at the named object and the named
projections, and that the canonical comparison map out of an augmented complex is the lift its
`exists_lift` produces.

The two statements are separated only to keep the ring-theoretic import of
`Homology/DerivedComplete/NoetherianCompleteIdealPowers.lean`, where the predicate happens to
live, out of the category-theoretic development.

## Main results

* `Stacks.MilnorTower.isDerivedLimitWithProjections_Q_milnorObj` — the image in `D(A)` of the
  strict Milnor fibre of a tower of cochain complexes is a derived limit of the tower through
  the images of the projections.
* `Stacks.MilnorTower.exists_isDerivedLimitWithProjections_augmented` — the form a consumer
  with a cone in hand uses: the comparison map is named, and is the canonical map of the
  augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.MilnorTower

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasProductsOfShape ℕ A] [HasProductsOfShape ℕ (DerivedCategory A)]

/-- **The strict Milnor fibre of a tower of cochain complexes is a derived limit of the tower
through the images of its projections.** Both the object and the projections are formulas in
the tower; only the connecting map of the presenting triangle is existentially quantified, and
`NoetherianAdicCompletion.IsDerivedLimitWithProjections` quantifies over nothing else. -/
public theorem isDerivedLimitWithProjections_Q_milnorObj (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (milnorObj F))
      (fun n : ℕ ↦ DerivedCategory.Q.map (proj F n)) :=
  exists_distTriang_Q_milnorObj F hpc

/-- **The canonical comparison map of an augmented complex, with the presentation it compares
against.** A complex with a compatible family of maps to the terms of a tower has a named map
into the named derived limit of the tower whose composites with the named projections are the
given maps. Nothing here is chosen: contrast
`Stacks.InverseSystem.exists_isDerivedLimit_comparison`, whose limit object, structural map and
comparison map are all existentially bound, so that no two instances of it can be compared. -/
public theorem exists_isDerivedLimitWithProjections_augmented
    {F : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : TowerAugmentation F)
    (hpc : IsIso (piComparison DerivedCategory.Q fun k : ℕ ↦ F.obj ⟨k⟩)) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (milnorObj F))
        (fun n : ℕ ↦ DerivedCategory.Q.map (proj F n)) ∧
      ∀ n : ℕ, DerivedCategory.Q.map a.augmentationMap ≫ DerivedCategory.Q.map (proj F n) =
        DerivedCategory.Q.map (a.app n) :=
  ⟨isDerivedLimitWithProjections_Q_milnorObj F hpc, Q_augmentationMap_proj a⟩

end Stacks.MilnorTower

end
