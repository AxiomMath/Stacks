module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Assembly
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelationSiblings.ZPowPullback

/-!
# The cube relation for every invertible module on an abelian variety

Let `k` be an algebraically closed field, `A` an abelian variety over `k` and `L` an invertible
`𝒪_A`-module. The cube module of `L` on `A × A × A` is trivial: this is the assembly of
`Cube/Assembly.lean` (steps 2-4 of the cube proof) applied to the openness at the unit
`Stacks.Groupoids.openAtUnitStatement` (`Cube/OpenAtUnit.lean`, step 1). This file records the
result as the property `Stacks.Groupoids.HasCubeRelation A` that the `_of_hasCubeRelation`
siblings of `CubeRelationSiblings/` consume, and as the isomorphism

`m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L`

of [Stacks, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE), with nothing assumed.

## Main results

* `Stacks.Groupoids.hasCubeRelation_of_openAtUnit`: `HasCubeRelation A`, given the statement of
  step 1 of the cube proof.
* `Stacks.Groupoids.nonempty_cubeRelation_of_hasCubeRelation`: `HasCubeRelation A` gives the
  isomorphism `m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L` of
  [Stacks, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE), in the spelling of
  `Stacks.Groupoids.nonempty_cubeRelation`.
* `Stacks.Groupoids.hasCubeRelation_of_isAlgClosed`: `HasCubeRelation A` for every abelian
  variety over an algebraically closed field.
* `Stacks.Groupoids.nonempty_cubeRelation_of_isAlgClosed`: the cube relation of Tag 0BFE for every
  invertible module on an abelian variety over an algebraically closed field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Stacks.SheafOfModules (schemeTensor picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **The cube relation as an isomorphism of invertible modules**, from `HasCubeRelation A`: the
cube class vanishes on the three coordinates of `A × A × A`, and the class of each of the seven
factors is the pullback class along the corresponding coordinate sum. -/
theorem nonempty_cubeRelation_of_hasCubeRelation (hcr : HasCubeRelation A)
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) :
    Nonempty
      (schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (schemeTensor (cubeObj A).left
              (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
              (pullbackOver (cubeProj₁ A) L))
            (pullbackOver (cubeProj₂ A) L))
          (pullbackOver (cubeProj₃ A) L) ≅
        schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
            (pullbackOver (cubeProj₁ A * cubeProj₃ A) L))
          (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)) := by
  have h := hcr L hL (cubeObj A) (cubeProj₁ A) (cubeProj₂ A) (cubeProj₃ A)
  rw [cubeClass_def] at h
  have h₁₂₃ := isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L hL
  have h₁ := isInvertible_pullbackOver (cubeProj₁ A) L hL
  have h₂ := isInvertible_pullbackOver (cubeProj₂ A) L hL
  have h₃ := isInvertible_pullbackOver (cubeProj₃ A) L hL
  have h₁₂ := isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL
  have h₁₃ := isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL
  have h₂₃ := isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL
  refine (Stacks.SheafOfModules.picardClass_eq_iff (cubeObj A).left.presheaf
    (cubeObj A).left.ringCatIsSheaf _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensor₄ (cubeObj A).left _ _ _ _ h₁₂₃ h₁ h₂ h₃)
    (Stacks.SheafOfModules.isInvertible_schemeTensor₃ (cubeObj A).left _ _ _ h₁₂ h₁₃ h₂₃)).mp ?_
  rw [Stacks.SheafOfModules.picardClass_schemeTensor₄ (cubeObj A).left _ _ _ _ h₁₂₃ h₁ h₂ h₃,
    Stacks.SheafOfModules.picardClass_schemeTensor₃ (cubeObj A).left _ _ _ h₁₂ h₁₃ h₂₃]
  rw [← sub_eq_zero, ← h]
  simp only [← Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass]
  abel

variable [IsAlgClosed k]

/-- **The cube relation for every invertible module on `A`**, given the openness of step 1. -/
theorem hasCubeRelation_of_openAtUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (hopen : OpenAtUnitStatement A) : HasCubeRelation A :=
  fun L hL _ f g t => cubeClass_eq_zero_of_openAtUnit L hL hopen f g t

/-- **The cube relation for every invertible module on an abelian variety over an algebraically
closed field**: the cube class `D_L(f, g, t)` vanishes for every invertible `L` and every
`f, g, t : B ⟶ A`. Steps 2-4 (`hasCubeRelation_of_openAtUnit`) applied to step 1
(`openAtUnitStatement`). -/
theorem hasCubeRelation_of_isAlgClosed [AlgebraicGeometry.IsAbelianVariety k A] :
    HasCubeRelation A :=
  hasCubeRelation_of_openAtUnit A (openAtUnitStatement A)

/-- **The cube relation of [Stacks, Tag 0BFE]** for an abelian variety `A` over an algebraically
closed field and an invertible `𝒪_A`-module `L`:

`m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L`

on `A × A × A`, the conclusion of `Stacks.Groupoids.nonempty_cubeRelation` with no hypothesis
beyond the algebraic closedness of `k`. -/
theorem nonempty_cubeRelation_of_isAlgClosed [AlgebraicGeometry.IsAbelianVariety k A]
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) :
    Nonempty
      (schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (schemeTensor (cubeObj A).left
              (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
              (pullbackOver (cubeProj₁ A) L))
            (pullbackOver (cubeProj₂ A) L))
          (pullbackOver (cubeProj₃ A) L) ≅
        schemeTensor (cubeObj A).left
          (schemeTensor (cubeObj A).left
            (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
            (pullbackOver (cubeProj₁ A * cubeProj₃ A) L))
          (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)) :=
  nonempty_cubeRelation_of_hasCubeRelation A (hasCubeRelation_of_isAlgClosed A) L hL

end Stacks.Groupoids

end
