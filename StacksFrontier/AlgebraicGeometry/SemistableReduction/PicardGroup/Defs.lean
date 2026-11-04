module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# The Picard group of a numerical type

The Picard group of a numerical type is the cokernel of the map
`ℤ^n → ℤ^n` whose `(i, j)` entry is `aᵢⱼ / wⱼ`. This file defines it and embeds
it into the cokernel of the intersection matrix itself.

## Main definitions

* `AlgebraicGeometry.NumericalType.picardRelationMatrix` and
  `AlgebraicGeometry.NumericalType.picardRelationMap`: the matrix `aᵢⱼ / wⱼ`
  and the linear map it induces.
* `AlgebraicGeometry.NumericalType.picardGroup`: its cokernel.
* `AlgebraicGeometry.NumericalType.intersectionMatrix`,
  `AlgebraicGeometry.NumericalType.intersectionMap` and
  `AlgebraicGeometry.NumericalType.intersectionCokernel`: the same data for the
  intersection matrix.

## Main results

* `AlgebraicGeometry.NumericalType.picardGroup_embeds_intersectionCokernel`.

## References

* [Stacks Project, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H)
* [Stacks Project, Tag 0CE7](https://stacks.math.columbia.edu/tag/0CE7)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-! ### The Picard group -/

/-- The relation matrix defining the Picard group of a numerical type.  Its row
`j`, column `i` entry is `aᵢⱼ / wⱼ`. -/
public abbrev picardRelationMatrix (T : NumericalType) :
    Matrix (Fin T.componentCount) (Fin T.componentCount) ℤ :=
  fun j i ↦ T.intersection i j / T.weight j

/-- The endomorphism of the finite free integer module whose cokernel is the
Picard group of a numerical type. -/
public def picardRelationMap (T : NumericalType) :
    (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T.componentCount → ℤ) :=
  Matrix.toLin' (picardRelationMatrix T)

/-- The Picard group of a numerical type, namely the cokernel of its relation
matrix. -/
@[stacks 0C7H]
public abbrev picardGroup (T : NumericalType) :=
  (Fin T.componentCount → ℤ) ⧸ LinearMap.range (picardRelationMap T)

/-- The relation associated to the `i`th standard basis vector has `j`th
coordinate `aᵢⱼ / wⱼ`. -/
@[simp]
public theorem picardRelationMap_single (T : NumericalType)
    (i : Fin T.componentCount) :
    picardRelationMap T (Pi.single i 1) =
      fun j ↦ T.intersection i j / T.weight j := by
  ext j
  simp [picardRelationMap]

/-! ### Comparison with the intersection cokernel -/

/-- The integral intersection matrix of a numerical type. -/
public abbrev intersectionMatrix (T : NumericalType) :
    Matrix (Fin T.componentCount) (Fin T.componentCount) ℤ :=
  fun j i ↦ T.intersection i j

/-- The endomorphism of the finite free integer module given by the
intersection matrix. -/
public def intersectionMap (T : NumericalType) :
    (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T.componentCount → ℤ) :=
  Matrix.toLin' (intersectionMatrix T)

/-- The cokernel of the integral intersection matrix of a numerical type. -/
public abbrev intersectionCokernel (T : NumericalType) :=
  (Fin T.componentCount → ℤ) ⧸ LinearMap.range (intersectionMap T)

private def weightMap (T : NumericalType) :
    (Fin T.componentCount → ℤ) →ₗ[ℤ] (Fin T.componentCount → ℤ) where
  toFun x i := T.weight i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_assoc, mul_comm]

private theorem weightMap_injective (T : NumericalType) :
    Function.Injective (weightMap T) :=
  fun _ _ h ↦ funext fun i ↦ mul_left_cancel₀ (ne_of_gt (T.weight_pos i)) (congr_fun h i)

private theorem weightMap_picardRelationMap (T : NumericalType)
    (x : Fin T.componentCount → ℤ) :
    weightMap T (picardRelationMap T x) = intersectionMap T x := by
  funext j
  change T.weight j * (∑ i, (T.intersection i j / T.weight j) * x i) =
    ∑ i, T.intersection i j * x i
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_assoc, Int.mul_ediv_cancel_of_dvd]
  rw [T.intersection_symm]
  exact T.weight_dvd_intersection j i

/-- The Picard group of a numerical type embeds in the cokernel of its
integral intersection matrix. -/
@[stacks 0CE7]
public theorem picardGroup_embeds_intersectionCokernel (T : NumericalType) :
    ∃ f : picardGroup T →+ intersectionCokernel T, Function.Injective f := by
  let f : picardGroup T →ₗ[ℤ] intersectionCokernel T :=
    (LinearMap.range (picardRelationMap T)).mapQ
      (LinearMap.range (intersectionMap T)) (weightMap T) (by
        rintro _ ⟨x, rfl⟩; exact ⟨x, (weightMap_picardRelationMap T x).symm⟩)
  refine ⟨f.toAddMonoidHom, fun x y hxy ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (picardRelationMap T)) x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (picardRelationMap T)) y
  dsimp [f] at hxy
  rw [Submodule.Quotient.eq] at hxy
  obtain ⟨z, hz⟩ := hxy
  exact (Submodule.Quotient.eq (LinearMap.range (picardRelationMap T))).2
    ⟨z, weightMap_injective T (by rw [map_sub, weightMap_picardRelationMap, hz])⟩

end AlgebraicGeometry.NumericalType
