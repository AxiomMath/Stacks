module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequenceSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap

/-!
# The kernel inclusion of [Stacks, Tag 0C4T] carries the multiplication of ideal sheaves

Let `D` be an effective Cartier divisor on a scheme `X`, let `i : E ⟶ X` be the inclusion of the
closed subscheme it cuts out, and let

`Kₙ = Stacks.Divisors.thickeningKernelMap D n : i_* i^* ℐ_{Dⁿ⁺¹} ⟶ 𝒪_{Dⁿ⁺²}`

be the kernel inclusion of the sequence of [Stacks, Tag 0C4T] at the thickenings of `D`. This file
proves that `Kₙ` carries the canonical multiplication of ideal sheaves
`Stacks.Divisors.idealTensorMul` to the ring multiplication of the structure sheaf of the
thickening, in the bidegree `(d, 1)`: multiplying a section of `ℐ_{Dᵈ}` by a section of `ℐ_D`,
reading the product in `ℐ_{Dᵈ⁺¹}` and carrying it through the unit of `i^* ⊣ i_*` and the kernel
inclusion `K_d` is multiplying the two ambient functions in `𝒪_X` and projecting to `𝒪_{Dᵈ⁺²}`.

The unit `ℐ_{Dᵈ⁺¹} ⟶ i_* i^* ℐ_{Dᵈ⁺¹}` is an epimorphism of sheaves
(`Stacks.ClosedImmersion.epi_unit_app`) but in general not surjective on `Γ(X, -)`. The statement
is therefore an equality of morphisms out of the tensor product
`Stacks.Divisors.idealTensorProd (D ^ d) D`, evaluated afterwards on sections over an open; on
sections it describes `K_d` on the image of the unit.

## Main results

* `Stacks.Divisors.unit_comp_thickeningKernelMap`: the characteristic property of the kernel
  inclusion, at the thickenings of `D`.
* `Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap`: the multiplicativity in
  bidegree `(d, 1)`, as an equality of morphisms out of a tensor product.
* `Stacks.Divisors.app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul` and
  `Stacks.Divisors.app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul_mul`: the same on
  sections over an open, on a local pure tensor, with the right-hand side as the product of the two
  ambient functions and as the product of their two images in the ring of functions on the
  thickening.

## Implementation notes

Each transport along an equality of ideal sheaves is taken as a hypothesis and discharged by
`subst`, rather than by rewriting an `eqToHom`. The target of `Stacks.Divisors.sumKernelMapOf` is
spelled `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeStructureSheaf`, in `X.Modules`,
while the target of `Stacks.IdealSheafSequence.divisorQuotientMap` is spelled
`(RingedSpaceModuleAdjunction.modulePushforward _).obj (SheafOfModules.unit _)`. The two are equal
by `rfl` but not syntactically equal, so an equation mixing them is not type-correct at `implicit`
transparency and a `rw` whose motive crosses the two fails; reassociations are therefore terms, not
rewrites.

## References

* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction (modulePullbackPushforwardAdjunction)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open scoped TensorProduct

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- Transporting the ideal sheaf along an equality of ideal sheaves commutes with the inclusion
into the structure sheaf. -/
lemma eqToHom_comp_idealInclusion {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg negativeTwist h) ≫ idealInclusion J = idealInclusion I := by
  subst h
  simp

/-- For an ideal sheaf `D'` equal to `C · D`, precomposing `Stacks.Divisors.sumKernelMapOf` with
the unit of `i^* ⊣ i_*` at `ℐ_D` gives the inclusion of `ℐ_D` into `𝒪_X` followed by the projection
to the structure sheaf of `D'`. -/
lemma unit_comp_sumKernelMapOf (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') :
    (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app
          (negativeTwist D) ≫ sumKernelMapOf D C D' hD hsum =
      idealInclusion D ≫ Stacks.IdealSheafSequence.divisorQuotientMap D' := by
  subst hsum
  rw [sumKernelMapOf_rfl]
  exact unit_comp_sumKernelMap D C hD

/-- Precomposing `Stacks.Divisors.thickeningKernelMap` with the unit of `i^* ⊣ i_*` at `ℐ_{Dⁿ⁺¹}`
gives the inclusion of `ℐ_{Dⁿ⁺¹}` into `𝒪_X` followed by the projection to `𝒪_{Dⁿ⁺²}`. -/
lemma unit_comp_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    (modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
          (negativeTwist (D ^ (n + 1))) ≫ thickeningKernelMap D n =
      idealInclusion (D ^ (n + 1)) ≫
        Stacks.IdealSheafSequence.divisorQuotientMap (D ^ (n + 2)) :=
  unit_comp_sumKernelMapOf (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance (mul_pow_succ_eq D n)

/-- `Stacks.Divisors.unit_comp_thickeningKernelMap` read at `Dᵈ · D` rather than at `Dᵈ⁺¹`. -/
lemma eqToHom_comp_unit_comp_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (d : ℕ) :
    eqToHom (congrArg negativeTwist (pow_succ D d).symm) ≫
        ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
            (negativeTwist (D ^ (d + 1))) ≫ thickeningKernelMap D d) =
      idealInclusion (D ^ d * D) ≫
        Stacks.IdealSheafSequence.divisorQuotientMap (D ^ (d + 2)) := by
  rw [unit_comp_thickeningKernelMap]
  exact (reassoc_of% eqToHom_comp_idealInclusion (pow_succ D d).symm) _

/-- The kernel inclusion of [Stacks, Tag 0C4T] carries the canonical multiplication of ideal
sheaves to the ring multiplication of the functions on the thickening, in the bidegree `(d, 1)`.

Multiplying `ℐ_{Dᵈ} ⊗ ℐ_D ⟶ ℐ_{Dᵈ⁺¹}` by `Stacks.Divisors.idealTensorMul`, mapping to the graded
piece by the unit of `i^* ⊣ i_*` and including into `𝒪_{Dᵈ⁺²}` by
`Stacks.Divisors.thickeningKernelMap` is multiplying the two sections inside `𝒪_X` by
`Stacks.Divisors.idealTensorToUnit` and projecting to `𝒪_{Dᵈ⁺²}`. -/
theorem idealTensorMul_comp_unit_comp_thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (d : ℕ) :
    idealTensorMul (D ^ d) D ≫ eqToHom (congrArg negativeTwist (pow_succ D d).symm) ≫
        ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
            (negativeTwist (D ^ (d + 1))) ≫ thickeningKernelMap D d) =
      idealTensorToUnit (D ^ d) D ≫
        Stacks.IdealSheafSequence.divisorQuotientMap (D ^ (d + 2)) := by
  refine (whisker_eq _ (eqToHom_comp_unit_comp_thickeningKernelMap D d)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (eq_whisker (idealTensorMul_comp_idealInclusion (D ^ d) D) _)

/-- The value of the left-hand composite of
`Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap` on the pure tensor of a section
of `ℐ_{Dᵈ}` and a section of `ℐ_D` is the image in `𝒪_{Dᵈ⁺²}` of the product of the two ambient
functions they represent. -/
theorem app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (d : ℕ) (U : X.Opens)
    (y : (idealSheafOfModules (D ^ d)).val.obj (op U))
    (m : (idealSheafOfModules D).val.obj (op U)) :
    ((idealTensorMul (D ^ d) D ≫ eqToHom (congrArg negativeTwist (pow_succ D d).symm) ≫
            ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
              (negativeTwist (D ^ (d + 1))) ≫ thickeningKernelMap D d)).val.app (op U)).hom
        (toTensorSheafSection X.toRingedSpace (idealSheafOfModules (D ^ d))
          (idealSheafOfModules D) (op U) (y ⊗ₜ m)) =
      (D ^ (d + 2)).subschemeι.app U
        (idealSheafSection (D ^ d) y * idealSheafSection D m) := by
  rw [idealTensorMul_comp_unit_comp_thickeningKernelMap]
  exact congrArg ((D ^ (d + 2)).subschemeι.app U)
    (idealTensorToUnit_app_tmul (D ^ d) D U y m)

/-- The value of the left-hand composite of
`Stacks.Divisors.idealTensorMul_comp_unit_comp_thickeningKernelMap` on the pure tensor of a section
of `ℐ_{Dᵈ}` and a section of `ℐ_D` is the product of the images in `𝒪_{Dᵈ⁺²}` of the two ambient
functions they represent. -/
theorem app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul_mul (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (d : ℕ) (U : X.Opens)
    (y : (idealSheafOfModules (D ^ d)).val.obj (op U))
    (m : (idealSheafOfModules D).val.obj (op U)) :
    ((idealTensorMul (D ^ d) D ≫ eqToHom (congrArg negativeTwist (pow_succ D d).symm) ≫
            ((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
              (negativeTwist (D ^ (d + 1))) ≫ thickeningKernelMap D d)).val.app (op U)).hom
        (toTensorSheafSection X.toRingedSpace (idealSheafOfModules (D ^ d))
          (idealSheafOfModules D) (op U) (y ⊗ₜ m)) =
      (D ^ (d + 2)).subschemeι.app U (idealSheafSection (D ^ d) y) *
        (D ^ (d + 2)).subschemeι.app U (idealSheafSection D m) := by
  rw [app_idealTensorMul_comp_unit_comp_thickeningKernelMap_tmul]
  exact ((D ^ (d + 2)).subschemeι.app U).hom.map_mul _ _

end Stacks.Divisors

end
