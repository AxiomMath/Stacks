module

public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic

/-!
# The recursions defining the comparison of the two tensor-power families

The defining equations of the recursions `Stacks.PowerFamilyBridge.natIso` and
`Stacks.PowerFamilyBridge.negIso`, which compare the tensor powers
`Stacks.SheafOfModules.TensorPower.tensorPower` of [Stacks, Tag 01CU] of an invertible sheaf of
modules `L` with the tensor powers `AlgebraicGeometry.SheafOfModules.tensorPow` in nonnegative and
nonpositive degree, and the integer comparison `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`
in terms of the two.

## Main results

* `Stacks.PowerFamilyBridge.natIso_zero` and `Stacks.PowerFamilyBridge.natIso_succ`: the
  recursion for the nonnegative half; `natIso (k + 1)` is `natIso k` whiskered by `L`, read
  between the successor comparisons `tensorPowerSuccIso` and `tensorPowSuccIso` of the two
  families.
* `Stacks.PowerFamilyBridge.negIso_zero` and `Stacks.PowerFamilyBridge.negIso_succ`: the
  recursion for the nonpositive half, whose step is a preimage under the fully faithful functor
  `- ⊗ L`.
* `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow_natCast` and
  `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow_negSucc`: the integer comparison in terms of
  the two halves, one clause for each constructor of `Int`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.PowerFamilyBridge

attribute [local implicit_reducible] structureSheaf
  Stacks.SheafOfModules.TensorSheafification.sheafify
  Stacks.SheafOfModules.Tensor.sheafTensor

attribute [local irreducible] PresheafOfModules.sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.TensorPower
open Stacks.InverseSection (tensorPowReindexIso)

variable [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-! ### The nonnegative half -/

/-- **The comparison in degree zero.** Both families are the structure sheaf there, and the
comparison is the composite of the two identifications. -/
theorem natIso_zero :
    natIso 𝒪 h𝒪 L 0 =
      tensorPowerReindex 𝒪 h𝒪 L (show ((0 : ℕ) : ℤ) = 0 by norm_num) ≪≫
        eqToIso (tensorPower_zero 𝒪 h𝒪 L) ≪≫ (tensorPowZeroIso 𝒪 h𝒪 L).symm ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num) :=
  rfl

/-- **The comparison is compatible with one more multiplication by `L`.** The step of the
recursion: `natIso (k + 1)` is `natIso k` whiskered on the right by `L`, read between
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` and
`AlgebraicGeometry.SheafOfModules.tensorPowSuccIso`, the successor comparisons of the two
families. -/
theorem natIso_succ (k : ℕ) :
    natIso 𝒪 h𝒪 L (k + 1) =
      tensorPowerReindex 𝒪 h𝒪 L (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowerSuccIso 𝒪 h𝒪 L (k : ℤ)).symm ≪≫
        (tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (k : ℤ)) L).symm ≪≫
        whiskerRightIso (natIso 𝒪 h𝒪 L k) L ≪≫
        (tensorPowSuccIso 𝒪 h𝒪 L (k : ℤ)).symm ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring) :=
  rfl

/-! ### The nonpositive half -/

/-- The comparison in degree zero, in the spelling the nonpositive half is indexed by. -/
theorem negIso_zero :
    negIso 𝒪 h𝒪 L 0 =
      tensorPowerReindex 𝒪 h𝒪 L (show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by norm_num) ≪≫
        natIso 𝒪 h𝒪 L 0 ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) by norm_num) :=
  rfl

/-- **The step down to the next negative degree.** The comparison in degree `-(k + 1)` is the
`CategoryTheory.Functor.preimageIso`, under the fully faithful functor `- ⊗ L`, of the comparison
in degree `-k`, read between the successor comparisons of the two families. -/
theorem negIso_succ (k : ℕ) :
    negIso 𝒪 h𝒪 L (k + 1) =
      tensorPowerReindex 𝒪 h𝒪 L
          (show -((k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) by push_cast; ring) ≪≫
        Functor.preimageIso
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).flip.obj L)
          (tensorPowerSuccIso 𝒪 h𝒪 L (-((k : ℤ) + 1)) ≪≫
            tensorPowerReindex 𝒪 h𝒪 L (show -((k : ℤ) + 1) + 1 = -(k : ℤ) by ring) ≪≫
            negIso 𝒪 h𝒪 L k ≪≫
            tensorPowReindexIso 𝒪 h𝒪 L (show -(k : ℤ) = -((k : ℤ) + 1) + 1 by ring) ≪≫
            tensorPowSuccIso 𝒪 h𝒪 L (-((k : ℤ) + 1)) ≪≫
            tensorIso 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (-((k : ℤ) + 1))) L) ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring) :=
  rfl

/-! ### The integer comparison in terms of the two halves -/

/-- In a nonnegative degree the integer comparison is the nonnegative half. -/
theorem tensorPowerIsoTensorPow_natCast (k : ℕ) :
    tensorPowerIsoTensorPow 𝒪 h𝒪 L ((k : ℕ) : ℤ) =
      tensorPowerReindex 𝒪 h𝒪 L (show (Int.ofNat k) = ((k : ℕ) : ℤ) by rfl) ≪≫
        natIso 𝒪 h𝒪 L k ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show ((k : ℕ) : ℤ) = (Int.ofNat k) by rfl) :=
  rfl

/-- In a negative degree the integer comparison is the nonpositive half. -/
theorem tensorPowerIsoTensorPow_negSucc (k : ℕ) :
    tensorPowerIsoTensorPow 𝒪 h𝒪 L (Int.negSucc k) =
      tensorPowerReindex 𝒪 h𝒪 L
          (show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) by rw [Int.negSucc_eq]; push_cast; ring) ≪≫
        negIso 𝒪 h𝒪 L (k + 1) ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show -((k + 1 : ℕ) : ℤ) = (Int.negSucc k) by rw [Int.negSucc_eq]; push_cast; ring) :=
  rfl

end Stacks.PowerFamilyBridge

end
