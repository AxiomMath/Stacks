module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# Invertibility of tensor products and of integer tensor powers

Ampleness of an invertible sheaf `L` on a scheme (Tag 01PS) is a condition on sections of the
tensor powers `L^{⊗ n}` for `n ≥ 1`, and an ample *family* (Tag 0FXR) is a condition on the
tensor powers of the members of the family. Both only make sense once each `L^{⊗ n}` is itself
known to be invertible, since the nonvanishing locus of a section (Tag 01CY) is defined for
invertible sheaves. This file supplies that input.

The two steps are part (1) of Tag 01CT — a tensor product of invertible sheaves is invertible
— and an induction over `ℤ` using the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of
Tag 01CU. The descending half of the induction uses that a module sheaf whose tensor product
with something is invertible is itself invertible, which is where the tensor-inverse
characterisation of Tag 0B8K enters.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible` is Tag 01CT part (1).
* `Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_isInvertible`: if `M ⊗ N` is
  invertible then so is `M`.
* `Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`: every integer tensor power of
  an invertible sheaf is invertible.

## Implementation notes

The native sheaf tensor bifunctor applied to `M` and `N` sheafifies
`PresheafOfModules.tensorObj M.val N.val`. This is the tensor product used by the
tensor-power successor isomorphism of
`StacksFrontier/AlgebraicGeometry/Divisors/TensorPower.lean`, so that isomorphism can be fed
directly to the lemmas stated here.

Part (2) of Tag 01CT — that the dual sheaf is invertible and that the evaluation map
`L ⊗ SheafHom(L, 𝒪) → 𝒪` is an isomorphism — is not here; it needs the internal `SheafHom` of
Tag 01CB and is independent of everything in this file.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  isInvertible_iff_tensorLeftFunctor_isEquivalence)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 01CT**, part (1). The tensor product of two invertible sheaves of
modules is invertible: tensoring by it is the composite of the two tensor functors. -/
@[stacks 01CT "tensor_invertible", instance]
theorem tensorProduct_isInvertible
    (L N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [IsInvertible O hO L] [IsInvertible O hO N] :
    IsInvertible O hO (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N) :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO _).mpr
    (Functor.isEquivalence_of_iso (Stacks.SheafOfModules.tensorLeftFunctorObjIso O hO L N).symm)

/-- A tensor factor of an invertible sheaf is invertible: if `M ⊗ N` has a tensor inverse `P`
then `N ⊗ P` is a tensor inverse of `M`. -/
theorem isInvertible_of_tensor_isInvertible
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    (h : IsInvertible O hO (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N)) :
    IsInvertible O hO M := by
  obtain ⟨P, ⟨f⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit O hO _).mp h
  exact isInvertible_of_tensor_iso_unit O hO
    (((Stacks.SheafOfModules.tensorLeftFunctorObjIso O hO M N).app P).symm ≪≫ f)

/-- Every integer tensor power of an invertible sheaf is invertible. Ascending from `L^{⊗ 0}`
uses Tag 01CT part (1) with the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`; descending
reads the same comparison backwards, so that `L^{⊗ (n - 1)}` is a tensor factor of the
invertible sheaf `L^{⊗ n}`. -/
theorem tensorPower_isInvertible
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) : IsInvertible O hO (tensorPower O hO L n) := by
  induction n using Int.induction_on with
  | zero => exact Stacks.SheafOfModules.isInvertible_unit O hO
  | succ k ih =>
      have := ih
      have : IsInvertible O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
              (tensorPower O hO L k)).obj L) :=
        tensorProduct_isInvertible O hO _ L
      exact isInvertible_of_iso O hO (tensorPowerSuccIso O hO L k)
  | pred k ih =>
      have := ih
      have : IsInvertible O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
              (tensorPower O hO L (-(k : ℤ) - 1))).obj L) :=
        isInvertible_of_iso O hO
          ((tensorPowerSuccIso O hO L (-(k : ℤ) - 1) ≪≫
            tensorPowerReindex O hO L (by omega : -(k : ℤ) - 1 + 1 = -(k : ℤ))).symm)
      exact isInvertible_of_tensor_isInvertible O hO _ L this

end Stacks.SheafOfModules.Invertible

end
