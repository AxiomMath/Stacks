module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

import Mathlib.RingTheory.LocalProperties.Reduced
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.FieldTheory.SeparableAlgebraic.TensorProduct
import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-!
# Geometric reducedness over a separable algebraic extension of the base field

Proof of `Algebra.isGeometricallyReduced_iff_of_isSeparable` (Stacks 0C2Y): for a separable
algebraic field extension `k'/k` and a `k'`-algebra `A`, the algebra `A` is geometrically reduced
over `k` if and only if it is geometrically reduced over `k'`.

The argument is the source's. If `A` is geometrically reduced over `k`, then for an algebraic
closure `K` of `k'` the ring `K ⊗[k] A` is reduced (Lemma 034N), and `K ⊗[k'] A` is a localization
of it because `k' ⊗[k] k' → k'` is a localization (Lemma 0C2X), hence reduced. Conversely, if `A`
is geometrically reduced over `k'`, then for an algebraic closure `K` of `k` the ring `k' ⊗[k] K`
is reduced, `k'/k` being separable, and `K ⊗[k] A = (k' ⊗[k] K) ⊗[k'] A` is reduced by Lemma 034N
over `k'`.

## Main results

* `Algebra.isGeometricallyReduced_iff_of_isSeparable`: Stacks 0C2Y.

## Implementation notes

Geometric reducedness is Mathlib's `Algebra.IsGeometricallyReduced`, checked on an algebraic
closure (`Algebra.isGeometricallyReduced_field_iff`). "Separable algebraic" is Mathlib's
`Algebra.IsSeparable k k'`, which includes algebraicity, and the `k`-algebra structure of `A` is
the restriction of its `k'`-algebra structure (`IsScalarTower k k' A`).

## References

* [Stacks Project, Tag 0C2Y](https://stacks.math.columbia.edu/tag/0C2Y)
-/

@[expose] public section

open scoped TensorProduct

/-- **Stacks 0C2Y.** For a separable algebraic field extension `k'/k`, a `k'`-algebra is
geometrically reduced over `k` if and only if it is geometrically reduced over `k'`. -/
@[stacks 0C2Y]
theorem Algebra.isGeometricallyReduced_iff_of_isSeparable (k k' A : Type*) [Field k] [Field k']
    [CommRing A] [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] :
    Algebra.IsGeometricallyReduced k A ↔ Algebra.IsGeometricallyReduced k' A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [Algebra.isGeometricallyReduced_field_iff]
    obtain ⟨M, hM⟩ := Algebra.TensorProduct.exists_isLocalization_mapOfCompatibleSMul_of_isSeparable
      k k' (AlgebraicClosure k') A
    let _ := (Algebra.TensorProduct.mapOfCompatibleSMul k' k k' (AlgebraicClosure k') A).toRingHom
      |>.toAlgebra
    exact isReduced_localizationPreserves M _ inferInstance
  · rw [Algebra.isGeometricallyReduced_field_iff]
    have : Algebra.IsGeometricallyReduced k k' := .of_isSeparable k k'
    have : IsReduced (k' ⊗[k] AlgebraicClosure k) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k k' (AlgebraicClosure k))
        (Algebra.TensorProduct.comm k k' (AlgebraicClosure k)).injective
    let e : (k' ⊗[k] AlgebraicClosure k) ⊗[k'] A ≃+* AlgebraicClosure k ⊗[k] A :=
      ((Algebra.TensorProduct.comm k' _ A).toRingEquiv.trans
        (Algebra.TensorProduct.cancelBaseChange k k' A A (AlgebraicClosure k)).toRingEquiv).trans
        (Algebra.TensorProduct.comm k A (AlgebraicClosure k)).toRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
