module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The transpose of a map of modules under extension of scalars

Let `β : A ⟶ A'` be a homomorphism of commutative rings, `M` an `A`-module and `P` an
`A'`-module.  An `A`-linear map from `M` to `P`, the target read as an `A`-module by
restriction of scalars along `β`, has a transpose `A' ⊗_A M ⟶ P`, which is `A'`-linear.  This
file names that transpose and records the two properties it is used through.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.transposeExtend`: the transpose.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.transposeExtend_one_tmul`: the transpose sends
  `1 ⊗ m` to the value of the original map at `m`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_transposeExtend_comp`: precomposing with
  an invertible map of `A`-modules leaves the transpose invertible.

## Route

The transpose is the inverse of the hom-set bijection of
`ModuleCat.extendRestrictScalarsAdj`.  The forward direction of that bijection evaluates a map
out of `A' ⊗_A M` at `1 ⊗ m`, by `ModuleCat.extendRestrictScalarsAdj_homEquiv_apply`, so the
element formula is one round trip of the bijection and needs no induction on tensors.  The
second result is `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`.

## Implementation notes

The element formula is stated for the scoped notation `1 ⊗ₜ[A, β] m` of
`ModuleCat.ChangeOfRings`, which is the spelling in which the carrier of
`ModuleCat.extendScalars` presents a pure tensor; the plain `TensorProduct` notation would
need an ambient `Algebra` instance, which a bare ring homomorphism does not supply.

## What is not done

**No assertion of any Stacks tag is proved here, and no project tag attribute is attached.**
This file is bookkeeping for a hom-set bijection; it says nothing about schemes, and in
particular nothing about when a transpose is invertible.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

variable {A A' : CommRingCat.{u}} (β : A ⟶ A')

/-- The transpose, under extension of scalars along `β`, of an `A`-linear map from `M` to an
`A'`-module `P` with its scalars restricted. -/
noncomputable def transposeExtend {M : ModuleCat.{u} A} {P : ModuleCat.{u} A'}
    (u : M ⟶ (ModuleCat.restrictScalars β.hom).obj P) :
    (ModuleCat.extendScalars β.hom).obj M ⟶ P :=
  ((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv M P).symm u

/-- The transpose sends `1 ⊗ m` to the value of the original map at `m`. -/
lemma transposeExtend_one_tmul {M : ModuleCat.{u} A} {P : ModuleCat.{u} A'}
    (u : M ⟶ (ModuleCat.restrictScalars β.hom).obj P) (m : M) :
    transposeExtend β u ((1 : A') ⊗ₜ[A, β.hom] m) = u m :=
  congr($(((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv M P).apply_symm_apply u).hom m)

/-- Precomposing with an invertible map of `A`-modules leaves the transpose invertible. -/
lemma isIso_transposeExtend_comp {M₀ M : ModuleCat.{u} A} {P : ModuleCat.{u} A'}
    (i : M₀ ⟶ M) [IsIso i] (u : M ⟶ (ModuleCat.restrictScalars β.hom).obj P)
    (hu : IsIso (transposeExtend β u)) : IsIso (transposeExtend β (i ≫ u)) := by
  have h : transposeExtend β (i ≫ u) =
      (ModuleCat.extendScalars β.hom).map i ≫ transposeExtend β u :=
    (ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv_naturality_left_symm i u
  have h2 : IsIso ((ModuleCat.extendScalars β.hom).map i) := Functor.map_isIso _ _
  rw [h]
  infer_instance

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
