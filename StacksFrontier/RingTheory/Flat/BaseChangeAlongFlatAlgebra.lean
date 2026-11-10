module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness over the base along a flat change of algebra

Let `R` be a ring, let `S → S'` be a flat map of `R`-algebras, let `M` be an `S`-module and put
`M' = S' ⊗_S M`. For an `R`-module `N` there is a natural identification
`M' ⊗_R N = S' ⊗_S (M ⊗_R N)`, so for a map `f : N → N'` of `R`-modules, the map `M' ⊗_R f`
is `S' ⊗_S (M ⊗_R f)`. Since `S'` is flat over `S`, if `M ⊗_R f` is injective then so is
`M' ⊗_R f`; if `S'` is faithfully flat over `S`, the converse holds as well. Hence if `M` is flat
over `R` then so is `M'`, and if `S → S'` is faithfully flat then `M` is flat over `R` if and only
if `M'` is.

## Main results

* `Module.Flat.tensorProduct_of_flat`: Stacks 0584 (1), if `M` is flat over `R` then
  `S' ⊗_S M` is flat over `R`.
* `Module.Flat.tensorProduct_iff_of_faithfullyFlat`: Stacks 0584 (2), if `S → S'` is faithfully
  flat then `M` is flat over `R` if and only if `S' ⊗_S M` is.

## Implementation notes

Stacks phrases flatness through tensoring on the left and computes the kernel of
`N ⊗_R M → N' ⊗_R M` after base change to `S'`; here tensor products are on the right, as in
Mathlib's `Module.Flat`, and the vanishing of that kernel is expressed as injectivity.

## References

* [Stacks, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {R S S' M : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']
  [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The map `(S' ⊗_S M) ⊗_R f` is the base change along `S → S'` of `M ⊗_R f`, under the
identification `(S' ⊗_S M) ⊗_R N = S' ⊗_S (M ⊗_R N)`. -/
theorem lTensor_tensorProduct_eq {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N']
    [Module R N] [Module R N'] (f : N →ₗ[R] N') :
    ((AlgebraTensorModule.assoc R S S' S' M N').toLinearMap.restrictScalars R ∘ₗ
      f.lTensor (S' ⊗[S] M)) =
      ((AlgebraTensorModule.lTensor S M f).lTensor S').restrictScalars R ∘ₗ
        (AlgebraTensorModule.assoc R S S' S' M N).toLinearMap.restrictScalars R := by
  refine TensorProduct.ext' fun x n => ?_
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply] at hx hy ⊢
    rw [add_tmul, map_add, map_add, hx, hy, map_add, map_add]

/-- The injectivity of `(S' ⊗_S M) ⊗_R f` in terms of that of `S' ⊗_S (M ⊗_R f)`. -/
theorem lTensor_tensorProduct_injective_iff {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N']
    [Module R N] [Module R N'] (f : N →ₗ[R] N') :
    Function.Injective (f.lTensor (S' ⊗[S] M)) ↔
      Function.Injective ((AlgebraTensorModule.lTensor S M f).lTensor S') := by
  have h := congrArg DFunLike.coe (lTensor_tensorProduct_eq (S := S) (S' := S') (M := M) f)
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at h
  rw [← (AlgebraTensorModule.assoc R S S' S' M N').injective.of_comp_iff, h,
    EquivLike.injective_comp]

/-- **Stacks 0584 (1)**: if `S → S'` is a flat map of `R`-algebras and `M` is an `S`-module that
is flat over `R`, then `S' ⊗_S M` is flat over `R`. -/
@[stacks 0584 "(1)", ega "0 6.2.1" "M⊗_A N is B-flat"]
theorem tensorProduct_of_flat [Module.Flat S S'] [Module.Flat R M] :
    Module.Flat R (S' ⊗[S] M) := by
  refine iff_lTensor_injectiveₛ.2 fun P _ _ N => ?_
  rw [lTensor_tensorProduct_injective_iff]
  exact lTensor_preserves_injective_linearMap _
    (lTensor_preserves_injective_linearMap (M := M) N.subtype Subtype.val_injective)

/-- **Stacks 0584 (2)**: if `S → S'` is a faithfully flat map of `R`-algebras, then an `S`-module
`M` is flat over `R` if and only if `S' ⊗_S M` is flat over `R`. -/
@[stacks 0584 "(2)"]
theorem tensorProduct_iff_of_faithfullyFlat {R S S' M : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FaithfullyFlat S S'] :
    Module.Flat R (S' ⊗[S] M) ↔ Module.Flat R M := by
  refine ⟨fun h => iff_lTensor_injectiveₛ.2 fun P _ _ N => ?_, fun _ => tensorProduct_of_flat⟩
  have hinj := lTensor_preserves_injective_linearMap (M := S' ⊗[S] M) N.subtype
    Subtype.val_injective
  rw [lTensor_tensorProduct_injective_iff, FaithfullyFlat.lTensor_injective_iff_injective] at hinj
  exact hinj

end Module.Flat
