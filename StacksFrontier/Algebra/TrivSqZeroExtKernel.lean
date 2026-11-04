module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of the augmentation of a trivial square-zero extension

The trivial square-zero extension `R[M] = TrivSqZeroExt R M` carries the augmentation
`TrivSqZeroExt.fstHom : R[M] →ₐ[R] R` reading off the scalar part. Its kernel is the copy of
`M` sitting inside `R[M]`, and that kernel is a square-zero ideal: this is the ideal `I` of the
square-zero extensions `k[V]` which index the tangent space of a deformation category
(Stacks 06IB), and the three facts below are what the lifting results of
`StacksFrontier/RingTheory/GradedAlgebra/LiftPresentation.lean` ask of such an `I`.

## Main definitions

* `TrivSqZeroExt.kerFstHomEquiv`: the kernel of the augmentation is `M`, as `R`-modules.

## Main results

* `TrivSqZeroExt.mem_ker_fstHom_iff`: the kernel is the vanishing of the scalar part.
* `TrivSqZeroExt.ker_fstHom_mul_self_eq_bot`: the kernel is square zero.
* `TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom`: the augmentation splits the extension, in
  the form the comparison map `I ⊗[R] P → Q` consumes.

## Implementation notes

`Module Rᵐᵒᵖ M` and `IsCentralScalar R M` are hypotheses rather than being supplied here,
because they are what makes `TrivSqZeroExt R M` a ring at all and the deformation-theoretic
callers install them as local instances on the module they are given.
-/

@[expose] public section

namespace TrivSqZeroExt

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

/-- The kernel of the augmentation of a trivial square-zero extension is the vanishing of the
scalar part. -/
theorem mem_ker_fstHom_iff (a : TrivSqZeroExt R M) :
    a ∈ RingHom.ker (fstHom R R M) ↔ a.fst = 0 :=
  RingHom.mem_ker

/-- An element of the kernel of the augmentation is the image of its module part. -/
theorem eq_inr_snd_of_mem_ker_fstHom {a : TrivSqZeroExt R M}
    (ha : a ∈ RingHom.ker (fstHom R R M)) : a = inr a.snd :=
  TrivSqZeroExt.ext (((mem_ker_fstHom_iff a).mp ha).trans (fst_inr R a.snd).symm) rfl

/-- **The kernel of the augmentation is a square-zero ideal**: the product of two elements with
vanishing scalar part is zero, which is the defining property of the trivial extension. -/
@[ega "IV 21.13.9" "more general"]
theorem ker_fstHom_mul_self_eq_bot :
    RingHom.ker (fstHom R R M) * RingHom.ker (fstHom R R M) = (⊥ : Ideal (TrivSqZeroExt R M)) := by
  refine le_antisymm (Ideal.mul_le.mpr fun a ha b hb => ?_) bot_le
  rw [Submodule.mem_bot, eq_inr_snd_of_mem_ker_fstHom ha, eq_inr_snd_of_mem_ker_fstHom hb,
    inr_mul_inr]

/-- **The kernel of the augmentation is `M`.** The isomorphism reads off the module part; its
inverse is the canonical inclusion of `M`. -/
def kerFstHomEquiv : ↥(RingHom.ker (fstHom R R M)) ≃ₗ[R] M where
  toFun a := (a : TrivSqZeroExt R M).snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨inr m, (mem_ker_fstHom_iff _).mpr (fst_inr R m)⟩
  left_inv a := Subtype.ext (eq_inr_snd_of_mem_ker_fstHom a.2).symm
  right_inv m := snd_inr R m

/-- The defining formula of `kerFstHomEquiv`. -/
@[simp]
theorem kerFstHomEquiv_apply (a : ↥(RingHom.ker (fstHom R R M))) :
    kerFstHomEquiv a = (a : TrivSqZeroExt R M).snd := rfl

/-- **The augmentation splits the extension.** Subtracting the constant with the same scalar
part lands in the kernel; this is the hypothesis `∀ a, a - algebraMap R A (ε a) ∈ I` of
`Ideal.exists_addMonoidHom_tmul_smul`, i.e. the only use that result makes of the splitting
`A = R ⊕ I`. -/
theorem sub_algebraMap_fst_mem_ker_fstHom (a : TrivSqZeroExt R M) :
    a - algebraMap R (TrivSqZeroExt R M) (fstHom R R M a) ∈ RingHom.ker (fstHom R R M) := by
  rw [mem_ker_fstHom_iff, fst_sub, algebraMap_eq_inl, fst_inl]
  exact sub_self _

/-- The augmentation of a trivial square-zero extension is surjective: the constants already
realise every scalar. -/
theorem surjective_fstHom : Function.Surjective (fstHom R R M) :=
  fun c => ⟨inl c, fst_inl M c⟩

end TrivSqZeroExt

end
