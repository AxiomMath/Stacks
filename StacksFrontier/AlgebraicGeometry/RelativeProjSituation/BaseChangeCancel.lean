module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Cancelling a base change

Let `R ⟶ S` and `R ⟶ A` be maps of commutative rings and let `B = S ⊗[R] A`. For an `A`-module
`M` and a `B`-module `N`, a map `g : M ⟶ N` which exhibits `N` as `S ⊗[R] M` exhibits it just as
well as `B ⊗[A] M`:

`B ⊗[A] M = (S ⊗[R] A) ⊗[A] M = S ⊗[R] M = N`.

This is the module-level counterpart of `Algebra.IsPushout.comp_iff`: it turns a base change of
modules read over the original base ring into one read over an intermediate algebra.

## Main results

* `Stacks.IsBaseChange.of_isPushout`: **the cancellation.**

## Implementation notes

The bijectivity is not reproved: it is
`Algebra.IsPushout.cancelBaseChange`, which already supplies the comparison
`B ⊗[A] M ≃ₗ[S] N`. What has to be added is that the same map is `B`-linear, and that is settled
by one formula — the comparison sends `b ⊗ x` to `b • g x` — proved by the induction that
`Algebra.IsPushout` provides on `B`: every element of `B` is built from the image of `A` by
scaling by `S` and adding. The same formula is then both the `B`-linearity and the normalisation
that `IsBaseChange.of_equiv` asks for.

The scalar actions of `R`, `S`, `A` and `B` on `N` are all taken as hypotheses with their towers,
rather than derived, because in the intended application each of them is a restriction of scalars
along a map that is not an instance.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks

/-- **Cancelling a base change.** If `B = S ⊗[R] A` and `g : M ⟶ N` exhibits the `B`-module `N`
as `S ⊗[R] M` for an `A`-module `M`, then it exhibits `N` as `B ⊗[A] M`. -/
public theorem IsBaseChange.of_isPushout
    {R S A B M N : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module S N] [Module A N] [Module B N]
    [IsScalarTower R S N] [IsScalarTower R A N] [IsScalarTower A B N] [IsScalarTower S B N]
    (g : M →ₗ[A] N) (hg : IsBaseChange S (g.restrictScalars R)) :
    IsBaseChange B g := by
  set e₀ : B ⊗[A] M ≃ₗ[S] N :=
    (Algebra.IsPushout.cancelBaseChange R S A B M) ≪≫ₗ hg.equiv with he₀
  have key : ∀ (b : B) (m : M), e₀ (b ⊗ₜ[A] m) = b • g m := by
    intro b m
    refine (Algebra.IsPushout.out (R := R) (S := S) (R' := A) (S' := B)).inductionOn b
      (motive := fun b => e₀ (b ⊗ₜ[A] m) = b • g m) ?_ ?_ ?_
    · intro a
      change e₀ (algebraMap A B a ⊗ₜ[A] m) = algebraMap A B a • g m
      have h1 : (algebraMap A B a) ⊗ₜ[A] m = (1 : B) ⊗ₜ[A] (a • m) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rw [h1, he₀, LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_tmul,
        IsBaseChange.equiv_tmul, one_smul, LinearMap.restrictScalars_apply, map_smul,
        ← IsScalarTower.algebraMap_smul B a (g m)]
    · intro s b hb
      rw [← TensorProduct.smul_tmul', map_smul, hb]
      exact (smul_assoc s b (g m)).symm
    · intro b₁ b₂ h₁ h₂
      rw [TensorProduct.add_tmul, map_add, h₁, h₂, add_smul]
  refine _root_.IsBaseChange.of_equiv (AddEquiv.toLinearEquiv e₀.toAddEquiv ?_) ?_
  · intro c x
    induction x with
    | tmul b m =>
        have hcb : c • (b ⊗ₜ[A] m) = (c * b) ⊗ₜ[A] m := by
          rw [← smul_eq_mul, TensorProduct.smul_tmul']
        rw [hcb]
        change e₀ _ = c • e₀ _
        rw [key, key, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  · intro m
    change e₀ ((1 : B) ⊗ₜ[A] m) = g m
    rw [key, one_smul]

end Stacks

end
