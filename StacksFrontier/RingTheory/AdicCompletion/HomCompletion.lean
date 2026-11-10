module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom

/-!
# The adic completion of a module of homomorphisms

Let `I` be an ideal of a Noetherian ring `A` and let `M`, `N` be finite `A`-modules.  Then
the `I`-adic completion of `Hom_A(M, N)` is the module of `A`-linear maps from `M` into the
`I`-adic completion of `N`: completing a homomorphism `f : M → N` amounts to composing it
with the canonical map `N → N̂`, and every `A`-linear map `M → N̂` arises this way from a
unique element of the completion.

Complementing this, a linear map out of a completion is determined by its restriction along
`M → M̂` as soon as its target is `I`-adically Hausdorff, since the submodules
`I ^ n • M̂` cut out the kernels of the truncations `M̂ → M / I ^ n M`.

## Main results

* `AdicCompletion.homCompletionEquiv` — the `A`-linear equivalence between the `I`-adic
  completion of `Hom_A(M, N)` and `Hom_A(M, N̂)`, for `M`, `N` finite over a Noetherian ring.
* `AdicCompletion.homCompletionEquiv_of_apply` — the equivalence carries the completion of
  `f : M →ₗ[A] N` to the composite of `f` with `N → N̂`; since the completions of the
  `f : M →ₗ[A] N` generate `Hom_A(M, N)^` topologically, this characterises it.
* `AdicCompletion.linearMap_ext_of` — two `A`-linear maps out of `M̂` into an `I`-adically
  Hausdorff module agree as soon as they agree on the image of `M`.

## Implementation notes

`homCompletionEquiv` is obtained from the completion-of-`Hom` comparison over the completed
ring `Â`, which identifies `Hom_A(M, N)^` with `Hom_Â(M̂, N̂)`, by rewriting `M̂` as the base
change `Â ⊗[A] M` and applying the adjunction `Hom_Â(Â ⊗[A] M, P) ≃ Hom_A(M, P)`.  Each step
is `Â`-linear, so the composite is restricted to `A` at the end.

## References

* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AdicCompletion

universe u

section Finite

variable {A M N : Type u} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- For finite modules `M`, `N` over a Noetherian ring `A` and an ideal `I ⊆ A`, the `I`-adic
completion of `Hom_A(M, N)` is the module of `A`-linear maps from `M` into the completion of
`N`.  This finiteness statement is one of the inputs to Stacks 00MB and Stacks 09BB. -/
public def homCompletionEquiv (I : Ideal A) :
    AdicCompletion I (M →ₗ[A] N) ≃ₗ[A] (M →ₗ[A] AdicCompletion I N) :=
  ((Stacks.AdicSystem.HomComparison.completedHomEquiv I).trans
    (((ofTensorProductEquivOfFiniteNoetherian I M).symm.arrowCongr
        (LinearEquiv.refl (AdicCompletion I A) (AdicCompletion I N))).trans
      (LinearMap.liftBaseChangeEquiv (AdicCompletion I A)).symm)).restrictScalars A

/-- `AdicCompletion.homCompletionEquiv` sends the completion of a homomorphism
`f : M →ₗ[A] N` to the composite of `f` with the canonical map `N → N̂`.  This identity
determines the equivalence, and is the form in which Stacks 00MB and Stacks 09BB use it. -/
public theorem homCompletionEquiv_of_apply (I : Ideal A) (f : M →ₗ[A] N) (m : M) :
    homCompletionEquiv I (of I (M →ₗ[A] N) f) m = of I N (f m) := by
  change Stacks.AdicSystem.HomComparison.completedHomEquiv I (of I (M →ₗ[A] N) f)
    ((ofTensorProductEquivOfFiniteNoetherian I M) (1 ⊗ₜ[A] m)) = _
  simp [Stacks.AdicSystem.HomComparison.completedHomEquiv_of_apply]

end Finite

/-- Two `A`-linear maps out of the `I`-adic completion of `M` into an `I`-adically Hausdorff
module agree as soon as they agree on the image of `M`.  For a finitely generated ideal the
image of `M` is dense in `M̂`, and this is the extensionality principle that density
provides.  It underlies the uniqueness half of Stacks 00MB. -/
public theorem linearMap_ext_of {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [IsHausdorff I N] (f g : AdicCompletion I M →ₗ[A] N)
    (hfg : ∀ m, f (of I M m) = g (of I M m)) : f = g := by
  refine LinearMap.ext fun x => sub_eq_zero.mp ?_
  have hmem : f x - g x ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule A N) := by
    refine (Submodule.mem_iInf _).mpr fun n => ?_
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A M))
      (eval I M n x)
    have hx : x - of I M m ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
      rw [pow_smul_top_eq_ker_eval (I := I) (M := M) hI]
      change eval I M n (x - of I M m) = 0
      rw [map_sub, eval_of, hm, sub_self]
    have hmap (k : AdicCompletion I M →ₗ[A] N) :
        k (x - of I M m) ∈ I ^ n • (⊤ : Submodule A N) :=
      Submodule.smul_top_le_comap_smul_top (I ^ n) k hx
    have hz := (I ^ n • (⊤ : Submodule A N)).sub_mem (hmap f) (hmap g)
    simpa only [map_sub, hfg m, sub_sub_sub_cancel_right] using hz
  rw [IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff I N)] at hmem
  exact hmem

end AdicCompletion

end
