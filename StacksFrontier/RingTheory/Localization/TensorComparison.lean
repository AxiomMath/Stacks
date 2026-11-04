module

public import StacksCore.RingTheory.Localization.BaseChange

/-!
# A tensor product of localizations, recognised from its values on pure tensors

`IsLocalization.isLocalizedModule_tensorMap`, which is the substance of [Stacks, Tag 00DL], says
that the *canonical* comparison `IsLocalization.tensorMap S Rₛ f g : M ⊗[R] N → M' ⊗[Rₛ] N'` is a
localization map when `f` and `g` are.  A consumer rarely has that map on the nose: it has a map
of its own — the restriction map of a presheaf of tensor products, say — and knows only what it
does to a pure tensor.  **This file records that knowing that is enough**, because a map out of a
tensor product is determined by its values on pure tensors.

## Main results

* `IsLocalization.isLocalizedModule_of_tensor`: **any** `R`-linear map
  `M ⊗[R] N → M' ⊗[Rₛ] N'` carrying `m ⊗ₜ n` to `f m ⊗ₜ g n` is a localization map at `S`, for
  `f` and `g` localization maps at `S`.

## Implementation notes

The hypothesis pins the map down completely — `TensorProduct.ext'` — so this is
`IsLocalization.isLocalizedModule_tensorMap` transported along an equality of maps rather than
along an isomorphism, and nothing has to be checked about the transport.

This is the tensor counterpart of
`IsLocalization.isLocalizedModule_of_exteriorPower` in
`StacksFrontier/LinearAlgebra/ExteriorPower/Localization.lean`, which recognises an exterior power of
a localization from its values on wedges, and the two are used together: the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF] has to be shown to localize on the basic opens of
an affine scheme, and its two factors are a tensor product and an exterior power.

## References

* [Stacks Project, Tag 00DL](https://stacks.math.columbia.edu/tag/00DL)

## Not done here

No tag is claimed: [Stacks, Tag 00DL] is already carried by
`IsLocalization.tensorLocalizeEquivTensor`, and this is a restatement of its proof's main step
for a non-canonical comparison, not a further assertion.

Nothing is said about three or more factors, nor about the compatibility of the recognition with
a change of the localization `Rₛ`.
-/

@[expose] public section

open scoped TensorProduct

/-- **A map out of `M ⊗[R] N` carrying `m ⊗ₜ n` to `f m ⊗ₜ g n` is a localization map**, for `f`
and `g` localization maps at `S`.

The hypothesis determines the map, so this is `IsLocalization.isLocalizedModule_tensorMap` read
at a comparison the consumer has built for itself. -/
theorem IsLocalization.isLocalizedModule_of_tensor {R : Type*} [CommSemiring R] (S : Submonoid R)
    (Rₛ : Type*) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {M M' N N' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [AddCommMonoid N'] [Module R N'] [Module Rₛ N'] [IsScalarTower R Rₛ N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') [IsLocalizedModule S f] [IsLocalizedModule S g]
    (Φ : M ⊗[R] N →ₗ[R] M' ⊗[Rₛ] N')
    (hΦ : ∀ (m : M) (n : N), Φ (m ⊗ₜ[R] n) = f m ⊗ₜ[Rₛ] g n) :
    IsLocalizedModule S Φ := by
  have heq : Φ = IsLocalization.tensorMap S Rₛ f g :=
    TensorProduct.ext' fun m n =>
      (hΦ m n).trans (IsLocalization.tensorMap_tmul S Rₛ f g m n).symm
  rw [heq]
  infer_instance

end
