module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFreeFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsUnique

/-!
# The coordinates of an element of `M ⊗_D Ω` against a finite basis

`Crystalline.IsCoordinateExpansion` asks for a family `θ : ι → (M → M)` with

`∇ m = ∑_i θ_i(m) ⬝ d x_i`,

the sum converging in the `p`-adic topology of `M ⊗̂_D Ω`.
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsUnique.lean` shows such a family is
unique once the `d x_i` are a basis of `Ω` and `M` is `p`-adically separated, and
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsInfinite.lean` constructs it,
`Crystalline.exists_isCoordinateExpansion_of_basis`, for a basis indexed by an arbitrary type.

This module records the finite-dimensional identity behind the coordinates: against a basis of
`Ω` indexed by a finite type, an element of the uncompleted tensor product `M ⊗_D Ω` is the sum of
its coordinates `Crystalline.tensorCoordinate`.

## Main results

* `Crystalline.sum_tensorCoordinate_tmul` — against a finite basis of `Ω`, an element of
  `M ⊗_D Ω` is the sum of its coordinates: `z = ∑_i (z)_i ⊗ b i`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### An element of `M ⊗_D Ω` is the sum of its coordinates -/

section Coordinates

variable {D : Type u} [CommRing D] {Omega : Type*} [AddCommGroup Omega] [Module D Omega]
  {M : Type*} [AddCommGroup M] [Module D M] {ι : Type uI} [DecidableEq ι] [Fintype ι]

/-- **Against a finite basis of `Ω`, an element of `M ⊗_D Ω` is the sum of its coordinates.**

`Crystalline.tensorCoordinate` is the evaluation at `j` of
`TensorProduct.equivFinsuppOfBasisRight`, so this is the inverse of that equivalence applied to
its own value, with the `Finsupp.sum` read as a sum over all of `ι`: the terms outside the
support contribute `0 ⊗ b i = 0`. -/
theorem sum_tensorCoordinate_tmul (b : Module.Basis ι D Omega) (z : M ⊗[D] Omega) :
    ∑ i, (tensorCoordinate (M := M) b i z) ⊗ₜ[D] b i = z := by
  conv_rhs => rw [← (TensorProduct.equivFinsuppOfBasisRight (M := M) b).symm_apply_apply z]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype _ _ fun i ↦ TensorProduct.zero_tmul M (b i)]
  rfl

end Coordinates

end Crystalline

end
