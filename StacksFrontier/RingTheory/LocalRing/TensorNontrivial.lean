module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two nonzero finite modules over a local ring is nonzero

Let `R` be a commutative local ring with residue field `κ`, and let `M` and `N` be finitely
generated `R`-modules, both nonzero.  Then

`M ⊗_R N ≠ 0`.

Finite generation cannot be dropped: over `ℤ_p` the modules `ℚ_p` and `ℤ/p` are both nonzero and
`ℚ_p ⊗ ℤ/p = 0`.

## The proof

By Nakayama a nonzero finite module has a nonzero reduction `κ ⊗_R M`, and a nonzero module over
a field carries a nonzero functional, which is automatically surjective.  So `M` admits a
surjection onto `κ`, and so does `N`; tensoring the two gives a surjection

`M ⊗_R N ↠ κ ⊗_R κ`,

and `κ ⊗_R κ` is nonzero by Nakayama again, `κ` being a nonzero finite `R`-module.  No
identification of `κ ⊗_R (M ⊗_R N)` with `(κ ⊗_R M) ⊗_κ (κ ⊗_R N)` is needed, and that is the
point of routing through functionals rather than through the base change of the tensor product.

## Main results

* `Stacks.LocalRing.exists_surjective_toResidueField`: a nonzero finite module over a local ring
  surjects onto the residue field.
* `Stacks.LocalRing.nontrivial_tensorProduct`: **the theorem of this file.**

## Implementation notes

Nakayama enters only through `IsLocalRing.subsingleton_tensorProduct`, Mathlib's statement that
`κ ⊗_R M` is trivial exactly when `M` is, for `M` finite.  The nonzero functional comes from
`Module.Projective.exists_dual_ne_zero`, which applies because every module over a field is free
and hence projective; its surjectivity is `Ideal.eq_bot_or_top` applied to its range, a submodule
of `κ` and so an ideal of a field.

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The reduction `κ ⊗_R M` of a nonzero finite module over a local ring is nonzero. -/
private theorem nontrivial_residueField_tensorProduct (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] : Nontrivial (IsLocalRing.ResidueField R ⊗[R] M) := by
  rw [← not_subsingleton_iff_nontrivial, IsLocalRing.subsingleton_tensorProduct]
  exact not_subsingleton M

/-- **A nonzero finite module over a local ring surjects onto the residue field.**  Its reduction
`κ ⊗_R M` is nonzero by Nakayama, a nonzero module over a field carries a nonzero functional, and
a nonzero functional into a field is surjective. -/
@[ega "IV 2.5.5.4" "more general"]
theorem exists_surjective_toResidueField (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ φ : M →ₗ[R] IsLocalRing.ResidueField R, Function.Surjective φ := by
  have := nontrivial_residueField_tensorProduct (R := R) M
  obtain ⟨v, hv⟩ := exists_ne (0 : IsLocalRing.ResidueField R ⊗[R] M)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (IsLocalRing.ResidueField R) hv
  have hfs : Function.Surjective f := by
    have hne : LinearMap.range f ≠ ⊥ := fun h => hf (by
      have : f v ∈ LinearMap.range f := LinearMap.mem_range_self f v
      rw [h, Submodule.mem_bot] at this
      exact this)
    exact LinearMap.range_eq_top.1 ((Ideal.eq_bot_or_top (LinearMap.range f)).resolve_left hne)
  refine ⟨(f.restrictScalars R).comp
    (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1), ?_⟩
  exact hfs.comp (TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
    IsLocalRing.residue_surjective)

/-- **The tensor product of two nonzero finite modules over a local ring is nonzero.**  Both
factors surject onto the residue field `κ`, so the tensor product surjects onto `κ ⊗_R κ`, which
is nonzero because `κ` is a nonzero finite `R`-module. -/
@[ega "0 1.7.5"]
theorem nontrivial_tensorProduct (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N] :
    Nontrivial (M ⊗[R] N) := by
  obtain ⟨φ, hφ⟩ := exists_surjective_toResidueField (R := R) M
  obtain ⟨ψ, hψ⟩ := exists_surjective_toResidueField (R := R) N
  have := nontrivial_residueField_tensorProduct (R := R) (IsLocalRing.ResidueField R)
  exact (TensorProduct.map_surjective hφ hψ).nontrivial

end Stacks.LocalRing

end
