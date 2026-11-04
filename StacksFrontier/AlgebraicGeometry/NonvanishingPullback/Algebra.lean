module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of a local ring detects the maximal-ideal submodule

For a local homomorphism of local rings `A → B` and an `A`-module `M`, an element `m` of `M`
lies in `𝔪_A · M` exactly when `1 ⊗ m` lies in `𝔪_B · (B ⊗_A M)`.

This is the algebraic content of Stacks Tag 0H78 — the inverse image of a nonvanishing locus is
the nonvanishing locus of the pulled-back section — once the stalk of a module pullback has been
identified with the base-changed stalk by Stacks Tag 0098. It is stated here, for plain rings and
modules, so that the geometric file carries no algebra.

## Main results

* `Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul`: the equivalence.
* `Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv`: `I · ⊤` is preserved by a
  linear equivalence, so the equivalence above can be read across any identification of the two
  modules.

## The route

Both sides are recognised as the vanishing of a pure tensor over a residue field.

* `m ∈ 𝔪_A · M` iff `(1 : κ_A) ⊗ m = 0`, because `κ_A ⊗_A M ≅ M / 𝔪_A M`
  (`TensorProduct.quotTensorEquivQuotSMul`) carries `1 ⊗ m` to the class of `m`.
* `1 ⊗ m ∈ 𝔪_B · (B ⊗_A M)` iff `(1 : κ_B) ⊗_B (1 ⊗_A m) = 0`, by the same equivalence for the
  `B`-module `B ⊗_A M`.
* The two are matched by cancelling the base change twice, through `B` and through `κ_A`
  (`TensorProduct.AlgebraTensorModule.cancelBaseChange`), and by faithful flatness of the residue
  field extension `κ_A → κ_B`, which is where `Module.FaithfullyFlat.one_tmul_eq_zero_iff` turns
  vanishing over `κ_B` back into vanishing over `κ_A`.

Locality of `A → B` enters exactly once, in the residue-field algebra: it is what makes `κ_A` act
on `κ_B` at all, and hence what makes the last step available.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.NonvanishingPullback

/-- A linear map sends `I • ⊤` into `I • ⊤`. -/
private theorem apply_mem_ideal_smul_top {R M N : Type u} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (I : Ideal R)
    (e : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    e x ∈ I • (⊤ : Submodule R N) := by
  have h : I • (⊤ : Submodule R M) ≤ Submodule.comap e (I • (⊤ : Submodule R N)) := by
    rw [Submodule.smul_le]
    intro r hr m _
    simpa only [Submodule.mem_comap, map_smul] using
      Submodule.smul_mem_smul hr (Submodule.mem_top (x := e m))
  exact h hx

/-- **`I · ⊤` is carried onto `I · ⊤` by a linear equivalence.** Membership of `x` in
`I • (⊤ : Submodule R M)` is membership of `e x` in `I • (⊤ : Submodule R N)`. -/
theorem mem_ideal_smul_top_iff_of_linearEquiv {R M N : Type u} [CommSemiring R]
    [AddCommMonoid M] [instM : Module R M] [AddCommMonoid N] [instN : Module R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ e x ∈ I • (⊤ : Submodule R N) :=
  ⟨apply_mem_ideal_smul_top I e.toLinearMap, fun h => by
    simpa using apply_mem_ideal_smul_top I e.symm.toLinearMap h⟩

/-- Membership in `𝔪 · M` is the vanishing of `1 ⊗ m` over the residue field. -/
private theorem mem_maximalIdeal_smul_top_iff_one_tmul_eq_zero {R M : Type u} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] (m : M) :
    m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m = 0 := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (IsLocalRing.maximalIdeal R) m,
    (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)).map_eq_zero_iff]
  exact Iff.rfl

/-- **Base change along a local homomorphism detects `𝔪 · M`.** For local rings `A` and `B` with
`A → B` a local homomorphism and `M` an `A`-module, `m` lies in `𝔪_A · M` exactly when `1 ⊗ m`
lies in `𝔪_B · (B ⊗_A M)`. -/
theorem mem_maximalIdeal_smul_iff_one_tmul {A B M : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [instAlg : Algebra A B] [instLoc : IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [instMod : Module A M] (m : M) :
    m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      (1 : B) ⊗ₜ[A] m ∈
        IsLocalRing.maximalIdeal B • (⊤ : Submodule B (B ⊗[A] M)) := by
  have hviaB : (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) = 0 ↔
      (1 : IsLocalRing.ResidueField B) ⊗ₜ[A] m = 0 := by
    rw [← TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul A B
      (IsLocalRing.ResidueField B) (1 : IsLocalRing.ResidueField B) m,
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (IsLocalRing.ResidueField B)
        (IsLocalRing.ResidueField B) M).symm.map_eq_zero_iff]
  have hviaK : (1 : IsLocalRing.ResidueField B) ⊗ₜ[A] m = 0 ↔
      (1 : IsLocalRing.ResidueField B) ⊗ₜ[IsLocalRing.ResidueField A]
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) = 0 := by
    rw [← TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul A
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
      (1 : IsLocalRing.ResidueField B) m,
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B) M).symm.map_eq_zero_iff]
  have hfaith : (1 : IsLocalRing.ResidueField B) ⊗ₜ[IsLocalRing.ResidueField A]
      ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) = 0 ↔
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m = 0 :=
    Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := IsLocalRing.ResidueField A)
      (M := IsLocalRing.ResidueField A ⊗[A] M) (A := IsLocalRing.ResidueField B) _
  exact (mem_maximalIdeal_smul_top_iff_one_tmul_eq_zero m).trans
    (((hfaith.symm.trans hviaK.symm).trans hviaB.symm).trans
      (mem_maximalIdeal_smul_top_iff_one_tmul_eq_zero ((1 : B) ⊗ₜ[A] m)).symm)

end Stacks.NonvanishingPullback

end
