module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs

/-!
# Freeness of `Ω` and the injectivity hypothesis of [Stacks, Tag 07JH]

The reduction
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor` of
[Stacks, Tag 07JH] has among its hypotheses

`hinj : ∀ Q : FirstOrderCrystal …, Function.Injective (toCompletedTensor p D Ω Q.carrier)`.

By `Crystalline.injective_toCompletedTensor_iff_isHausdorff`, `hinj` is `p`-adic Hausdorffness of
`M ⊗_D Ω`. It does not follow from `p`-adic completeness of `M`, which is item (07JB): the tensor
product of two `p`-adically separated modules need not be separated, and
`Crystalline.not_injective_toCompletedTensor_of_isUnit` exhibits a situation in which `hinj` fails.
This file proves `hinj` when `Ω` is free over `D`: a basis of `Ω` indexed by `ι` gives
`M ⊗_D Ω ≅ (ι →₀ M)`, and the finitely supported families in a Hausdorff module form a Hausdorff
module, with no finiteness assumption on `ι`.

## Main results

* `Crystalline.map_mem_pow_smul_top_of_mem` — a linear map carries `Iⁿ • ⊤` into `Iⁿ • ⊤`.
* `Crystalline.isHausdorff_of_injective` and `Crystalline.isHausdorff_of_linearEquiv` —
  `I`-adic Hausdorffness pulls back along an injective linear map, hence transports along a linear
  equivalence.
* `Crystalline.isHausdorff_finsupp` — the finitely supported families in an `I`-adically Hausdorff
  module are `I`-adically Hausdorff, for an arbitrary index type.
* `Crystalline.isHausdorff_tensorProduct_of_basis` — if `Ω` is free over `R` and `M` is
  `I`-adically Hausdorff then so is `M ⊗_R Ω`.
* `Crystalline.injective_toCompletedTensor_of_basis` — the canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is
  injective when `Ω` is free over `D` and `M` is `p`-adically Hausdorff.
* `Crystalline.forall_injective_toCompletedTensor_of_basis` — the hypothesis `hinj` of
  `Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor` from
  a basis of `Ω` alone.
* `Crystalline.equivalence07JH_of_isEquivalence_functor_of_basis` — for a reduction datum and
  a basis of `Ω`, [Stacks, Tag 07JH] follows from `Functor.IsEquivalence Rd.functor` and `hlift`.

## References

* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public section

open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### Hausdorffness along linear maps -/

section Transfer

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A linear map carries the `n`-th step `I ^ n • ⊤` of the `I`-adic filtration into the `n`-th
step.** -/
theorem map_mem_pow_smul_top_of_mem (I : Ideal R) (f : N →ₗ[R] M) (n : ℕ) {x : N}
    (hx : x ∈ (I ^ n • ⊤ : Submodule R N)) : f x ∈ (I ^ n • ⊤ : Submodule R M) := by
  have hmap := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at hmap
  exact Submodule.smul_mono le_rfl le_top hmap

/-- A linear map into an `I`-adically Hausdorff module kills every element lying in all steps of the
`I`-adic filtration. -/
private theorem map_eq_zero_of_forall_smodEq_zero (I : Ideal R) (f : N →ₗ[R] M)
    (hM : IsHausdorff I M) {x : N} (hx : ∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R N)]) :
    f x = 0 :=
  hM.haus _ fun n ↦ SModEq.zero.mpr
    (map_mem_pow_smul_top_of_mem I f n (SModEq.zero.mp (hx n)))

/-- **`I`-adic Hausdorffness pulls back along an injective linear map.** If `N` embeds
`R`-linearly into an `I`-adically Hausdorff module `M` then `N` is `I`-adically Hausdorff. -/
theorem isHausdorff_of_injective (I : Ideal R) (f : N →ₗ[R] M) (hf : Function.Injective f)
    (hM : IsHausdorff I M) : IsHausdorff I N :=
  ⟨fun _ hx ↦ hf ((map_eq_zero_of_forall_smodEq_zero I f hM hx).trans (map_zero f).symm)⟩

/-- **`I`-adic Hausdorffness transports along a linear equivalence.** -/
theorem isHausdorff_of_linearEquiv (I : Ideal R) (e : N ≃ₗ[R] M) (hM : IsHausdorff I M) :
    IsHausdorff I N :=
  isHausdorff_of_injective I e.toLinearMap e.injective hM

/-- **Finitely supported families in a Hausdorff module are Hausdorff**, for an arbitrary index
type `ι`. -/
theorem isHausdorff_finsupp {ι : Type*} (I : Ideal R) (hM : IsHausdorff I M) :
    IsHausdorff I (ι →₀ M) :=
  ⟨fun _ hx ↦ Finsupp.ext fun i ↦
    map_eq_zero_of_forall_smodEq_zero I (Finsupp.lapply (M := M) (R := R) i) hM hx⟩

end Transfer

/-! ### The tensor product with a free module -/

section Free

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The tensor product of a Hausdorff module with a free module is Hausdorff.** If `M` is
`I`-adically Hausdorff and `Ω` is free over `R`, then `M ⊗_R Ω` is `I`-adically Hausdorff. -/
theorem isHausdorff_tensorProduct_of_basis {ι : Type*} {Omega : Type*} [AddCommGroup Omega]
    [Module R Omega] (I : Ideal R) (b : Module.Basis ι R Omega) (hM : IsHausdorff I M) :
    IsHausdorff I (M ⊗[R] Omega) := by
  classical
  exact isHausdorff_of_linearEquiv I (TensorProduct.equivFinsuppOfBasisRight b)
    (isHausdorff_finsupp I hM)

end Free

/-! ### The hypothesis `hinj` under freeness of `Ω` -/

section Hinj

/-- The canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is injective as soon as `Ω` is free over `D` and `M` is
`p`-adically Hausdorff. -/
theorem injective_toCompletedTensor_of_basis (p : ℕ) (D : Type u) [CommRing D] (Omega : Type u)
    [AddCommGroup Omega] [Module D Omega] (M : Type u) [AddCommGroup M] [Module D M]
    {ι : Type*} (b : Module.Basis ι D Omega)
    (hM : IsHausdorff (DividedPowers.pAdicIdeal (A := D) p) M) :
    Function.Injective (toCompletedTensor p D Omega M) :=
  (injective_toCompletedTensor_iff_isHausdorff p D Omega M).mpr
    (isHausdorff_tensorProduct_of_basis _ b hM)

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} (p : ℕ) {κ : Type uI} (dx : κ → Omega)

/-- Given a basis of `Ω` over `D`, with an arbitrary index type, the canonical map
`M ⊗_D Ω → M ⊗̂_D Ω` is injective on the module of every first-order crystal datum. This is the
hypothesis `hinj` of
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`. -/
theorem forall_injective_toCompletedTensor_of_basis {ι : Type*}
    (b : Module.Basis ι (D : Type u) Omega) :
    ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p (D : Type u) Omega Q.carrier) := by
  intro Q
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Q.carrier :=
    Q.isPAdicallyComplete
  exact injective_toCompletedTensor_of_basis p (D : Type u) Omega Q.carrier b
    IsAdicComplete.toIsHausdorff

end Hinj

/-! ### The reduction of [Stacks, Tag 07JH] under freeness of `Ω` -/

section Reduction

open CategoryTheory AlgebraicGeometry GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega] [Module D Omega]
  [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  {ι : Type uI} {dx : ι → Omega} [IsAffine S.X] [IsAffine S.S.scheme]
  {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-- **The reduction of [Stacks, Tag 07JH] under freeness of `Ω`.** For a reduction datum `Rd` whose
functor is an equivalence, given a basis of `Ω` over `D` and the factorisation `hlift` of the
connection of every pair through `M ⊗_D Ω`, the equivalence of [Stacks, Tag 07JH] holds for `Rd`.
-/
theorem equivalence07JH_of_isEquivalence_functor_of_basis
    (Rd : Reduction07JG S A D g Omega d p dx hp) (hR : Functor.IsEquivalence Rd.functor)
    {κ : Type*} (b : Module.Basis κ (D : Type u) Omega)
    (hlift : ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Equivalence07JH Rd :=
  equivalence07JH_of_isEquivalence_functor Rd hR
    (forall_injective_toCompletedTensor_of_basis p dx b) hlift

end Reduction

end Crystalline

end
