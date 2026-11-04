module

public import Mathlib.RingTheory.Localization.BaseChange
import StacksCore.Tactic.StacksAttribute

/-! ## Base change of localization

Stacks tag 00DL: for `R`-modules `M` and `N`, localization commutes with tensor product,
`S⁻¹M ⊗_{S⁻¹R} S⁻¹N ≅ S⁻¹(M ⊗_R N)`, as `S⁻¹R`-modules.

Everything here is phrased for abstract localizations rather than the concrete `LocalizedModule`:
`Rₛ` is any localization of `R` at `S`, and `f`, `g`, `h` are arbitrary localization maps of
`M`, `N` and `M ⊗[R] N`. The concrete statement is recovered by taking `Rₛ := Localization S`
and the three maps to be `LocalizedModule.mkLinearMap`.

The substance is `IsLocalization.isLocalizedModule_tensorMap`: the canonical map
`M ⊗[R] N → M' ⊗[Rₛ] N'` is itself a localization map. Stacks' isomorphism is then the
comparison of two localizations of the same module, `IsLocalization.tensorLocalizeEquivTensor`,
and `IsLocalization.tensorLocalizeEquivTensor_tmul` pins it down as *the* canonical one: it is
the map sending `f m ⊗ₜ g n` to `h (m ⊗ₜ n)`, which over `LocalizedModule` reads
`(m/s) ⊗ (n/t) ↦ (m ⊗ n)/(st)`.
-/

add_to_stacks 00DK LocalizedModule.equivTensorProduct

@[expose] public section

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (Rₛ : Type*) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M M' N N' P : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']
  [AddCommMonoid N'] [Module R N'] [Module Rₛ N'] [IsScalarTower R Rₛ N']
  [AddCommMonoid P] [Module R P] [Module Rₛ P] [IsScalarTower R Rₛ P]
  (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : M ⊗[R] N →ₗ[R] P)

/-- The canonical `R`-linear map `M ⊗[R] N → M' ⊗[Rₛ] N'` induced by localization maps
`f : M → M'` and `g : N → N'`, sending `m ⊗ₜ n` to `f m ⊗ₜ g n`. -/
noncomputable def IsLocalization.tensorMap : M ⊗[R] N →ₗ[R] M' ⊗[Rₛ] N' :=
  ((IsLocalization.moduleTensorEquiv S Rₛ M' N').symm.restrictScalars R) ∘ₗ
    TensorProduct.map f g

@[simp]
lemma IsLocalization.tensorMap_tmul (m : M) (n : N) :
    IsLocalization.tensorMap S Rₛ f g (m ⊗ₜ n) = f m ⊗ₜ[Rₛ] g n :=
  rfl

/-- **Stacks 00DL**, the substance: if `M'` and `N'` are localizations of `M` and `N` at `S`,
then `M' ⊗[Rₛ] N'` is a localization of `M ⊗[R] N` at `S`. -/
instance IsLocalization.isLocalizedModule_tensorMap
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (IsLocalization.tensorMap S Rₛ f g) := by
  unfold IsLocalization.tensorMap; infer_instance

/-- **Stacks 00DL.** Localization commutes with tensor product: for any localization `P` of
`M ⊗[R] N` at `S`, there is a canonical `Rₛ`-linear isomorphism `M' ⊗[Rₛ] N' ≃ P`. Taking
`Rₛ = S⁻¹R`, `M' = S⁻¹M`, `N' = S⁻¹N` and `P = S⁻¹(M ⊗_R N)` gives the isomorphism
`S⁻¹M ⊗_{S⁻¹R} S⁻¹N ≅ S⁻¹(M ⊗_R N)` of the Stacks project. -/
@[stacks 00DL, ega "0 1.3.4" "more general"]
noncomputable def IsLocalization.tensorLocalizeEquivTensor
    [IsLocalizedModule S f] [IsLocalizedModule S g] [IsLocalizedModule S h] :
    M' ⊗[Rₛ] N' ≃ₗ[Rₛ] P :=
  LinearEquiv.extendScalarsOfIsLocalization S Rₛ
    (IsLocalizedModule.linearEquiv S (IsLocalization.tensorMap S Rₛ f g) h)

/-- The isomorphism of Stacks 00DL is the canonical one: it sends `f m ⊗ₜ g n` to `h (m ⊗ₜ n)`.
Concretely, `(m/s) ⊗ (n/t) ↦ (m ⊗ n)/(st)`. -/
@[simp]
lemma IsLocalization.tensorLocalizeEquivTensor_tmul
    [IsLocalizedModule S f] [IsLocalizedModule S g] [IsLocalizedModule S h] (m : M) (n : N) :
    IsLocalization.tensorLocalizeEquivTensor S Rₛ f g h (f m ⊗ₜ g n) = h (m ⊗ₜ n) := by
  simpa using! IsLocalizedModule.linearEquiv_apply S
    (IsLocalization.tensorMap S Rₛ f g) h (m ⊗ₜ n)
