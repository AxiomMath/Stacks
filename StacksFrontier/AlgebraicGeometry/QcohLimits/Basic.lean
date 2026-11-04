module

public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A kernel of a morphism of quasi-coherent modules is quasi-coherent

Let `X` be a scheme and let `φ : M ⟶ N` be a morphism of quasi-coherent `𝒪_X`-modules.  This
file proves that `kernel φ` is quasi-coherent.  It is the limit analogue of
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`, and it is the
ingredient missing from the implication of Stacks Tag 0H88 which says that an `A`-module that is
quasi-coherent over the structure sheaf is quasi-coherent over `A`.

## Main results

* `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`: a kernel of a morphism of
  quasi-coherent `𝒪_X`-modules is quasi-coherent.

## Implementation notes

The argument for colimits — a diagram of quasi-coherent modules on a spectrum comes from a
diagram of modules along `~`, which preserves the colimit because it is a left adjoint — has no
analogue here: `~` is not a right adjoint, and Mathlib does not record that it is exact.  What is
used instead is that quasi-coherence is detected by localization on basic opens,
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
together with its converse
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` for `M` and `N`.
That reduces the statement to the fact that localization of modules commutes with kernels,
which is `LinearMap.toKerLocalized_isLocalizedModule`.

Two identifications connect the two sides.  On sections over an affine open `U` and over a basic
open `X.basicOpen a` inside it, `Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel` identifies
the sections of `kernel φ` with the kernel of the map on sections, by
`Stacks.AlgebraicGeometry.QcohLimits.kerEquivOfExact`; and the localization of the map on
sections over `U` is the map on sections over `X.basicOpen a`, by uniqueness of maps out of a
localization together with the naturality of `φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.AlgebraicGeometry.QcohLimits

/-- **A kernel of a morphism of quasi-coherent modules is quasi-coherent.** -/
@[ega "I 4.1.1" "kernel"]
instance isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (kernel φ).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule_restrictₗ _ fun U hU a ↦ ?_
  let := moduleOfLE M (X.basicOpen_le a)
  let := moduleOfLE N (X.basicOpen_le a)
  let := moduleOfLE (kernel φ) (X.basicOpen_le a)
  have hloc : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
  have htM : IsScalarTower Γ(X, U) Γ(X, X.basicOpen a) Γ(M, X.basicOpen a) :=
    isScalarTowerOfLE M (X.basicOpen_le a)
  have htN : IsScalarTower Γ(X, U) Γ(X, X.basicOpen a) Γ(N, X.basicOpen a) :=
    isScalarTowerOfLE N (X.basicOpen_le a)
  have hfM : IsLocalizedModule.Away a (restrictₗ M (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ M hU a rfl (X.basicOpen_le a)
  have hfN : IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ N hU a rfl (X.basicOpen_le a)
  set gV := (IsLocalizedModule.map (Submonoid.powers a) (restrictₗ M (X.basicOpen_le a))
    (restrictₗ N (X.basicOpen_le a))) (appₗ φ U) with hgVdef
  have hmap : gV = appOfLEₗ φ (X.basicOpen_le a) := by
    refine IsLocalizedModule.linearMap_ext (Submonoid.powers a)
      (restrictₗ M (X.basicOpen_le a)) (restrictₗ N (X.basicOpen_le a)) ?_
    rw [hgVdef, IsLocalizedModule.map_comp]
    exact LinearMap.ext fun x ↦ (app_naturality φ (X.basicOpen_le a) x).symm
  have hexV : Function.Exact (appOfLEₗ (kernel.ι φ) (X.basicOpen_le a)) gV := fun b ↦ by
    rw [show gV b = φ.app (X.basicOpen a) b from congr($hmap b)]
    exact exact_app_kernel φ (X.basicOpen a) b
  set eU := kerEquivOfExact (appₗ (kernel.ι φ) U) (appₗ φ U) (injective_app_kernel_ι φ U)
    (exact_app_kernel φ U) with heU
  set eV := kerEquivOfExact (appOfLEₗ (kernel.ι φ) (X.basicOpen_le a)) gV
    (injective_app_kernel_ι φ (X.basicOpen a)) hexV with heV
  have hτ : IsLocalizedModule.Away a (LinearMap.toKerIsLocalized (Submonoid.powers a)
      (restrictₗ M (X.basicOpen_le a)) (restrictₗ N (X.basicOpen_le a)) (appₗ φ U)) :=
    LinearMap.toKerLocalized_isLocalizedModule Γ(X, X.basicOpen a) _ _ _ _
  have hcomm : (LinearMap.toKerIsLocalized (Submonoid.powers a)
        (restrictₗ M (X.basicOpen_le a)) (restrictₗ N (X.basicOpen_le a))
        (appₗ φ U)) ∘ₗ eU.toLinearMap =
      eV.toLinearMap ∘ₗ restrictₗ (kernel φ) (X.basicOpen_le a) := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.toKerIsLocalized_apply_coe, heU, heV]
    exact (app_naturality (kernel.ι φ) (X.basicOpen_le a) x).symm
  have h1 : IsLocalizedModule.Away a ((LinearMap.toKerIsLocalized (Submonoid.powers a)
      (restrictₗ M (X.basicOpen_le a)) (restrictₗ N (X.basicOpen_le a))
      (appₗ φ U)) ∘ₗ eU.toLinearMap) :=
    (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers a)
      eU.toLinearMap eU.bijective).mpr hτ
  rw [hcomm] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_left (S := Submonoid.powers a)
    eV.toLinearMap eV.bijective).mp h1

end Stacks.AlgebraicGeometry.QcohLimits

end
