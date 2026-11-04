module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart

/-!
# Sections of the cokernel of a monomorphism over an affine chart

Let `φ : F ⟶ G` be a monomorphism of `𝒪_X`-modules on an algebraic space `X` with `F` cartesian on
affine charts (for instance quasi-coherent). Over an affine étale chart `W` of `X` the sequence
`F(W) → G(W) → (coker φ)(W) → 0` is exact.

## Main results

* `AlgebraicGeometry.Space.surjective_cokernel_π_app_of_mono`: if `F` is cartesian on affine
  charts, then `G(W) → (coker φ)(W)` is surjective for every affine étale chart `W`.
* `AlgebraicGeometry.Space.exact_cokernel_π_app_of_mono`: the sequence
  `F(W) → G(W) → (coker φ)(W)` is exact for every étale chart `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- If `φ : F ⟶ G` is a monomorphism of `𝒪_X`-modules and `F` is cartesian on affine charts, then
the map `G(W) → (coker φ)(W)` is surjective for every étale chart `W` with affine underlying
scheme. -/
theorem surjective_cokernel_π_app_of_mono {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [Mono φ] (hF : IsCartesianOnAffineCharts F) (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective ((cokernel.π φ).val.app (op W)) := by
  refine surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS X (cokernel.π φ)
    inferInstance ?_ W hW
  exact IsCartesianOnAffineCharts.of_iso
    (IsLimit.conePointUniqueUpToIso (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _))
      (limit.isLimit _)) hF

/-- If `φ : F ⟶ G` is a monomorphism of `𝒪_X`-modules, then for every étale chart `W` the sequence
`F(W) → G(W) → (coker φ)(W)` of sections is exact. -/
theorem exact_cokernel_π_app_of_mono {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G)
    [Mono φ] (W : SmallEtale B S hS X.1) :
    Function.Exact (φ.val.app (op W)) ((cokernel.π φ).val.app (op W)) :=
  SheafOfModules.exact_val_app_cokernel_π φ (op W)
    (bijective_moduleHom_app (Abelian.factorThruImage φ) (inv (Abelian.factorThruImage φ))
      (IsIso.hom_inv_id _) (IsIso.inv_hom_id _) W).2

end AlgebraicGeometry.Space

end
