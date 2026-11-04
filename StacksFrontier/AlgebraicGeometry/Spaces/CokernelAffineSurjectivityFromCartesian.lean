module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity

/-!
# Cokernels of modules cartesian on affine charts

Let `F` be an algebraic space and let `f : M ⟶ N` be a morphism of `𝒪_F`-modules on its small étale
site, with `M` and `N` cartesian on affine charts. The canonical epimorphisms
`CategoryTheory.Abelian.factorThruImage f` and `CategoryTheory.Limits.cokernel.π f` are surjective
on the sections over every affine étale chart; consequently the image and the cokernel of `f` are
cartesian on affine charts, and the cokernel is quasi-coherent on the small étale site. This is the
cokernel clause of Stacks 03M1(3), with the base change criterion of Descent, Proposition 03DX(2)
in place of quasi-coherence.

## Main results

* `AlgebraicGeometry.Space.surjective_val_app_factorThruImage_of_cartesian`: the canonical
  epimorphism of a morphism of modules cartesian on affine charts onto its image is surjective on
  the sections over an affine chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_image_of_cartesian`: the image of a morphism
  of modules cartesian on affine charts is cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian`: the projection onto the
  cokernel of a morphism of modules cartesian on affine charts is surjective on the sections over
  an affine chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel_of_cartesian`: being cartesian on
  affine charts is stable under cokernels.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_cartesian`: the cokernel of a morphism
  of `𝒪_F`-modules cartesian on affine charts is quasi-coherent on the small étale site.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The canonical epimorphism of a morphism of `𝒪_F`-modules cartesian on affine charts onto its
image is surjective on the sections over an affine étale chart.** -/
theorem surjective_val_app_factorThruImage_of_cartesian
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((Abelian.factorThruImage f).val.app (op U)) :=
  surjective_val_app_of_epi_of_cartesian (Abelian.factorThruImage f) hM
    (isCartesianOnAffineCharts_kernel_factorThruImage f hM hN) U hU

/-- **The image of a morphism of `𝒪_F`-modules cartesian on affine charts is cartesian on affine
charts.** -/
theorem isCartesianOnAffineCharts_image_of_cartesian
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (Abelian.image f) := by
  have hk : IsCartesianOnAffineCharts (kernel f) := isCartesianOnAffineCharts_kernel f hM hN
  have hki : IsCartesianOnAffineCharts (kernel (cokernel.π (kernel.ι f))) :=
    IsCartesianOnAffineCharts.of_iso (asIso (Abelian.factorThruImage (kernel.ι f))) hk
  have hiso : ∀ W : SmallEtale B S hS F, Function.Surjective
      ((Abelian.factorThruImage (kernel.ι f)).val.app (op W)) := fun W =>
    (bijective_moduleHom_app (Abelian.factorThruImage (kernel.ι f))
      (inv (Abelian.factorThruImage (kernel.ι f))) (IsIso.hom_inv_id _)
      (IsIso.inv_hom_id _) W).2
  exact IsCartesianOnAffineCharts.of_iso (Abelian.coimageIsoImage f)
    (isCartesianOnAffineCharts_cokernel (kernel.ι f) (cokernel.π (kernel.ι f))
      (fun W hW => surjective_val_app_of_epi_of_cartesian (cokernel.π (kernel.ι f)) hM hki W hW)
      (fun W _ => SheafOfModules.exact_val_app_cokernel_π (kernel.ι f) (op W) (hiso W))
      hk hM)

/-- **The projection onto the cokernel of a morphism of `𝒪_F`-modules cartesian on affine charts is
surjective on the sections over an affine étale chart.** -/
theorem surjective_val_app_cokernel_π_of_cartesian
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((cokernel.π f).val.app (op U)) :=
  surjective_val_app_of_epi_of_cartesian (cokernel.π f) hN
    (isCartesianOnAffineCharts_image_of_cartesian f hM hN) U hU

/-- **The cokernel of a morphism of `𝒪_F`-modules cartesian on affine charts is cartesian on affine
charts.** -/
theorem isCartesianOnAffineCharts_cokernel_of_cartesian
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (cokernel f) :=
  isCartesianOnAffineCharts_cokernel f (cokernel.π f)
    (fun U hU => surjective_val_app_cokernel_π_of_cartesian f hM hN U hU)
    (fun U hU => SheafOfModules.exact_val_app_cokernel_π f (op U)
      (surjective_val_app_factorThruImage_of_cartesian f hM hN U hU))
    hM hN

/-- **The cokernel of a morphism of `𝒪_F`-modules cartesian on affine charts is quasi-coherent on
the small étale site.** -/
theorem isQuasicoherentOnSite_cokernel_of_cartesian
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    (cokernel f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_cokernel_of_cartesian f hM hN)

end AlgebraicGeometry.Space

end
