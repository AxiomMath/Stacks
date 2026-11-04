module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite

/-!
# Surjectivity on affine-chart sections from a uniform hypothesis

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`Modules.{u, u} B S hS F hF` be its `𝒪_F`-modules. The statements of this file take a hypothesis
`h03DW`: every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`) is surjective on the sections over every
affine étale chart. From it they derive the surjectivity hypotheses `hpi` and `him` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian` and `h03DW` of
`AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact` and
`AlgebraicGeometry.Space.isQuasicoherent_right_of_shortExact`.

## Main results

* `AlgebraicGeometry.Space.surjective_val_app_of_isSplitEpi`: a split epimorphism of
  `𝒪_F`-modules is surjective on the sections over every étale chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel_factorThruImage`: the kernel of the
  canonical epimorphism of `f` onto its image is cartesian on affine charts as soon as the source
  and target of `f` are.
* `AlgebraicGeometry.Space.surjective_val_app_factorThruImage_of_h03DW`: the canonical
  epimorphism onto the image is surjective on the sections over affine charts.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_image_of_h03DW`: the image of a morphism of
  modules cartesian on affine charts is cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_h03DW`: the projection onto the
  cokernel is surjective on the sections over affine charts.
* `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_h03DW`: the right-hand map of a
  short exact sequence is surjective on the sections over affine charts.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DW`: the cokernel of a morphism
  of modules cartesian on affine charts is quasi-coherent on the small étale site.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Split epimorphisms -/

/-- A split epimorphism of `𝒪_F`-modules is surjective on the sections over every étale
chart. -/
theorem surjective_val_app_of_isSplitEpi {G G' : Modules.{u, m} B S hS F hF} (q : G ⟶ G')
    [IsSplitEpi q] (U : SmallEtale B S hS F) :
    Function.Surjective (q.val.app (op U)) := fun y ↦
  ⟨(section_ q).val.app (op U) y,
    congrArg (fun l ↦ l y) (moduleHom_app_comp_eq_id (section_ q) q (IsSplitEpi.id q) U)⟩

/-! ### The kernel of the canonical epimorphism onto the image -/

/-- The kernel of the canonical epimorphism of `f` onto its image is cartesian on affine charts
as soon as the source and the target of `f` are. -/
theorem isCartesianOnAffineCharts_kernel_factorThruImage
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (kernel (Abelian.factorThruImage f)) :=
  IsCartesianOnAffineCharts.of_iso
    (kernelIsoOfEq (Abelian.image.fac f).symm ≪≫
      kernelCompMono (Abelian.factorThruImage f) (Abelian.image.ι f))
    (isCartesianOnAffineCharts_kernel f hM hN)

/-! ### Surjectivity on affine-chart sections -/

/-- If every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is
surjective on the sections over affine étale charts, then so is the canonical epimorphism of `f`
onto its image, for `f` between modules cartesian on affine charts. -/
theorem surjective_val_app_factorThruImage_of_h03DW
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((Abelian.factorThruImage f).val.app (op U)) :=
  h03DW (Abelian.factorThruImage f) inferInstance
    (isCartesianOnAffineCharts_kernel_factorThruImage f hM hN) U hU

/-- If every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is
surjective on the sections over affine étale charts, then the image of a morphism of
`𝒪_F`-modules cartesian on affine charts is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_image_of_h03DW
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (Abelian.image f) := by
  have hk : IsCartesianOnAffineCharts (kernel f) := isCartesianOnAffineCharts_kernel f hM hN
  have hki : IsCartesianOnAffineCharts (kernel (cokernel.π (kernel.ι f))) :=
    IsCartesianOnAffineCharts.of_iso (asIso (Abelian.factorThruImage (kernel.ι f))) hk
  have hiso : ∀ W : SmallEtale B S hS F, Function.Surjective
      ((Abelian.factorThruImage (kernel.ι f)).val.app (op W)) := fun W ↦
    (bijective_moduleHom_app (Abelian.factorThruImage (kernel.ι f))
      (inv (Abelian.factorThruImage (kernel.ι f))) (IsIso.hom_inv_id _)
      (IsIso.inv_hom_id _) W).2
  exact IsCartesianOnAffineCharts.of_iso (Abelian.coimageIsoImage f)
    (isCartesianOnAffineCharts_cokernel (kernel.ι f) (cokernel.π (kernel.ι f))
      (fun W hW ↦ h03DW (cokernel.π (kernel.ι f)) inferInstance hki W hW)
      (fun W _ ↦ SheafOfModules.exact_val_app_cokernel_π (kernel.ι f) (op W) (hiso W))
      hk hM)

/-- If every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is
surjective on the sections over affine étale charts, then so is the projection onto the cokernel
of a morphism between modules cartesian on affine charts. -/
theorem surjective_val_app_cokernel_π_of_h03DW
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((cokernel.π f).val.app (op U)) :=
  h03DW (cokernel.π f) inferInstance
    (isCartesianOnAffineCharts_image_of_h03DW f h03DW hM hN) U hU

/-- If every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is
surjective on the sections over affine étale charts, then so is the right-hand map of a short
exact sequence whose left-hand term is cartesian on affine charts. -/
theorem surjective_g_val_app_of_shortExact_of_h03DW
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (h₁ : IsCartesianOnAffineCharts T.X₁) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective (T.g.val.app (op U)) := by
  obtain ⟨e, -⟩ := SheafOfModules.exists_isKernelIso_of_shortExact hT
  exact h03DW T.g hT.epi_g (IsCartesianOnAffineCharts.of_iso e h₁) U hU

/-! ### Quasi-coherence of cokernels -/

/-- If every epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is
surjective on the sections over affine étale charts, then the cokernel of a morphism of
`𝒪_F`-modules cartesian on affine charts is quasi-coherent on the small étale site. -/
theorem isQuasicoherentOnSite_cokernel_of_h03DW {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    (cokernel f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_cokernel_of_isCartesian B S hS F hF f hM hN
    (surjective_val_app_cokernel_π_of_h03DW f h03DW hM hN)
    (surjective_val_app_factorThruImage_of_h03DW f h03DW hM hN)

end AlgebraicGeometry.Space

end
