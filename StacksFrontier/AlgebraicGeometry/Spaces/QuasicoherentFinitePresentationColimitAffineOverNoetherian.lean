module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverQuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardCounitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPreservesFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherianUnconditional

/-!
# Quasi-coherent modules on a space affine over a Noetherian space are filtered colimits

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` with `Y` Noetherian.
**Stacks 07UW**: every quasi-coherent `𝒪_X`-module is a filtered colimit of `𝒪_X`-modules of
finite presentation, over a small filtered index category.

## Main results

* `AlgebraicGeometry.Space.exists_isColimit_isFinitePresentation_of_isAffineHom`: every
  quasi-coherent `𝒪_X`-module is a filtered colimit, over a small filtered index category, of
  `𝒪_X`-modules of finite presentation.

## References

* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryTheory.FilteredColimitCokernelPresentation (IsCompactDiagram
  exists_small_isColimit_cokernel)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Stacks 07UW.**  Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S`
with `Y` Noetherian.  Then every quasi-coherent `𝒪_X`-module is a filtered colimit of
`𝒪_X`-modules of finite presentation, over a small filtered index category. -/
theorem exists_isColimit_isFinitePresentation_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ∃ (K : Type u) (inst : SmallCategory K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ Modules.{u, u} B S hS X.1 X.2)
        (φ : D ⟶ (Functor.const K).obj F),
        (∀ k, (D.obj k).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) := by
  classical
  have hNoeth := fun (Z : AlgebraicSpaces B S hS) hZN N hN =>
    exists_isFiltered_isColimit_isFinitePresentation_of_isNoetherian B S hS hZ Z hZN N hN
  have hpush := fun (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W) hg N hN =>
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS g hg N hN
  have hpull := isQuasicoherentOnSite_and_isFinitePresentation_modulePullback B S hS
  have hepi := epi_counit_modulePullbackAdjunction_app_of_isAffineHom B S hS
  obtain ⟨I, instI, hfilI, H, cH, e, hHfp, ⟨hcolH⟩, hepie, hqcH⟩ :=
    exists_epi_isColimit_isFinitePresentation_of_isAffineHom B S hS hZ hNoeth hpush hpull hepi
      f hf hY F hF
  have hkerqc : (kernel e).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_isCartesian B S hS X.1 X.2 e
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2)
  obtain ⟨J, instJ, hfilJ, G, cG, e', hGfp, ⟨hcolG⟩, hepie', -⟩ :=
    exists_epi_isColimit_isFinitePresentation_of_isAffineHom B S hS hZ hNoeth hpush hpull hepi
      f hf hY (kernel e) hkerqc
  obtain ⟨hqcX, hqsX⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom_of_isNoetherian
      B S hS hZ X Y f hf hY
  have hcompact : IsCompactDiagram I G := by
    intro j
    have := hGfp j
    exact preservesColimitsOfShape_coyoneda_of_isFinitePresentation B S hS X.1 X.2 hZ
      hqcX hqsX (G.obj j) I
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  obtain ⟨K, instK, hfilK, D, c, hcpt, ⟨hc⟩, hk⟩ :=
    exists_small_isColimit_cokernel cH cG (e' ≫ kernel.ι e) hcolH hcolG hcompact
  have hcok := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι e) (kernel.condition e)) (kernelIsKernel e)
  have hiso : c.pt ≅ F :=
    eqToIso hcpt ≪≫ cokernelEpiComp e' (kernel.ι e) ≪≫
      IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι e)) hcok
  refine ⟨K, instK, hfilK, D, c.ι ≫ (Functor.const K).map hiso.hom, fun k => ?_,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext hiso fun k => rfl)⟩⟩
  obtain ⟨j, i, α, -, heq⟩ := hk k
  have := hHfp i
  have := hGfp j
  rw [heq]
  infer_instance

end AlgebraicGeometry.Space

end
