module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingQuasicoherent

/-!
# Global sections of a quasi-coherent module on an algebraic space, read on one étale chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `F` be a quasi-coherent
`𝒪_X`-module and let `U` be an étale chart of `X` whose points cover every weakly associated
point of `F`.  Stacks 0CUP asserts that the restriction `Γ(X, F) → Γ(U, F)` is then injective:
a global section dying on `U` dies everywhere.

The argument of the source is followed.  A global section `s` dying on `U` determines a
morphism `𝒪_X → F` whose image `F'` is quasi-coherent, as the image of a morphism of
quasi-coherent modules.  The section is a global section of
`AlgebraicGeometry.Space.outsideChartSubmodule`, the subsheaf of sections of `F` whose support
maps outside the image of `|U| → |X|`, so `F'` is a submodule of that subsheaf, which has no
weakly associated point.  Hence `F'` has no weakly associated point (Stacks 0CTZ), so `F' = 0`
by Stacks 0CU0, and `s = 0`.

## Main results

* `AlgebraicGeometry.Space.eval_eq_zero_of_eval_eq_zero`: a global section of a quasi-coherent
  `F` dying on `U` dies on every étale chart.
* `AlgebraicGeometry.Space.injective_sections_eval_of_weaklyAssociatedPoints_subset`:
  **Stacks 0CUP**.

## Implementation notes

Global sections are `SheafOfModules.sections`, the compatible families on the whole small étale
site; the site has no terminal object, so there is no single chart carrying `Γ(X, F)`.  The
restriction to the chart `U` is evaluation at `U`, and the conclusion is injectivity of that
evaluation.  The difference of two global sections is formed inside the proof of the main
theorem rather than through the additive structure of
`Stacks.Cohomology.SiteModules.sectionsAddCommGroup`.

The module universe is the universe `u` of the schemes, where the abelian structure of
`AlgebraicGeometry.Space.Modules`, quasi-coherence of images and Stacks 0CU0 are available.  The
instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`, whose module universe cannot be
`u`, is removed in this file.

## References

* [Stacks Project, Tag 0CUP](https://stacks.math.columbia.edu/tag/0CUP)
* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- A global section of a quasi-coherent `𝒪_X`-module `F` vanishing on an étale chart `U` whose
points carry every weakly associated point of `F` vanishes over every étale chart.

This is the argument of the source.  Let `F'` be the image of the morphism `𝒪_X → F`
determined by the section; it is quasi-coherent, as the image of a morphism of quasi-coherent
modules.  The section is a global section of the subsheaf
`AlgebraicGeometry.Space.outsideChartSubmodule` of sections supported outside the image of the
points of `U`, so `F'` is a submodule of that subsheaf, which has no weakly associated point by
`AlgebraicGeometry.Space.weaklyAssociatedPoints_outsideChartSubmodule_eq_empty`.  Hence `F'` has
no weakly associated point (Stacks 0CTZ) and vanishes by Stacks 0CU0, and so does the section,
which is the image of `1`. -/
theorem eval_eq_zero_of_eval_eq_zero
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (U : SmallEtale B S hS X.1)
    (hU : weaklyAssociatedPoints B S hS X F ⊆ Set.range (chartSchemeToPoints B S hS X.1 U))
    (s : F.sections) (hs : s.eval (op U) = 0) (W : SmallEtale B S hS X.1) :
    s.eval (op W) = 0 := by
  set N := outsideChartSubmodule B S hS X F U
  let φ : SheafOfModules.unit _ ⟶ N.toSheafOfModules :=
    N.toSheafOfModules.unitHomEquiv.symm (outsideChartSection B S hS X F U s hs)
  have hψ : F.unitHomEquiv (φ ≫ N.ι) = s := by
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    rfl
  have hI : (image (φ ≫ N.ι)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_image_unconditional B S hS X.1 X.2 (φ ≫ N.ι) inferInstance ‹_›
  have hzero : IsZero (image (φ ≫ N.ι)) :=
    isZero_of_weaklyAssociatedPoints_eq_empty B S hS X _
      (Set.subset_empty_iff.mp
        ((weaklyAssociatedPoints_outsideChartSubmodule_eq_empty B S hS X F U hU) ▸
          weaklyAssociatedPoints_subset_of_mono B S hS
            (image.lift { I := N.toSheafOfModules, m := N.ι, e := φ, fac := rfl })))
  have h0 : φ ≫ N.ι = 0 := by
    rw [← image.fac (φ ≫ N.ι), hzero.eq_of_src (image.ι (φ ≫ N.ι)) 0, comp_zero]
  rw [← hψ, h0]
  exact map_zero ((0 : SheafOfModules.unit _ ⟶ F).val.app (op W)).hom

/-- **Stacks Project, Tag 0CUP.** Let `F` be a quasi-coherent `𝒪_X`-module on an algebraic space
`X` and let `U` be an étale chart of `X` such that every weakly associated point of `F` lies in
the image of `|U| → |X|`.  Then the restriction `Γ(X, F) → Γ(U, F)` of global sections to the
chart is injective. -/
@[stacks 0CUP]
theorem injective_sections_eval_of_weaklyAssociatedPoints_subset
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (U : SmallEtale B S hS X.1)
    (weakAss_subset :
      weaklyAssociatedPoints B S hS X F ⊆ Set.range (chartSchemeToPoints B S hS X.1 U)) :
    Function.Injective fun s : F.sections => s.eval (op U) := by
  intro s t hst
  have hcompat : ∀ ⦃W V : (SmallEtale B S hS X.1)ᵒᵖ⦄ (f : W ⟶ V),
      F.val.map f (s.eval W - t.eval W) = s.eval V - t.eval V := fun {_ _} f =>
    (map_sub (ConcreteCategory.hom (F.val.map f)) _ _).trans
      (congr_arg₂ (· - ·) (PresheafOfModules.sections_property s f)
        (PresheafOfModules.sections_property t f))
  have hd : (PresheafOfModules.sectionsMk (fun W => s.eval W - t.eval W) hcompat).eval (op U)
      = 0 := sub_eq_zero_of_eq hst
  refine PresheafOfModules.sections_ext _ _ fun W => sub_eq_zero.mp ?_
  exact eval_eq_zero_of_eval_eq_zero B S hS X F U weakAss_subset _ hd W.unop

end AlgebraicGeometry.Space

end
