module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFinitePresentationBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of finite presentation along an fpqc covering of algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module. If
`{f_i : X_i → X}` is an fpqc covering of algebraic spaces for which every `f_i^* F` is of finite
presentation, then `F` is of finite presentation ([Stacks, Tag 060V]). This is deduced from the
case of schemes, [Stacks, Tag 05B0], by étale localization.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc`: a quasi-coherent module whose
  pullbacks along an fpqc covering are of finite presentation is of finite presentation.

## References

* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `F` be a quasi-coherent `𝒪_X`-module on an algebraic space `X` and let
`{f_i : X_i → X}` be an fpqc covering such that each `f_i^* F` is an `𝒪_{X_i}`-module of finite
presentation. Then `F` is an `𝒪_X`-module of finite presentation. -/
@[stacks 060V]
theorem isFinitePresentation_of_pullback_fpqc {I : Type v} {X : AlgebraicSpaces B S hS}
    (Xᵢ : I → AlgebraicSpaces B S hS) (f : ∀ i, Xᵢ i ⟶ X)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (hfp : ∀ i, ((modulePullback B S hS (f i)).obj F).IsFinitePresentation) :
    F.IsFinitePresentation := by
  refine (isFinitePresentation_iff_forall_over B S hS X.obj X.property F).2 fun V ↦ ?_
  obtain ⟨T, c, g, hc, hcov, hsq⟩ := exists_chart_fpqc_refinement B S hS Xᵢ f hf V
  refine (isFinitePresentation_restrictToChart_iff B S hS X F hF V).1 ?_
  have : (restrictToChart B S hS X.property F V).IsQuasicoherent :=
    isQuasicoherent_restrictToChart_viaIdEtaleChart B S hS X F hF V
  refine _root_.AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover
    (restrictToChart B S hS X.property F V)
    { I₀ := I
      X := fun i ↦ (BigFppfOver.toScheme B S hS).obj (T i)
      f := fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)
      mem₀ := by simpa using hcov } fun i ↦ ?_
  refine Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (chartRestrictionBaseChangeIso B S hS (f i) F hF V
      ⟨CostructuredArrow.mk (c i), hc i⟩ (g i) (hsq i)).symm ?_
  exact (isFinitePresentation_restrictToChart_iff B S hS (Xᵢ i)
      ((modulePullback B S hS (f i)).obj F)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) F hF)
      ⟨CostructuredArrow.mk (c i), hc i⟩).2
    ((isFinitePresentation_iff_forall_over B S hS (Xᵢ i).obj (Xᵢ i).property _).1 (hfp i) _)

end AlgebraicGeometry.Space
