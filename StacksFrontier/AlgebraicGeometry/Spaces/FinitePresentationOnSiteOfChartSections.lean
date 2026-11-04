module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianAffineChartFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Finite presentation on the small étale site from the sections over affine charts

A quasi-coherent `𝒪_F`-module whose sections over enough affine étale charts are finitely
presented modules is of finite presentation on the small étale site (Stacks 03DL(7)).  Over an
affine chart `Z` with `G(Z)` finitely presented, a presentation of `G(Z)` presents `G` on the
slice site at `Z`
(`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_of_finitePresentation`, the sections
over affine charts above `Z` being base changes of `G(Z)` by Descent, Proposition 03DX(2)), and
these slices cover.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_finitePresentation_sections`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A quasi-coherent module with finitely presented sections over enough affine charts is of
finite presentation** (Stacks 03DL(7)): if the étale charts satisfying `P` are affine with
finitely presented sections, and every sieve containing all the arrows out of such charts
covers, the module is of finite presentation on the small étale site. -/
theorem isFinitePresentationOnSite_of_finitePresentation_sections (G : Modules.{u, u} B S hS F hF)
    (hG : G.IsQuasicoherentOnSite) (P : SmallEtale B S hS F → Prop)
    (hP : ∀ W, P W →
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W)))
    (hcov : ∀ (U : SmallEtale B S hS F) (R : Sieve U),
      (∀ ⦃W : SmallEtale B S hS F⦄ (a : W ⟶ U), P W → R a) →
        R ∈ SmallEtale.topology B S hS F U) :
    G.IsFinitePresentationOnSite := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG
  refine ⟨fun U => ?_⟩
  refine ⟨Σ W : SmallEtale B S hS F, {a : W ⟶ U // P W}, fun i => i.1, fun i => i.2.1, ?_,
    fun i => ?_⟩
  · exact hcov U _ fun W a hW => Sieve.ofArrows_mk _ _ (⟨W, a, hW⟩ : Σ W : SmallEtale B S hS F,
      {a : W ⟶ U // P W})
  · obtain ⟨hWaff, hWfp⟩ := hP i.1 i.2.2
    have := hWfp
    exact hasFiniteGlobalPresentation_over_of_finitePresentation G hcart hWaff

end AlgebraicGeometry.Space

end
