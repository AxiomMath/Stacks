module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationOnSiteOfChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.RingTheory.MilnorPatching.RelativeSquareFinitePresentation

/-!
# The glued module of finitely presented pieces is finitely presented

In the situation of Stacks 08KV, if `A` and `B'` are of finite presentation and flat over `Y` and
over `Z'`, and the base change `P ⟶ Y'` is locally of finite presentation on charts, then the
glued module `a_*A ×_{(c ≫ a)_*c^*A} b_*B'` is of finite presentation (Stacks 08KR, the
finite-presentation half of Stacks 08IW): on an affine chart diagram this is Stacks 08KP.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 08KP](https://stacks.math.columbia.edu/tag/08KP)
* [Stacks Project, Tag 08KR](https://stacks.math.columbia.edu/tag/08KR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

variable {A : Modules.{u, u} B S hS V.1 V.2} {B' : Modules.{u, u} B S hS U'.1 U'.2}
  {φ : (modulePushforward B S hS a).obj A ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A)}
  {ψ : (modulePushforward B S hS b).obj B' ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A)}
  (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)

/-- **The glued module of finitely presented pieces is finitely presented** (Stacks 08KR): if
`A` and `B'` are quasi-coherent of finite presentation and flat over `Y` and over `Z'`, and the
restriction of functions along every affine chart diagram of `P` over `Y'` is of finite
presentation, the glued module is of finite presentation. -/
theorem isFinitePresentationOnSite_glue (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ)
    (hAf : IsFlatOver B S hS V.2 pV.hom A) (hBf : IsFlatOver B S hS U'.2 pU'.hom B')
    (hAfp : A.IsFinitePresentationOnSite) (hBfp : B'.IsFinitePresentationOnSite)
    (hρ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom),
      IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U) →
      IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
        BigFppfOver.toScheme B S hS).obj dT.V) →
        (chartDiagramRestrict B S hS p dT).FinitePresentation)
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    (pullback φ ψ).IsFinitePresentationOnSite := by
  refine isFinitePresentationOnSite_of_finitePresentation_sections _
    (E.isQuasicoherentOnSite_glue φ ψ hA hB) (HasAffineChartDiagram B S hS p)
    (fun W hW => ?_) (mem_topology_of_hasAffineChartDiagram B S hS p)
  obtain ⟨hWaff, V₀, q, hq, hVaff⟩ := hW
  let dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom :=
    ⟨W, V₀, q, hq.symm⟩
  refine ⟨hWaff, ?_⟩
  obtain ⟨h₁, h₂⟩ := E.isBaseChangeAlong_glueFst_glueSnd dT hWaff hVaff hA hB hθ (hφ dT) (hψ dT)
  exact (E.isRelativeSquare dT hWaff hVaff).finitePresentation_of_flat (hρ dT hWaff hVaff)
    (E.flat_glue_sections dT hWaff hVaff hA hB hθ hAf hBf (hφ dT) (hψ dT)) h₁ h₂
    (module_finitePresentation_sections_of_isFinitePresentationOnSite A hA hAfp (E.WY dT)
      (E.isAffine_WY dT hWaff))
    (module_finitePresentation_sections_of_isFinitePresentationOnSite B' hB hBfp (E.WZ' dT)
      (E.isAffine_WZ' dT hWaff))

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
