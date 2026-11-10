module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact

/-!
# Projectivity of the sections of a chart restriction, read on the small étale site

For a morphism `g : Z₀ ⟶ U` of étale charts of an algebraic space `X` and a quasi-coherent
`𝒪_X`-module `G`, the Zariski pullback along `g` of the restriction
`AlgebraicGeometry.Space.restrictToChart` of `G` to `U` (the module of Stacks 0CVY) is identified
with the unsheafified restriction of `G` to `Z₀`, and projectivity of its global sections is
transported to the sections `G(Z₀)`.

## Main results

* `AlgebraicGeometry.Space.nonempty_pullback_restrictToChart_chartRestrictionSheaf`: the Zariski
  pullback along `g` of `G|_U` is isomorphic to `AlgebraicGeometry.Space.chartRestrictionSheaf` at
  `Z₀`, the unsheafified restriction of `G` to the chart `Z₀` whose sections over a Zariski open
  are the sections of `G` over the étale chart that open cuts out.
* `AlgebraicGeometry.Space.projective_sections_of_projective_pullback_restrictToChart`: if the
  global sections of that pullback are projective over the functions on a further object of the
  site, then so is `G(Z₀)`.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- For `G` a quasi-coherent `𝒪_X`-module and `g : Z₀ ⟶ U` a morphism of étale scheme charts of
`X`, the Zariski pullback of `G|_U` along the morphism of chart schemes is isomorphic to the
unsheafified restriction `AlgebraicGeometry.Space.chartRestrictionSheaf` of `G` to `Z₀`. -/
theorem nonempty_pullback_restrictToChart_chartRestrictionSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    {Z₀ U : SmallEtale B S hS X.1} (g : Z₀ ⟶ U) :
    Nonempty ((Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChart B S hS X.2 G U) ≅ chartRestrictionSheaf B S hS X G Z₀) := by
  obtain ⟨e⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS X G hG g
  exact ⟨(Scheme.Modules.pullback (chartSchemeMap g)).mapIso
      (restrictToChartIsoRestrictToChartScheme B S hS X.2 G U) ≪≫ e ≪≫
    (restrictToChartIsoRestrictToChartScheme B S hS X.2 G Z₀).symm ≪≫
    restrictToChartIsoChartRestrictionSheaf B S hS X G Z₀⟩

/-- Let `G` be a quasi-coherent `𝒪_X`-module, let `g : Z₀ ⟶ U` be a morphism of étale scheme
charts of `X`, let `E'` be an object of the big fppf site and let `k` be a morphism from the object
of `Z₀` to `E'`. If the global sections of the Zariski pullback of `G|_U` along `g` form a
projective module over the functions on `E'`, then so do the sections `G(Z₀)` of `G` over the
chart `Z₀`, the scalars acting through `k` in both cases. -/
theorem projective_sections_of_projective_pullback_restrictToChart
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    {Z₀ U : SmallEtale B S hS X.1} (g : Z₀ ⟶ U) (E' : BigFppfOver B S hS)
    (k : (SmallEtale.toOver B S hS X.1).obj Z₀ ⟶ E')
    (hproj :
      letI M := (Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChart B S hS X.2 G U)
      letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤) :=
        Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map k).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) Γ(M, ⊤)) :
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
    Module.Projective Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)
      (G.val.obj (op Z₀) : Type u) := by
  obtain ⟨e⟩ := nonempty_pullback_restrictToChart_chartRestrictionSheaf B S hS X G hG g
  let M := (Scheme.Modules.pullback (chartSchemeMap g)).obj
    (restrictToChart B S hS X.2 G U)
  let : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (Γ(M, ⊤) : Type u) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
  let : Module Γ((BigFppfOver.toScheme B S hS).obj E', ⊤) (G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map k).appTop.hom
  let φ₁ : (Γ(M, ⊤) : Type u) ≃+ (Γ(chartRestrictionSheaf B S hS X G Z₀, ⊤) : Type u) :=
    (((Scheme.Modules.toPresheaf (chartScheme Z₀)).mapIso e).app (op ⊤)).addCommGroupIsoToAddEquiv
  let φ₂ : (G.val.obj (op Z₀) : Type u) ≃+
      (Γ(chartRestrictionSheaf B S hS X G Z₀, ⊤) : Type u) :=
    (chartRestrictionSheafTopEquiv B S hS X G Z₀).toAddEquiv
  refine Stacks.AdicCompletion.SplitShortExact.projective_of_ringEquiv
    (RingEquiv.refl Γ((BigFppfOver.toScheme B S hS).obj E', ⊤)) (φ₁.trans φ₂.symm)
    (fun a x => ?_) hproj
  have h₁ : ∀ (c : Γ(chartScheme Z₀, ⊤)) (y : (Γ(M, ⊤) : Type u)), φ₁ (c • y) = c • φ₁ y :=
    fun c y => Scheme.Modules.Hom.app_smul e.hom c y
  have h₂ : ∀ (c : Γ(chartScheme Z₀, ⊤))
      (y : (Γ(chartRestrictionSheaf B S hS X G Z₀, ⊤) : Type u)),
      φ₂.symm (c • y) = c • φ₂.symm y :=
    (chartRestrictionSheafTopEquiv B S hS X G Z₀).symm.map_smul
  change φ₂.symm (φ₁ (((BigFppfOver.toScheme B S hS).map k).appTop.hom a • x)) =
    ((BigFppfOver.toScheme B S hS).map k).appTop.hom a • φ₂.symm (φ₁ x)
  rw [h₁, h₂]

end AlgebraicGeometry.Space

end
