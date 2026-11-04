module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.Glue
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent

/-!
# Invertibility of the module glued from invertible chart modules

Let `𝓜` be a chart-scheme module system on an algebraic space `X`
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem`).  If every chart module `M U` is finite
locally free of rank one on the scheme of the chart — equivalently, invertible — then the glued
module `𝓜.glue` is an invertible `𝒪_X`-module on the small étale ringed site of `X`.

The proof is the one of `AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`:
invertibility on the small étale site of `X` is finite local freeness of rank one
(`AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`), a rank is local
on the site, and on the slice at an affine chart `A` the glued module has rank one as soon as its
Zariski chart module of Stacks 03DX (2) has
(`Space.isFiniteLocallyFreeOfRank_over_of_isFiniteLocallyFreeOfRank_chartSchemeModule`).
That chart module is the restriction of the glued module to the chart scheme
(`AlgebraicGeometry.Space.restrictToChartSchemeIsoChartSchemeModule`), which is `M A`
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem.restrictToChartSchemeGlueIso`).

## Main results

* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.isFiniteLocallyFreeOfRank_glue`: if every
  chart module has rank `r` on the Zariski site of its chart scheme, the glued module has rank
  `r` on the small étale ringed site of `X`.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.isInvertible_glue_of_isFiniteLocallyFreeOfRank`
  and `AlgebraicGeometry.Space.ChartSchemeModuleSystem.isInvertible_glue`: **the glued module of
  rank-one, respectively invertible, chart modules is invertible.**
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.ChartSchemeModuleSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (𝓜 : ChartSchemeModuleSystem B S hS X)

/-- **If every chart module has rank `r`, the glued module has rank `r`** on the small étale
ringed site of `X`.  A rank is local on the site, the affine étale charts cover it, and on the
slice at an affine chart `A` the rank of the glued module is the rank of its Zariski chart
module, which is `M A`. -/
theorem isFiniteLocallyFreeOfRank_glue (r : ℕ)
    (h : ∀ U : SmallEtale B S hS X.1,
      RingedSite.IsFiniteLocallyFreeOfRank (chartScheme U).zariskiRingedSite (𝓜.M U) r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) 𝓜.glue r := by
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover
      (smallEtaleRingedSite B S hS X.obj X.property) 𝓜.glue r).2
    ⟨{T : SmallEtale B S hS X.obj // IsAffine (chartScheme T)}, fun T ↦ T.1,
      SmallEtale.coversTop_affineCharts B S hS X.obj, ?_⟩
  rintro ⟨A, -⟩
  refine isFiniteLocallyFreeOfRank_over_of_isFiniteLocallyFreeOfRank_chartSchemeModule B S hS X
    𝓜.glue 𝓜.isQuasicoherentOnSite_glue A r ?_
  exact RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    ((𝓜.restrictToChartSchemeGlueIso A).symm ≪≫
      restrictToChartSchemeIsoChartSchemeModule B S hS X 𝓜.glue 𝓜.isQuasicoherentOnSite_glue A)
    (h A)

/-- **The glued module of a system of rank-one chart modules is invertible** on the small étale
ringed site of `X`: it has rank one there
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem.isFiniteLocallyFreeOfRank_glue`), and a module
of rank one on the small étale site of an algebraic space is invertible
(`AlgebraicGeometry.Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`). -/
theorem isInvertible_glue_of_isFiniteLocallyFreeOfRank
    (h : ∀ U : SmallEtale B S hS X.1,
      RingedSite.IsFiniteLocallyFreeOfRank (chartScheme U).zariskiRingedSite (𝓜.M U) 1) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).property 𝓜.glue :=
  (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one 𝓜.glue).2
    (𝓜.isFiniteLocallyFreeOfRank_glue 1 h)

/-- **The glued module of a system of invertible chart modules is invertible** on the small
étale ringed site of `X`.  An invertible module on a scheme has rank one on its Zariski ringed
site (`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`, the ringed
site of opens of a scheme being locally ringed), so this is
`AlgebraicGeometry.Space.ChartSchemeModuleSystem.isInvertible_glue_of_isFiniteLocallyFreeOfRank`.
-/
theorem isInvertible_glue
    (h : ∀ U : SmallEtale B S hS X.1, Stacks.Ample.IsInvertibleModule (chartScheme U) (𝓜.M U)) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).property 𝓜.glue := by
  refine 𝓜.isInvertible_glue_of_isFiniteLocallyFreeOfRank fun U ↦ ?_
  have : Stacks.SheafOfModules.IsInvertible (chartScheme U).zariskiRingedSite.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (chartScheme U).zariskiRingedSite.O).property
      (𝓜.M U) := h U
  exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
    (chartScheme U).zariskiRingedSite _
    (Stacks.Picard.ZariskiSite.schemeRingedSite_isLocallyRinged (chartScheme U))

end AlgebraicGeometry.Space.ChartSchemeModuleSystem

end
