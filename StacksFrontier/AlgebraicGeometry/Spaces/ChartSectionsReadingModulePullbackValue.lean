module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReadingPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartSplitting

/-!
# The value of a morphism out of an inverse image on a chart section, read on the scheme

Let `u : U ⟶ X` be a morphism of algebraic spaces, `ℰ` a quasi-coherent `𝒪_X`-module,
`d = (U_c ⟶ V)` a chart diagram over `u` and `φ : u^*ℰ ⟶ 𝓞'` a morphism of `𝒪_U`-modules. The
value of `φ` on the section of `u^*ℰ` over `U_c` attached to `x ∈ ℰ(V)` is read on the scheme of
`U_c` as the reading of `φ` applied to the pullback along `g : U_c ⟶ V` of the reading of `x`,
through the comparisons of readings: this is the naturality of
`AlgebraicGeometry.Space.chartSectionsReadingEquiv` combined with its value on chart sections of
inverse images. For `𝓞' = 𝒪_U`, given the unit compatibility of the identification
`chartSectionsReadingEquiv`, this computes the value of `φ` itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X U : AlgebraicSpaces B S hS} (u : U ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2)
  (hE : E.IsQuasicoherentOnSite) (d : ChartDiagram B S hS U.1 X.1 u.hom)
  (w : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS X d.V =
    chartToSpace B S hS U d.U ≫ u)

/-- **θ of the value of `φ` on a chart section of an inverse image**: the reading of `φ` applied
to the comparison of readings of the pulled-back reading of the section. -/
theorem chartSectionsReadingEquiv_map_modulePullbackChartSection
    {O' : Modules.{u, u} B S hS U.1 U.2} (φ : (modulePullback B S hS u).obj E ⟶ O')
    (x : E.val.obj (op d.V)) :
    chartSectionsReadingEquiv O' d.U
        (φ.val.app (op d.U) (modulePullbackChartSection B S hS u E d x)) =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS U d.U))
          (chartFppfObject B S hS U d.U).left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS U d.U)).inverse.map
          ((modulePullback B S hS (chartToSpace B S hS U d.U)).map φ))).app ⊤
        ((schemeReadingModulePullbackIso u E (chartToSpace B S hS U d.U)).inv.app ⊤
          ((schemeReadingPullbackIso E hE d.g w).hom.app ⊤
            (pullbackSectionHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
              (schemeReading E (chartToSpace B S hS X d.V)) ⊤ ⊤ le_top
              (chartSectionsReadingEquiv E d.V x)))) := by
  have h1 := chartSectionsReadingEquiv_naturality φ d.U (modulePullbackChartSection B S hS u E d x)
  have h2 := chartSectionsReadingEquiv_modulePullbackChartSection u E hE d w x
  rw [h2] at h1
  exact h1

/-- **The value of a morphism `u^*ℰ ⟶ 𝒪_U` on a chart section of the inverse image**, read on the
scheme of the chart, given the unit compatibility `hb` of `chartSectionsReadingEquiv` at `d.U`. -/
theorem modulePullbackChartSection_value_eq_reading
    (UA : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS U))
      (chartToSpace B S hS U d.U) ≅ Scheme.unitModule (chartScheme d.U))
    (hb : ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS U)).val.obj (op d.U),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS U)) d.U r) = r)
    (φ : (modulePullback B S hS u).obj E ⟶ SheafOfModules.unit (structureRingSheaf B S hS U))
    (x : E.val.obj (op d.V)) :
    φ.val.app (op d.U) (modulePullbackChartSection B S hS u E d x) =
      UA.hom.app ⊤
        (((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS U d.U))
          (chartFppfObject B S hS U d.U).left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS U d.U)).inverse.map
          ((modulePullback B S hS (chartToSpace B S hS U d.U)).map φ))).app ⊤
        ((schemeReadingModulePullbackIso u E (chartToSpace B S hS U d.U)).inv.app ⊤
          ((schemeReadingPullbackIso E hE d.g w).hom.app ⊤
            (pullbackSectionHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
              (schemeReading E (chartToSpace B S hS X d.V)) ⊤ ⊤ le_top
              (chartSectionsReadingEquiv E d.V x))))) := by
  have h1 := chartSectionsReadingEquiv_map_modulePullbackChartSection u E hE d w φ x
  have h2 := hb (φ.val.app (op d.U) (modulePullbackChartSection B S hS u E d x))
  rw [h1] at h2
  exact h2.symm

end AlgebraicGeometry.Space

end
