module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionIdChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Relative flatness of a direct image along a finite morphism of algebraic spaces

Let `φ : Z ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`g : Y ⟶ T` be a morphism of algebraic spaces and let `𝒢` be a quasi-coherent `𝒪_Z`-module which
is flat over `T` along `φ ≫ g`.  Then the direct image `φ_*𝒢` is flat over `T` along `g`.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartSchemeModulePushforwardIso`: the restriction of the
  direct image `φ_*𝒢` along a representable `φ` to an étale scheme chart `U` of the target is the
  scheme-level direct image of the restriction of `𝒢` to the chart `U ×_Y Z`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartToSpace_baseChangeChart`: the base-changed chart
  `U ×_Y Z` and the chart `U` form a cartesian square over `φ`.
* `AlgebraicGeometry.Space.isFlatOver_modulePushforward_of_isFinite`: **the direct image of a
  quasi-coherent module flat over `T` along a finite morphism is flat over `T`.**

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)
  (U : SmallEtale B S hS Y.1)

/-- **The base-changed chart is cartesian over `f`**: the represented space of the chart
`U ×_Y X` of `X`, mapping to `X` by its structure morphism and to the represented space of `U` by
the cartesian projection, is the fibre product of `f` and the structure morphism of `U`. -/
theorem isPullback_chartToSpace_baseChangeChart :
    IsPullback (chartToSpace B S hS X (baseChangeChart B S hS f hrep U))
      (representedSpaceMap B S hS (baseChangeChartHom B S hS f hrep U)) f
      (chartToSpace B S hS Y U) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F)) (isPullback_baseChangeChartHom B S hS f hrep U)

/-- **The chart restriction of a direct image along a representable morphism.**  The
restriction of `f_*𝒢` to an étale scheme chart `U` of `Y` is the scheme-level direct image, along
the cartesian projection `U ×_Y X ⟶ U`, of the restriction of `𝒢` to the chart `U ×_Y X` of
`X`. -/
def restrictToChartSchemeModulePushforwardIso (G : Modules.{u, u} B S hS X.1 X.2) :
    restrictToChartScheme B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj G) U ≅
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (baseChangeChartHom B S hS f hrep U).left)).obj
        (restrictToChartScheme B S hS X.1 X.2 G (baseChangeChart B S hS f hrep U)) := by
  rw [restrictToChartScheme_eq_atIdEtaleChart B S hS Y U,
    restrictToChartScheme_eq_atIdEtaleChart B S hS X (baseChangeChart B S hS f hrep U)]
  exact (restrictToChartSchemeFunctor B S hS _ _ _).mapIso
      ((modulePushforwardEtaleBaseChangeIso B S hS _ _ _ _
        (isPullback_chartToSpace_baseChangeChart B S hS f hrep U)
        (isEtale_chartToSpace B S hS Y U)).app G).symm ≪≫
    restrictToChartSchemePushforwardIdEtaleChartIso' B S hS
      (baseChangeChartHom B S hS f hrep U) _

end Chart

/-- **The direct image along a finite morphism preserves flatness over the base.**  Let
`φ : Z ⟶ Y` be finite, `g : Y ⟶ T` and `𝒢` a quasi-coherent `𝒪_Z`-module flat over `T` along
`φ ≫ g`.  Then `φ_*𝒢` is flat over `T` along `g`. -/
theorem isFlatOver_modulePushforward_of_isFinite {Z Y T : AlgebraicSpaces B S hS} (φ : Z ⟶ Y)
    (hφ : IsFinite B S hS φ.hom) (g : Y ⟶ T) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (hG : G.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS Z.2 (φ ≫ g).hom G) :
    IsFlatOver B S hS Y.2 g.hom ((modulePushforward B S hS φ).obj G) := by
  intro d
  let hrep := relativelyRepresentable_hom_of_isFinite B S hS φ hφ
  let W := baseChangeChart B S hS φ hrep d.U
  let p := baseChangeChartHom B S hS φ hrep d.U
  have hp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) :=
    isFinite_baseChangeChartHom B S hS φ hrep hφ d.U
  let e : ChartDiagram B S hS Z.1 T.1 (φ ≫ g).hom :=
    { U := W
      V := d.V
      g := p ≫ d.g
      comm := by
        show hrep.fst d.U.obj.hom ≫ φ.hom ≫ g.hom = yoneda.map (p ≫ d.g) ≫ d.V.obj.hom
        rw [Functor.map_comp, Category.assoc, ← d.comm, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ g.hom) (isPullback_baseChangeChartHom B S hS φ hrep d.U).w }
  have hW := hflat e
  change AlgebraicGeometry.IsFlatOver _ (restrictToChart B S hS Z.2 G W) at hW
  have : SheafOfModules.IsQuasicoherent (restrictToChart B S hS Z.2 G W) :=
    isQuasicoherent_restrictToChart B S hS Z G hG W
  show AlgebraicGeometry.IsFlatOver _ (restrictToChart B S hS Y.2 _ d.U)
  rw [restrictToChart_eq_restrictToChartScheme] at hW ⊢
  refine (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
    (restrictToChartSchemeModulePushforwardIso B S hS φ hrep d.U G)).2 ?_
  have : SheafOfModules.IsQuasicoherent (restrictToChartScheme B S hS Z.1 Z.2 G W) := by
    rw [← restrictToChart_eq_restrictToChartScheme]; infer_instance
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS φ hrep d.U).left) := by
    have : _root_.AlgebraicGeometry.IsFinite (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) (baseChangeChartHom B S hS φ hrep d.U).left) := hp
    infer_instance
  exact (AlgebraicGeometry.isFlatOver_pushforward_iff _ ((BigFppfOver.toScheme B S hS).map d.g)
    _).1 hW

end AlgebraicGeometry.Space

end
