module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecChartMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecUniversalProperty
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism into a relative spectrum over a chart is compatible with change of chart

Let `X` be an algebraic space over `S` and `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras
on its small étale site. For an étale scheme chart `V` of `X`,
`AlgebraicGeometry.Space.chartRelativeSpecLift` turns a map of algebras
`A|_{chartScheme V} ⟶ g_* 𝒪_T` on the chart into a morphism
`T ⟶ \underline{Spec}_{chartScheme V}(A|_{chartScheme V})` over the chart. This file proves that
the construction commutes with change of chart: for a morphism `h : V₁ ⟶ V₂` of charts the lift
over `V₁` followed by `AlgebraicGeometry.Space.chartRelativeSpecChartMap` is the lift over `V₂` of
the chart-changed algebra map.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap`: the chart-changed algebra map, the
  algebra-level chart comparison `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom`
  followed by the direct image of the given map along `chartSchemeMap h`.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecLift_comp_chartRelativeSpecChartMap`: the two lifts
  agree.
* `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_naturality`: the chart-changed algebra map is
  natural in the algebra sheaf: the chart change of `α|_{V₁} ≫ φ` is the chart restriction of `α`
  at `V₂` followed by the chart change of `φ`.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V₁ V₂ : SmallEtale B S hS X.1} (h : V₁ ⟶ V₂)
    {T : Scheme.{u}} (g : T ⟶ chartScheme V₁)
    (φ : chartSchemeAlgebra B S hS X A V₁ ⟶ Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g)

/-- The chart-changed algebra map: a map `A|_{chartScheme V₁} ⟶ g_* 𝒪_T` of algebras on the smaller
chart becomes the map `A|_{chartScheme V₂} ⟶ (g ≫ chartSchemeMap h)_* 𝒪_T` on the larger one given
by the algebra-level chart comparison `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom`
followed by the direct image of the given map along `chartSchemeMap h`. -/
def chartSchemeAlgebraLiftMap :
    chartSchemeAlgebra B S hS X A V₂ ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra (g ≫ chartSchemeMap h) :=
  chartSchemeAlgebraPushforwardHom B S hS X A h ≫
    (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map φ

/-- The morphism of relative spectra over `chartSchemeMap h`, as a morphism of schemes over
`chartScheme V₂`. -/
def chartRelativeSpecChartOverHom :
    (Over.mk (chartRelativeSpecToChart B S hS X A hA V₁ ≫ chartSchemeMap h) :
        Over (chartScheme V₂)) ⟶
      Over.mk (chartRelativeSpecToChart B S hS X A hA V₂) :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₁
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₂
  Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom (chartSchemeMap h)
    (chartSchemeAlgebra B S hS X A V₂) (chartSchemeAlgebra B S hS X A V₁)
    (chartSchemeAlgebraPushforwardHom B S hS X A h)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.chartRelativeSpecChartOverHom`
is `AlgebraicGeometry.Space.chartRelativeSpecChartMap`. -/
theorem chartRelativeSpecChartOverHom_left :
    (chartRelativeSpecChartOverHom B S hS X A hA h).left =
      chartRelativeSpecChartMap B S hS X A hA h :=
  (chartRelativeSpecChartMap_eq B S hS X A hA h).symm

/-- The map on pushed-forward structure sheaves induced by
`AlgebraicGeometry.Space.chartRelativeSpecChartOverHom` is the algebra-level chart comparison, read
through the two universal isomorphisms. -/
theorem pushforwardAlgebraMap_chartRelativeSpecChartOverHom :
    haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₁
    haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₂
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (chartRelativeSpecChartOverHom B S hS X A hA h) =
      (chartRelativeSpecPushforwardIso B S hS X A hA V₂).hom ≫
        chartSchemeAlgebraPushforwardHom B S hS X A h ≫
          (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
            (chartRelativeSpecPushforwardIso B S hS X A hA V₁).inv :=
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₁
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₂
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverBaseHom
    (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V₂)
    (chartSchemeAlgebra B S hS X A V₁) (chartSchemeAlgebraPushforwardHom B S hS X A h)

/-- The lift into the relative spectrum over the smaller chart, read over the larger chart:
`AlgebraicGeometry.Space.chartRelativeSpecLift` at `V₁` pushed along `CategoryTheory.Over.map`. -/
def chartRelativeSpecLiftOverChart :
    (Over.mk (g ≫ chartSchemeMap h) : Over (chartScheme V₂)) ⟶
      Over.mk (chartRelativeSpecToChart B S hS X A hA V₁ ≫ chartSchemeMap h) :=
  (Over.map (chartSchemeMap h)).map (chartRelativeSpecLift B S hS X A hA V₁ g φ)

/-- The underlying morphism of schemes is unchanged by reading the lift over the larger chart. -/
theorem chartRelativeSpecLiftOverChart_left :
    (chartRelativeSpecLiftOverChart B S hS X A hA h g φ).left =
      (chartRelativeSpecLift B S hS X A hA V₁ g φ).left :=
  rfl

/-- The map on pushed-forward structure sheaves induced by
`AlgebraicGeometry.Space.chartRelativeSpecLiftOverChart` is the direct image along
`chartSchemeMap h` of the one induced by the lift itself, which is the given algebra map read
through the universal isomorphism. -/
theorem pushforwardAlgebraMap_chartRelativeSpecLiftOverChart :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (chartRelativeSpecLiftOverChart B S hS X A hA h g φ) =
      (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
        ((chartRelativeSpecPushforwardIso B S hS X A hA V₁).hom ≫ φ) :=
  Eq.trans
    (Stacks.AlgebraPullbackQcoh.algebraPushforward_map_pushforwardAlgebraMap
      (chartSchemeMap h) (chartRelativeSpecLift B S hS X A hA V₁ g φ)).symm
    (congrArg (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
      (pushforwardAlgebraMap_chartRelativeSpecLift B S hS X A hA V₁ g φ))

/-- The lift into the relative spectrum over a chart commutes with change of chart: for a morphism
`h : V₁ ⟶ V₂` of étale scheme charts of `X`, a scheme `T` over `chartScheme V₁` and a map
`φ : A|_{chartScheme V₁} ⟶ g_* 𝒪_T` of algebras on the smaller chart, the induced morphism
`T ⟶ \underline{Spec}_{V₁}(A|_{V₁})` followed by the morphism of relative spectra over
`chartSchemeMap h` is the morphism `T ⟶ \underline{Spec}_{V₂}(A|_{V₂})` induced by the
chart-changed algebra map `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap`. -/
@[sga "3 III 0.1.7" "0.1.7(a) functoriality"]
theorem chartRelativeSpecLift_comp_chartRelativeSpecChartMap :
    (chartRelativeSpecLift B S hS X A hA V₁ g φ).left ≫
        chartRelativeSpecChartMap B S hS X A hA h =
      (chartRelativeSpecLift B S hS X A hA V₂ (g ≫ chartSchemeMap h)
        (chartSchemeAlgebraLiftMap B S hS X A h g φ)).left := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₁
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V₂
  have key : chartRelativeSpecLiftOverChart B S hS X A hA h g φ ≫
        chartRelativeSpecChartOverHom B S hS X A hA h =
      chartRelativeSpecLift B S hS X A hA V₂ (g ≫ chartSchemeMap h)
        (chartSchemeAlgebraLiftMap B S hS X A h g φ) := by
    have halg : ((chartRelativeSpecPushforwardIso B S hS X A hA V₂).hom ≫
            chartSchemeAlgebraPushforwardHom B S hS X A h ≫
              (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
                (chartRelativeSpecPushforwardIso B S hS X A hA V₁).inv) ≫
          (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
            ((chartRelativeSpecPushforwardIso B S hS X A hA V₁).hom ≫ φ) =
        (chartRelativeSpecPushforwardIso B S hS X A hA V₂).hom ≫
          chartSchemeAlgebraPushforwardHom B S hS X A h ≫
            (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map φ := by
      rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
        Iso.inv_hom_id_assoc]
    refine chartRelativeSpecLift_ext B S hS X A hA V₂ (g ≫ chartSchemeMap h) ?_
    rw [Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp,
      pushforwardAlgebraMap_chartRelativeSpecLiftOverChart,
      pushforwardAlgebraMap_chartRelativeSpecChartOverHom,
      pushforwardAlgebraMap_chartRelativeSpecLift, chartSchemeAlgebraLiftMap]
    exact halg
  rw [← key, Over.comp_left, chartRelativeSpecChartOverHom_left,
    chartRelativeSpecLiftOverChart_left]

/-! ### Naturality of the chart change in the algebra sheaf -/

section Naturality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (α : A ⟶ C)
    {V₁ V₂ : SmallEtale B S hS X.1} (h : V₁ ⟶ V₂) {T : Scheme.{u}} (g : T ⟶ chartScheme V₁)
    (φ : chartSchemeAlgebra B S hS X C V₁ ⟶ Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g)

/-- The chart change of an algebra map is natural in the algebra sheaf: for a morphism `α : A ⟶ C`
of sheaves of commutative `𝒪_X`-algebras and a map `φ : C|_{chartScheme V₁} ⟶ g_* 𝒪_T` of algebras
on the smaller chart, the chart change of the composite `α|_{V₁} ≫ φ` is the chart restriction of
`α` at the larger chart followed by the chart change of `φ`. -/
theorem chartSchemeAlgebraLiftMap_naturality :
    (chartSchemeAlgebraFunctor B S hS X V₂).map α ≫
        chartSchemeAlgebraLiftMap B S hS X C h g φ =
      chartSchemeAlgebraLiftMap B S hS X A h g
        ((chartSchemeAlgebraFunctor B S hS X V₁).map α ≫ φ) :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun k ↦ k ≫ (Stacks.AffineAlgebraEquivalence.algebraPushforward
          (chartSchemeMap h)).map φ)
        (chartSchemeAlgebraPushforwardHom_naturality B S hS X α h))
      (Eq.trans (Category.assoc _ _ _)
        (congrArg (fun k ↦ chartSchemeAlgebraPushforwardHom B S hS X A h ≫ k)
          ((Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map_comp
            ((chartSchemeAlgebraFunctor B S hS X V₁).map α) φ).symm)))

end Naturality

end AlgebraicGeometry.Space

end
