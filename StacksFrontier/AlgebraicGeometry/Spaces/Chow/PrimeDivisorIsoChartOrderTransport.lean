module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# The order of vanishing of a section transported across an isomorphism, read on one chart

Let `e : X ≅ Y` be an isomorphism of decent, locally Noetherian, integral algebraic spaces over
`S`, let `Z` be a prime divisor of `X`, let `𝒩` be an invertible `𝒪_Y`-module and `τ` a regular
meromorphic section of it. This file proves

`ord_{e(Z), 𝒩}(τ) = ord_{Z, e^*𝒩}(e^*τ)`

at the canonical ratios of Stacks 0EPR, with no comparison of the henselian local rings at the
two generic points and no hypothesis relating the two canonical ratios.

Both sides are evaluated on an affine étale chart `V` of `X` trivializing `e^*𝒩`, as the order of
vanishing of the chart ratio in the total ring of fractions of `𝒪_{V, v}`
(`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`). Postcomposition
with `e` (Stacks 03LP, `AlgebraicGeometry.Space.smallEtalePostcomp`) carries `V` to a chart of `Y`
with the same underlying scheme and the same points, and on it the chart ratio of `e^*τ` is the
chart pullback of the chart ratio of `τ`. So the two orders of vanishing are those of one element
of one ring.

The chart data are: an affine étale chart `V` of `X`, a point `v` of its scheme over the generic
point of `Z`, a compatible family `eM` of free generators of `𝒩` over the postcomposed chart, and
a compatible family `eL` of free generators of `e^*𝒩` over `V` whose value at the identity chart
is the image of that of `eM` under the chart component of the unit of Stacks 03D7
(`AlgebraicGeometry.Space.modulePullbackChartFMap`), that is, the generator over `V` is the
pullback of the generator over the postcomposed chart.

## Main definitions

* `AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram`: a chart of `X` and its
  postcomposition with `f`, as a commuting square of étale scheme charts over `f` whose vertical
  morphism of schemes is the identity.

## Main results

* `AlgebraicGeometry.Space.chartSchemeToPoints_smallEtalePostcomp`: postcomposition carries the
  point of `|X|` determined by a chart point to the point of `|Y|` determined by the same chart
  point.
* `AlgebraicGeometry.Space.chartPointMeromorphicMap_chartMeromorphicFunctionPullback`: the chart
  pullback of a meromorphic function along
  `AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram`, read at a point of the chart scheme,
  is that function read there.
* `AlgebraicGeometry.Space.chartRatio_pullbackMeromorphicSection`: the chart ratio of the
  pullback of a meromorphic section is the chart pullback of its chart ratio.
* `AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq`: the
  order of vanishing of a regular meromorphic section along a prime divisor is carried by an
  isomorphism of spaces.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### A chart of `X` and its postcomposition, as one diagram of charts -/

/-- The diagram of étale scheme charts over an étale `f : X ⟶ Y` whose chart of `Y` is the
postcomposition of the given chart of `X` with `f` and whose vertical morphism of schemes is the
identity. -/
@[reducible] def etaleSmallPostcompChartDiagram (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS X.1) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := V
  V := (smallEtalePostcomp B S hS f hf).obj V
  g := 𝟙 ((SmallEtale.toOver B S hS Y.1).obj ((smallEtalePostcomp B S hS f hf).obj V))
  comm :=
    ((congrArg (· ≫ ((smallEtalePostcomp B S hS f hf).obj V).1.hom)
        (yoneda.map_id
          ((SmallEtale.toOver B S hS Y.1).obj ((smallEtalePostcomp B S hS f hf).obj V)))).trans
      (Category.id_comp _)).symm

/-- Postcomposition does not change the point of the space that a point of the chart scheme
determines, beyond carrying it along `f`. -/
theorem chartSchemeToPoints_smallEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS X.1) (x : chartScheme V) :
    chartSchemeToPoints B S hS Y.1 ((smallEtalePostcomp B S hS f hf).obj V) x =
      pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 V x) :=
  (pointsMap_chartSchemeToPoints B S hS X.1 f.hom V x).symm

/-! ### The reading of a meromorphic function at a chart point is unchanged -/

attribute [local instance] chartMeromorphicFunctionAlgebra

/-- Pullback of regular functions along the vertical morphism of schemes of
`AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram`, which is the identity, is the
identity. -/
theorem chartSectionPullback_postcompChartDiagram (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS X.1)
    (r : (structurePresheaf B S hS Y.1).obj (op ((smallEtalePostcomp B S hS f hf).obj V))) :
    (chartSectionPullback B S hS (etaleSmallPostcompChartDiagram B S hS f hf V)).hom r = r :=
  have h : chartSectionPullback B S hS (etaleSmallPostcompChartDiagram B S hS f hf V) = 𝟙 _ :=
    (Scheme.Γ_map_op _).trans
      ((congrArg Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map_id
        ((SmallEtale.toOver B S hS Y.1).obj
          ((smallEtalePostcomp B S hS f hf).obj V)))).trans Scheme.Hom.id_appTop)
  ConcreteCategory.congr_hom h r

/-- The chart pullback of a meromorphic function along
`AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram`, read at a point of the chart scheme, is
the function read there. -/
theorem chartPointMeromorphicMap_chartMeromorphicFunctionPullback (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (hfm : PullbacksMeromorphicSections B S hS f.hom)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (hV' : IsAffine (chartScheme ((smallEtalePostcomp B S hS f hf).obj V)))
    (hK : IsFractionRing ((structurePresheaf B S hS X.1).obj (op V))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)))
    (hK' : IsFractionRing
      ((structurePresheaf B S hS Y.1).obj (op ((smallEtalePostcomp B S hS f hf).obj V)))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj
        (op ((smallEtalePostcomp B S hS f hf).obj V))))
    (v : chartScheme V)
    (c : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj
      (op ((smallEtalePostcomp B S hS f hf).obj V))) :
    chartPointMeromorphicMap B S hS X V hV hK v
        (chartMeromorphicFunctionPullback B S hS f hfm
          (etaleSmallPostcompChartDiagram B S hS f hf V) c) =
      chartPointMeromorphicMap B S hS Y ((smallEtalePostcomp B S hS f hf).obj V) hV' hK' v c := by
  have := hK'
  refine RingHom.congr_fun (IsLocalization.ringHom_ext
    (M := ((structurePresheaf B S hS Y.1).obj
      (op ((smallEtalePostcomp B S hS f hf).obj V)))⁰)
    (j := (chartPointMeromorphicMap B S hS X V hV hK v).comp
      (chartMeromorphicFunctionPullback B S hS f hfm
        (etaleSmallPostcompChartDiagram B S hS f hf V)))
    (k := chartPointMeromorphicMap B S hS Y ((smallEtalePostcomp B S hS f hf).obj V) hV' hK' v)
    (RingHom.ext fun r ↦ ?_)) c
  refine Eq.trans (congrArg (chartPointMeromorphicMap B S hS X V hV hK v)
    (chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf B S hS f hfm
      (etaleSmallPostcompChartDiagram B S hS f hf V) r)) ?_
  refine Eq.trans (chartPointMeromorphicMap_algebraMap B S hS X V hV hK v _) ?_
  refine Eq.trans ?_ (chartPointMeromorphicMap_algebraMap B S hS Y
    ((smallEtalePostcomp B S hS f hf).obj V) hV' hK' v r).symm
  exact congrArg (fun z ↦ algebraMap ((chartScheme V).presheaf.stalk v)
      (FractionRing ((chartScheme V).presheaf.stalk v))
      (((chartScheme V).presheaf.germ ⊤ v trivial).hom z))
    (chartSectionPullback_postcompChartDiagram B S hS f hf V r)

/-! ### The chart ratio of a pulled-back section -/

/-- The chart ratio of the pullback of a meromorphic section is the chart pullback of its chart
ratio. Let `f : X ⟶ Y` be étale and pull back meromorphic sections, let `𝒩` be an `𝒪_Y`-module
free over the postcomposition `V'` of an étale chart `V` of `X` on a compatible family `eM`, and
let `eL` be a compatible family freely generating `f^*𝒩` over `V` whose value at the identity
chart is the image of the value of `eM` at the identity chart under the chart component of the
unit of Stacks 03D7. Then for every meromorphic section `t` of `𝒩`,

`(f^*t) / eL = f^♯(t / eM)`

in `𝒦_X(V)`. -/
theorem chartRatio_pullbackMeromorphicSection (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hfm : PullbacksMeromorphicSections B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1)
    (eM : (W : SmallEtale B S hS Y.1) →
      (W ⟶ (smallEtalePostcomp B S hS f hf).obj V) → M.val.obj (op W))
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1)
      (k : W ⟶ (smallEtalePostcomp B S hS f hf).obj V) (g : W' ⟶ W),
      (M.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ (smallEtalePostcomp B S hS f hf).obj V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (eL : (W : SmallEtale B S hS X.1) → (W ⟶ V) →
      ((modulePullback B S hS f).obj M).val.obj (op W))
    (hLcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (((modulePullback B S hS f).obj M).val.map g.op).hom (eL W k) = eL W' (g ≫ k))
    (hLfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eL W k)
    (heq : eL V (𝟙 V) =
      (modulePullbackChartFMap B S hS f M).app (etaleSmallPostcompChartDiagram B S hS f hf V)
        (eM ((smallEtalePostcomp B S hS f hf).obj V)
          (𝟙 ((smallEtalePostcomp B S hS f hf).obj V))))
    (t : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M) :
    chartRatio B S hS X.1 X.2 ((modulePullback B S hS f).obj M) V eL hLcompat hLfree
        (pullbackMeromorphicSection B S hS f M hfm t) =
      chartMeromorphicFunctionPullback B S hS f hfm (etaleSmallPostcompChartDiagram B S hS f hf V)
        (chartRatio B S hS Y.1 Y.2 M ((smallEtalePostcomp B S hS f hf).obj V) eM
          hMcompat hMfree t) := by
  refine chartRatio_eq_of_eval_eq B S hS X.1 X.2 ((modulePullback B S hS f).obj M) V eL
    hLcompat hLfree (pullbackMeromorphicSection B S hS f M hfm t) _ ?_
  rw [heq]
  refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS f M hfm t
    (etaleSmallPostcompChartDiagram B S hS f hf V) _
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS Y.1 Y.2 M
      ((smallEtalePostcomp B S hS f hf).obj V) eM hMcompat hMfree t)) ?_
  exact congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) V)
    (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hfm
      (etaleSmallPostcompChartDiagram B S hS f hf V) _ _)

/-! ### The transport of the order of vanishing of a section across an isomorphism -/

/-- The order of vanishing of a regular meromorphic section along a prime divisor is carried by
an isomorphism of spaces. Let `e : X ≅ Y` be an isomorphism of decent, locally Noetherian,
integral algebraic spaces over `S`, let `Z` be a prime divisor of `X`, let `𝒩` be an invertible
`𝒪_Y`-module and `τ` a regular meromorphic section of it. Let `V` be an affine étale chart of `X`
over which `e^*𝒩` is free on a compatible family `eL` that is the image of a compatible family
`eM` of free generators of `𝒩` over the postcomposed chart of `Y`, and let `v` be a point of the
chart scheme over the generic point of `Z`. Then

`ord_{e(Z), 𝒩}(τ) = ord_{Z, e^*𝒩}(e^*τ)`

at the canonical ratios of Stacks 0EPR on both sides. -/
theorem orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq
    (hXdec : IsDecentSpace B S hS X.1) (hYdec : IsDecentSpace B S hS Y.1)
    (Z : PrimeDivisor B S hS X.1) (e : X ≅ Y)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : IsInvertibleModule (B := B) Y M)
    (τ : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (hτ : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 M τ)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (hV' : IsAffine (chartScheme ((smallEtalePostcomp B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom)).obj V)))
    (eM : (W : SmallEtale B S hS Y.1) →
      (W ⟶ (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V) →
        M.val.obj (op W))
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1)
      (k : W ⟶ (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V)
      (g : W' ⟶ W), (M.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1)
      (k : W ⟶ (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (eL : (W : SmallEtale B S hS X.1) → (W ⟶ V) →
      ((modulePullback B S hS e.hom).obj M).val.obj (op W))
    (hLcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (((modulePullback B S hS e.hom).obj M).val.map g.op).hom (eL W k) = eL W' (g ≫ k))
    (hLfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eL W k)
    (heq : eL V (𝟙 V) =
      (modulePullbackChartFMap B S hS e.hom M).app
        (etaleSmallPostcompChartDiagram B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom) V)
        (eM ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V)
          (𝟙 ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V))))
    (v : chartScheme V)
    (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v)] :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    orderOfVanishingSection.{u, u} B S hS Y.2 hYdec
          (Z.pushforwardOfIso B S hS X.2 Y.2 hYdec ((ObjectProperty.ι _).mapIso e)) M τ
          ((Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
            ((ObjectProperty.ι _).mapIso e)).canonicalLocalRatio B S hS Y.2 hYdec M hM
              hYint hYN) =
      orderOfVanishingSection.{u, u} B S hS X.2 hXdec Z
        ((modulePullback B S hS e.hom).obj M)
        (pullbackMeromorphicSection B S hS e.hom M
          (pullbacksMeromorphicSections_of_flat B S hS e.hom.hom
            (isFlat_of_isEtale B S hS (isEtale_hom_of_isIso B S hS e.hom))) τ)
        (Z.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS e.hom).obj M)
          (modulePullbackInvertible e.hom M hM) hXint hXN) := by
  have : ∀ W : PrimeDivisor B S hS X.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS X.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have : ∀ W : PrimeDivisor B S hS Y.1,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
  have hwaX := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS X.2 hXint
  have hfinX := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hXN
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  have : Nontrivial
      ((chartScheme ((smallEtalePostcomp B S hS e.hom
        (isEtale_hom_of_isIso B S hS e.hom)).obj V)).presheaf.stalk v) :=
    inferInstanceAs (Nontrivial ((chartScheme V).presheaf.stalk v))
  have : IsNoetherianRing
      ((chartScheme ((smallEtalePostcomp B S hS e.hom
        (isEtale_hom_of_isIso B S hS e.hom)).obj V)).presheaf.stalk v) :=
    inferInstanceAs (IsNoetherianRing ((chartScheme V).presheaf.stalk v))
  have : Ring.KrullDimLE 1
      ((chartScheme ((smallEtalePostcomp B S hS e.hom
        (isEtale_hom_of_isIso B S hS e.hom)).obj V)).presheaf.stalk v) :=
    inferInstanceAs (Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v))
  have hσ := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS e.hom
    (pullbacksMeromorphicSections_of_flat B S hS e.hom.hom
      (isFlat_of_isEtale B S hS (isEtale_hom_of_isIso B S hS e.hom))) M hM τ hτ
  have hvY : chartSchemeToPoints B S hS Y.1
      ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V) v =
      (Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
        ((ObjectProperty.ι _).mapIso e)).genericPoint B S hS Y.1 := by
    rw [chartSchemeToPoints_smallEtalePostcomp B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom) V v, hv,
      Z.genericPoint_pushforwardOfIso B S hS X.2 Y.2 hYdec ((ObjectProperty.ι _).mapIso e)]
    rfl
  have hratio := chartRatio_pullbackMeromorphicSection B S hS e.hom
    (isEtale_hom_of_isIso B S hS e.hom)
    (pullbacksMeromorphicSections_of_flat B S hS e.hom.hom
      (isFlat_of_isEtale B S hS (isEtale_hom_of_isIso B S hS e.hom))) M V eM hMcompat hMfree
    eL hLcompat hLfree heq τ
  have hcX := IsUnit.map
    (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX V hV) v)
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwaX hfinX
      ((modulePullback B S hS e.hom).obj M) V hV eL hLcompat hLfree _ hσ)
  have hcY := IsUnit.map
    (chartPointMeromorphicMap B S hS Y
      ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V) hV'
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY _ hV') v)
    (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwaY hfinY M _ hV' eM
      hMcompat hMfree τ hτ)
  have hread : chartPointMeromorphicMap B S hS Y
        ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V) hV'
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY _ hV') v
        (chartRatio B S hS Y.1 Y.2 M _ eM hMcompat hMfree τ) =
      chartPointMeromorphicMap B S hS X V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX V hV) v
        (chartRatio B S hS X.1 X.2 ((modulePullback B S hS e.hom).obj M) V eL hLcompat hLfree
          (pullbackMeromorphicSection B S hS e.hom M _ τ)) :=
    ((congrArg (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX V hV) v)
        hratio).trans
      (chartPointMeromorphicMap_chartMeromorphicFunctionPullback B S hS e.hom
        (isEtale_hom_of_isIso B S hS e.hom) _ V hV hV'
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwaX hfinX V hV)
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY _ hV') v _)).symm
  refine Eq.trans ((Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
    ((ObjectProperty.ι _).mapIso e)).orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
    B S hS hYdec hYint hYN hwaY hfinY M hM τ hτ _ hV' eM hMcompat hMfree v hvY hcY) ?_
  refine Eq.trans ?_ (Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
    B S hS hXdec hXint hXN hwaX hfinX ((modulePullback B S hS e.hom).obj M)
    (modulePullbackInvertible e.hom M hM) _ hσ V hV eL hLcompat hLfree v hv hcX).symm
  exact Ring.ordTotalFracInt_congr
    ((chartScheme ((smallEtalePostcomp B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom)).obj V)).presheaf.stalk v) hcY hcX hread

end AlgebraicGeometry.Space

end
