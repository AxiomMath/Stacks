module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAffineTest
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapRingLevelZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.RingTheory.TensorProduct.LTensorVanishingTower

/-!
# The vanishing locus over an affine object of the site, read on rings

Let `D` be a situation of Stacks 083F whose target is the algebraic space of an **affine** object
`Y₀` of the big fppf category over `S`, and let `V₀` be an affine étale chart of its source space
through which every morphism from a representable presheaf factors — the shape the chart case of
Stacks 083J part (2) reaches once the situation has been base changed to an affine stage and the
source space replaced by an affine chart, where `V₀` is the identity chart of that chart.

This file identifies the vanishing locus of such a situation at an affine test scheme `T` with
the vanishing of a single extension of scalars of the sections of `u` over `V₀`,

`u_T = 0` if and only if `𝒪_X(V₀) ⊗_{Γ(Y₀, ⊤)} Γ(T, ⊤)` kills `u(V₀)`,

assembles from it the ring-level reading of the vanishing locus,
`AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus`, with `base = Γ(Y₀, ⊤)`, and
concludes the chart case of clause (2) of Stacks 083J at the affine stages of an arbitrary
situation, so that this case need not be assumed.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartRingLevelZeroLocus` and
  `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartRingLevelZeroLocus`: the
  **limit-free** replacements of the chart case of clause (2) of Stacks 083J and of that case at
  the affine stages, namely the ring-level reading of the vanishing locus of the chart situation.
  They are stated here, where they are proved, and not beside the two reductions
  `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineChartZeroDescent_of_ringLevelZeroLocus`
  and
  `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus`
  that consume them: those supply the limit content and so live above this file, and stating the
  predicates beside them made this file import
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`, which put the
  affine endgame of Stacks 0CWC — which needs this file — above the clauses of Stacks 0CWC that
  consume that endgame.  Nothing of the limit content is stated here: neither predicate mentions
  a limit.
* `AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom`: the structure morphism of a test
  scheme, read as a morphism of the big fppf category.
* `AlgebraicGeometry.Space.ModuleMapSituation.chartDiagramTestHom`: the morphism of the category
  from the chart of `X ×_{Y₀} T` of a chart diagram to the test object.
* `AlgebraicGeometry.Space.ModuleMapSituation.ringLevelZeroLocusOfTerminalAffineChart`: the
  ring-level reading of the vanishing locus.

## Main results

* `AlgebraicGeometry.Space.Modules.app_eq_zero_of_isCartesianOnAffineCharts`: vanishing of a map
  of modules passes from an affine chart to an affine chart over it, when the source module is
  cartesian on affine charts.
* `AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom_comp` and
  `AlgebraicGeometry.Space.ModuleMapSituation.appTop_testSiteHom`: the algebra structures on the
  functions of the test schemes are functorial, which is the field `algebraMap_sections`.
* `AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom_comp_of_chartDiagram`: the two routes
  from the chart of `X ×_{Y₀} T` to `Y₀` agree.
* `AlgebraicGeometry.Space.ModuleMapSituation.lTensor_val_app_eq_zero_of_isZeroAt` and
  `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_lTensor_val_app_eq_zero`: the two
  directions of the displayed equivalence, assembled as
  `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_baseChange_val_app`.
* `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineChartRingLevelZeroLocus_of_eq` and
  `AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartRingLevelZeroLocus`: the chart
  case of clause (2), in its limit-free form, over an affine object of the site and then at
  every affine stage of an arbitrary situation.

## Implementation notes

**Why the base ring is `Γ(Y₀, ⊤)` and not `Γ(S, ⊤)`.**  The field
`AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus.base` is free: any ring carrying
functorial algebra structures on the functions of the test schemes type-checks, so taking the
functions on the base would fill every field except `zero_iff` with no mathematics at all.  It
would also make `zero_iff` **false**, hence that structure unsatisfiable and every theorem
carrying it vacuous: for `S = \Spec k`, `Y₀ = W = \Spec k[t]`, `ℱ = 𝒢 = 𝒪` and `u`
multiplication by `t`, the base change of `u` vanishes at the test object `T = \Spec k[t]/(t)`
over `Y₀`, while the base change of the sections of `u` to `k[t] ⊗_k k[t]/(t)` sends `1 ⊗ 1` to
`t ⊗ 1 ≠ 0`.  What forces the correct ring is the Cartesian square
`AlgebraicGeometry.Space.ModuleMapSituation.isPullback_chartScheme_testChartDiagram`, whose
cospan vertex is the scheme of `Y₀`: the ring of functions of the base-changed chart is the
tensor product over `Γ(Y₀, ⊤)` and over nothing else.

**The two directions are not the same statement, and only one of them is about one chart.**  The
forward direction reads the vanishing of `u_T` at a *single* chart of `X ×_{Y₀} T`, the base
change of `V₀`, and transports it along
`AlgebraicGeometry.Space.ModuleMapSituation.chartRingTestAlgEquiv`.  The converse has to produce
vanishing over *every* chart, and that is what the hypothesis on `V₀` is for: every chart of
`X ×_{Y₀} T` maps to the base change of `V₀`
(`CategoryTheory.Functor.relativelyRepresentable.lift`), which is affine, and vanishing descends
along a morphism of affine charts because the inverse image of `ℱ` is quasi-coherent hence
cartesian on affine charts.

**Why not a cover by arbitrary affine chart diagrams.**  The obvious route for the converse —
`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows` together with the cover-density of
`AlgebraicGeometry.Space.exists_ofArrows_hasAffineChartDiagram` — does not work here, and the
obstruction is a spelling one rather than a mathematical one.  It would compare the sections of
`ℱ` over two different chart *spaces*, that of `V₀` and that of the diagram's chart of `X`, so
the base ring of the extension of scalars would have to be converted between the two spellings
of the chart ring; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeVanishingChartRing.lean` record that this
conversion does not terminate inside the heartbeat limit, and measurement confirms that the
single step which performs it under a `LinearMap.lTensor` is what exceeds the limit, while each
of the ring identification, the module-carrier identification and the chart-wise criterion is
cheap on its own.  The route taken here keeps one spelling throughout — the chart-space one, in
which the chart-wise criterion delivers its right-hand side — and so needs no conversion.

**No flatness of `𝒢`.**  The ideal-theoretic route through
`Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero` is unavailable: its hypothesis is flatness
of the target sections, which the chart case does not provide.  Only quasi-coherence is used,
which the situation carries.

**Where the algebra structures come from.**  All of them are pullback of functions along a
morphism of the big fppf category: `AlgebraicGeometry.Space.chartRestrict` along a chart
morphism, `AlgebraicGeometry.Space.chartDiagramRestrict` along the vertical morphism of a chart
diagram, and `AlgebraicGeometry.Space.chartToSiteRingHom` along a morphism to `Y₀` are all
`Scheme.Hom.appTop` of the image of that morphism, definitionally.  So every scalar tower needed
is an equality of composites in the category, and the one that is not formal is
`AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom_comp_of_chartDiagram`: the two routes
from the chart of `X ×_{Y₀} T` to `Y₀`, through `V₀` and through `T`, agree, which is the
commutation of the Cartesian square defining `X ×_{Y₀} T`.

**The transport of the target equality.**  The hypothesis that the target of the situation is the
algebraic space of `Y₀` is the equality of objects `D.Y = AlgebraicGeometry.schemeSpace Y₀`, the
form the rest of this development uses, and the statements about structure morphisms have that
equality's `eqToHom` composed in.  Each proof that has to see the corner as `yoneda.obj Y₀`
destructures the situation and substitutes, after which the transport is the identity; no
`eqToHom` survives into a statement about rings.

## References

* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Modules

/-- **Vanishing of a map of modules passes from an affine chart to an affine chart over it, when
the source module is cartesian on affine charts.**

Over a morphism `ψ : U' ⟶ U` of affine étale charts the sections of a cartesian module over `U'`
are the base change of the sections over `U`
(`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`), so every section over `U'` is in the image
of the base change comparison; and the comparison is natural in the module
(`AlgebraicGeometry.Space.app_sectionsBaseChange`), so the map on sections over `U'` is the
extension of scalars of the map on sections over `U`, which is zero.

This is the direction that vanishing does *not* have for free: the other direction, from `U'` to
a chart over it, is the sheaf property and needs no cartesianness
(`AlgebraicGeometry.Space.Modules.map_app_eq_zero`).  Only the source module is assumed
cartesian; nothing is assumed of the target. -/
theorem app_eq_zero_of_isCartesianOnAffineCharts {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : IsCartesianOnAffineCharts M) (φ : M ⟶ N)
    {U U' : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U'))
    (ψ : U' ⟶ U) (h : φ.val.app (op U) = 0) :
    φ.val.app (op U') = 0 := by
  let := chartAlgebra (hF := X.2) ψ
  have hzero : (φ.val.app (op U)).hom = 0 := congrArg ModuleCat.Hom.hom h
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨z, hz⟩ := (hM U U' hU hU' ψ).2 x
  rw [← hz, app_sectionsBaseChange φ ψ z, hzero]
  rw [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  rfl

end Modules

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀)

/-! ### The limit-free chart hypotheses of clause (2) -/

/-- **The chart case of clause (2), reduced to a limit-free hypothesis.**  The chart case
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent` with its conclusion — a
statement about limits — replaced by the ring-level reading of the vanishing locus of the chart
situation, `AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus`, which mentions no
limit at all.

This is strictly more primitive than the chart case, and
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineChartZeroDescent_of_ringLevelZeroLocus`
is the reduction.  What that proof supplies is the whole limit content of the chart case: the
global sections of a limit of affine schemes are the filtered colimit of the global sections of
the stages (Stacks 01YW), and Algebra, Lemma 05LI part (1) holds along the resulting system of
base-changed algebras.  What remains carried is the identification of vanishing at a *single*
affine test scheme with the vanishing of a base change of the sections of `u` on the chart —
the step the implementation notes of this file name. -/
def HasAffineChartRingLevelZeroLocus (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  SheafOfModules.IsFiniteTypeOnSite D.F →
  ∀ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
    ∀ g : schemeSpace W ⟶ D.X, IsFlat B S hS g.hom →
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
          Set.range (pointsMap B S hS (schemeSpace W).1 g.hom) →
        ∀ (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
          (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite),
          Nonempty ((D.pullbackSituation g hF hG).RingLevelZeroLocus)

/-- **The chart case at the affine stages, reduced to the limit-free hypothesis.**  The
ring-level reading of the vanishing locus of the chart situation over each affine stage; this is
the strictly more primitive replacement of
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartZeroDescent`. -/
def HasAffineStageChartRingLevelZeroLocus (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
    (D.baseChangeTestScheme T).HasAffineChartRingLevelZeroLocus

/-! ### The structure morphism of a test scheme as a morphism of the category -/

/-- **The structure morphism of a test scheme, as a morphism of the big fppf category.**  The
target of the situation being the algebraic space of `Y₀`, the structure morphism of a test
scheme is a morphism of representable presheaves, hence the Yoneda image of a morphism of the
category. -/
def testSiteHom (T : D.SchemesOver) : T.left ⟶ Y₀ :=
  yoneda.preimage (T.hom.hom ≫ (eqToHom hDY).hom)

/-- The Yoneda image of `AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom` is the
structure morphism of the test scheme. -/
theorem yoneda_map_testSiteHom (T : D.SchemesOver) :
    yoneda.map (testSiteHom B S hS D hDY T) = T.hom.hom ≫ (eqToHom hDY).hom :=
  Functor.map_preimage _ _

/-- The morphisms of the category attached to the test schemes are compatible with morphisms of
test schemes. -/
theorem testSiteHom_comp {T T' : D.SchemesOver} (k : T ⟶ T') :
    k.left ≫ testSiteHom B S hS D hDY T' = testSiteHom B S hS D hDY T := by
  refine yoneda.map_injective ?_
  have h : yoneda.map k.left ≫ T'.hom.hom = T.hom.hom :=
    congrArg (fun m : (schemeSpaceFunctor B S hS).obj T.left ⟶ D.Y => m.hom)
      (CostructuredArrow.w k)
  have e1 : yoneda.map (k.left ≫ testSiteHom B S hS D hDY T') =
      yoneda.map k.left ≫ yoneda.map (testSiteHom B S hS D hDY T') := yoneda.map_comp _ _
  have e2 : yoneda.map k.left ≫ yoneda.map (testSiteHom B S hS D hDY T') =
      (yoneda.map k.left ≫ T'.hom.hom) ≫ (eqToHom hDY).hom := by
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (fun m : yoneda.obj T'.left ⟶ yoneda.obj Y₀ => yoneda.map k.left ≫ m)
      (yoneda_map_testSiteHom B S hS D hDY T')
  have e3 : (yoneda.map k.left ≫ T'.hom.hom) ≫ (eqToHom hDY).hom =
      yoneda.map (testSiteHom B S hS D hDY T) :=
    (congrArg (fun m : yoneda.obj T.left ⟶ D.Y.obj => m ≫ (eqToHom hDY).hom) h).trans
      (yoneda_map_testSiteHom B S hS D hDY T).symm
  exact e1.trans (e2.trans e3)

/-- **The algebra structures on the functions of the test schemes are functorial.**  This is the
field `algebraMap_sections` of
`AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus` for the algebra structures given
by pullback of functions along
`AlgebraicGeometry.Space.ModuleMapSituation.testSiteHom`. -/
theorem appTop_testSiteHom {T T' : D.SchemesOver} (k : T ⟶ T')
    (r : (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)) :
    (D.testScheme.map k).appTop.hom
        (((BigFppfOver.toScheme B S hS).map (testSiteHom B S hS D hDY T')).appTop.hom r) =
      ((BigFppfOver.toScheme B S hS).map (testSiteHom B S hS D hDY T)).appTop.hom r := by
  rw [← testSiteHom_comp B S hS D hDY k, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-! ### The two routes from a chart of the base change to `Y₀` -/

/-- **The chart of `X ×_{Y₀} T` of an affine chart diagram lies over the test object.**  Its
structure morphism to the base-change space, followed by the projection to the test object, is a
morphism of representable presheaves, hence the Yoneda image of a morphism of the category. -/
def chartDiagramTestHom (T : D.SchemesOver)
    (d : ChartDiagram B S hS (D.baseChangeSpace T).1 D.X.1 (D.baseChangeProjection T).hom) :
    d.U.1.left ⟶ T.left :=
  yoneda.preimage (d.U.1.hom ≫ (D.baseChangeInclusion T).hom)

/-- **The two routes from the chart of `X ×_{Y₀} T` to `Y₀` agree**: the one through the chart
`d.V` of `X` and the terminal chart `V₀`, and the one through the test object.

This is the commutation of the Cartesian square defining `X ×_{Y₀} T`
(`AlgebraicGeometry.Space.ModuleMapSituation.isPullback_hom_baseChangeSpace`), read through the
commutation carried by the chart diagram and the one carried by the chart morphism to `V₀`.  It
is the only step of the file that is not formal, and it is what makes the ring of functions of
`d.U` an algebra over `𝒪_X(V₀) ⊗_{Γ(Y₀, ⊤)} Γ(T, ⊤)`. -/
theorem testSiteHom_comp_of_chartDiagram (T : D.SchemesOver)
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (d : ChartDiagram B S hS (D.baseChangeSpace T).1 D.X.1 (D.baseChangeProjection T).hom)
    (ι : d.V ⟶ V₀) :
    (d.g ≫ ι.hom.left) ≫ α =
      chartDiagramTestHom B S hS D T d ≫ testSiteHom B S hS D hDY T := by
  revert ι
  revert d
  revert hα
  revert α
  revert V₀
  revert T
  revert hDY
  obtain ⟨X, Y, f, F, G, qF, qG, u⟩ := D
  dsimp only
  rintro rfl T V₀ α hα d ι
  refine yoneda.map_injective ?_
  have hα' : V₀.1.hom ≫ f.hom = yoneda.map α := (Category.comp_id _).symm.trans hα
  have hk' : yoneda.map (testSiteHom B S hS _ rfl T) = T.hom.hom :=
    (yoneda_map_testSiteHom B S hS _ rfl T).trans (Category.comp_id _)
  have hβ : yoneda.map (chartDiagramTestHom B S hS _ T d) =
      d.U.1.hom ≫ (ModuleMapSituation.baseChangeInclusion _ T).hom := Functor.map_preimage _ _
  have hι : yoneda.map ι.hom.left ≫ V₀.1.hom = d.V.1.hom := CostructuredArrow.w ι.hom
  have hw : (ModuleMapSituation.baseChangeProjection _ T).hom ≫ f.hom =
      (ModuleMapSituation.baseChangeInclusion _ T).hom ≫ T.hom.hom :=
    (ModuleMapSituation.isPullback_hom_baseChangeSpace B S hS _ T).w
  have hιf : yoneda.map ι.hom.left ≫ V₀.1.hom ≫ f.hom = d.V.1.hom ≫ f.hom := by
    rw [← Category.assoc, hι]
  have key : yoneda.map d.g ≫ d.V.1.hom ≫ f.hom =
      d.U.1.hom ≫ (ModuleMapSituation.baseChangeInclusion _ T).hom ≫ T.hom.hom := by
    rw [← Category.assoc, ← d.comm, Category.assoc, hw]
  have hleft : yoneda.map ((d.g ≫ ι.hom.left) ≫ α) =
      yoneda.map d.g ≫ d.V.1.hom ≫ f.hom := by
    rw [Functor.map_comp, Functor.map_comp, ← hα']
    exact (Category.assoc _ _ _).trans (congrArg (fun m => yoneda.map d.g ≫ m) hιf)
  have hright : yoneda.map (chartDiagramTestHom B S hS _ T d ≫ testSiteHom B S hS _ rfl T) =
      d.U.1.hom ≫ (ModuleMapSituation.baseChangeInclusion _ T).hom ≫ T.hom.hom := by
    rw [Functor.map_comp, hβ, hk']
    exact Category.assoc _ _ _
  exact hleft.trans (key.trans hright.symm)

/-! ### The vanishing locus at an affine test scheme, read on the chart ring

The chart ring used below is the ring of functions of the identity chart of the *chart space* of
`V₀`, and the map is the sections of `u` read there.  That is the spelling in which the
chart-wise criterion
`AlgebraicGeometry.Space.ModuleMapSituation.val_app_testChartDiagram_eq_zero_iff_lTensor`
delivers its right-hand side, and it is kept throughout; the implementation notes of this file
record why it must not be converted to the sections over `V₀` itself.  Two consequences of that
choice show up as noise in what follows, and both are deliberate.

First, the `CommRing` instance of that ring is supplied by hand: the identity chart's declared
type is `SmallEtale B S hS (yoneda.obj _)` rather than
`SmallEtale B S hS (AlgebraicGeometry.Space.chartSpace _ _).obj`, so
`AlgebraicGeometry.Space.chartRing_commRing` does not match it at instance transparency even
though it applies at default transparency.  Second, the identification of
`AlgebraicGeometry.Space.ModuleMapSituation.chartRingTestAlgEquiv` is given an explicit type, so
that its tensor product is read with this chart ring as the middle factor; otherwise the
`Algebra` instance on the tensor product is sought over the other spelling and is not found. -/

/-- Vanishing of `u` on the chart of `X ×_{Y₀} T` over `V₀` is vanishing of the extension of
scalars of the sections of `u` over `V₀` to the test scheme. -/
private theorem val_app_testChartDiagram_eq_zero_iff_lTensor_tensor
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (T : D.SchemesOver) (k : T.left ⟶ Y₀)
    (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    letI : CommRing
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
      chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
    letI := siteMorphismAlgebra B S hS k
    letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) := 
      chartSiteAlgebra B S hS D.X V₀ α
    (((modulePullback B S hS (D.baseChangeProjection T)).map D.u).val.app
        (op (testChartDiagram B S hS D hDY T k hk V₀).U) = 0) ↔
    LinearMap.lTensor (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
        (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u))
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) = 0 := by
  let : CommRing
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
  let := siteMorphismAlgebra B S hS k
  let : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartSiteAlgebra B S hS D.X V₀ α
  let : Algebra (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
      (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
        (testChartDiagram B S hS D hDY T k hk V₀).U) :=
    chartDiagramAlgebra B S hS (D.baseChangeProjection T)
      (testChartDiagram B S hS D hDY T k hk V₀)
  have e : (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
        (testChartDiagram B S hS D hDY T k hk V₀).U) ≃ₐ[
      chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))]
      (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
        (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u)) :=
    chartRingTestAlgEquiv B S hS D hDY T k hk V₀ α hα hT hY₀ hV₀
  exact (val_app_testChartDiagram_eq_zero_iff_lTensor B S hS D hDY T k hk V₀ α hα hT hY₀
    hV₀).trans (Stacks.Flattening.lTensor_eq_zero_iff_of_algEquiv
    ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
        (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
      (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) e)

/-- **Vanishing of the base change of `u` at an affine test scheme kills the extension of
scalars of the sections of `u` over the chart of `V₀` to `𝒪_X(V₀) ⊗_{Γ(Y₀, ⊤)} Γ(T, ⊤)`.**

The base change of `V₀` by `T` is one chart of `X ×_{Y₀} T`, over which the vanishing of `u_T`
is the vanishing of an extension of scalars of the sections of `u`
(`AlgebraicGeometry.Space.ModuleMapSituation.val_app_testChartDiagram_eq_zero_iff_lTensor`), and
the ring of functions of that chart is the displayed tensor product
(`AlgebraicGeometry.Space.ModuleMapSituation.chartRingTestAlgEquiv`).  No covering is involved,
and nothing is assumed of `V₀` beyond affineness. -/
theorem lTensor_val_app_eq_zero_of_isZeroAt
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (T : D.SchemesOver) (k : T.left ⟶ Y₀)
    (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hzero : D.IsZeroAt (modulePullbackSystem B S hS) T) :
    letI : CommRing
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
      chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
    letI := siteMorphismAlgebra B S hS k
    letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) := 
      chartSiteAlgebra B S hS D.X V₀ α
    LinearMap.lTensor (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
        (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u))
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) = 0 := by
  exact (val_app_testChartDiagram_eq_zero_iff_lTensor_tensor B S hS D hDY hY₀ V₀ α hα hV₀ T k hk
    hT).mp
    (val_app_testChartDiagram_eq_zero B S hS D hDY T k hk V₀ hzero)

/-- **Conversely, vanishing of that extension of scalars gives the vanishing of the base change
of `u` at the test scheme** — provided every morphism from a representable presheaf into the
source space factors through `V₀`, which is what `hV₀term` asks and what the identity chart of a
representable source space satisfies.

Here is where `hV₀term` is used, and why the covering argument of
`AlgebraicGeometry.Space.exists_ofArrows_hasAffineChartDiagram` is *not*.  Vanishing of a map of
`𝒪`-modules is the vanishing of its map on sections over every affine chart of `X ×_{Y₀} T`
(`AlgebraicGeometry.Space.Modules.eq_zero_of_forall_app_isAffine_eq_zero`).  By `hV₀term` every
such chart admits a morphism to the base change of `V₀`
(`CategoryTheory.Functor.relativelyRepresentable.lift`), which is itself affine
(`AlgebraicGeometry.Space.ModuleMapSituation.isAffine_chartScheme_testChartDiagram`); and
vanishing descends along a morphism of affine charts because the inverse image of `ℱ` is
quasi-coherent, hence cartesian on affine charts
(`AlgebraicGeometry.Space.Modules.app_eq_zero_of_isCartesianOnAffineCharts`).  So it suffices to
know the vanishing at the *single* chart that is the base change of `V₀`, which is what the
hypothesis of this lemma supplies.

Going instead through a cover by arbitrary affine chart diagrams would compare the sections of
`ℱ` over two different chart *spaces* — that of `V₀` and that of the diagram's chart of `X` — so
the base ring of the extension of scalars would have to be converted between its two spellings,
which does not terminate; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeVanishingChartRing.lean`.

No flatness of `𝒢` is used, and nothing is assumed of `𝒢` beyond the quasi-coherence the
situation already carries. -/
theorem isZeroAt_of_lTensor_val_app_eq_zero
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom)
    (T : D.SchemesOver) (k : T.left ⟶ Y₀)
    (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hv :
      letI : CommRing
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
      letI := siteMorphismAlgebra B S hS k
      letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartSiteAlgebra B S hS D.X V₀ α
      LinearMap.lTensor (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
          (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u))
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) = 0) :
    D.IsZeroAt (modulePullbackSystem B S hS) T := by
  have h4 := (val_app_testChartDiagram_eq_zero_iff_lTensor_tensor B S hS D hDY hY₀ V₀ α hα hV₀ T k
    hk hT).mpr hv
  have hcart : IsCartesianOnAffineCharts
      ((modulePullback B S hS (D.baseChangeProjection T)).obj D.F) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (D.baseChangeSpace T).1
      (D.baseChangeSpace T).2 _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (D.baseChangeProjection T) D.F D.quasicoherent_F)
  refine Modules.eq_zero_of_forall_app_isAffine_eq_zero B S hS
    ((modulePullback B S hS (D.baseChangeProjection T)).map D.u) fun U' hU'aff => ?_
  obtain ⟨h, hh⟩ := hV₀term U'.1.left (U'.1.hom ≫ (D.baseChangeProjection T).hom)
  exact Modules.app_eq_zero_of_isCartesianOnAffineCharts B S hS hcart _
    (isAffine_chartScheme_testChartDiagram B S hS D hDY T k hk V₀ α hα hT hY₀ hV₀) hU'aff
    (ObjectProperty.homMk (CostructuredArrow.homMk
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).lift U'.1.hom h hh)
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).lift_fst
        U'.1.hom h hh))) h4

/-! ### The ring-level reading of the vanishing locus -/

/-- **The vanishing locus of the situation at an affine test scheme, as the vanishing of one
base change of the sections of `u` over the chart.**  This is the field `zero_iff` of
`AlgebraicGeometry.Space.ModuleMapSituation.RingLevelZeroLocus`; the two directions are
`AlgebraicGeometry.Space.ModuleMapSituation.lTensor_val_app_eq_zero_of_isZeroAt` and
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_lTensor_val_app_eq_zero`, read through
the two spellings of an extension of scalars
(`Stacks.Flattening.baseChange_eq_zero_iff_lTensor`). -/
theorem isZeroAt_iff_baseChange_val_app
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom)
    (T : D.SchemesOver) (hT : IsAffine (D.testScheme.obj T)) :
    letI : CommRing
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
      chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
    letI := siteMorphismAlgebra B S hS (testSiteHom B S hS D hDY T)
    letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
      chartSiteAlgebra B S hS D.X V₀ α
    (D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      LinearMap.baseChange
          (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
            (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
            (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u))
          ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) = 0) := by
  let : CommRing
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
  let := siteMorphismAlgebra B S hS (testSiteHom B S hS D hDY T)
  let : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartSiteAlgebra B S hS D.X V₀ α
  exact ⟨fun hz =>
      (Stacks.Flattening.baseChange_eq_zero_iff_lTensor
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) _).mpr
        (lTensor_val_app_eq_zero_of_isZeroAt B S hS D hDY hY₀ V₀ α hα hV₀ T
          (testSiteHom B S hS D hDY T) (yoneda_map_testSiteHom B S hS D hDY T).symm hT hz),
    fun hb =>
      isZeroAt_of_lTensor_val_app_eq_zero B S hS D hDY hY₀ V₀ α hα hV₀ hV₀term T
        (testSiteHom B S hS D hDY T) (yoneda_map_testSiteHom B S hS D hDY T).symm hT
        ((Stacks.Flattening.baseChange_eq_zero_iff_lTensor
          ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) _).mp hb)⟩

/-- **The ring-level reading of the vanishing locus of a situation over an affine object of the
site, at an affine chart of its source space through which every representable factors.**

The base ring is `Γ(Y₀, ⊤)`, the chart ring is the ring of functions of the chart, and the two
modules are the sections of `ℱ` and of `𝒢` there; finiteness of the source module is where
finite type of `ℱ` enters, through Descent, Proposition 03DX(2)
(`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`).  The content is the
field `zero_iff`, which is
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_baseChange_val_app`.

**The base ring is not free.**  See the implementation notes of this file: with `Γ(S, ⊤)` in
place of `Γ(Y₀, ⊤)` every other field would type-check with no mathematics at all and `zero_iff`
would be false, so the structure would be unsatisfiable and every theorem carrying it vacuous.
What forces `Γ(Y₀, ⊤)` is the Cartesian square
`AlgebraicGeometry.Space.ModuleMapSituation.isPullback_chartScheme_testChartDiagram`, whose
cospan vertex is the scheme of `Y₀`. -/
def ringLevelZeroLocusOfTerminalAffineChart
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom) :
    D.RingLevelZeroLocus where
  base := (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
  commRing_base := inferInstance
  algebra_sections T := siteMorphismAlgebra B S hS (testSiteHom B S hS D hDY T)
  algebraMap_sections _ _ κ r := appTop_testSiteHom B S hS D hDY κ r
  chart := chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
  commRing_chart :=
    chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
  algebra_chart := chartSiteAlgebra B S hS D.X V₀ α
  source := (((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
      (isEtale_chartToSpace B S hS D.X V₀)).obj D.F).val.obj
    (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) : Type u)
  addCommGroup_source := inferInstance
  module_source := inferInstance
  finite_source := module_finite_sections_of_isFiniteTypeOnSite D.F D.quasicoherent_F hFft V₀ hV₀
  target := (((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
      (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
    (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) : Type u)
  addCommGroup_target := inferInstance
  module_target := inferInstance
  map := (((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
      (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
    (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom
  zero_iff := isZeroAt_iff_baseChange_val_app B S hS D hDY hY₀ V₀ α hα hV₀ hV₀term

include hDY in
/-- **The chart case of clause (2) of Stacks 083J, in its limit-free form, for a situation whose
target is the algebraic space of an affine object of the site.**

The chart used is the identity chart of the source space of the chart situation, which is the
algebraic space of the affine object `W`: it is affine, and every morphism from a representable
presheaf into `yoneda.obj W` factors through it by the Yoneda lemma, which is the hypothesis
`hV₀term` of
`AlgebraicGeometry.Space.ModuleMapSituation.ringLevelZeroLocusOfTerminalAffineChart`.

The antecedent `SheafOfModules.IsFiniteTypeOnSite D.F` of
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartRingLevelZeroLocus` is used, and must
be: it is what makes the sections of the inverse image of `ℱ` on the chart a *finite* module,
which is the hypothesis of Algebra, Lemma 05LI part (1) and without which the limit statement
that the ring-level reading feeds is false — see the docstring of
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent`. -/
theorem hasAffineChartRingLevelZeroLocus_of_eq
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀)) :
    D.HasAffineChartRingLevelZeroLocus := by
  intro hFft W hW g _ _ hF hG
  refine ⟨ringLevelZeroLocusOfTerminalAffineChart B S hS (D.pullbackSituation g hF hG) hDY hY₀
    (isFiniteTypeOnSite_modulePullback B S hS g D.F hFft) (idEtaleChart B S hS W)
    (yoneda.preimage ((D.pullbackSituation g hF hG).f.hom ≫ (eqToHom hDY).hom)) ?_ hW
    fun c i => ⟨yoneda.preimage i,
      (Functor.map_preimage yoneda i).symm.trans (Category.comp_id _).symm⟩⟩
  exact (congrArg (fun m => m ≫ (eqToHom hDY).hom)
    (Category.id_comp (D.pullbackSituation g hF hG).f.hom)).trans
      (Functor.map_preimage yoneda _).symm


/-- **The chart case of clause (2) of Stacks 083J at the affine stages, in its limit-free
form, for every situation of Stacks 083F.**

This is the hypothesis `hstage` of this development's Stacks 0CWC, with the limit content of
part (2) proved rather than assumed; it is therefore no longer carried.  No hypothesis on the
situation is needed: the stage `T` is affine by assumption, the target of the base-changed
situation is the algebraic space of `T.left` on the nose, and the chart case over it is
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineChartRingLevelZeroLocus_of_eq`. -/
theorem hasAffineStageChartRingLevelZeroLocus :
    D.HasAffineStageChartRingLevelZeroLocus := fun T hT =>
  hasAffineChartRingLevelZeroLocus_of_eq B S hS (D.baseChangeTestScheme T) rfl hT

end ModuleMapSituation

end AlgebraicGeometry.Space

end
