module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeVanishingChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOverSpecQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartScalarTowerOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapChartwiseVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq
public import StacksFrontier.RingTheory.Flat.LTensorBaseChangeCancel

/-!
# The étale chart of a base change by a test object, and its ring of functions

Let `B` be a big fppf site over a scheme `S`, let `X` be an algebraic space over an object `Y₀`
of the big fppf category over `S` — a situation of Stacks 083F whose target is the algebraic
space of `Y₀` — and let `T` be a test scheme over it, that is, an object of the category with a
morphism `k : T ⟶ Y₀`.

This file builds, out of an étale scheme chart `V` of `X`, an étale scheme chart of the base
change `X ×_{Y₀} T` lying over `V`, and identifies its ring of functions.  Three things are
proved about it, and they are what a chart-wise argument on `X ×_{Y₀} T` needs:

* it comes with a commutative diagram of étale charts over the projection
  `X ×_{Y₀} T ⟶ X` whose chart of `X` is `V` itself;
* when `V`, `T` and `Y₀` are affine, so is the new chart — it is the fibre product of the two
  over `Y₀`;
* its ring of functions is `𝒪_X(V) ⊗_{Γ(Y₀, ⊤)} Γ(T, ⊤)`, as an `𝒪_X(V)`-algebra for the
  algebra structure the chart diagram carries.

The case `Y₀ = AlgebraicGeometry.Space.baseTerminal`, where the target is the *final* algebraic
space and `Γ(Y₀, ⊤)` is `Γ(S, ⊤)`, is the one the situation of Stacks 0CWA over an affine base
uses, and the `ModuleMapFlatTargetSituation` half of this file is exactly that instance: the
final algebraic space over `S` **is** the algebraic space of the final object of the category,
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.toModuleMapSituation_Y`, by definition, so
every statement there is an application of the corresponding relative one with the transport
taken to be the identity.  Nothing is reproved.

## Main definitions

* `AlgebraicGeometry.Space.siteMorphismAlgebra`: the `Γ(Y₀, ⊤)`-algebra structure on the ring of
  global functions of an object of the big fppf category over `S` equipped with a morphism to
  `Y₀`.
* `AlgebraicGeometry.Space.siteObjectBaseAlgebra`: the `Γ(S, ⊤)`-algebra structure on the ring
  of global functions of an object of the big fppf category over `S`, which is the previous one
  at the final object.
* `AlgebraicGeometry.Space.ModuleMapSituation.testChartDiagram`: the commutative diagram of
  étale charts formed by a chart `V` of `X` and its base change by a test scheme whose structure
  morphism is the Yoneda image of a morphism of the category.
* `AlgebraicGeometry.Space.ModuleMapSituation.testChartProjection`: the projection from the
  base-changed chart to the test object, in the category.
* `AlgebraicGeometry.Space.ModuleMapSituation.chartRingTestAlgEquiv`: the identification of its
  ring of functions with `𝒪_X(V) ⊗_{Γ(Y₀, ⊤)} Γ(T, ⊤)`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTest`: an object of the big fppf
  category over `S`, read as a test scheme over the final algebraic space.  The closed
  subscheme of Stacks 083K,
  `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.specQuotientTest`, is this construction
  at `AlgebraicGeometry.Space.specQuotientOver`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTestChartDiagram`: the commutative
  diagram of étale charts formed by a chart `V` of `X` and its base change.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTestChartProjection`: the
  projection from the base-changed chart to the test object.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.chartRingBaseTestAlgEquiv`: the
  identification of its ring of functions with the tensor product.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.relativelyRepresentable_baseChangeProjection'`:
  the projection `X ×_{Y₀} T ⟶ X` is relatively representable.
* `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_chartScheme_testChartDiagram`: the
  base-changed chart is the fibre product of the chart and the test scheme over `Y₀`, as
  schemes.
* `AlgebraicGeometry.Space.ModuleMapSituation.isAffine_chartScheme_testChartDiagram`: it is
  affine when the chart, the test object and `Y₀` are.
* `AlgebraicGeometry.Space.ModuleMapSituation.val_app_testChartDiagram_eq_zero_iff_lTensor`:
  the base change of the map of modules vanishes on the sections over the base-changed chart
  exactly when an extension of scalars of its sections over `V` vanishes.
* `ModuleMapFlatTargetSituation.relativelyRepresentable_baseChangeProjection`: the projection
  `X ×_S T ⟶ X` is relatively representable.
* `ModuleMapFlatTargetSituation.isPullback_chartScheme_baseTestChartDiagram`:
  the base-changed chart is the fibre product of the chart and the test scheme over the base,
  as schemes.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isAffine_chartScheme_baseTestChartDiagram`:
  it is affine when the chart and the test object are.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_baseTestChartDiagram_eq_zero`:
  if the base change of the map of modules at the test object vanishes, it vanishes on the
  sections over the base-changed chart.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.lTensor_val_app_eq_zero_of_isZeroAt`:
  the same, read as the vanishing of an extension of scalars to the ring of functions of the
  base-changed chart.

## Implementation notes

**Where the chart comes from.**  The structure morphism of the test object is assumed to be the
Yoneda image of a morphism `k : T ⟶ Y₀` of the big fppf category — which is no assumption when
the target of the situation is the algebraic space of `Y₀`, `yoneda` being fully faithful, and
which holds for the final algebraic space because its presheaf is represented by the base.  So
it is relatively representable by Stacks 02W9, and relative representability is stable under
base change (Stacks 02WB), so the projection `X ×_{Y₀} T ⟶ X` is relatively representable too.
Base change of étale scheme charts along a relatively representable morphism is Stacks 03G2 part
(4), `AlgebraicGeometry.Space.smallBaseChange`, and the chart produced here is its value at `V`;
the chart diagram is `AlgebraicGeometry.Space.baseChangeChartDiagram`.

**Why the new chart is the fibre product over `Y₀`, and not merely over `X`.**  Pasting
the representability square of the projection at `V` with the Cartesian square defining
`X ×_{Y₀} T` gives a square whose cospan is the two structure morphisms to `Y₀`; both legs
are then morphisms of representable presheaves, so the square descends to the big fppf
category over `S` — `yoneda` is fully faithful — and from there to schemes, where both
functors preserve fibre products.  That is the square the affineness and the tensor
identification are read off from: `AlgebraicGeometry.isAffine_of_isAffineHom` for the first
and `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` for the second.

**How the target is said to be the algebraic space of `Y₀`.**  By an equality
`D.Y = AlgebraicGeometry.schemeSpace Y₀` of objects, which is the form the rest of this
development uses (`AlgebraicGeometry.Space.ModuleMapSituation.AffineChartZeroLocusClosed`), and
the two hypotheses about the structure morphisms are stated with that equality's `eqToHom`
composed in.  Each proof that needs to see the corner as `yoneda.obj Y₀` destructures the
situation and substitutes, after which the transport is the identity; at the terminal instance
the equality is `rfl` and the transport is literally the identity.  No `eqToHom` survives into
any of the statements about charts, rings or modules.

**The spellings.**  Three places need care, and each is the same phenomenon: a corner of a
Cartesian square has two definitionally equal spellings, and only one of them is matched.
`rw` refuses a goal that mixes them, because the intermediate expression is not type-correct at
`implicit` transparency; `CategoryTheory.IsPullback.of_eq` transports a square along equalities
of its four morphisms by an application instead, where the two spellings are reconciled by
unfolding.  The codomain of
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTestChartProjection` is declared to
be the object of the category rather than the underlying object of the test scheme for the same
reason: instance search does not unfold the projection of a test scheme to its object, so the
`IsAffine` hypothesis would not be found at the corner.  And the algebra structures of the
tensor identification are introduced twice, once with the ring of functions spelt
`AlgebraicGeometry.Space.chartRing` and once spelt `Γ(-, ⊤)`, by the same term: the two are the
same type, but instance search does not cross between them, while a definitional check does.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 02WB](https://stacks.math.columbia.edu/tag/02WB)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

section ArbitraryBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `Γ(V, ⊤)`-algebra structure on the ring of global functions of an object of the big fppf
category over `S` equipped with a morphism to `V`. -/
@[instance_reducible]
def siteMorphismAlgebra {T V : BigFppfOver B S hS} (k : T ⟶ V) :
    Algebra (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
  ((BigFppfOver.toScheme B S hS).map k).appTop.hom.toAlgebra

namespace ModuleMapSituation

/-- If the target of the situation is the algebraic space of `Y₀` and the structure morphism of
the test scheme `T` is the Yoneda image of a morphism `k : T ⟶ Y₀`, then that structure morphism
is relatively representable. -/
theorem relativelyRepresentable_hom_of_eq (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver)
    (k : T.left ⟶ Y₀) (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k) :
    yoneda.relativelyRepresentable T.hom.hom := by
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  revert hk k T hDY
  obtain ⟨X, Y, f, F, G, qF, qG, u⟩ := D
  dsimp only
  rintro rfl T k hk
  rw [(Category.comp_id _).symm.trans hk]
  exact Functor.relativelyRepresentable.map yoneda k

/-- The base change `X ×_Y T` by a test scheme `T` is the fibre product of `f : X ⟶ Y` and the
structure morphism of `T`. -/
theorem isPullback_baseChangeSpace (D : ModuleMapSituation.{u, u} B S hS) (T : D.SchemesOver) :
    IsPullback (D.baseChangeProjection T) (D.baseChangeInclusion T) D.f T.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The same square, read on the underlying presheaves. -/
theorem isPullback_hom_baseChangeSpace (D : ModuleMapSituation.{u, u} B S hS)
    (T : D.SchemesOver) :
    IsPullback (D.baseChangeProjection T).hom (D.baseChangeInclusion T).hom D.f.hom T.hom.hom :=
  AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_baseChangeSpace B S hS T)

/-- If the target of the situation is the algebraic space of `Y₀` and the structure morphism of
the test scheme `T` is the Yoneda image of a morphism `k : T ⟶ Y₀`, then the projection
`X ×_{Y₀} T ⟶ X` is relatively representable. -/
theorem relativelyRepresentable_baseChangeProjection' (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver)
    (k : T.left ⟶ Y₀) (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k) :
    yoneda.relativelyRepresentable (D.baseChangeProjection T).hom :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (D.isPullback_hom_baseChangeSpace B S hS T).flip
    (D.relativelyRepresentable_hom_of_eq B S hS hDY T k hk)

variable (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver) (k : T.left ⟶ Y₀)
    (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k) (V : SmallEtale B S hS D.X.1)

/-- The chart diagram over the projection `X ×_{Y₀} T ⟶ X` formed by a chart `V` of `X` and its
base change, an étale chart of `X ×_{Y₀} T`. -/
def testChartDiagram :
    ChartDiagram B S hS (D.baseChangeSpace T).1 D.X.1 (D.baseChangeProjection T).hom :=
  baseChangeChartDiagram B S hS (D.baseChangeProjection T)
    (D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk) V

/-- The chart of `X` of the base-change chart diagram is the given chart. -/
theorem testChartDiagram_V : (testChartDiagram B S hS D hDY T k hk V).V = V := rfl

/-- The projection from the base change of the chart `V` to the test object, in the big fppf
category over `S`. -/
def testChartProjection :
    (D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback V.1.hom ⟶
      T.left :=
  yoneda.preimage
    ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).fst V.1.hom ≫
      (D.baseChangeInclusion T).hom)

/-- The Yoneda image of the projection to the test object is the composite of the two
projections it was chosen to be the preimage of. -/
theorem yoneda_map_testChartProjection :
    yoneda.map (testChartProjection B S hS D hDY T k hk V) =
      (D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).fst V.1.hom ≫
        (D.baseChangeInclusion T).hom :=
  Functor.map_preimage _ _

/-- The square of presheaves exhibiting the base-changed chart as the fibre product of the
chart of `X` and the test object over the target of the situation. -/
theorem isPullback_yoneda_testChartDiagram :
    IsPullback
        (yoneda.map
          ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom))
        ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).fst V.1.hom ≫
          (D.baseChangeInclusion T).hom)
        (V.1.hom ≫ D.f.hom) T.hom.hom :=
  (((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).isPullback
    V.1.hom).paste_horiz (D.isPullback_hom_baseChangeSpace B S hS T).flip).flip

/-- **The square in the big fppf category over `S`: the base-changed chart is the fibre product
of the chart of `X` and the test object over `Y₀`.** -/
theorem isPullback_site_testChartDiagram (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α) :
    IsPullback
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom)
      (testChartProjection B S hS D hDY T k hk V) α k := by
  revert hα α hk k
  revert V
  revert T
  revert hDY
  obtain ⟨X, Y, f, F, G, qF, qG, u⟩ := D
  dsimp only
  rintro rfl T V k hk α hα
  refine IsPullback.of_map_of_faithful yoneda
    (IsPullback.of_eq (isPullback_yoneda_testChartDiagram B S hS _ rfl T k hk V) rfl
      (yoneda_map_testChartProjection B S hS _ rfl T k hk V).symm
      ((Category.comp_id _).symm.trans hα) ((Category.comp_id _).symm.trans hk))

/-- **The base-changed chart is the fibre product of the chart of `X` and the test scheme over
the scheme of `Y₀`, as schemes.** -/
theorem isPullback_chartScheme_testChartDiagram (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom))
      ((BigFppfOver.toScheme B S hS).map (testChartProjection B S hS D hDY T k hk V))
      ((BigFppfOver.toScheme B S hS).map α) ((BigFppfOver.toScheme B S hS).map k) :=
  (isPullback_site_testChartDiagram B S hS D hDY T k hk V α hα).map
    (BigFppfOver.toScheme B S hS)

/-- **The base change of an affine chart by an affine test object over an affine object of the
site is affine.** -/
theorem isAffine_pullback_baseChangeProjection' (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback V.1.hom)) := by
  have := hT
  have := hY₀
  have := hV
  have hg : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map k) := inferInstance
  have := AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
    (isPullback_chartScheme_testChartDiagram B S hS D hDY T k hk V α hα).flip hg
  exact AlgebraicGeometry.isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom))

/-- **The chart of `X ×_{Y₀} T` of the chart diagram of an affine chart and an affine test
object is affine.** -/
theorem isAffine_chartScheme_testChartDiagram (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (testChartDiagram B S hS D hDY T k hk V).U) :=
  isAffine_pullback_baseChangeProjection' B S hS D hDY T k hk V α hα hT hY₀ hV

/-- Pullback of functions to the base-changed chart along the projection to the chart of `X`,
followed by the chart's own morphism to `Y₀`, is pullback along the composite — which is what
the base-changed chart's `Γ(Y₀, ⊤)`-algebra structure is taken to be. -/
theorem appTop_testChartDiagram_chartToSite (α : V.1.left ⟶ Y₀)
    (r : (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)) :
    ((BigFppfOver.toScheme B S hS).map
          ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd
            V.1.hom)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map α).appTop.hom r) =
      ((BigFppfOver.toScheme B S hS).map
        ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom ≫
          α)).appTop.hom r := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- **The ring of functions of the base change of an affine chart by an affine test object over
an affine object of the site is the tensor product over the functions of that object.** -/
def chartRingTestAlgEquiv (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS D.X.1 D.X.2 V) := chartSiteAlgebra B S hS D.X V α
    letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u) := siteMorphismAlgebra B S hS k
    letI : Algebra (chartRing B S hS D.X.1 D.X.2 V)
        (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
          (testChartDiagram B S hS D hDY T k hk V).U) :=
      chartDiagramAlgebra B S hS (D.baseChangeProjection T)
        (testChartDiagram B S hS D hDY T k hk V)
    chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
        (testChartDiagram B S hS D hDY T k hk V).U ≃ₐ[chartRing B S hS D.X.1 D.X.2 V]
      TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartRing B S hS D.X.1 D.X.2 V)
        (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u) := by
  haveI := hT
  haveI := hY₀
  haveI := hV
  haveI := isAffine_pullback_baseChangeProjection' B S hS D hDY T k hk V α hα hT hY₀ hV
  letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u) :=
    chartSiteAlgebra B S hS D.X V α
  letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u) := siteMorphismAlgebra B S hS k
  letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj
        ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback
          V.1.hom), ⊤) : Type u) :=
    siteMorphismAlgebra B S hS
      ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd V.1.hom ≫ α)
  letI : Algebra (chartRing B S hS D.X.1 D.X.2 V)
      (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
        (testChartDiagram B S hS D hDY T k hk V).U) :=
    chartDiagramAlgebra B S hS (D.baseChangeProjection T)
      (testChartDiagram B S hS D hDY T k hk V)
  letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj
        ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback
          V.1.hom), ⊤) : Type u) :=
    chartDiagramAlgebra B S hS (D.baseChangeProjection T)
      (testChartDiagram B S hS D hDY T k hk V)
  have hsq := isPullback_chartScheme_testChartDiagram B S hS D hDY T k hk V α hα
  have hf : algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u) =
      ((BigFppfOver.toScheme B S hS).map α).appTop.hom := rfl
  have hg : algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u) =
      ((BigFppfOver.toScheme B S hS).map k).appTop.hom := rfl
  have hu : ∀ a : (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u),
      ((BigFppfOver.toScheme B S hS).map
            ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).snd
              V.1.hom)).appTop.hom
          (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
            (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u) a) =
        algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (Γ((BigFppfOver.toScheme B S hS).obj
            ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback
              V.1.hom), ⊤) : Type u) a :=
    appTop_testChartDiagram_chartToSite B S hS D hDY T k hk V α
  have hv : ∀ a : (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u),
      ((BigFppfOver.toScheme B S hS).map
            (testChartProjection B S hS D hDY T k hk V)).appTop.hom
          (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
            (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u) a) =
        algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (Γ((BigFppfOver.toScheme B S hS).obj
            ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback
              V.1.hom), ⊤) : Type u) a := by
    intro a
    have h := congrArg
      (fun m : chartScheme (testChartDiagram B S hS D hDY T k hk V).U ⟶
        (BigFppfOver.toScheme B S hS).obj Y₀ => m.appTop.hom a) hsq.w
    simp only [Scheme.Hom.comp_appTop] at h
    rw [hg]
    exact h.symm.trans (hu a)
  have key : ∀ b : (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u),
      AlgebraicGeometry.algEquivTensorAppTopOfIsPullback hsq hf hg hu hv
          (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u)
            (TensorProduct (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
              (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u)
              (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u)) b) =
        algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) : Type u)
          (Γ((BigFppfOver.toScheme B S hS).obj
            ((D.relativelyRepresentable_baseChangeProjection' B S hS hDY T k hk).pullback
              V.1.hom), ⊤) : Type u) b := by
    intro b
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp only [Algebra.algebraMap_self_apply]
    rw [AlgebraicGeometry.algEquivTensorAppTopOfIsPullback_tmul hsq hf hg hu hv, map_one, mul_one]
    rfl
  exact AlgEquiv.ofRingEquiv
    (f := (AlgebraicGeometry.algEquivTensorAppTopOfIsPullback hsq hf hg hu hv).symm.toRingEquiv)
    fun b =>
      (AlgebraicGeometry.algEquivTensorAppTopOfIsPullback hsq hf hg hu hv).symm_apply_eq.2
        (key b).symm

/-- **Vanishing of the base change of the map of modules at the test object gives its vanishing
on the sections over the base change of every chart of `X`.** -/
theorem val_app_testChartDiagram_eq_zero
    (hzero : D.IsZeroAt (modulePullbackSystem B S hS) T) :
    ((modulePullback B S hS (D.baseChangeProjection T)).map D.u).val.app
        (op (testChartDiagram B S hS D hDY T k hk V).U) = 0 :=
  Modules.app_eq_zero_of_eq_zero B S hS hzero _

/-- **The chart-wise reading of the vanishing at the test object, as an iff.** -/
theorem val_app_testChartDiagram_eq_zero_iff_lTensor (α : V.1.left ⟶ Y₀)
    (hα : (V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hV : IsAffine (chartScheme V)) :
    letI : Algebra
      (chartRing B S hS (chartSpace B S hS D.X (testChartDiagram B S hS D hDY T k hk V).V).1
        (chartSpace B S hS D.X (testChartDiagram B S hS D hDY T k hk V).V).2
        (chartSpaceIdChartDiagram B S hS (D.baseChangeProjection T)
          (testChartDiagram B S hS D hDY T k hk V)).V)
      (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
        (testChartDiagram B S hS D hDY T k hk V).U) :=
      chartDiagramAlgebra B S hS (D.baseChangeProjection T)
        (testChartDiagram B S hS D hDY T k hk V)
    (((modulePullback B S hS (D.baseChangeProjection T)).map D.u).val.app
        (op (testChartDiagram B S hS D hDY T k hk V).U) = 0) ↔
      LinearMap.lTensor
        (chartRing B S hS (D.baseChangeSpace T).1 (D.baseChangeSpace T).2
          (testChartDiagram B S hS D hDY T k hk V).U)
        (((etaleModulePullback B S hS
                (chartToSpace B S hS D.X (testChartDiagram B S hS D hDY T k hk V).V)
                (isEtale_chartToSpace B S hS D.X
                  (testChartDiagram B S hS D hDY T k hk V).V)).map D.u).val.app
            (op (chartSpaceIdChartDiagram B S hS (D.baseChangeProjection T)
              (testChartDiagram B S hS D hDY T k hk V)).V)).hom = 0 :=
  val_app_eq_zero_iff_lTensor_chartRing B S hS (D.baseChangeProjection T)
    D.quasicoherent_F D.quasicoherent_G D.u (testChartDiagram B S hS D hDY T k hk V)
    (isAffine_chartScheme_testChartDiagram B S hS D hDY T k hk V α hα hT hY₀ hV) hV

end ModuleMapSituation

end ArbitraryBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]

/-- The `Γ(S, ⊤)`-algebra structure on the ring of global functions of an object of the big
fppf category over `S`, given by its structure morphism to the base.  Not an instance: it
depends on the object.

This is `AlgebraicGeometry.Space.siteMorphismAlgebra` at the final object of the category, whose
scheme is the base and along whose structure morphism pullback of functions *is* pullback along
the structure morphism of the object. -/
@[instance_reducible]
def siteObjectBaseAlgebra (T : BigFppfOver B S hS) :
    Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
  siteMorphismAlgebra B S hS (toBaseTerminal B S hS T)

namespace ModuleMapFlatTargetSituation

variable (D : ModuleMapFlatTargetSituation B S hS) (T : BigFppfOver B S hS)

/-- An object of the big fppf category over `S`, read as a test scheme over the final algebraic
space. -/
def baseTest : (D.toModuleMapSituation B S hS).SchemesOver :=
  CostructuredArrow.mk
    ((terminalSpace_isTerminal B S hS).from ((schemeSpaceFunctor B S hS).obj T))

/-- The test scheme `specQuotientTest I` is `baseTest` at the object `specQuotientOver I`. -/
theorem specQuotientTest_eq_baseTest (I : Ideal Γ(S, ⊤)) :
    D.specQuotientTest B S hS I = D.baseTest B S hS (specQuotientOver B S hS I) := rfl

/-- The structure morphism of the test object is the Yoneda image of the structure morphism of
the object of the site. -/
theorem baseTest_hom_hom :
    (D.baseTest B S hS T).hom.hom = yoneda.map (toBaseTerminal B S hS T) :=
  (baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _

/-- The identification of the target of the situation with the algebraic space of the final
object of the big fppf category over `S`.  It is an equality by definition: both are the
presheaf represented by the base. -/
theorem toModuleMapSituation_Y :
    (D.toModuleMapSituation B S hS).Y = schemeSpace (baseTerminal B S hS) := rfl

/-- `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTest_hom_hom` in the form the
relative statements consume, the transport along
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.toModuleMapSituation_Y` being the
identity. -/
theorem baseTest_hom_comp_eqToHom :
    (D.baseTest B S hS T).hom.hom ≫ (eqToHom (D.toModuleMapSituation_Y B S hS)).hom =
      yoneda.map (toBaseTerminal B S hS T) :=
  (Category.comp_id _).trans (D.baseTest_hom_hom B S hS T)

/-- The structure morphism of the test object is relatively representable. -/
theorem relativelyRepresentable_baseTest_hom :
    yoneda.relativelyRepresentable (D.baseTest B S hS T).hom.hom :=
  ModuleMapSituation.relativelyRepresentable_hom_of_eq B S hS
    (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
    (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T)

/-- The base change by a test object is a fibre product. -/
theorem isPullback_baseChange :
    IsPullback ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      ((D.toModuleMapSituation B S hS).baseChangeInclusion (D.baseTest B S hS T))
      (D.toModuleMapSituation B S hS).f (D.baseTest B S hS T).hom :=
  ModuleMapSituation.isPullback_baseChangeSpace B S hS (D.toModuleMapSituation B S hS)
    (D.baseTest B S hS T)

/-- The same square, read on the underlying presheaves. -/
theorem isPullback_hom_baseChange :
    IsPullback
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T)).hom
      ((D.toModuleMapSituation B S hS).baseChangeInclusion (D.baseTest B S hS T)).hom
      (D.toModuleMapSituation B S hS).f.hom (D.baseTest B S hS T).hom.hom :=
  ModuleMapSituation.isPullback_hom_baseChangeSpace B S hS (D.toModuleMapSituation B S hS)
    (D.baseTest B S hS T)

/-- **The projection from the base change by a test object is relatively representable.** -/
theorem relativelyRepresentable_baseChangeProjection :
    yoneda.relativelyRepresentable
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T)).hom :=
  ModuleMapSituation.relativelyRepresentable_baseChangeProjection' B S hS
    (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
    (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T)

variable (V : SmallEtale B S hS (D.toModuleMapSituation B S hS).X.1)

/-- The structure morphism of a chart of `X` to the base is the Yoneda image of the vertical
morphism of `AlgebraicGeometry.Space.baseChartDiagram`, in the form the relative statements
consume: the target of the situation is terminal, so the two morphisms of presheaves into it
agree. -/
theorem chartToBase_comp_eqToHom :
    (V.1.hom ≫ (D.toModuleMapSituation B S hS).f.hom) ≫
        (eqToHom (D.toModuleMapSituation_Y B S hS)).hom =
      yoneda.map (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g :=
  (baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _

/-- **The chart diagram of a chart of `X` and its base change by a test object.** -/
def baseTestChartDiagram :
    ChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
      (D.toModuleMapSituation B S hS).X.1
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T)).hom :=
  ModuleMapSituation.testChartDiagram B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V

/-- The chart of `X` of the base-change chart diagram is the given chart. -/
theorem baseTestChartDiagram_V : (D.baseTestChartDiagram B S hS T V).V = V := rfl

/-- **The projection from the base-changed chart to the test object**, in the big fppf category
over `S`.  Its codomain is written as the object of the category rather than as the underlying
object of the test scheme, so that the corner of the Cartesian square below is that object:
instance search does not unfold the projection of a test scheme to its object. -/
def baseTestChartProjection :
    (D.relativelyRepresentable_baseChangeProjection B S hS T).pullback V.1.hom ⟶ T :=
  ModuleMapSituation.testChartProjection B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V

/-- The Yoneda image of the projection to the test object is the composite of the projection to
`X ×_S T` and the projection `X ×_S T ⟶ T`. -/
theorem yoneda_map_baseTestChartProjection :
    yoneda.map (D.baseTestChartProjection B S hS T V) =
      (D.relativelyRepresentable_baseChangeProjection B S hS T).fst V.1.hom ≫
        ((D.toModuleMapSituation B S hS).baseChangeInclusion (D.baseTest B S hS T)).hom :=
  ModuleMapSituation.yoneda_map_testChartProjection B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V

/-- The square of presheaves exhibiting the base-changed chart as the fibre product of the
chart of `X` and the test object over the base. -/
theorem isPullback_yoneda_baseTestChartDiagram :
    IsPullback
        (yoneda.map
          ((D.relativelyRepresentable_baseChangeProjection B S hS T).snd V.1.hom))
        ((D.relativelyRepresentable_baseChangeProjection B S hS T).fst V.1.hom ≫
          ((D.toModuleMapSituation B S hS).baseChangeInclusion (D.baseTest B S hS T)).hom)
        (V.1.hom ≫ (D.toModuleMapSituation B S hS).f.hom)
        (D.baseTest B S hS T).hom.hom :=
  ModuleMapSituation.isPullback_yoneda_testChartDiagram B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V

/-- The square in the big fppf category over `S`: the base-changed chart is the fibre product
of the chart of `X` and the test object over the base. -/
theorem isPullback_site_baseTestChartDiagram :
    IsPullback ((D.relativelyRepresentable_baseChangeProjection B S hS T).snd V.1.hom)
        (D.baseTestChartProjection B S hS T V)
        (toBaseTerminal B S hS V.1.left) (toBaseTerminal B S hS T) :=
  IsPullback.of_eq
    (ModuleMapSituation.isPullback_site_testChartDiagram B S hS
      (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
      (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T) V
      (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g
      (D.chartToBase_comp_eqToHom B S hS V))
    rfl rfl (Over.mkIdTerminal.hom_ext _ _) rfl

/-- **The base-changed chart is the fibre product of the chart of `X` and the test scheme over
the base, as schemes.** -/
theorem isPullback_chartScheme_baseTestChartDiagram :
    IsPullback
        ((BigFppfOver.toScheme B S hS).map
          ((D.relativelyRepresentable_baseChangeProjection B S hS T).snd V.1.hom))
        ((BigFppfOver.toScheme B S hS).map (D.baseTestChartProjection B S hS T V))
        (chartToBase B S hS (D.toModuleMapSituation B S hS).X V) (B.inclusion.map T.hom) :=
  ModuleMapSituation.isPullback_chartScheme_testChartDiagram B S hS
    (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
    (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T) V
    (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g
    (D.chartToBase_comp_eqToHom B S hS V)

/-- **The base change of an affine chart by an affine test object is affine.** -/
theorem isAffine_pullback_baseChangeProjection
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((D.relativelyRepresentable_baseChangeProjection B S hS T).pullback V.1.hom)) :=
  ModuleMapSituation.isAffine_pullback_baseChangeProjection' B S hS
    (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
    (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T) V
    (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g
    (D.chartToBase_comp_eqToHom B S hS V) hT ‹IsAffine S› hV

/-- **The chart of `X ×_S T` of the chart diagram of an affine chart and an affine test object
is affine.** -/
theorem isAffine_chartScheme_baseTestChartDiagram
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (D.baseTestChartDiagram B S hS T V).U) :=
  D.isAffine_pullback_baseChangeProjection B S hS T V hT hV

/-- Pullback of functions to the base-changed chart along the two projections agrees with
pullback along its own structure morphism to the base. -/
theorem appTop_baseTestChartDiagram_chartToBase (r : Γ(S, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (D.baseTestChartDiagram B S hS T V).g).appTop.hom
        ((chartToBase B S hS (D.toModuleMapSituation B S hS).X
          (D.baseTestChartDiagram B S hS T V).V).appTop.hom r) =
      (chartToBase B S hS
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T))
          (D.baseTestChartDiagram B S hS T V).U).appTop.hom r := by
  have h := congrArg
    (fun k : chartScheme (D.baseTestChartDiagram B S hS T V).U ⟶ S => k.appTop.hom r)
    (chartToBase_comp_chartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V))
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h

/-- **The ring of functions of the base change of an affine chart by an affine test object is
the tensor product of the ring of functions of the chart and the ring of functions of the test
scheme over the ring of functions of the base.**

The isomorphism is one of `𝒪_X(V)`-algebras for the algebra structure
`AlgebraicGeometry.Space.chartDiagramAlgebra` of the chart diagram of the chart and its base
change, which is what compatibility with the chart diagram means. -/
def chartRingBaseTestAlgEquiv (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    letI : Algebra Γ(S, ⊤)
        (chartRing B S hS (D.toModuleMapSituation B S hS).X.1
          (D.toModuleMapSituation B S hS).X.2 V) :=
      chartBaseAlgebra B S hS (D.toModuleMapSituation B S hS).X V
    letI : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
      siteObjectBaseAlgebra B S hS T
    letI : Algebra
        (chartRing B S hS (D.toModuleMapSituation B S hS).X.1
          (D.toModuleMapSituation B S hS).X.2 V)
        (chartRing B S hS
          ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
          ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).2
          (D.baseTestChartDiagram B S hS T V).U) :=
      chartDiagramAlgebra B S hS
        ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
        (D.baseTestChartDiagram B S hS T V)
    chartRing B S hS
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).2
        (D.baseTestChartDiagram B S hS T V).U ≃ₐ[
      chartRing B S hS (D.toModuleMapSituation B S hS).X.1
        (D.toModuleMapSituation B S hS).X.2 V]
      TensorProduct Γ(S, ⊤)
        (chartRing B S hS (D.toModuleMapSituation B S hS).X.1
          (D.toModuleMapSituation B S hS).X.2 V)
        (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
  ModuleMapSituation.chartRingTestAlgEquiv B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V
    (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g
    (D.chartToBase_comp_eqToHom B S hS V) hT ‹IsAffine S› hV

/-- **Vanishing of the base change of the map of modules at the test object gives its vanishing
on the sections over the base change of every chart of `X`.**

Vanishing of a map of modules is vanishing of its map on sections over every chart, so no
covering argument is involved: the base-changed chart is one chart among others.  It is the
chart over which `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartRing` reads the
vanishing as the vanishing of an extension of scalars along
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.chartRingBaseTestAlgEquiv`. -/
theorem val_app_baseTestChartDiagram_eq_zero
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    ((modulePullback B S hS
          ((D.toModuleMapSituation B S hS).baseChangeProjection
            (D.baseTest B S hS T))).map (D.toModuleMapSituation B S hS).u).val.app
        (op (D.baseTestChartDiagram B S hS T V).U) = 0 :=
  ModuleMapSituation.val_app_testChartDiagram_eq_zero B S hS (D.toModuleMapSituation B S hS)
    (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T) (toBaseTerminal B S hS T)
    (D.baseTest_hom_comp_eqToHom B S hS T) V hzero

/-- **The chart-wise reading of the vanishing at the test object, over the base-changed chart
of an affine chart.**

This is `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartRing` at the chart diagram of
a chart and its base change, whose left-hand side is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_baseTestChartDiagram_eq_zero`.
The left tensor factor is the ring of functions of the base-changed chart, which
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.chartRingBaseTestAlgEquiv` identifies
with `𝒪_X(V) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`. -/
theorem lTensor_val_app_eq_zero_of_isZeroAt
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    letI : Algebra
      (chartRing B S hS
        (chartSpace B S hS (D.toModuleMapSituation B S hS).X
          (D.baseTestChartDiagram B S hS T V).V).1
        (chartSpace B S hS (D.toModuleMapSituation B S hS).X
          (D.baseTestChartDiagram B S hS T V).V).2
        (chartSpaceIdChartDiagram B S hS
          ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
          (D.baseTestChartDiagram B S hS T V)).V)
      (chartRing B S hS
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
        ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).2
        (D.baseTestChartDiagram B S hS T V).U) := chartDiagramAlgebra B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)
    LinearMap.lTensor
        (chartRing B S hS
          ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
          ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).2
          (D.baseTestChartDiagram B S hS T V).U)
        (((etaleModulePullback B S hS
                (chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                  (D.baseTestChartDiagram B S hS T V).V)
                (isEtale_chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                  (D.baseTestChartDiagram B S hS T V).V)).map
              (D.toModuleMapSituation B S hS).u).val.app
            (op (chartSpaceIdChartDiagram B S hS
              ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
              (D.baseTestChartDiagram B S hS T V)).V)).hom = 0 :=
  (ModuleMapSituation.val_app_testChartDiagram_eq_zero_iff_lTensor B S hS
      (D.toModuleMapSituation B S hS) (D.toModuleMapSituation_Y B S hS) (D.baseTest B S hS T)
      (toBaseTerminal B S hS T) (D.baseTest_hom_comp_eqToHom B S hS T) V
      (baseChartDiagram B S hS (D.toModuleMapSituation B S hS).X V).g
      (D.chartToBase_comp_eqToHom B S hS V) hT ‹IsAffine S› hV).1
    (D.val_app_baseTestChartDiagram_eq_zero B S hS T V hzero)

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
