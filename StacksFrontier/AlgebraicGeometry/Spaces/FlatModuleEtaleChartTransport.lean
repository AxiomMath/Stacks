module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence

/-!
# Flatness over a scheme target, read on an étale scheme chart of the source

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `f : X ⟶ h_V` be a
morphism of algebraic spaces into a *represented* one, and let `a : h_U ⟶ X` be an étale scheme
chart of `X` which factors `f` through a morphism `α : U ⟶ V` of the big fppf site.  This file
transports `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the condition of Stacks 05VV at a point,
from the point of `|X|` cut out by a point `u` of the chart scheme to the Zariski condition
`AlgebraicGeometry.IsFlatOverAt` of Stacks 08KT part (1) for the represented module comparison of
the chart pullback of `F`, over the morphism of representing schemes of `α`, at `u`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAt_representedZariskiRestriction_of_isFlatOverAtPoint`:
  **the transport**, from the condition at a chart point of the algebraic space to the
  ringed-space condition on the representing schemes.

## Implementation notes

The chart `a` and the factorisation `α` make a commuting square of étale scheme charts of `f`,
`AlgebraicGeometry.Space.etaleChartDiagramOfFactorization`, whose source chart is `a` and whose
target chart is the identity chart of `V`.  The chart independence of Stacks 05VU, in the form
`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram`, reads the condition
at the point of `|X|` cut out by `u` as flatness of the restriction `F|_a` over `V` at `u`; the
point of `|X|` is literally the one named in the statement, since
`AlgebraicGeometry.Space.pointOfEtaleChart` is that image of `u` unfolded.

What then remains is to replace `F|_a` by the represented comparison of the chart pullback
`a^* F`.  That is the base change of the chart restriction,
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, taken on the square whose source chart
is the identity chart of `U` and whose vertical morphism is `𝟙 U`; its left-hand side is the
Zariski inverse image along the identity, stripped by
`AlgebraicGeometry.Scheme.Modules.pullbackId`.  Flatness over the base at a point only depends
on the isomorphism class of the module, which is
`AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso`, so the comparison carries the condition
across.

Quasi-coherence of `F` is used only through the base-change comparison, which is where Stacks
05VU needs it as well.  The module universe is that of the structure rings, which is where
`AlgebraicGeometry.Space.restrictToChart` lands in `AlgebraicGeometry.Scheme.Modules`.

Nothing here is tagged: Stacks 05VU is registered where the chart independence is proved, and
this is that statement read at one chart of a morphism with represented target.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart diagram cut out by an étale chart and a factorization -/

/-- An étale morphism from a represented algebraic space, read as an object of the small étale
site of the target: the chart condition of `AlgebraicGeometry.Space.IsEtaleChart` is étaleness
of every represented base change, which is what `AlgebraicGeometry.Space.IsEtale` asks for. -/
def etaleChartOfIsEtale {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X.1) (ha : IsEtale B S hS a) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk a, (isEtale_iff_presheaf_of_yoneda B S hS a).1 ha⟩

/-- An étale scheme chart `a` of `X` together with a factorization of `f : X ⟶ h_V` through a
morphism `α : U ⟶ V` of the big fppf site, read as a commuting square of étale scheme charts of
`f`: the chart `a` on the source, the identity chart of `V` on the target, joined by `α`. -/
def etaleChartDiagramOfFactorization {V : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace V) {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X.1)
    (ha : IsEtale B S hS a) (α : U ⟶ V) (hcomm : a ≫ f.hom = yoneda.map α) :
    ChartDiagram B S hS X.1 (schemeSpace V).1 f.hom where
  U := etaleChartOfIsEtale B S hS a ha
  V := selfChart B S hS V
  g := α
  comm := hcomm.trans (Category.comp_id (yoneda.map α)).symm

/-! ### The transport -/

/-- The Zariski inverse image of a sheaf of modules along the image of an identity morphism of
the big fppf site is the sheaf itself. -/
def pullbackToSchemeMapIdIso (U : BigFppfOver B S hS)
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (𝟙 U))).obj M ≅ M :=
  eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj M)
      ((BigFppfOver.toScheme B S hS).map_id U)) ≪≫
    (Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj U)).app M

/-- The restriction of `F` to an étale scheme chart `a` of `X` is isomorphic to the represented
comparison of the pullback of `F` along `a`.

This is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso` on the square joining the
identity chart of `U` to the chart `a` by the identity of `U`, whose Zariski inverse image is
stripped by `AlgebraicGeometry.Space.pullbackToSchemeMapIdIso`. -/
def restrictToChartIsoRepresentedZariskiRestrictionPullback {X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X.1) (ha : IsEtale B S hS a)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha) ≅
      representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U)
        ((modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj F) :=
  (pullbackToSchemeMapIdIso B S hS U
      (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha))).symm ≪≫
    restrictToChartBaseChangeIso B S hS (X := schemeSpace U) (Z := X)
      (ObjectProperty.homMk a) F hF (etaleChartOfIsEtale B S hS a ha)
      (selfChart B S hS U) (𝟙 U)
      (congrArg (fun φ : yoneda.obj U ⟶ yoneda.obj U => φ ≫ a) (yoneda.map_id U))

/-- **Flatness over a represented target at a point of an étale scheme chart, read on the
representing schemes.** Let `f : X ⟶ h_V` be a morphism of algebraic spaces into a represented
one, let `a : h_U ⟶ X` be an étale scheme chart factoring `f` through `α : U ⟶ V`, and let `F`
be a quasi-coherent `𝒪_X`-module.  If `F` is flat over `h_V`, in the sense of Stacks 05VV, at
the point of `|X|` cut out by a point `u` of the scheme `U`, then the represented comparison of
the chart pullback `a^* F` is flat over the morphism of representing schemes of `α`, in the
ringed-space sense of Stacks 08KT part (1), at `u`.

This is the chart independence of Stacks 05VU on the square
`AlgebraicGeometry.Space.etaleChartDiagramOfFactorization`, followed by the base-change
comparison `AlgebraicGeometry.Space.restrictToChartIsoRepresentedZariskiRestrictionPullback` of
the restriction of `F` to the chart with the comparison module of the pullback. -/
theorem isFlatOverAt_representedZariskiRestriction_of_isFlatOverAtPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X.1) (ha : IsEtale B S hS a)
    (α : U ⟶ V) (hcomm : a ≫ f.hom = yoneda.map α)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (u : (BigFppfOver.toScheme B S hS).obj U)
    (h : IsFlatOverAtPoint B S hS X.2 f.hom F
      (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u))) :
    AlgebraicGeometry.IsFlatOverAt
      (LocallyRingedSpace.forgetToSheafedSpace.map
        ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
      (representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U)
        ((modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj F)) u :=
  (AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _
      (restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS a ha F hF) u).1
    ((isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF
      (etaleChartDiagramOfFactorization B S hS f a ha α hcomm) u).1 h)

end AlgebraicGeometry.Space

end

