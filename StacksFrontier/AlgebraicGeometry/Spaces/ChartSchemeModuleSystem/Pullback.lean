module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.Glue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The pullback of a glued module, read on a chart square

Let `𝓜` be a chart-scheme module system on an algebraic space `X`
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem`) and let `a : X' ⟶ X` be a morphism of
algebraic spaces.  A *chart square* of `a` is an étale chart `W` of `X'`, an étale chart `V` of
`X` and a morphism `g : W ⟶ V` of the underlying objects of the big fppf site with
`yoneda.map g ≫ V.hom = W.hom ≫ a.hom`.  On such a square the pullback `a^*(glue 𝓜)` is computed
by the chart module of `V`:

`(a^* glue 𝓜)|_W ≅ g^*(M V)`

on the scheme of `W`.  The special case of the identity chart of a scheme `T` over `X` is the
base change `AlgebraicGeometry.Space.baseChangeModule` of the glued module along a morphism
`p : yoneda.obj T ⟶ X` which factors through a chart `V` of `X`.

The comparison is the composite of the composition comparisons of Stacks 03LU along the two sides
of the square, the counit of Stacks 03LY at `V`
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem.glueChartModuleIso`), the identification
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` of the inverse image of the
module attached to `M V` along `g`, and the base identification of Stacks 03DX (2).

## Main definitions

* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartModuleRestrictionModulePullbackGlueIso`:
  the restriction of `a^*(glue 𝓜)` to the small étale site of the represented space of `W` is
  the module attached to `g^*(M V)`.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.restrictToChartSchemeModulePullbackGlueIso`:
  **`(a^* glue 𝓜)|_W ≅ g^*(M V)` on the scheme of `W`.**
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.baseChangeModuleGlueIso`: **the base change of
  the glued module to a scheme `T` along `p = g ≫ V` is `g^*(M V)`.**
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.baseChangeModuleGlueIsoOfChartSquare`: the
  same, read through a comparison of `g^*(M V)` with the value at the identity chart of a
  chart-scheme module system on the represented space of `T`.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.ChartSquare`: a chart square of a morphism of
  algebraic spaces, with `…ChartSquare.postcomp` and `…ChartSquare.precomp` its composites with
  morphisms of charts, and `…ComparisonCompatTarget` and `…ComparisonCompatSource` the two
  compatibilities of a family of chart-square comparisons `g^*(M V) ≅ M' W` with the transitions
  of the two systems.
* `Space.ChartSchemeModuleSystem.restrictToChartSchemeModulePullbackGlueIsoOfComparison`:
  on every chart square, `(a^* glue 𝓜)|_W ≅ (glue 𝓜')|_W` through such a comparison.

## What is not here

The global isomorphism `a^*(glue 𝓜) ≅ glue 𝓜'` from a family of chart-square comparisons
satisfying the two compatibilities is not constructed: the charts of `X'` carrying a chart square
cover `X'` but are not all of its charts, so the chartwise isomorphisms above must be glued by
descent of morphisms along that covering (the fullness half of Stacks 04W8), and their pairwise
compatibility on the overlaps requires the naturality of
`AlgebraicGeometry.Space.ChartSchemeModuleSystem.restrictToChartSchemeModulePullbackGlueIso` in
the chart square.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.ChartSchemeModuleSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (𝓜 : ChartSchemeModuleSystem B S hS X)

/-- **The restriction of a pulled-back glued module to a chart of a chart square.**  For a chart
square `g : W ⟶ V` of `a : X' ⟶ X`, the restriction of `a^*(glue 𝓜)` to the small étale site of
the represented space of `W` is the module attached through Stacks 03DX (2) to `g^*(M V)`. -/
def chartModuleRestrictionModulePullbackGlueIso {X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    (W : SmallEtale B S hS X'.1) (V : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X'.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    (chartModuleRestriction B S hS X' W).obj ((modulePullback B S hS a).obj 𝓜.glue) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X' W)).functor.obj
        (quasicoherentPullbackObj B S hS g (𝓜.qcohObj V))).obj :=
  (modulePullbackCompIso B S hS (chartToSpace B S hS X' W) a).app 𝓜.glue ≪≫
    eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj 𝓜.glue)
      (ObjectProperty.hom_ext _ hg :
        representedSpaceMap B S hS g ≫ chartToSpace B S hS X V =
          chartToSpace B S hS X' W ≫ a).symm) ≪≫
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS g)
      (chartToSpace B S hS X V)).app 𝓜.glue).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso (𝓜.glueChartModuleIso V) ≪≫
    modulePullbackRepresentedQuasicoherentIso B S hS g (𝓜.qcohObj V)

/-- **The pullback of the glued module, read on the scheme of a chart square.**  For
`a : X' ⟶ X` and a chart square `g : W ⟶ V` of `a`
(`yoneda.map g ≫ V.hom = W.hom ≫ a.hom`), the restriction of `a^*(glue 𝓜)` to the scheme of
`W` is the pullback `g^*(M V)` of the chart module of `V` along the morphism of schemes
underlying `g`. -/
def restrictToChartSchemeModulePullbackGlueIso {X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    (W : SmallEtale B S hS X'.1) (V : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X'.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    restrictToChartScheme B S hS X'.1 X'.2 ((modulePullback B S hS a).obj 𝓜.glue) W ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj (𝓜.M V) :=
  restrictToChartSchemeIsoRestrictModule B S hS X' _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a _
        𝓜.isQuasicoherentOnSite_glue) W ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme W) (chartFppfObject B S hS X' W).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X' W)).inverse.mapIso
        ((chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X' _ W).symm ≪≫
          𝓜.chartModuleRestrictionModulePullbackGlueIso a W V g hg)) ≪≫
    representedZariskiModuleQuasicoherentSchemeIso B S hS (chartFppfObject B S hS X' W)
      (quasicoherentPullbackObj B S hS g (𝓜.qcohObj V))

/-- **The base change of the glued module to a scheme over a chart.**  For a scheme `T` over the
base and a morphism `p : yoneda.obj T ⟶ X` which factors as `yoneda.map g ≫ V.hom` through an
étale chart `V` of `X`, the base change `AlgebraicGeometry.Space.baseChangeModule` of the glued
module along `p` is `g^*(M V)`. -/
def baseChangeModuleGlueIso (T : BigFppfOver B S hS) (p : yoneda.obj T ⟶ X.1)
    (V : SmallEtale B S hS X.1) (g : T ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = p) :
    baseChangeModule B S hS 𝓜.glue T p ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj (𝓜.M V) :=
  𝓜.restrictToChartSchemeModulePullbackGlueIso
    (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (ObjectProperty.homMk p)
    (idEtaleChart B S hS T) V g (hg.trans (Category.id_comp p).symm)

/-- **The base change of the glued module along a chart square of a scheme is the value at the
identity chart of a system on the scheme.**  If `𝓜'` is a chart-scheme module system on the
algebraic space represented by `T` and `c` identifies `g^*(M V)` with its value at the identity
chart of `T`, for a factorization `p = yoneda.map g ≫ V.hom`, then the base change of the glued
module along `p` is `𝓜'.M (idEtaleChart T)`. -/
def baseChangeModuleGlueIsoOfChartSquare (T : BigFppfOver B S hS) (p : yoneda.obj T ⟶ X.1)
    (𝓜' : ChartSchemeModuleSystem B S hS (schemeSpace T))
    (V : SmallEtale B S hS X.1) (g : T ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = p)
    (c : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj (𝓜.M V) ≅
      𝓜'.M (idEtaleChart B S hS T)) :
    baseChangeModule B S hS 𝓜.glue T p ≅ 𝓜'.M (idEtaleChart B S hS T) :=
  𝓜.baseChangeModuleGlueIso T p V g hg ≪≫ c

/-! ### Chart squares and comparisons of systems along a morphism -/

/-- **A chart square of a morphism `a : X' ⟶ X` of algebraic spaces**: an étale chart `W` of
`X'`, an étale chart `V` of `X` and a morphism `g` of the underlying objects of the big fppf site
with `yoneda.map g ≫ V.hom = W.hom ≫ a.hom`. -/
structure ChartSquare {X' : AlgebraicSpaces B S hS} (a : X' ⟶ X) where
  /-- the chart of the source -/
  W : SmallEtale B S hS X'.1
  /-- the chart of the target -/
  V : SmallEtale B S hS X.1
  /-- the morphism of the underlying objects of the big fppf site -/
  g : (SmallEtale.toOver B S hS X'.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V
  /-- the square commutes over `a` -/
  w : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom

namespace ChartSquare

variable {X' : AlgebraicSpaces B S hS} {a : X' ⟶ X}

/-- A chart square followed by a morphism of charts of the target. -/
@[simps]
def postcomp (q : ChartSquare a) {V₀ : SmallEtale B S hS X.1} (k : q.V ⟶ V₀) :
    ChartSquare a where
  W := q.W
  V := V₀
  g := q.g ≫ (SmallEtale.toOver B S hS X.1).map k
  w := by
    rw [Functor.map_comp, Category.assoc, yoneda_map_toOver_map_comp_hom, q.w]

/-- A chart square preceded by a morphism of charts of the source. -/
@[simps]
def precomp (q : ChartSquare a) {W₁ : SmallEtale B S hS X'.1} (l : W₁ ⟶ q.W) :
    ChartSquare a where
  W := W₁
  V := q.V
  g := (SmallEtale.toOver B S hS X'.1).map l ≫ q.g
  w := by
    rw [Functor.map_comp, Category.assoc, q.w, ← Category.assoc,
      yoneda_map_toOver_map_comp_hom]

end ChartSquare

/-- **Compatibility of chart-square comparisons with the transitions of the target system**: for
a chart square `q` and a morphism `k : q.V ⟶ V₀` of charts of `X`, the comparison at the
composite square is the comparison at `q` after the pullback of `τ k`. -/
def ComparisonCompatTarget {X' : AlgebraicSpaces B S hS} {a : X' ⟶ X}
    (𝓜' : ChartSchemeModuleSystem B S hS X')
    (c : ∀ q : ChartSquare a,
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).obj (𝓜.M q.V) ≅
        𝓜'.M q.W) : Prop :=
  ∀ (q : ChartSquare a) {V₀ : SmallEtale B S hS X.1} (k : q.V ⟶ V₀),
    (c (q.postcomp k)).hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map q.g)
          (chartSchemeMap k)).inv.app (𝓜.M V₀) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).map (𝓜.τ k).hom ≫
          (c q).hom

/-- **Compatibility of chart-square comparisons with the transitions of the source system**: for
a chart square `q` and a morphism `l : W₁ ⟶ q.W` of charts of `X'`, the comparison at the
composite square is the pullback of the comparison at `q` followed by `τ' l`. -/
def ComparisonCompatSource {X' : AlgebraicSpaces B S hS} {a : X' ⟶ X}
    (𝓜' : ChartSchemeModuleSystem B S hS X')
    (c : ∀ q : ChartSquare a,
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).obj (𝓜.M q.V) ≅
        𝓜'.M q.W) : Prop :=
  ∀ (q : ChartSquare a) {W₁ : SmallEtale B S hS X'.1} (l : W₁ ⟶ q.W),
    (c (q.precomp l)).hom =
      (Scheme.Modules.pullbackComp (chartSchemeMap l)
          ((BigFppfOver.toScheme B S hS).map q.g)).inv.app (𝓜.M q.V) ≫
        (Scheme.Modules.pullback (chartSchemeMap l)).map (c q).hom ≫ (𝓜'.τ l).hom

/-- **The pullback of the glued module, read on any chart square, through comparisons with a
system on the source.**  For a chart square `q` of `a` and a comparison `c q` of `g^*(M V)` with
the chart module `M' W` of a system on `X'`, the restriction of `a^*(glue 𝓜)` to the scheme of
`W` is `M' W`. -/
def restrictToChartSchemeModulePullbackGlueIsoOfComparison {X' : AlgebraicSpaces B S hS}
    {a : X' ⟶ X} (𝓜' : ChartSchemeModuleSystem B S hS X') (q : ChartSquare a)
    (c : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).obj (𝓜.M q.V) ≅
      𝓜'.M q.W) :
    restrictToChartScheme B S hS X'.1 X'.2 ((modulePullback B S hS a).obj 𝓜.glue) q.W ≅
      restrictToChartScheme B S hS X'.1 X'.2 𝓜'.glue q.W :=
  𝓜.restrictToChartSchemeModulePullbackGlueIso a q.W q.V q.g q.w ≪≫ c ≪≫
    (𝓜'.restrictToChartSchemeGlueIso q.W).symm

end AlgebraicGeometry.Space.ChartSchemeModuleSystem

end
