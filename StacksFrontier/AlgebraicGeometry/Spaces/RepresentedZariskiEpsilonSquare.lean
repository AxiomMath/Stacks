module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiNaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus
import StacksCore.Tactic.StacksAttribute

/-!
# The square of ringed sites `f₀ ∘ ε_X = ε_Y ∘ f_small` of Derived Categories of Spaces, 08GH

Let `S` be a scheme, let `φ : U ⟶ V` be a morphism of objects of the big fppf site over `S`, let
`f₀ : X₀ ⟶ Y₀` be the morphism of the underlying schemes, and let `X = h_U` and `Y = h_V` be the
algebraic spaces they represent, so that `f = f_small` is the morphism of small étale topoi of the
represented morphism `h_φ : X ⟶ Y`.  Stacks 08GH asserts, as the reason for its two squares of
derived categories, that the diagram of ringed sites

```
X_{0, Zar} ◂──ε_X── X_étale
    │                  │
   f₀                  f
    ▼                  ▼
Y_{0, Zar} ◂──ε_Y── Y_étale
```

commutes, with "details omitted".  **This module supplies those details.**  Stacks calls a
diagram of ringed topoi commutative when its two composites are 2-isomorphic in the sense of
Stacks 04IC, and that is what is proved: the square of continuous site functors commutes up to a
canonical natural isomorphism, hence so do the direct images of the two composite morphisms of
ringed topoi `f₀ ∘ ε_X` and `ε_Y ∘ f_small`, and that isomorphism carries the structure map of one
composite to the structure map of the other.

Here `ε` is `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom` (Stacks 071P,
Equation 75.4.0.1, Stacks 08H7) and `f` is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` (Stacks 03G8).

## Main definitions

* `AlgebraicGeometry.Space.representedEpsilonCharts`: the left-and-down branch of the square on
  sites, `W ↦ f₀^{-1}(W)` read as an étale chart of `X`.
* `AlgebraicGeometry.Space.representedEpsilonChartsBaseChange`: the up-and-right branch,
  `W ↦ X ×_Y W` read as an étale chart of `X`.
* `AlgebraicGeometry.Space.representedEpsilonChartBaseChangeIso`: the conjugate of the chart
  base-change comparison of
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, which carries base change of
  étale charts of the representing schemes to base change of étale charts of the spaces.
* `AlgebraicGeometry.Space.representedZariskiEpsilonCompLeft` and
  `AlgebraicGeometry.Space.representedZariskiEpsilonCompRight`: the two composite morphisms of
  ringed topoi `f₀ ∘ ε_X` and `ε_Y ∘ f_small` of the square.
* `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`: **the square of Stacks 08GH**, as a
  2-isomorphism of those two composites.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonSiteSquare`: **the square of sites of Stacks 08GH
  commutes.**  Pulling a Zariski open of `Y₀` back along `f₀` and viewing it as an étale chart of
  `X` is viewing it as an étale chart of `Y` and base-changing along `f`.
* `AlgebraicGeometry.Space.representedEpsilonPushforwardIso`: **the direct images of the two
  composites agree**, which is the square of Stacks 08GH read on the underlying topoi.
* `AlgebraicGeometry.Space.representedEpsilonSquare_commutes`: **the isomorphism of direct images
  carries the structure map of one composite to that of the other**, which is the second
  component of the 2-isomorphism; `AlgebraicGeometry.Space.representedEpsilonSquare_key` and
  `AlgebraicGeometry.Space.representedEpsilonSquare_key_app` are its inverse-free form and its
  reading on sections.
* `AlgebraicGeometry.Space.representedEpsilonChartTriangle_apply`: **the triangle of schemes**
  the structure-map half reduces to — a component of the square, followed by the restriction of
  `f₀` to a Zariski open `W` of `Y₀`, is the cartesian projection `X ×_Y W ⟶ W`.
* `AlgebraicGeometry.Space.representedEpsilonGamma`: **the resulting identification of regular
  functions**, which is the whole content of the structure-map half; and
  `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom_forgetFSharp_app`, the
  structure map of `ε` on sections.
* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_inverse_toScheme`,
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_inverse_forget` and
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_inverse_chartMap`: **the equivalence
  of the small étale site of a represented algebraic space with that of the representing scheme
  changes nothing about a chart** — not its scheme, not its object of the bounded category of
  schemes, not its structure morphism.  The equivalence is built by
  `CategoryTheory.ObjectProperty.Equivalence.congrFullSubcategory` and nothing in the library
  computed it on objects before; these are the rules the structure-map half of the square needs.

## Implementation notes

The two branches are both restrictions along continuous functors, and that is how the comparison
is built: `AlgebraicGeometry.Space.representedEpsilonSiteSquare` is an isomorphism of the two
composite site functors, and
`AlgebraicGeometry.Space.representedEpsilonPushforwardIso` is its image under
`CategoryTheory.Functor.sheafPushforwardContinuousIso` together with the two identifications of
a composite of restrictions with the restriction along the composite.

The square is assembled from the two halves the library already carries, and no part of either
is rebuilt here:

* on the Zariski edge, `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` — base-changing an open
  `W ⊆ Y₀` along `f₀` gives the preimage open `f₀^{-1}(W)`;
* on the étale edge, `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` — chart base
  change along a represented morphism of algebraic spaces is base change of the underlying
  scheme charts.

The second is stated for the *functors* of the equivalences
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, while `ε` is built from their
*inverses*; `AlgebraicGeometry.Space.representedEpsilonChartBaseChangeIso` conjugates it, which
is where the unit and counit of those equivalences are used and the only place they are.

For the étale direct image the comparison used is
`AlgebraicGeometry.Space.chartComparison` rather than
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`.  The two have the same
endpoints, but only the first is computable on sections; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoChartProjection.lean` record why.

## Scope

**The tag is registered on `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`, and it
covers one of the remark's three clauses.**  Remark 75.6.3 asserts (1) that the square of `Lf₀^*`
and `Lf^*` against the two identifications of Lemma 071Q commutes, (2) as the reason, that the
diagram of ringed sites displayed above commutes — "details omitted" — and (3) that the square of
`Rf_{0,*}` and `Rf_*` commutes when `f` is quasi-compact and quasi-separated.  **Only (2) is
proved here**, and the clause string of the tag says so.  Clauses (1) and (3) need the derived
pullback and total direct image of the two sides and the equivalences of Lemma 071Q, none of
which this file touches.

The absence recorded in the scope sections of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentComplex.lean` (step 2 of
its account of Stacks 0D0X) and of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRelativeRingedToposHom.lean` is
the absence of clause (2), and it is what this file removes.

## Implementation notes on the two spellings of one topology

`AlgebraicGeometry.Scheme.zariskiRingedTopos` is a `def`, so neither instance search nor a
rewrite's motive sees through it: `(Y₀.zariskiRingedTopos).J`, `.C` and `.category` do not reduce
to `TopologicalSpace.Opens.grothendieckTopology ↥Y₀`, `Y₀.Opens` and
`Preorder.smallCategory _`.  A comparison of direct images has its *type* in the
`AlgebraicGeometry.RingedTopos.Topos` spelling, since that is what
`AlgebraicGeometry.RingedToposHom` carries, and its
`CategoryTheory.Functor.sheafPushforwardContinuous` factors in the other; with the two mixed, no
factor can be abstracted.  Two measures keep this file clear of that:

* every topology is written at the `AlgebraicGeometry.RingedTopos.J` spelling, and the continuity
  of each branch is restated there — the statements are the existing ones, re-read.  Because
  instance search does not see through the `def` either, the two composite instances pass their
  arguments to `CategoryTheory.Functor.isContinuous_comp` explicitly, as
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean`
  already does for its own composites;
* the trailing factors of `AlgebraicGeometry.Space.representedZariskiEpsilonCompRightIso` are
  `CategoryTheory.Functor.sheafPushforwardContinuousComp`, which *is* `Iso.refl`, rather than
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` at an identity isomorphism, which is
  equal to the identity only by a lemma.  That is what makes
  `AlgebraicGeometry.Space.representedZariskiEpsilonCompRightIso_hom_app_apply` hold by `rfl`
  instead of by rewriting, and it is why
  `AlgebraicGeometry.Space.representedZariskiEpsilonCompLeftIso` can be `Iso.refl`.

Where an identity still has to be used across the remaining boundary — the one between an étale
chart of `X` built from `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and the étale
scheme it came from — it is applied with `exact` or `congrArg` and never rewritten, and every
intermediate step is stated over abstract objects of the bounded category of schemes.  That is
the discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChange.lean` prescribe, and
`AlgebraicGeometry.Space.representedEpsilonTriangleAux` and
`AlgebraicGeometry.Space.representedEpsilonAppTopAux` are the abstract statements it calls for.

## References

* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH), the square; its
  commutativity as a diagram of ringed topoi is proved here, its two squares of derived
  categories are not.
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC), 2-morphisms of morphisms
  of ringed topoi, which is what "the diagram commutes" means.
* [Stacks Project, Tag 071P](https://stacks.math.columbia.edu/tag/071P), Section 75.4, whose
  Equation 75.4.0.1 is the `ε` used here.
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7), that equation.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), base change of étale
  charts.
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), morphisms of ringed
  topoi, their composition, and when a diagram of them commutes.
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), the statement the square
  is needed for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-! ### The two branches of the square on sites -/

/-- The Zariski opens of the scheme representing an algebraic space, read as étale charts of
that space: the site functor underlying `ε`. -/
abbrev representedEpsilonFunctor (W : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj W).Opens ⥤ SmallEtale B S hS (yoneda.obj W) :=
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj W) W.left.property ⋙
    (representedSmallEtaleEquivalence B S hS W).inverse

/-- Chart base change along a represented morphism of algebraic spaces. -/
abbrev representedChartBaseChange :
    SmallEtale B S hS (yoneda.obj V) ⥤ SmallEtale B S hS (yoneda.obj U) :=
  smallBaseChange B S hS (representedSpaceMap B S hS φ)
    (relativelyRepresentable_yoneda_map B S hS φ)

/-- **The left-and-down branch of the square of Stacks 08GH on sites.**  A Zariski open `W` of
`Y₀` is pulled back along the representing morphism of schemes and the preimage open is read as
an étale chart of `X = h_U`. -/
abbrev representedEpsilonCharts :
    ((BigFppfOver.toScheme B S hS).obj V).Opens ⥤ SmallEtale B S hS (yoneda.obj U) :=
  Opens.map ((BigFppfOver.toScheme B S hS).map φ).base ⋙ representedEpsilonFunctor B S hS U

/-- **The up-and-right branch of the square of Stacks 08GH on sites.**  A Zariski open `W` of
`Y₀` is read as an étale chart of `Y = h_V` and base-changed along `f`. -/
abbrev representedEpsilonChartsBaseChange :
    ((BigFppfOver.toScheme B S hS).obj V).Opens ⥤ SmallEtale B S hS (yoneda.obj U) :=
  representedEpsilonFunctor B S hS V ⋙ representedChartBaseChange B S hS φ

/-! ### Continuity of the branches -/

/-- Chart base change along a represented morphism is continuous, being a morphism of sites. -/
instance isContinuous_representedChartBaseChange :
    (representedChartBaseChange B S hS φ).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj V)) (SmallEtale.topology B S hS (yoneda.obj U)) :=
  (smallBaseChange_isMorphismOfSites B S hS (representedSpaceMap B S hS φ)
    (relativelyRepresentable_yoneda_map B S hS φ)).toIsContinuous

/-! The topology of the small Zariski site is written here as
`(X₀.zariskiRingedTopos).J` rather than as `TopologicalSpace.Opens.grothendieckTopology ↥X₀`.
The two are definitionally equal, but `AlgebraicGeometry.Scheme.zariskiRingedTopos` is a `def`, so
neither instance search nor a rewrite's motive sees through it: a comparison of direct images
whose *type* is in the `AlgebraicGeometry.RingedTopos.Topos` spelling — which is what
`AlgebraicGeometry.RingedToposHom` carries — and whose
`CategoryTheory.Functor.sheafPushforwardContinuous` factors are in the other cannot have one of
those factors abstracted.  With one spelling throughout, `AlgebraicGeometry.RingedTopos.Topos`
being a reducible abbreviation for `CategoryTheory.Sheaf _.J _`, the two agree syntactically.
That is why the continuity of each branch is restated below at this spelling. -/

/-- Taking preimages of opens along the representing morphism of schemes is continuous, at the
spelling of the topology that the morphisms of ringed topoi use. -/
instance isContinuous_opensMap_zariskiRingedTopos :
    (Opens.map ((BigFppfOver.toScheme B S hS).map φ).base).IsContinuous
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J :=
  _root_.AlgebraicGeometry.SmallEtale.isContinuous_opensMap (associatedBigEtaleSite B)
    (Over.Hom.left φ)

/-- The inclusion of the small Zariski site of the representing scheme into its small étale site
is continuous, at the spelling of the topology that the morphisms of ringed topoi use. -/
instance isContinuous_opensToSmallEtale_zariskiRingedTopos (W : BigFppfOver B S hS) :
    (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property).IsContinuous
      ((BigFppfOver.toScheme B S hS).obj W).zariskiRingedTopos.J
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property) :=
  _root_.AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj W) W.left.property

/-- The site functor underlying `ε` is continuous: it is the continuous inclusion of the small
Zariski site into the small étale site of the representing scheme, followed by the equivalence
of that site with the small étale site of the represented space. -/
instance isContinuous_representedEpsilonFunctor (W : BigFppfOver B S hS) :
    (representedEpsilonFunctor B S hS W).IsContinuous
      ((BigFppfOver.toScheme B S hS).obj W).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS W)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_opensToSmallEtale_zariskiRingedTopos B S hS W) inferInstance

/-- The left-and-down branch `representedEpsilonCharts` of the square of sites is continuous. -/
instance isContinuous_representedEpsilonCharts :
    (representedEpsilonCharts B S hS φ).IsContinuous
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J _
    (isContinuous_opensMap_zariskiRingedTopos B S hS φ)
    (isContinuous_representedEpsilonFunctor B S hS U)

/-- The up-and-right branch `representedEpsilonChartsBaseChange` of the square of sites is
continuous. -/
instance isContinuous_representedEpsilonChartsBaseChange :
    (representedEpsilonChartsBaseChange B S hS φ).IsContinuous
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).J _
    (isContinuous_representedEpsilonFunctor B S hS V)
    (isContinuous_representedChartBaseChange B S hS φ)

/-! ### The square of sites -/

/-- **Chart base change of the represented morphism, conjugated to the inverses of the
equivalences of small étale sites.**  Base-changing étale charts of the representing scheme `Y₀`
along `f₀` and transporting to `X = h_U` is transporting to `Y = h_V` and base-changing charts
along `f`.

This is `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` read on the inverses of the
two equivalences, which is the direction `ε` is built in: the unit of the source's equivalence
cancels the functor it is conjugated by and the counit of the target's cancels the other. -/
def representedEpsilonChartBaseChangeIso :
    (representedSmallEtaleEquivalence B S hS V).inverse ⋙ representedChartBaseChange B S hS φ ≅
      _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
          (Over.Hom.left φ) ⋙
        (representedSmallEtaleEquivalence B S hS U).inverse :=
  Functor.isoWhiskerLeft (representedSmallEtaleEquivalence B S hS V).inverse
      ((Functor.rightUnitor (representedChartBaseChange B S hS φ)).symm ≪≫
        Functor.isoWhiskerLeft (representedChartBaseChange B S hS φ)
          (representedSmallEtaleEquivalence B S hS U).unitIso ≪≫
        Functor.isoWhiskerRight
          (representedSmallEtaleBaseChangeIso B S hS φ
            (relativelyRepresentable_yoneda_map B S hS φ))
          (representedSmallEtaleEquivalence B S hS U).inverse) ≪≫
    (representedSmallEtaleEquivalence B S hS V).invFunIdAssoc
      (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
          (Over.Hom.left φ) ⋙
        (representedSmallEtaleEquivalence B S hS U).inverse)

/-- **The square of sites of Stacks 08GH commutes.**  For a Zariski open `W` of the scheme `Y₀`
representing `Y`, pulling `W` back along the representing morphism of schemes `f₀` and reading
the preimage open as an étale chart of `X` is the same as reading `W` as an étale chart of `Y`
and base-changing it along `f`.

Both branches are the composite of two identifications the library already carries: that the
base change of an open along a morphism of schemes is the preimage open
(`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`), and that chart base change of a represented
morphism of algebraic spaces is base change of the underlying scheme charts
(`AlgebraicGeometry.Space.representedEpsilonChartBaseChangeIso`). -/
def representedEpsilonSiteSquare :
    representedEpsilonCharts B S hS φ ≅ representedEpsilonChartsBaseChange B S hS φ :=
  Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B)
        (Over.Hom.left φ)) (representedSmallEtaleEquivalence B S hS U).inverse ≪≫
    Functor.isoWhiskerLeft
      (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
      (representedEpsilonChartBaseChangeIso B S hS φ).symm

/-! ### How the equivalence of small étale sites acts on charts

`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is produced from
`CategoryTheory.ObjectProperty.Equivalence.congrFullSubcategory` and nothing in the library says
what it does to an object.  It does nothing: an étale chart of `h_U` and an étale `U`-scheme are
the same datum presented twice, and the equivalence is the reindexing.  The three rules below
record that, and they are what the structure-map half of the square of Stacks 08GH needs — see
the scope section of this file. -/

/-- **The equivalence of small étale sites does not change the underlying scheme of a chart.**
Transporting an étale scheme over `U` to an étale chart of `h_U` and taking the scheme of that
chart is taking the scheme of the étale `U`-scheme.  An equality of functors, so it holds of the
morphisms of charts as well as of the charts. -/
theorem representedSmallEtaleEquivalence_inverse_toScheme (W : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS W).inverse ⋙
        SmallEtale.toOver B S hS (yoneda.obj W) ⋙ BigFppfOver.toScheme B S hS =
      _root_.AlgebraicGeometry.SmallEtale.toScheme (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property :=
  rfl

/-- **The equivalence of small étale sites does not change the underlying object of the bounded
category of schemes.**  This is
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_inverse_toScheme` one step earlier,
before the bounded category is included into schemes, which is the level at which the cartesian
projections of chart base change live. -/
theorem representedSmallEtaleEquivalence_inverse_forget (W : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS W).inverse ⋙
        SmallEtale.toOver B S hS (yoneda.obj W) ⋙ BigFppfOver.forget B S hS =
      _root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property ⋙
        Over.forget _ :=
  rfl

/-- **The equivalence of small étale sites does not change the structure morphism of a chart.**
The chart morphism of the transported chart, read through the Yoneda correspondence, is the
structure morphism of the étale `U`-scheme it came from. -/
theorem representedSmallEtaleEquivalence_inverse_chartMap (W : BigFppfOver B S hS)
    (Z : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj W) W.left.property) :
    (yonedaEquiv ((representedSmallEtaleEquivalence B S hS W).inverse.obj Z).1.hom).left =
      Z.obj.hom :=
  rfl

/-! ### The triangle of schemes the structure-map half reduces to

The compatibility of the square with the structure maps reduces, over a Zariski open `W` of
`Y₀`, to one equation of morphisms of schemes: the component of the square at `W` followed by the
restriction `f₀ ∣_ W` is the cartesian projection `X ×_Y W ⟶ W`.  That equation is proved here,
together with the identification of global regular functions it gives.

Every statement in this section is phrased over *abstract* objects of the bounded category of
schemes, and the passage to the objects of the square — which are definitionally but not
syntactically those — is made by `exact`, never by a rewrite.  The objects of the square are
built from `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and from a chosen
relative-representability witness, neither of which unfolds at `implicit` transparency, so a
rewrite whose motive crosses the boundary fails; this is the discipline the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChange.lean` prescribe. -/

section Triangle

variable {C : Type*} [Category* C] {A P K Oo Xo Yo : C}

/-- **The triangle, over abstract objects.**  If `pf, ps` are the two legs of a square over
`ι, a`, if `b` carries `P` into that square over `j`, and if `n` and `c` are maps whose
composites with `j` and `ι` agree over `a`, then `n ≫ b ≫ pf` and `c` agree after composing
with `ι`.

Stated abstractly on purpose: instantiated at the square of Stacks 08GH every object is
definitionally but not syntactically the one written here, and `exact` crosses that boundary
where a rewrite cannot. -/
theorem representedEpsilonTriangleAux (n : A ⟶ P) (b : P ⟶ K) (pf : K ⟶ Oo) (ps : K ⟶ Xo)
    (ι : Oo ⟶ Yo) (a : Xo ⟶ Yo) (j : P ⟶ Xo) (d : A ⟶ Xo) (c : A ⟶ Oo)
    (hcond : pf ≫ ι = ps ≫ a) (hbs : b ≫ ps = j) (hn : n ≫ j = d)
    (hc : c ≫ ι = d ≫ a) :
    (n ≫ b ≫ pf) ≫ ι = c ≫ ι := by
  subst hbs hn
  rw [hc]
  simp [hcond]

end Triangle

/-- **The triangle of schemes of the square of Stacks 08GH**, for any map `n` of the chart
schemes over `X₀` and any candidate projection `c` over `Y₀`: `n`, followed by the
identification of the base change of the open `W` with the preimage open and by the cartesian
projection to `W`, is `c`.

The open immersion of `W` is a monomorphism, so the two agree as soon as they agree over `Y₀`,
which is what `hn` and `hc` say. -/
theorem representedEpsilonChartTriangle (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    {A : (associatedBigEtaleSite B).Scheme}
    (n : A ⟶ _root_.AlgebraicGeometry.SmallEtale.preimageSchemeObj
      (associatedBigEtaleSite B) (Over.Hom.left φ) O)
    (c : A ⟶ (associatedBigEtaleSite B).obj (O : Scheme.{u})
      (_root_.AlgebraicGeometry.BigEtaleOver.contains_opens (associatedBigEtaleSite B)
        V.left.property O))
    (d : A ⟶ U.left)
    (hn : n ≫ ObjectProperty.homMk
        (((BigFppfOver.toScheme B S hS).map φ) ⁻¹ᵁ O).ι = d)
    (hc : c ≫ _root_.AlgebraicGeometry.SmallEtale.opensSchemeι
        (associatedBigEtaleSite B) O = d ≫ Over.Hom.left φ) :
    n ≫ (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso
          (associatedBigEtaleSite B) (Over.Hom.left φ) O).hom.hom.left ≫
        pullback.fst (_root_.AlgebraicGeometry.SmallEtale.opensSchemeι
          (associatedBigEtaleSite B) O) (Over.Hom.left φ) = c := by
  have := _root_.AlgebraicGeometry.SmallEtale.mono_opensSchemeι
    (associatedBigEtaleSite B) O
  exact (cancel_mono (_root_.AlgebraicGeometry.SmallEtale.opensSchemeι
      (associatedBigEtaleSite B) O)).1
    (representedEpsilonTriangleAux n _ (pullback.fst _ _) (pullback.snd _ _) _ _ _ d c
      pullback.condition
      (_root_.AlgebraicGeometry.SmallEtale.openPullbackIso_hom_snd
        (associatedBigEtaleSite B) (Over.Hom.left φ) O)
      hn hc)

/-- **The triangle at a component of the square of Stacks 08GH.**  For any morphism `m` of
étale charts of `X` from `X ×_Y W` to `f₀^{-1}(W)` — in particular for the component of
`AlgebraicGeometry.Space.representedEpsilonSiteSquare` at `W` — the scheme map of `m`, followed
by the restriction of `f₀` to `W`, is the cartesian projection of chart base change.

The two hypotheses of `AlgebraicGeometry.Space.representedEpsilonChartTriangle` are supplied by
`AlgebraicGeometry.Space.representedChart_w` for `m`, read through
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_inverse_chartMap`, and by the
representability square `AlgebraicGeometry.Space.isPullback_representedChart_schemes`. -/
theorem representedEpsilonChartTriangle_apply
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (m : (representedEpsilonChartsBaseChange B S hS φ).obj O ⟶
      (representedEpsilonCharts B S hS φ).obj O) :
    m.hom.left.left ≫ (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso
          (associatedBigEtaleSite B) (Over.Hom.left φ) O).hom.hom.left ≫
        pullback.fst (_root_.AlgebraicGeometry.SmallEtale.opensSchemeι
          (associatedBigEtaleSite B) O) (Over.Hom.left φ) =
      ((relativelyRepresentable_yoneda_map B S hS φ).snd
        ((representedEpsilonFunctor B S hS V).obj O).1.hom).left :=
  representedEpsilonChartTriangle B S hS φ O _ _ _ (representedChart_w B S hS m)
    (isPullback_representedChart_schemes B S hS φ
      (relativelyRepresentable_yoneda_map B S hS φ)
      ((representedEpsilonFunctor B S hS V).obj O)).w

/-! ### The identification of regular functions -/

/-- Global regular functions along a factored morphism of schemes, over abstract objects: if
`n ≫ q = p` and `u` followed by `q` on global functions is `v`, then `u` followed by `p` is `v`
followed by `n`. -/
theorem representedEpsilonAppTopAux {A P Oc : Scheme.{u}} (n : A ⟶ P) (q : P ⟶ Oc) (p : A ⟶ Oc)
    (hp : n ≫ q = p) {R : CommRingCat.{u}} (v : R ⟶ Γ(P, ⊤)) (u : R ⟶ Γ(Oc, ⊤))
    (hu : u ≫ q.appTop = v) :
    u ≫ p.appTop = v ≫ n.appTop := by
  rw [← hp, Scheme.Hom.comp_appTop, ← Category.assoc, hu]

/-- **The identification of regular functions that the structure-map half of the square of
Stacks 08GH asks for.**  Over a Zariski open `W` of `Y₀`: a section of `𝒪_{Y₀}` over `W`, pulled
back along the cartesian projection `X ×_Y W ⟶ W` of chart base change, is the same as the
section pulled back along `f₀`, restricted to `f₀^{-1}(W)` and then pulled back along the scheme
map of the component `m` of the square.

The left-hand pullback is the one `f_small^♯` becomes under
`AlgebraicGeometry.Space.chartComparison_structureSharp`; the right-hand one is `ε_X^♯` after
`f₀^♯`, by `AlgebraicGeometry.SmallEtale.topIso_inv_appTop_baseChangeOpens`.  So this is the
whole content of the structure-map compatibility, with only the bookkeeping of the two
comparisons of direct images left; see the scope section of this file. -/
theorem representedEpsilonGamma (O : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (m : (representedEpsilonChartsBaseChange B S hS φ).obj O ⟶
      (representedEpsilonCharts B S hS φ).obj O) :
    (Scheme.Opens.topIso O).inv ≫
        ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS φ).snd
            ((representedEpsilonFunctor B S hS V).obj O).1.hom)).appTop =
      (((BigFppfOver.toScheme B S hS).map φ).app O ≫
          (Scheme.Opens.topIso (((BigFppfOver.toScheme B S hS).map φ) ⁻¹ᵁ O)).inv) ≫
        (B.inclusion.map m.hom.left.left).appTop := by
  have hn := (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (representedEpsilonChartTriangle_apply B S hS φ O m))
  exact representedEpsilonAppTopAux _ _ _ hn _ _
    ((congrArg (fun g => (Scheme.Opens.topIso O).inv ≫ Scheme.Hom.appTop g)
      (B.inclusion.map_comp _ _)).trans
      (_root_.AlgebraicGeometry.SmallEtale.topIso_inv_appTop_baseChangeOpens
        (associatedBigEtaleSite B) (Over.Hom.left φ) O))

/-- **`ε^♯` on sections.**  Over a Zariski open `W` of the representing scheme, the structure map
of `ε` is the identification of the sections of `𝒪_{W₀}` over `W` with the global regular
functions on the open subscheme `W`.

Both comparisons `ε` is composed of contribute nothing: the Zariski-to-étale one is that
identification (`AlgebraicGeometry.SmallEtale.commRingStructureMap`) and the one along the
equivalence of small étale sites is the identity
(`AlgebraicGeometry.Space.representedEtaleStructureMap`). -/
theorem representedToSchemeZariskiRingedToposHom_forgetFSharp_app (W : BigFppfOver B S hS)
    (Z : ((BigFppfOver.toScheme B S hS).obj W).zariskiRingedTopos.C)
    (t : ((((BigFppfOver.toScheme B S hS).obj W).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj W).zariskiRingedTopos.O)).obj.obj (op Z)) :
    (AlgebraicGeometry.RingedToposHom.forgetFSharp
        (representedToSchemeZariskiRingedToposHom B S hS W)).hom.app (op Z) t =
      (forget CommRingCat.{u}).map (Scheme.Opens.topIso Z).inv t :=
  CategoryTheory.Sheaf.hom_congr_app_apply
    (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj W) W.left.property)
      (representedEtaleRingedToposHom B S hS W)) (op Z) t

/-! ### The two composite morphisms of ringed topoi -/

/-- **The left-and-down composite `f₀ ∘ ε_X`** of the square of Stacks 08GH: the comparison `ε`
of the small étale ringed topos of `X = h_U` with the small Zariski ringed topos of the
representing scheme `X₀`, followed by the morphism of Zariski ringed topoi of `f₀`. -/
abbrev representedZariskiEpsilonCompLeft :
    AlgebraicGeometry.RingedToposHom
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos :=
  AlgebraicGeometry.RingedToposHom.comp
    (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
    (Y := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos)
    (Z := ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos)
    (representedZariskiSchemeHom B S hS φ)
    (representedToSchemeZariskiRingedToposHom B S hS U)

/-- **The up-and-right composite `ε_Y ∘ f_small`** of the square of Stacks 08GH: the morphism of
small étale ringed topoi of the represented morphism of algebraic spaces, followed by the
comparison `ε` of the small étale ringed topos of `Y = h_V` with the small Zariski ringed topos
of the representing scheme `Y₀`. -/
abbrev representedZariskiEpsilonCompRight :
    AlgebraicGeometry.RingedToposHom
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos :=
  AlgebraicGeometry.RingedToposHom.comp
    (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
    (Y := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V))
    (Z := ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos)
    (representedToSchemeZariskiRingedToposHom B S hS V)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))

/-- **The direct image of `f₀ ∘ ε_X` is restriction along the left-and-down branch of the square
of sites, on the nose.**  Both `ε_X` and `f₀` are given by restriction along a continuous functor,
and restriction along a composite of functors of sites *is* the composite of the restrictions —
`CategoryTheory.Functor.sheafPushforwardContinuousComp` is `Iso.refl`.  So no comparison is
needed on this side, and the identification is the identity. -/
def representedZariskiEpsilonCompLeftIso :
    (representedZariskiEpsilonCompLeft B S hS φ).toToposHom.pushforward ≅
      (representedEpsilonCharts B S hS φ).sheafPushforwardContinuous (Type u)
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J :=
  Iso.refl _

/-- The left-hand comparison is the identity. -/
@[simp]
theorem representedZariskiEpsilonCompLeftIso_hom :
    (representedZariskiEpsilonCompLeftIso B S hS φ).hom = 𝟙 _ :=
  rfl

/-- The direct image of `ε_Y ∘ f_small` is restriction along the up-and-right branch of the
square of sites.  The étale direct image is identified with restriction along chart base change
by `AlgebraicGeometry.Space.chartComparison`, the represented morphism being relatively
representable. -/
def representedZariskiEpsilonCompRightIso :
    (representedZariskiEpsilonCompRight B S hS φ).toToposHom.pushforward ≅
      (representedEpsilonChartsBaseChange B S hS φ).sheafPushforwardContinuous (Type u)
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J :=
  Functor.isoWhiskerRight
      (chartComparison B S hS (representedSpaceMap B S hS φ)
        (relativelyRepresentable_yoneda_map B S hS φ))
      ((representedSmallEtaleEquivalence B S hS V).inverse.sheafPushforwardContinuous (Type u)
          (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
          (SmallEtale.topology B S hS (yoneda.obj V)) ⋙
        (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).sheafPushforwardContinuous
          (Type u) ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) ≪≫
    Functor.isoWhiskerLeft
      ((representedChartBaseChange B S hS φ).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS (yoneda.obj V))
        (SmallEtale.topology B S hS (yoneda.obj U)))
      (Functor.sheafPushforwardContinuousComp
        (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
        (representedSmallEtaleEquivalence B S hS V).inverse (Type u)
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).J) ≪≫
    Functor.sheafPushforwardContinuousComp
      (representedEpsilonFunctor B S hS V) (representedChartBaseChange B S hS φ) (Type u)
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J

/-- **The right-hand comparison, on sections, is the chart comparison.**  Its two trailing
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` factors are identities, restriction along
a composite of functors of sites being the composite of the restrictions, so over a Zariski open
`W` of `Y₀` the comparison is `AlgebraicGeometry.Space.chartComparison` read at the étale chart of
`Y` cut out by `W`. -/
theorem representedZariskiEpsilonCompRightIso_hom_app_apply
    (Oop : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (x : ((representedZariskiEpsilonCompRight B S hS φ).toToposHom.pushforward.obj
      (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).obj.obj Oop) :
    (((representedZariskiEpsilonCompRightIso B S hS φ).hom.app
        (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).hom.app Oop) x =
      (((chartComparison B S hS (representedSpaceMap B S hS φ)
          (relativelyRepresentable_yoneda_map B S hS φ)).hom.app
        (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).hom.app
        (op ((representedEpsilonFunctor B S hS V).obj Oop.unop))) x :=
  rfl

/-- **The structure maps of the two composites agree, on sections.**  Over a Zariski open `W` of
`Y₀` both sides are pullbacks of regular functions to the chart `X ×_Y W`, and they agree by
`AlgebraicGeometry.Space.representedEpsilonGamma`.

Stated at sections rather than as an equation of morphisms of sheaves, and with every ingredient
instantiated before it is used: each of the four identities below is an equation between elements
of a `Type u`, so its motive is type-correct, whereas the same identities as general rewrite rules
abstract an object of `(Y₀.zariskiRingedTopos).C` against one of `Y₀.Opens` and fail. -/
theorem representedEpsilonSquare_key_app
    (Oop : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (s : ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).obj.obj Oop) :
    ((Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app
        (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).hom.app Oop
      ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS U)).hom.app
        (op ((Opens.map ((BigFppfOver.toScheme B S hS).map φ).base).obj Oop.unop))
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedZariskiSchemeHom B S hS φ)).hom.app Oop s)) =
    ((representedZariskiEpsilonCompRightIso B S hS φ).hom.app
        (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).hom.app Oop
      ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))).hom.app
        (op ((representedEpsilonFunctor B S hS V).obj Oop.unop))
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app Oop s)) := by
  have hV := representedToSchemeZariskiRingedToposHom_forgetFSharp_app B S hS V Oop.unop s
  have hU := representedToSchemeZariskiRingedToposHom_forgetFSharp_app B S hS U
    ((Opens.map ((BigFppfOver.toScheme B S hS).map φ).base).obj Oop.unop)
    ((AlgebraicGeometry.RingedToposHom.forgetFSharp
      (representedZariskiSchemeHom B S hS φ)).hom.app Oop s)
  have hC := representedZariskiEpsilonCompRightIso_hom_app_apply B S hS φ Oop
    ((AlgebraicGeometry.RingedToposHom.forgetFSharp
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))).hom.app
      (op ((representedEpsilonFunctor B S hS V).obj Oop.unop))
      ((AlgebraicGeometry.RingedToposHom.forgetFSharp
        (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app Oop s))
  have hP := chartComparison_structureSharp B S hS (representedSpaceMap B S hS φ)
    (relativelyRepresentable_yoneda_map B S hS φ)
    ((representedEpsilonFunctor B S hS V).obj Oop.unop)
    ((AlgebraicGeometry.RingedToposHom.forgetFSharp
      (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app Oop s)
  have hG := ConcreteCategory.congr_hom
    (representedEpsilonGamma B S hS φ Oop.unop
      ((representedEpsilonSiteSquare B S hS φ).inv.app Oop.unop)) s
  exact (congrArg (fun z ↦
        ((Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app
            (structureSetSheaf B S hS (representedAlgebraicSpace B S hS U))).hom.app Oop z)
      hU).trans
    (hG.symm.trans ((congrArg (fun z ↦ (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_yoneda_map B S hS φ).snd
            ((representedEpsilonFunctor B S hS V).obj Oop.unop).1.hom)).op) z)
      hV).symm.trans (hP.symm.trans hC.symm)))

/-- **The structure maps of the two composites agree through the comparison of their direct
images.**  This is the second component of the 2-isomorphism, in the form that has no inverse in
it, obtained from `AlgebraicGeometry.Space.representedEpsilonSquare_key_app` section by
section. -/
theorem representedEpsilonSquare_key :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedZariskiEpsilonCompLeft B S hS φ) ≫
        (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedZariskiEpsilonCompRight B S hS φ) ≫
        (representedZariskiEpsilonCompRightIso B S hS φ).hom.app
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) := by
  rw [AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
      (representedZariskiSchemeHom B S hS φ) (representedToSchemeZariskiRingedToposHom B S hS U),
    AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
      (representedToSchemeZariskiRingedToposHom B S hS V)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))]
  exact CategoryTheory.Sheaf.hom_ext_sections
    (fun Oop s ↦ representedEpsilonSquare_key_app B S hS φ Oop s)

/-- **The square of Stacks 08GH on the underlying topoi.**  The direct images of the two
composite morphisms of ringed topoi `f₀ ∘ ε_X` and `ε_Y ∘ f_small` are canonically isomorphic,
by `AlgebraicGeometry.Space.representedEpsilonSiteSquare`.

This is the first of the two components of a 2-isomorphism of the two composites; the
compatibility with the structure maps is not proved, see the scope section of this file. -/
def representedEpsilonPushforwardIso :
    (representedZariskiEpsilonCompLeft B S hS φ).toToposHom.pushforward ≅
      (representedZariskiEpsilonCompRight B S hS φ).toToposHom.pushforward :=
  representedZariskiEpsilonCompLeftIso B S hS φ ≪≫
    Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J ≪≫
    (representedZariskiEpsilonCompRightIso B S hS φ).symm

/-- The direct-image comparison of the square is the square of sites followed by the right-hand
comparison backwards; the left-hand one is the identity. -/
theorem representedEpsilonPushforwardIso_hom_app :
    (representedEpsilonPushforwardIso B S hS φ).hom.app
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) =
      (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) ≫
        (representedZariskiEpsilonCompRightIso B S hS φ).inv.app
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) :=
  rfl

/-- **The structure maps of the two composites agree through
`AlgebraicGeometry.Space.representedEpsilonPushforwardIso`.**  This is the second component of
the 2-isomorphism of the two composites, in the form the structure
`AlgebraicGeometry.RingedToposHom.TwoIso` asks for. -/
theorem representedEpsilonSquare_commutes :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedZariskiEpsilonCompLeft B S hS φ) ≫
        (representedEpsilonPushforwardIso B S hS φ).hom.app
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
        (representedZariskiEpsilonCompRight B S hS φ) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (representedZariskiEpsilonCompRightIso B S hS φ).inv.app _)
    (representedEpsilonSquare_key B S hS φ)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (_ ≫ ·) ((representedZariskiEpsilonCompRightIso B S hS φ).hom_inv_id_app _)).trans
    (Category.comp_id _)

/-- **Stacks 08GH: the diagram of ringed sites of Remark 75.6.3 is commutative.**  For a morphism
`f` of representable algebraic spaces and a morphism `f₀` of schemes representing it, the two
composites of morphisms of ringed topoi

`f₀ ∘ ε_X, ε_Y ∘ f_small : (X_étale, 𝒪_X) ⟶ (Y_{0, Zar}, 𝒪_{Y₀})`

are 2-isomorphic: their direct images are isomorphic
(`AlgebraicGeometry.Space.representedEpsilonPushforwardIso`, from the square of sites
`AlgebraicGeometry.Space.representedEpsilonSiteSquare`) and the isomorphism carries the structure
map of one to the structure map of the other
(`AlgebraicGeometry.Space.representedEpsilonSquare_commutes`).

This is what Stacks calls the commutativity of a diagram of ringed topoi, and it is the clause of
Remark 75.6.3 whose details the source omits. -/
noncomputable def representedEpsilonSquareTwoIso :
    AlgebraicGeometry.RingedToposHom.TwoIso.{u, u + 1, u, u, u, u}
      (A := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      (B := ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos)
      (representedZariskiEpsilonCompLeft B S hS φ)
      (representedZariskiEpsilonCompRight B S hS φ) where
  e := representedEpsilonPushforwardIso B S hS φ
  commutes := representedEpsilonSquare_commutes B S hS φ

end AlgebraicGeometry.Space

end
