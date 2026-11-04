module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence

/-!
# The chart square of a cartesian square of algebraic spaces

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a **cartesian** square of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, with `f` and `f'` representable, and let `d` be a commuting diagram of étale scheme charts
over `g`.  Base change of charts along `f` and `f'`, Stacks 03G2 part (4), turns `d` into a
square of étale scheme charts

```
d.U ×_{Y'} X' --q--> d.V ×_Y X
      |                  |
    d.U -----d.g-----> d.V
```

and this file proves that **that square of charts is cartesian as a square of schemes**, and
that when the three lower-left corners are affine the square of rings of regular functions it
induces is a pushout.

The square of charts is the chartwise content of the base-change clause of Stacks 02KG: over a
diagram of affine charts the sections of `f_*F` are the sections of `F` over `d.V ×_Y X`, those
of `f'_*(i^*F)` are the sections of `i^*F` over `d.U ×_{Y'} X'`, and the pushout of rings below
is what turns the first, base-changed to the chart of `Y'`, into the second.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeChartSquareMap`: the morphism `q` of charts, obtained from the
  universal property of the representable base change along `f`.
* `AlgebraicGeometry.Space.chartDiagramOfSquare`: the resulting diagram of étale scheme charts
  over `i`, whose charts are the two base-changed charts and whose vertical morphism is `q`.

## Main results

* `AlgebraicGeometry.Space.baseChangeChartSquareMap_snd`: the chart square commutes.
* `AlgebraicGeometry.Space.isPullback_baseChangeChartSquare`: it is cartesian in the big fppf
  site, and `AlgebraicGeometry.Space.isPullback_baseChangeChartSquare_scheme`: hence as a square
  of schemes.
* `AlgebraicGeometry.Space.isPushout_appTop_chartSquare`: **the induced square of rings of
  regular functions is a pushout** when the chart of `Y`, the chart of `Y'` and the base-changed
  chart of `X` are affine.
* `AlgebraicGeometry.Space.isPushout_appTop_chartSquare_of_isAffineHom`: the same, with the
  affineness of the base-changed chart of `X` supplied by affineness of `f`.

## Implementation notes

The morphism `q` is `CategoryTheory.Functor.relativelyRepresentable.lift` for `f` at the
composite `d.U ×_{Y'} X' ⟶ X' ⟶ X` over `d.U ⟶ d.V`, so its two characterizing identities are
`lift_fst` and `lift_snd`; the first *is* the commutativity of the chart diagram over `i` and
the second is the commutativity of the chart square.  Nothing is constructed by hand.

Cartesianness is the two-step idiom of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangePasting.lean`: paste the
representability square of `f'` at the chart of `Y'` with the given cartesian square, read in
presheaves by `AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_hom`, to get a cartesian
square over `Y`; cancel the representability square of `f` at the chart of `Y` out of it on the
right; descend through `yoneda`, which is fully faithful, and push forward to schemes.  The two
rewrites before the pasting are exactly `lift_fst` and the commutativity of `d`.

The pushout of rings is `AlgebraicGeometry.isPushout_appTop_of_isPullback`, whose three
affineness instances are supplied as hypotheses and installed with `have` so that instance
search finds them, as `AlgebraicGeometry.Space.isPushout_appTop_representablePullback` already
does for the square of two charts over one morphism.  Affineness of the fourth corner is not
needed: it is derived there from the other three.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)

/-- The compatibility which the universal property of the base change along `f` consumes: the
base-changed chart of `X'` maps to `X`, over the morphism `d.U ⟶ d.V` of charts of the base. -/
theorem baseChangeChartSquareMap_cond (comm : i ≫ f = f' ≫ g) :
    (hf'.fst d.U.1.hom ≫ i.hom) ≫ f.hom =
      yoneda.map (hf'.snd d.U.1.hom ≫ d.g) ≫ d.V.1.hom := by
  rw [Category.assoc, show i.hom ≫ f.hom = f'.hom ≫ g.hom from congrArg (fun k ↦ k.hom) comm,
    ← Category.assoc, hf'.w d.U.1.hom, Category.assoc, d.comm, yoneda.map_comp, Category.assoc]

/-- **The morphism of base-changed charts over `i`.**  Base change along `f'` of the chart `d.U`
of `Y'` maps to the base change along `f` of the chart `d.V` of `Y`, by the universal property
of the latter. -/
def baseChangeChartSquareMap (comm : i ≫ f = f' ≫ g) :
    (SmallEtale.toOver B S hS X'.1).obj ((smallBaseChange B S hS f' hf').obj d.U) ⟶
      (SmallEtale.toOver B S hS X.1).obj ((smallBaseChange B S hS f hf).obj d.V) :=
  hf.lift (hf'.fst d.U.1.hom ≫ i.hom) (hf'.snd d.U.1.hom ≫ d.g)
    (baseChangeChartSquareMap_cond B S hS i f' f g hf' d comm)

/-- The morphism of base-changed charts is a morphism of charts over `i`: that is the first
characterizing identity of the universal property it was built by. -/
theorem baseChangeChartSquareMap_fst (comm : i ≫ f = f' ≫ g) :
    yoneda.map (baseChangeChartSquareMap B S hS i f' f g hf hf' d comm) ≫ hf.fst d.V.1.hom =
      hf'.fst d.U.1.hom ≫ i.hom :=
  hf.lift_fst _ _ _

/-- **The chart square commutes**: the morphism of base-changed charts followed by the cartesian
projection to `d.V` is the cartesian projection to `d.U` followed by the vertical morphism of
`d`. -/
theorem baseChangeChartSquareMap_snd (comm : i ≫ f = f' ≫ g) :
    baseChangeChartSquareMap B S hS i f' f g hf hf' d comm ≫ hf.snd d.V.1.hom =
      hf'.snd d.U.1.hom ≫ d.g :=
  hf.lift_snd _ _ _

/-- **The diagram of étale scheme charts over `i` which the chart square is.**  Its chart of `X'`
is the base change of `d.U` along `f'`, its chart of `X` is the base change of `d.V` along `f`,
and its vertical morphism of schemes is `AlgebraicGeometry.Space.baseChangeChartSquareMap`. -/
def chartDiagramOfSquare (comm : i ≫ f = f' ≫ g) : ChartDiagram B S hS X'.1 X.1 i.hom where
  U := (smallBaseChange B S hS f' hf').obj d.U
  V := (smallBaseChange B S hS f hf).obj d.V
  g := baseChangeChartSquareMap B S hS i f' f g hf hf' d comm
  comm := (baseChangeChartSquareMap_fst B S hS i f' f g hf hf' d comm).symm

/-- **The chart square of a cartesian square of algebraic spaces is cartesian** in the big fppf
site of `S`.

The square of `X'` over `X` and `Y'` over `Y` being cartesian, the chart `d.U ×_{Y'} X'` is a
fibre product of `d.U` and `X` over `Y`, and so is `d.U ×_{d.V} (d.V ×_Y X)`; cancelling the
representability square of `f` at `d.V` out of the pasted square is exactly that comparison. -/
theorem isPullback_baseChangeChartSquare (sq : IsPullback i f' f g) :
    IsPullback (baseChangeChartSquareMap B S hS i f' f g hf hf' d sq.w) (hf'.snd d.U.1.hom)
      (hf.snd d.V.1.hom) d.g := by
  have hbig : IsPullback
      (yoneda.map (baseChangeChartSquareMap B S hS i f' f g hf hf' d sq.w) ≫ hf.fst d.V.1.hom)
      (yoneda.map (hf'.snd d.U.1.hom)) f.hom (yoneda.map d.g ≫ d.V.1.hom) := by
    rw [baseChangeChartSquareMap_fst B S hS i f' f g hf hf' d sq.w, ← d.comm]
    exact (hf'.isPullback d.U.1.hom).paste_horiz (AlgebraicSpaces.isPullback_hom B S hS sq)
  refine IsPullback.of_map_of_faithful yoneda (IsPullback.of_right hbig ?_
    (hf.isPullback d.V.1.hom))
  exact (yoneda.map_comp _ _).symm.trans
    ((congrArg yoneda.map (baseChangeChartSquareMap_snd B S hS i f' f g hf hf' d sq.w)).trans
      (yoneda.map_comp _ _))

/-- **The chart square of a cartesian square of algebraic spaces is a cartesian square of
schemes**: `AlgebraicGeometry.Space.isPullback_baseChangeChartSquare` pushed forward along the
functor to schemes, which preserves fibre products. -/
theorem isPullback_baseChangeChartSquare_scheme (sq : IsPullback i f' f g) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartSquareMap B S hS i f' f g hf hf' d sq.w))
      ((BigFppfOver.toScheme B S hS).map (hf'.snd d.U.1.hom))
      ((BigFppfOver.toScheme B S hS).map (hf.snd d.V.1.hom))
      ((BigFppfOver.toScheme B S hS).map d.g) :=
  (isPullback_baseChangeChartSquare B S hS i f' f g hf hf' d sq).map (BigFppfOver.toScheme B S hS)

/-- **The square of rings of regular functions of the chart square is a pushout.**  For a
cartesian square of algebraic spaces with `f` and `f'` representable and a diagram `d` of étale
scheme charts over `g` whose two charts are affine, and whose base change along `f` is affine,
the regular functions on `d.U ×_{Y'} X'` are the tensor product of those on `d.V ×_Y X` and
those on `d.U` over those on `d.V`.

This is the ring-level content of the base-change clause of Stacks 02KG at a diagram of affine
charts.  Affineness of `d.U ×_{Y'} X'` is not assumed: for a cartesian square of schemes with
three affine corners the fourth is affine. -/
theorem isPushout_appTop_chartSquare (sq : IsPullback i f' f g)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS f hf).obj d.V))) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (hf.snd d.V.1.hom)).appTop
      ((BigFppfOver.toScheme B S hS).map d.g).appTop
      ((BigFppfOver.toScheme B S hS).map
        (baseChangeChartSquareMap B S hS i f' f g hf hf' d sq.w)).appTop
      ((BigFppfOver.toScheme B S hS).map (hf'.snd d.U.1.hom)).appTop := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) := hU
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) := hV
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y'.1).obj d.U)) := hU
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj d.V)) := hV
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback d.V.1.hom)) := hW
  exact isPushout_appTop_of_isPullback
    (isPullback_baseChangeChartSquare_scheme B S hS i f' f g hf hf' d sq)

/-- `AlgebraicGeometry.Space.isPushout_appTop_chartSquare` with affineness of the base-changed
chart of `X` supplied by affineness of `f`: the base change of an affine chart along an affine
morphism is affine, Stacks 03WF. -/
theorem isPushout_appTop_chartSquare_of_isAffineHom (sq : IsPullback i f' f g)
    (haff : IsAffineHom B S hS f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (hf.snd d.V.1.hom)).appTop
      ((BigFppfOver.toScheme B S hS).map d.g).appTop
      ((BigFppfOver.toScheme B S hS).map
        (baseChangeChartSquareMap B S hS i f' f g hf hf' d sq.w)).appTop
      ((BigFppfOver.toScheme B S hS).map (hf'.snd d.U.1.hom)).appTop :=
  isPushout_appTop_chartSquare B S hS i f' f g hf hf' d sq hU hV
    (isAffine_smallBaseChange_obj B S hS f hf haff d.V hV)

end AlgebraicGeometry.Space

end
