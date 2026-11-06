module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.EtaleChartFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Basic

/-!
# Flat base change of a pseudo-coherent morphism of algebraic spaces

A pseudo-coherent morphism of algebraic spaces over `S` stays pseudo-coherent after base change
along a flat morphism of algebraic spaces. This is the algebraic-spaces form of flat base change
for pseudo-coherence, Stacks 06BS; the schemes form is
`AlgebraicGeometry.pseudoCoherent_of_isPullback_of_flat`, Stacks 0680, which the source's proof
of 06BS points to as its only input.

Pseudo-coherence is *not* stable under arbitrary base change — the warning printed after Stacks
06BR — so the general base-change statement for an every-étale-chart property, Stacks 0AMM,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderBaseChange`, does not apply, and
flatness of the base of the base change is used in an essential way.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.PseudoCoherent.respectsRight_etale`: postcomposition with an étale morphism
  of schemes preserves pseudo-coherence.
* `AlgebraicGeometry.pseudoCoherent_isEtaleLocalOnSourceAndTarget`: pseudo-coherence of morphisms
  of schemes is étale local on the source and target in the sense of Stacks 04QZ, granted that it
  is local on the source for the étale topology.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isPullback_of_isFlat`: Stacks 06BS for an arbitrary
  cartesian square of algebraic spaces whose base map is flat.
* `AlgebraicGeometry.Space.isPseudoCoherent_pullback_snd`: Stacks 06BS in the `pullback` spelling,
  for the chosen fibre product of Stacks 02X2.
* `AlgebraicGeometry.Space.isPseudoCoherent_baseChange_of_isFlat`: **Stacks 06BS**, unconditional,
  for an arbitrary cartesian square of algebraic spaces whose base map is flat.
* `AlgebraicGeometry.Space.isPseudoCoherent_pullback_snd_of_isFlat`: the same, unconditional, in
  the `pullback` spelling.

## Implementation notes

The base-changed morphism in `AlgebraicGeometry.Space.isPseudoCoherent_pullback_snd` is the second
projection out of the fibre product of the underlying presheaves of points, which is again an
algebraic space by Stacks 02X2; the fibre product and its cartesian square are
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` and
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`. Both statements quantify over objects
of `AlgebraicGeometry.AlgebraicSpaces`, so no algebraicity hypothesis is carried: that the spaces
of the square are algebraic spaces over `S` is the source's own standing hypothesis, and for the
fibre product it is automatic.

Pseudo-coherence of a morphism of algebraic spaces is the every-étale-chart condition of Stacks
03MJ, condition (1), so the conclusion has to be verified on an *arbitrary* commuting square of
étale charts of the base-changed morphism. That square need not be comparable with a chart square
of the original morphism — an étale chart of the base-changed source composed with the projection
to the original source is étale only when the base of the base change is — so the proof produces
one chart square whose chart of the source is surjective and upgrades it to every square by the
equivalence of conditions (1) and (2) of Stacks 03MJ,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`.

That surjective square is built exactly as in the proof of Stacks 0AMM: choose a surjective étale
atlas `b : V ⟶ Z` of the common target and lift it through the given morphism to a surjective
étale atlas `a : U ⟶ Y` with a morphism `h : U ⟶ V` of the site over it (Stacks 02X1), choose an
atlas `d : D ⟶ X` of the base of the base change, pull `b` back along `d ≫ f` to `rV : rObj ⟶ V`,
and pull `h` back along `rV`. Stacks 0AMM concludes with base change of the scheme-morphism
property along `rV`; what replaces arbitrary base-change stability here is that `rV` is *flat*: the
square exhibiting `rV` as a base change of `b` is a square of étale charts of the flat morphism
`f`, with chart `rD ≫ d` of its source and chart `b` of its target, so flatness of `f` as a
morphism of algebraic spaces says precisely that the scheme morphism underlying `rV` is flat.
Stacks 0680 then applies, and its conclusion is transported from Mathlib's chosen pullback along
the comparison isomorphism, which is étale.

The only things proved here about pseudo-coherence of morphisms of *schemes* are the two
properties that argument asks of it. Base change along a flat morphism is Stacks 0680. For étale
locality on the source and target, postcomposition with an étale morphism preserves
pseudo-coherence because an étale morphism is flat and locally of finite presentation, hence
pseudo-coherent by Stacks 0695, and pseudo-coherent morphisms compose by Stacks 0681; base change
along an étale morphism is Stacks 0680 again, an étale morphism being flat; so étale locality on
the source alone already gives étale locality on the source and target in the sense of Stacks
04QZ, by the formal half of Stacks 04R2.

## Étale locality on the source

`AlgebraicGeometry.pseudoCoherent_isEtaleLocalOnSourceAndTarget`, and the two theorems that
reduce to it, take as a hypothesis

  `MorphismProperty.IsLocalAtSource (@AlgebraicGeometry.PseudoCoherent) Scheme.etalePrecoverage`,

that pseudo-coherence of morphisms of *schemes* is local on the source for the étale topology.
That is the case of Stacks 04R3 asserted in the introduction to the source's own section, and it
is `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage`: pseudo-coherence is local
on the source for the syntomic topology by Stacks 0698, and an étale morphism is syntomic, so
every étale covering family is a syntomic one.

Supplying that instance makes both forms unconditional, which is what Stacks 06BS asserts, and
the attribute sits on `AlgebraicGeometry.Space.isPseudoCoherent_baseChange_of_isFlat`, the
cartesian-square form: it is the statement for an arbitrary flat base change, and the `pullback`
spelling is the special case of it at the chosen fibre product.

## References

* [Stacks Project, Tag 06BS](https://stacks.math.columbia.edu/tag/06BS)
* [Stacks Project, Tag 0680](https://stacks.math.columbia.edu/tag/0680)
* [Stacks Project, Tag 0681](https://stacks.math.columbia.edu/tag/0681)
* [Stacks Project, Tag 0695](https://stacks.math.columbia.edu/tag/0695)
* [Stacks Project, Tag 0698](https://stacks.math.columbia.edu/tag/0698)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Étale locality of pseudo-coherence on the source and target -/

/-- Postcomposition with an étale morphism preserves pseudo-coherence: an étale morphism is flat
and locally of finite presentation, hence pseudo-coherent by Stacks 0695, and pseudo-coherent
morphisms of schemes compose by Stacks 0681. -/
theorem PseudoCoherent.respectsRight_etale :
    MorphismProperty.RespectsRight (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    let : Etale i := hi
    let : PseudoCoherent f := hf
    exact inferInstance

/-- Granted that pseudo-coherence of morphisms of schemes is local on the source for the étale
topology, it is étale local on the source and target in the sense of Stacks 04QZ.

Étale locality on the source gives preservation under precomposition with an étale morphism,
Stacks 0680 gives preservation under base change along an étale morphism, since an étale morphism
is flat, and the chart criterion is assembled from the two using preservation under
postcomposition with an étale morphism. -/
theorem pseudoCoherent_isEtaleLocalOnSourceAndTarget
    (hsrc : MorphismProperty.IsLocalAtSource
      (@PseudoCoherent.{u} : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage) :
    IsEtaleLocalOnSourceAndTarget (@PseudoCoherent.{u} : MorphismProperty Scheme.{u}) := by
  let := hsrc
  let := PseudoCoherent.respectsRight_etale.{u}
  refine
    { precomp := respectsLeft_etale_of_isLocalAtSource _
      pullbackSnd_of_etale := fun f hf g hg => ?_
      iff_forall_exists_etale_neighborhood := fun f => ?_ }
  · let : Etale g := hg
    let : PseudoCoherent f := hf
    exact pseudoCoherent_pullback_snd f g
  · classical
    refine ⟨fun hf x => ⟨_, _, 𝟙 _, 𝟙 _, f, x, inferInstance, inferInstance, by simp, by simp,
      hf⟩, fun hx => ?_⟩
    choose U V a b k u ha hb hu hcomm hP using hx
    refine MorphismProperty.IsLocalAtSource.of_forall_comp
      (ofArrows_mem_etalePrecoverage_iff.mpr ⟨fun x => ⟨x, u x, hu x⟩, ha⟩) ?_
    rintro W g ⟨x⟩
    rw [← hcomm x]
    exact MorphismProperty.RespectsRight.postcomp (Q := @Etale) (b x) (hb x) (k x) (hP x)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_pseudoCoherentFlatBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Flat base change of pseudo-coherence -/

/-- **Stacks Project, Tag 06BS.** A flat base change of a pseudo-coherent morphism of algebraic
spaces is pseudo-coherent: in a cartesian square with `g : Y ⟶ Z` pseudo-coherent and
`f : X ⟶ Z` flat, the base change `g' : Y' ⟶ X` of `g` along `f` is pseudo-coherent.

The hypothesis `hsrc`, that pseudo-coherence of morphisms of schemes is local on the source for
the étale topology, is the case of Stacks 04R3 that the introduction to Stacks 06BQ asserts. It is
a statement about morphisms of schemes alone, and it is available:
`AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage` proves it. This form is kept
because taking the locality as a hypothesis is sometimes convenient at a call site; the
unconditional statement, which carries the `@[stacks 06BS]` registration, is
`AlgebraicGeometry.Space.isPseudoCoherent_baseChange_of_isFlat` below, obtained from this one by
discharging `hsrc`. -/
theorem isPseudoCoherent_of_isPullback_of_isFlat
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hflat : IsFlat B S hS f.hom)
    (hf : IsPseudoCoherent B S hS g.hom) :
    IsPseudoCoherent B S hS g'.hom :=
  holdsOnEveryEtaleChart_of_isPullback_of_isFlat B S hS
    (@_root_.AlgebraicGeometry.PseudoCoherent.{u} : MorphismProperty Scheme.{u})
    (pseudoCoherent_isEtaleLocalOnSourceAndTarget hsrc)
    (fun a c hc ha => @_root_.AlgebraicGeometry.pseudoCoherent_pullback_snd _ _ _ a c hc ha)
    sq hflat hf

/-- **Stacks Project, Tag 06BS**, in the `pullback` spelling: if `f : X ⟶ Y` is a pseudo-coherent
morphism of algebraic spaces and `g : Y' ⟶ Y` is flat, then the projection `X ×_Y Y' ⟶ Y'` is
pseudo-coherent.

The hypothesis `hsrc` is as in `AlgebraicGeometry.Space.isPseudoCoherent_of_isPullback_of_isFlat`,
and is likewise dischargeable by
`AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage`. -/
theorem isPseudoCoherent_pullback_snd
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom)
    (hf : IsPseudoCoherent B S hS f.hom) :
    IsPseudoCoherent B S hS (Limits.pullback.snd f.hom g.hom) :=
  isPseudoCoherent_of_isPullback_of_isFlat B S hS hsrc
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hg hf

/-- **Stacks 06BS.** A flat base change of a pseudo-coherent morphism of algebraic spaces over `S`
is pseudo-coherent: in a cartesian square with `g : Y ⟶ Z` pseudo-coherent and `f : X ⟶ Z` flat,
the base change `g' : Y' ⟶ X` of `g` along `f` is pseudo-coherent. -/
@[stacks 06BS]
theorem isPseudoCoherent_baseChange_of_isFlat
    {X Y Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hflat : IsFlat B S hS f.hom)
    (hf : IsPseudoCoherent B S hS g.hom) :
    IsPseudoCoherent B S hS g'.hom :=
  isPseudoCoherent_of_isPullback_of_isFlat B S hS
    _root_.AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage.{u} sq hflat hf

/-- **Stacks 06BS** in the `pullback` spelling: if `f : X ⟶ Y` is a pseudo-coherent morphism of
algebraic spaces over `S` and `g : Y' ⟶ Y` is flat, then the projection `X ×_Y Y' ⟶ Y'` is
pseudo-coherent. -/
theorem isPseudoCoherent_pullback_snd_of_isFlat
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom) (hf : IsPseudoCoherent B S hS f.hom) :
    IsPseudoCoherent B S hS (Limits.pullback.snd f.hom g.hom) :=
  isPseudoCoherent_pullback_snd B S hS
    _root_.AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage.{u} f g hg hf

end Space

end AlgebraicGeometry

end
