module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.EtaleChartFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect

/-!
# Flat base change of a perfect morphism of algebraic spaces

A perfect morphism of algebraic spaces over `S` stays perfect after base change along a flat
morphism of algebraic spaces. This is the algebraic-spaces form of flat base change for
perfection, Stacks 06C0; the schemes form is
`AlgebraicGeometry.perfect_of_isPullback_of_flat`, Stacks 0688, which the source's proof of
06C0 points to as its only input.

Perfection is *not* stable under arbitrary base change — the warning printed after Stacks
06BZ — so the general base-change statement for an every-étale-chart property, Stacks 0AMM,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderBaseChange`, does not apply, and
flatness of the base of the base change is used in an essential way.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.perfect_isEtaleLocalOnSourceAndTarget`: perfection of morphisms of schemes
  is étale local on the source and target in the sense of Stacks 04QZ, granted that it is local
  on the source for the étale topology.
* `AlgebraicGeometry.Space.isPerfect_of_isPullback_of_isFlat`: Stacks 06C0 for an arbitrary
  cartesian square of algebraic spaces whose base map is flat.
* `AlgebraicGeometry.Space.isPerfect_pullback_snd`: Stacks 06C0 in the `pullback` spelling, for
  the chosen fibre product of Stacks 02X2.

## Implementation notes

Perfection of a morphism of algebraic spaces is the every-étale-chart condition of Stacks 03MJ,
condition (1), so the conclusion has to be verified on an *arbitrary* commuting square of étale
charts of the base-changed morphism. That square need not be comparable with a chart square of
the original morphism: an étale chart of the base-changed source composed with the projection to
the original source is étale only when the base of the base change is, and the composite of a
chart of the common target with the flat base map is flat rather than étale. So the proof
produces one chart square whose chart of the source is surjective and upgrades it to every
square by the equivalence of conditions (1) and (2) of Stacks 03MJ,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`.

That surjective square is built exactly as in the proof of Stacks 0AMM: choose a surjective
étale atlas `b : V ⟶ Z` of the common target and lift it through the given morphism to a
surjective étale atlas `a : U ⟶ Y` with a morphism `h : U ⟶ V` of the site over it (Stacks
02X1), choose an atlas `d : D ⟶ X` of the base of the base change, pull `b` back along `d ≫ f`
to `rV : rObj ⟶ V`, and pull `h` back along `rV`. Stacks 0AMM concludes with base change of the
scheme-morphism property along `rV`; what replaces arbitrary base-change stability here is that
`rV` is *flat*: the square exhibiting `rV` as a base change of `b` is a square of étale charts
of the flat morphism `f`, with chart `rD ≫ d` of its source and chart `b` of its target, so
flatness of `f` as a morphism of algebraic spaces says precisely that the scheme morphism
underlying `rV` is flat. Stacks 0688 then applies, and its conclusion is transported from
Mathlib's chosen pullback along the comparison isomorphism, which is étale.

The two properties of perfection of morphisms of *schemes* that the étale-locality structure of
Stacks 04QZ asks for beyond locality on the source are both available: base change along an
étale morphism is Stacks 0688, an étale morphism being flat, and precomposition with an étale
morphism is `AlgebraicGeometry.Perfect.respectsLeft_etale`, an étale morphism being flat and
locally of finite presentation, hence perfect, and perfect morphisms composing by Stacks 0689.

## Carried hypothesis

All three results below carry one hypothesis beyond the source, namely

  `MorphismProperty.IsLocalAtSource (@AlgebraicGeometry.Perfect) Scheme.etalePrecoverage`,

that perfection of morphisms of *schemes* is local on the source for the étale topology. It is a
statement about morphisms of schemes alone, and it is the single input the chain Stacks
04R3 → 04R2 → 03MJ → 06C0 still lacks; supplying that one term turns the two theorems below
into Stacks 06C0 with no further work.

## No `@[stacks 06C0]`

Stacks 06C0 asserts flat base change of a perfect morphism of algebraic spaces outright, so no
attribute is attached to any declaration here: tagging a statement that carries the hypothesis
above would record that hypothesis as part of the tag's content. The tag belongs on whatever
discharges it. The declarations that would discharge it do not exist:

* an instance `MorphismProperty.IsLocalAtSource (@AlgebraicGeometry.Perfect)
  Scheme.etalePrecoverage`. The corresponding instances for the companion properties are
  `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage`, which rests on Stacks
  0698, `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_syntomicPrecoverage`, and
  `AlgebraicGeometry.Flat.isLocalAtSource_etalePrecoverage`; perfection has neither.
* the two Zariski localities `IsZariskiLocalAtSource (@AlgebraicGeometry.Perfect)` and
  `IsZariskiLocalAtTarget (@AlgebraicGeometry.Perfect)`, without which the reduction of étale
  locality to a statement about affine schemes,
  `AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, cannot be applied. They are the
  reason perfection is not an `AlgebraicGeometry.HasRingHomProperty`: its finite-Tor-dimension
  half carries a derived tensor product as data, and the property of ring maps expressing that
  half, together with its `RingHom.PropertyIsLocal` certificate, is private to
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal`.
* the affine descent itself: that a perfect composite `g ≫ f` with `g` a surjective syntomic
  morphism of affine schemes forces `f` perfect. The pseudo-coherent case is
  `AlgebraicGeometry.pseudoCoherent_of_comp_surjective_syntomic_of_isAffine`; the
  finite-Tor-dimension case has no counterpart.

The same shape is taken by `AlgebraicGeometry.Space.isPseudoCoherent_of_isPullback_of_isFlat`
for Stacks 06BS and by `AlgebraicGeometry.Space.isPerfect_comp` for Stacks 06C1. The hypothesis
of the latter is the full étale-locality structure of Stacks 04QZ, which
`AlgebraicGeometry.perfect_isEtaleLocalOnSourceAndTarget` below reduces to locality on the
source alone.

## References

* [Stacks Project, Tag 06C0](https://stacks.math.columbia.edu/tag/06C0)
* [Stacks Project, Tag 0688](https://stacks.math.columbia.edu/tag/0688)
* [Stacks Project, Tag 0689](https://stacks.math.columbia.edu/tag/0689)
* [Stacks Project, Tag 06BZ](https://stacks.math.columbia.edu/tag/06BZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0698](https://stacks.math.columbia.edu/tag/0698)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Étale locality of perfection on the source and target -/

/-- Granted that perfection of morphisms of schemes is local on the source for the étale
topology, it is étale local on the source and target in the sense of Stacks 04QZ.

Étale locality on the source gives the chart criterion, Stacks 0688 gives preservation under
base change along an étale morphism, since an étale morphism is flat, and precomposition with
an étale morphism is `AlgebraicGeometry.Perfect.respectsLeft_etale`. -/
theorem perfect_isEtaleLocalOnSourceAndTarget
    (hsrc : MorphismProperty.IsLocalAtSource
      (@Perfect.{u} : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage) :
    IsEtaleLocalOnSourceAndTarget (@Perfect.{u} : MorphismProperty Scheme.{u}) := by
  let := hsrc
  let := Perfect.respectsRight_etale.{u}
  refine
    { precomp := Perfect.respectsLeft_etale.{u}
      pullbackSnd_of_etale := fun f hf g hg => ?_
      iff_forall_exists_etale_neighborhood := fun f => ?_ }
  · let : Etale g := hg
    let : Perfect f := hf
    exact perfect_pullback_snd f g
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

/-! ### Flat base change of an every-étale-chart property -/

/-! ### Flat base change of perfection -/

/-- A flat base change of a perfect morphism of algebraic spaces is perfect: in a cartesian
square with `g : Y ⟶ Z` perfect and `f : X ⟶ Z` flat, the base change `g' : Y' ⟶ X` of `g`
along `f` is perfect.

The hypothesis `hsrc`, that perfection of morphisms of schemes is local on the source for the
étale topology, is the case of Stacks 04R3 for perfection. It is a statement about morphisms of
schemes alone, and it is the only input of the proof that is unavailable; the attribute
`@[stacks 06C0]` is therefore deliberately withheld, since Stacks 06C0 is unconditional. -/
theorem isPerfect_of_isPullback_of_isFlat
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.Perfect.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hflat : IsFlat B S hS f.hom)
    (hf : IsPerfect B S hS g.hom) :
    IsPerfect B S hS g'.hom :=
  holdsOnEveryEtaleChart_of_isPullback_of_isFlat B S hS
    (@_root_.AlgebraicGeometry.Perfect.{u} : MorphismProperty Scheme.{u})
    (perfect_isEtaleLocalOnSourceAndTarget hsrc)
    (fun a c hc ha => by
      let : Flat c := hc
      let : _root_.AlgebraicGeometry.Perfect a := ha
      exact _root_.AlgebraicGeometry.perfect_pullback_snd a c)
    sq hflat hf

/-- Flat base change of a perfect morphism of algebraic spaces in the `pullback` spelling: if
`f : X ⟶ Y` is a perfect morphism of algebraic spaces and `g : Y' ⟶ Y` is flat, then the
projection `X ×_Y Y' ⟶ Y'` is perfect.

The hypothesis `hsrc` and the withheld attribute are as in
`AlgebraicGeometry.Space.isPerfect_of_isPullback_of_isFlat`. -/
theorem isPerfect_pullback_snd
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.Perfect.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom)
    (hf : IsPerfect B S hS f.hom) :
    IsPerfect B S hS (Limits.pullback.snd f.hom g.hom) :=
  isPerfect_of_isPullback_of_isFlat B S hS hsrc
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hg hf

end Space

end AlgebraicGeometry

end
