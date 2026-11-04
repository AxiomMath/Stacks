module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Étale morphisms of algebraic spaces and unramifiedness

An étale morphism of algebraic spaces over a scheme `S` is unramified, and conversely a
morphism which is flat, unramified and locally of finite presentation is étale. Together
these say that étaleness of a morphism of algebraic spaces is flatness plus unramifiedness
plus local finite presentation, exactly as for morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.isUnramified_of_isEtale`: **Stacks 06CR**, an étale morphism of
  algebraic spaces is unramified.
* `AlgebraicGeometry.Space.isEtale_of_isFlat_of_isUnramified`: **Stacks 06LU**, a locally
  finitely presented, flat, unramified morphism of algebraic spaces is étale.

## Implementation notes

Both directions reduce to the corresponding statement about morphisms of *schemes* and need
no étale descent, because étaleness of a morphism of algebraic spaces has two equivalent
chart descriptions which point in opposite directions. Stacks 06CR reads the chart condition
directly, through `AlgebraicGeometry.Space.etale_of_comp_etale_chart`: in a commuting square of
étale charts of an étale morphism the morphism of schemes on top is étale, hence unramified
by [Stacks Project, Tag 02HE], an étale morphism of schemes being formally unramified and
locally of finite type. Stacks 06LU goes the other way, through condition (4) of
[Stacks Project, Tag 03FS]: it is enough to exhibit *one* commuting square of étale charts
with surjective source chart whose morphism of schemes is étale, and lifting an atlas of the
target by [Stacks Project, Tag 02X1] produces such a square, on whose top morphism the three
hypotheses give flatness, formal unramifiedness (again by Tag 02HE) and local finite
presentation — which is `AlgebraicGeometry.Etale.of_formallyUnramified_of_flat`.

In particular Stacks 06LU does not need the étale case of [Stacks Project, Tag 04R3]: the
single-square criterion of Tag 03FS replaces the passage from the every-chart to the
one-surjective-chart condition of [Stacks Project, Tag 03MJ].

Stacks 06CR asks nothing of either source or target: the chart condition it reads is about the
morphism alone. Stacks 06LU does need both to be algebraic spaces, since Tag 03FS takes atlases
of the source and of the target.

The two remaining consequences of étaleness in this part of the chapter are stated beside
the other such implications rather than here: an étale morphism of algebraic spaces is
locally of finite type ([Stacks Project, Tag 06LT]) and locally quasi-finite
([Stacks Project, Tag 03XU]) are
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiFinite.lean`, and flatness
([Stacks Project, Tag 0467]) and local finite presentation
([Stacks Project, Tag 0468]) are in
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothAtlas.lean`.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06CR.** An étale morphism of algebraic spaces over `S` is unramified.

In a commuting square of étale charts of `f` the morphism of schemes on top is étale, hence
formally unramified and locally of finite type, hence unramified by
[Stacks Project, Tag 02HE]. Nothing is asked of the target. -/
@[stacks 06CR]
theorem isUnramified_of_isEtale {f : X ⟶ Y} (hf : IsEtale B S hS f) :
    IsUnramified B S hS f := by
  intro U V a b h ha hb hcomm
  have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb hcomm
  exact (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mpr
    ⟨inferInstance, inferInstance⟩

/-- **Stacks 06LU.** A morphism of algebraic spaces over `S` which is locally of finite
presentation, flat and unramified is étale.

Lift an atlas `q` of the target through `f` by [Stacks Project, Tag 02X1] to a surjective
étale chart `p` of the source over a morphism `α` of the site. The three hypotheses, read on
that one square, say that the scheme morphism underlying `α` is locally of finite
presentation, flat and unramified, hence formally unramified by [Stacks Project, Tag 02HE]
and therefore étale. One such square suffices by condition (4) of
[Stacks Project, Tag 03FS]. -/
@[stacks 06LU]
theorem isEtale_of_isFlat_of_isUnramified (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (hunr : IsUnramified B S hS f) :
    IsEtale B S hS f := by
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  have hsq : yoneda.map α ≫ q = p ≫ f := hcomm.symm
  have : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map α) := hlfp U V p q α hpEtale hqEtale hsq
  have : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map α) :=
    hflat U V p q α hpEtale hqEtale hsq
  have : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map α) :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mp
      (hunr U V p q α hpEtale hqEtale hsq)).2
  exact (isEtale_iff_exists_etale_chart_square B S hS hX hY f).mpr
    ⟨U, V, p, q, α, hcomm, hpSurj, hpEtale, hqEtale,
      _root_.AlgebraicGeometry.Etale.of_formallyUnramified_of_flat _⟩

end AlgebraicGeometry.Space

end
