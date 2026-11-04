module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Base change of an every-étale-chart property of morphisms of algebraic spaces

A property of morphisms of algebraic spaces over `S` of the form
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` — condition (1) of Stacks 03MJ, the shape
taken by local finite type, local quasi-finiteness, flatness and smoothness — is stable under
base change. This file proves that in two strengths, which are useful in different places.

The cheap half asks nothing of the property but restricts the *base* of the base change: if
the morphism one base-changes along is étale after every representable base change, then an
étale chart of the base-changed source composes with the base-changed morphism to an étale
chart of the original source, and an étale chart of the new target composes to an étale chart
of the old one, so a chart square for the base change is literally a chart square for the
original morphism. Nothing of Stacks 03MJ is needed. That covers every use made of base change
in a Zariski- or étale-localisation argument, where the base of the base change is an open
immersion or an étale chart.

The full half is Stacks 0AMM: for a property of morphisms of schemes which is étale local on
the source and target (Stacks 04QZ) and stable under base change, the induced property of
morphisms of algebraic spaces is stable under base change along an *arbitrary* morphism. This
is the route the general tags take — Stacks 03XH for local finite type, 03XL for local
quasi-finiteness, 03MO for flatness and 03ZE for smoothness — and it goes through the
equivalence of conditions (1) and (2) of Stacks 03MJ.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isPullback` is the relatively-étale base
  change statement for an arbitrary property of scheme morphisms, and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_pullback_fst` is its form for the canonical
  pullback.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isPullback`,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isPullback` and
  `AlgebraicGeometry.Space.isFlat_of_isPullback` are the three instances of it which the
  localisation arguments use.
* `AlgebraicGeometry.Space.presheaf_etale_of_isOpenImmersion` supplies the hypothesis for
  an open immersion, which is the case a Zariski localisation produces.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderBaseChange`: **Stacks 0AMM**,
  base change along an arbitrary morphism for an étale-local, base-change stable property.
* `AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange_of_isEtaleLocal`: the
  specialisation to smoothness, Stacks 03ZE *conditional on* étale locality of smoothness of
  morphisms of schemes.
* `AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange_of_isLocalAtSource`: the same,
  conditional only on smoothness of morphisms of schemes being local on the source for the
  étale topology.

## Implementation notes

In the relatively-étale half the hypothesis on the base of the base change is the relative
property `CategoryTheory.MorphismProperty.presheaf` of étaleness rather than
`AlgebraicGeometry.Space.IsEtale`, for two reasons. It is the weaker of the two to assume
in the presence of a representable source — `AlgebraicGeometry.Space.IsEtale` is recovered
from it by `AlgebraicGeometry.Space.isEtale_of_presheaf_etale` and conversely by
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale` — and it is the form that is stable
under base change and composition, which is exactly what the argument consumes. The two
closure properties come from `CategoryTheory.MorphismProperty.relative`:
`AlgebraicGeometry.Space.presheaf_of_isPullback` for base change and
`AlgebraicGeometry.Space.isMultiplicative_presheaf_etale` for composition, the latter
assembled by hand where it is proved because synthesis does not find it. No algebraicity
hypothesis appears in that half: the statement is about chart squares of presheaves and the
argument never forms an atlas.

Stacks 0AMM is stated as a `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` on the
category of algebraic spaces over `S`, so it applies to an arbitrary cartesian square rather
than to a chosen fibre product; the chosen fibre product of Stacks 02X2 is used inside the
proof only to name one, and the given square is compared to it by
`CategoryTheory.IsPullback.isoIsPullback`. Its proof is the one Stacks 0AMM points to. Given a
cartesian square with `g' : Y' ⟶ X` the base change of `g : Y ⟶ Z` along `f : X ⟶ Z`, choose a
surjective étale scheme atlas `b` of `Z` and lift it through `g` to a surjective étale atlas
`a` of `Y` (Stacks 02X1); the square over `h : U ⟶ V` that this produces carries `P`, by the
hypothesis on `g`. Choose also an atlas `d` of `X`. Pulling `b` back along `d ≫ f` and then `h`
back along that gives a single commuting square of étale charts of `g'` whose chart of the
source is surjective — the chart being assembled by the universal property of the two fibre
products involved — and whose underlying morphism of schemes is a base change of `h`, hence
has `P`. Stacks 03MJ then upgrades that one surjective square to every square.

`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange_of_isEtaleLocal` is **not** tagged
`03ZE`, because it carries a hypothesis that Stacks 03ZE does not: that smoothness of morphisms
of schemes is étale local on the source and target, which is Stacks 04R3 for smoothness and is
not available. Supplying that one term turns this into 03ZE with no further work; it is the
only input the Stacks 03MJ to 0AMM to 03ZE chain still lacks.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions are relatively étale -/

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is an
open immersion is étale: an open immersion of schemes is étale. -/
theorem inverseImage_isOpenImmersion_le_inverseImage_etale :
    MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
  intro U V i hi
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) := hi
  exact inferInstanceAs (AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map i))

/-- An open immersion of algebraic spaces over `S` in the sense of Stacks 02YU is étale
after every representable base change. -/
theorem presheaf_etale_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsOpenImmersion B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone
    (inverseImage_isOpenImmersion_le_inverseImage_etale B S hS) _ hf

/-- An open immersion of algebraic spaces over `S`, in the sense of Stacks 02YU part (1), is
étale: an open immersion of schemes is étale, so every representable base change of an open
immersion of presheaves is étale, which is the étale-chart definition of étaleness. -/
theorem isEtale_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsOpenImmersion B S hS f) : IsEtale B S hS f :=
  isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hf)

/-! ### Base change of condition (1) of Stacks 03MJ along a relatively étale morphism -/

/-- A property of scheme morphisms which holds on every étale chart of `f : X ⟶ Y` holds on
every étale chart of the base change of `f` along a morphism `g : Z ⟶ Y` which is étale
after every representable base change.

The square is the one with `p` over `f` and `q` over `g`, so `p : W ⟶ Z` is the base change
of `f` and `q : W ⟶ X` is the base change of `g`. -/
theorem holdsOnEveryEtaleChart_of_isPullback {P : MorphismProperty Scheme.{u}}
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P p := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hq := presheaf_of_isPullback B S hS sq hg
  intro U V a b h ha hb hcomm
  refine hf U V (a ≫ q) (b ≫ g) h
    (MorphismProperty.comp_mem _ a q ha hq)
    (MorphismProperty.comp_mem _ b g hb hg) ?_
  rw [← Category.assoc, hcomm, Category.assoc, sq.w, Category.assoc]

/-- A property of scheme morphisms which holds on every étale chart of `f : X ⟶ Y` holds on
every étale chart of the first projection of `Z ×[Y] X`, when `g : Z ⟶ Y` is étale after
every representable base change. -/
theorem holdsOnEveryEtaleChart_pullback_fst {P : MorphismProperty Scheme.{u}}
    {X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (pullback.fst g f) :=
  holdsOnEveryEtaleChart_of_isPullback B S hS (IsPullback.of_hasPullback g f) hg hf

/-! ### The three properties of this shape -/

/-- **Stacks 03XH for a relatively étale base change.** The base change of a morphism of
algebraic spaces over `S` which is locally of finite type along a morphism which is étale
after every representable base change is locally of finite type.

This is weaker than the tag, which allows an arbitrary morphism of algebraic spaces as the
base of the base change. -/
theorem isLocallyOfFiniteType_of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS p :=
  holdsOnEveryEtaleChart_of_isPullback B S hS sq hg hf

/-- **Stacks 03XL for a relatively étale base change.** The base change of a locally
quasi-finite morphism of algebraic spaces over `S` along a morphism which is étale after
every representable base change is locally quasi-finite.

This is weaker than the tag, which allows an arbitrary morphism of algebraic spaces as the
base of the base change. -/
theorem isLocallyQuasiFinite_of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : IsLocallyQuasiFinite B S hS f) :
    IsLocallyQuasiFinite B S hS p :=
  holdsOnEveryEtaleChart_of_isPullback B S hS sq hg hf

/-- **Stacks 03MO for a relatively étale base change.** The base change of a flat morphism
of algebraic spaces over `S` along a morphism which is étale after every representable base
change is flat.

This is weaker than the tag, which allows an arbitrary morphism of algebraic spaces as the
base of the base change. -/
theorem isFlat_of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : IsFlat B S hS f) :
    IsFlat B S hS p :=
  holdsOnEveryEtaleChart_of_isPullback B S hS sq hg hf

/-! ### Base change along an arbitrary morphism, for an étale-local property -/

/-- A property of morphisms of schemes which is étale local on the source and
target and stable under base change induces a base-change stable property of morphisms of
algebraic spaces over `S`, namely the condition that it hold on every commuting square of etale
charts. -/
@[stacks 0AMM]
theorem holdsOnEveryEtaleChart_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom) := by
  refine ⟨?_⟩
  intro X Y Y' Z f g f' g' sq hf
  let T := BigFppfOver.toScheme B S hS
  let QEtale : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  let QSurjective : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  let E := QEtale.presheaf
  let R := QSurjective.presheaf
  have : QEtale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have : QSurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QEtale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : QSurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : E.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange QEtale
  have : R.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange QSurjective
  have : E.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition QEtale
  have : R.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QSurjective
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Z.property.exists_atlas
  obtain ⟨U, a, h, hab, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y.property Z.property g.hom V b
      hbSurj hbEtale
  have hPchart : P (T.map h) := hf U V a b h haEtale hbEtale hab.symm
  obtain ⟨D, d, hdSurj, hdEtale⟩ := X.property.exists_atlas
  let rObj := hbEtale.rep.pullback (d ≫ f.hom)
  let rV : rObj ⟶ V := hbEtale.rep.fst' (d ≫ f.hom)
  let rD : rObj ⟶ D := hbEtale.rep.snd (d ≫ f.hom)
  have hrD_etale : AlgebraicGeometry.Etale (T.map rD) :=
    hbEtale.property (d ≫ f.hom) (yoneda.map rV) rD
      (hbEtale.rep.isPullback' (d ≫ f.hom))
  let H := Limits.pullback h rV
  let hU : H ⟶ U := Limits.pullback.fst h rV
  let hR : H ⟶ rObj := Limits.pullback.snd h rV
  have hpbH : IsPullback (yoneda.map hU) (yoneda.map hR) (yoneda.map h) (yoneda.map rV) :=
    (IsPullback.of_hasPullback h rV).map yoneda
  have hpbR : IsPullback (yoneda.map rV) (yoneda.map rD) b (d ≫ f.hom) :=
    hbEtale.rep.isPullback' (d ≫ f.hom)
  have hpbOuter : IsPullback (yoneda.map hU)
      (yoneda.map (hR ≫ rD)) (a ≫ g.hom) (d ≫ f.hom) := by
    simpa only [Functor.map_comp, ← hab] using hpbH.paste_vert hpbR
  let Yc := AlgebraicSpaces.fiberProduct B S hS f g
  let fC : Yc ⟶ Y := ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)
  let gC : Yc ⟶ X := ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)
  have hsq : IsPullback fC.hom gC.hom g.hom f.hom :=
    (IsPullback.of_hasPullback f.hom g.hom).flip
  have hpbC : IsPullback fC gC g f := (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).flip
  let e : Y' ≅ Yc := sq.isoIsPullback _ _ hpbC
  have he : e.hom ≫ gC = g' := sq.isoIsPullback_hom_snd _ _ hpbC
  let J := Limits.pullback gC.hom d
  let jYc := Limits.pullback.fst gC.hom d
  let jD := Limits.pullback.snd gC.hom d
  have hpbJ : IsPullback jYc jD gC.hom d := IsPullback.of_hasPullback gC.hom d
  have hpbJY : IsPullback (jYc ≫ fC.hom) jD g.hom (d ≫ f.hom) := hpbJ.paste_horiz hsq
  let j : yoneda.obj H ⟶ J := hpbJY.lift (yoneda.map hU ≫ a)
    (yoneda.map (hR ≫ rD)) (by simpa only [Category.assoc] using hpbOuter.w)
  have hpbHJ : IsPullback (yoneda.map hU) j a (jYc ≫ fC.hom) := by
    simpa [j] using hpbOuter.of_bot' hpbJY
  have hbEtale' : E (yoneda.map rD ≫ d) :=
    MorphismProperty.comp_mem E _ _ (MorphismProperty.relative_map (F := yoneda) hrD_etale) hdEtale
  have hPbase : P (T.map hR) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback h rV).map T) hPchart
  let c : yoneda.obj H ⟶ Y'.obj := (j ≫ jYc) ≫ e.inv.hom
  have hchart : ∀ Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      Q.IsStableUnderBaseChange → Q.IsStableUnderComposition → Q a → Q d → Q c :=
    fun Q _ _ ha hd => MorphismProperty.RespectsIso.postcomp Q e.inv.hom (j ≫ jYc)
      (MorphismProperty.comp_mem Q j jYc
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbHJ ha)
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbJ.flip hd))
  have hc' : E c := hchart E inferInstance inferInstance haEtale hdEtale
  have hs' : R c := hchart R inferInstance inferInstance haSurj hdSurj
  have heInvHom : e.inv.hom ≫ g'.hom = gC.hom := by
    rw [← he]
    simp
  have hcomm : c ≫ g'.hom = yoneda.map hR ≫ (yoneda.map rD ≫ d) := by
    rw [Category.assoc, heInvHom, Category.assoc, hpbJ.w,
      reassoc_of% (hpbJY.lift_snd _ _ _ : j ≫ jD = _)]
    simp only [Functor.map_comp, Category.assoc]
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP Y'.property X.property
    g'.hom).mpr ⟨H, rObj, c, yoneda.map rD ≫ d, hR, hc', hbEtale', hs', hcomm.symm, hPbase⟩

/-- The specialisation of Stacks 0AMM to smoothness: granted that smoothness of morphisms of
schemes is étale local on the source and target, smoothness of morphisms of algebraic spaces
over `S` is stable under base change.

This is Stacks 03ZE together with its one missing input. The hypothesis is Stacks 04R3 for
smoothness; smoothness of morphisms of schemes is already stable under base change in Mathlib,
so that is all that is needed. -/
theorem isSmooth_isStableUnderBaseChange_of_isEtaleLocal
    (hP : IsEtaleLocalOnSourceAndTarget (@AlgebraicGeometry.Smooth.{u})) :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSmooth B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) hP

/-- Stacks 03ZE reduced to a single statement about morphisms of *schemes*: if smoothness of
morphisms of schemes is local on the source for the étale topology, then smoothness of
morphisms of algebraic spaces over `S` is stable under base change.

Everything between the two is supplied here: Stacks 04R3 for smoothness follows from the
hypothesis by `AlgebraicGeometry.smooth_isEtaleLocalOnSourceAndTarget`,
bypassing Stacks 04R2, and Stacks 03MJ and 0AMM carry it to algebraic spaces. The hypothesis
is Stacks 036U restricted to étale coverings; it is the only input the chain lacks. -/
theorem isSmooth_isStableUnderBaseChange_of_isLocalAtSource
    (hsrc : MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth.{u}) Scheme.etalePrecoverage) :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSmooth B S hS f.hom) :=
  isSmooth_isStableUnderBaseChange_of_isEtaleLocal B S hS
    (let := hsrc; smooth_isEtaleLocalOnSourceAndTarget)

end AlgebraicGeometry.Space

end
