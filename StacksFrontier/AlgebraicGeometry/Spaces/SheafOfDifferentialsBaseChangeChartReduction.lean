module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsFibreProduct

/-!
# Stacks 05ZC reduced to a cartesian square of schemes of the site

Stacks 05ZC asserts that for a cartesian square of algebraic spaces

```
X' --g'--> X
|          |
p'         p
v          v
Y' --g-->  Y
```

the comparison map `c_{g'} : (g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX is an isomorphism, with no
hypothesis on `g`.  The source proves it from the case of schemes — Morphisms, Lemma 01V0 — by
étale localization, Stacks 04CU.

This file carries out the localization step in full, with nothing carried.
`AlgebraicGeometry.Space.exists_baseChangeChartTower` produces a tower of étale charts whose two
chart squares of schemes are cartesian and whose chart of `X'` is surjective, and
`AlgebraicGeometry.Space.isIso_of_isIso_chartComparison` turns the question for `c_{g'}` into the
same question for the comparison map of that chart square.  What is left is therefore exactly one
statement, and it mentions no algebraic space:

> for a cartesian square of schemes of the big fppf site over `S`, the comparison map of
> Stacks 04CX of the square they form when read as *represented* algebraic spaces is an
> isomorphism.

That statement is `AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso` below.  It is the
invertibility clause of Stacks 04CS applied to the two columns of the square together with
Morphisms, Lemma 01V0: by Stacks 04CS, proved in this tree as
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, both sides are the small-étale
modules of Stacks 03DU attached to the Zariski sheaves of relative differentials of the two
columns, and the associated-module functor commutes with pullback by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`; that route would further need
the identification of the comparison map itself with the small-étale module of the scheme-level
canonical map `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` of Stacks 01UV, which is a
statement about the universal derivations and not about the modules alone.  The statement is
proved by another route, through derivations:
`AlgebraicGeometry.Space.isSchemeSquareDifferentialsIso_of_derivationRestriction` applied to
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`.

## Main definitions

* `AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`: the one statement this reduction of
  Stacks 05ZC takes — invertibility of the comparison map of Stacks 04CX for a cartesian square of schemes of
  the site, read as a square of represented algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare`:
  **Stacks 05ZC from that statement alone.**  The étale localization is done here; no clause of
  Stacks 04CU and no sections-level identification is carried.
* `AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback_of_schemeSquare`: **Stacks 05ZD from the
  same statement**, through
  `AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback`, which reduces the direct-sum assertion
  to Stacks 05ZC at the two orientations of the cartesian square by the transitivity sequence of
  Stacks 05Z8.  No chartwise form of Morphisms, Lemma 01V1 is needed.

## Implementation notes

The tower is applied to the degenerate triangle `q = 𝟙 Y`, `h = g`, `q' = 𝟙 Y'`: its lower
cartesian square is then `IsPullback g (𝟙 Y') (𝟙 Y) g`, which is
`CategoryTheory.IsPullback.of_id_snd`, and its upper square is the given one.  What the tower is
used for is only its *upper* chart square
`AlgebraicGeometry.Space.BaseChangeChartTower.isPullbackX` and the four charts, so nothing of the
lower one is consumed beyond its existence.

The charts of `Y` and of `Y'` produced by the tower are the ones carried by `C.V` and by
`C.V ×_{C.W} C.W'`; it is the *same* chart of `Y` that the chart of `X` lies over and that the
chart of `Y'` is a base change of, which is why the chart square of schemes is cartesian without
any comparison between independently chosen charts.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1), the lifting of a chart
  along a morphism, which is what the tower is built from.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The last statement Stacks 05ZC needed.**  For morphisms `k : U' ⟶ U`, `r : U ⟶ V`,
`r' : U' ⟶ V'`, `l : V' ⟶ V` of schemes of the big fppf site over `S` forming a commutative
square whose underlying square of schemes is cartesian, the comparison map of Stacks 04CX of the
square of *represented* algebraic spaces is an isomorphism.

No algebraic space, no chart and no étale morphism occurs: this is Morphisms, Lemma 01V0 read on
the small étale sites.

**It is proved**, and not through the invertibility clause of Stacks 04CS, which would have
needed the compatibility of
Stacks 03LC (1) with the universal derivations.  The route is the interchangeable derivation form
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareDerivation.lean`), in
which only the direct image of modules and the structure map occur;
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction` is the proof and
`AlgebraicGeometry.Space.isSchemeSquareDifferentialsIso_of_derivationRestriction` carries it
back here. -/
abbrev IsSchemeSquareDifferentialsIso : Prop :=
  ∀ (U V U' V' : BigFppfOver B S hS) (k : U' ⟶ U) (r : U ⟶ V) (r' : U' ⟶ V') (l : V' ⟶ V)
    (hk : schemeSpaceMap k ≫ schemeSpaceMap r = schemeSpaceMap r' ≫ schemeSpaceMap l),
    IsPullback ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map r')
        ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map l) →
      IsIso (sheafOfDifferentialsMap B S hS (schemeSpaceMap k) (schemeSpaceMap r)
        (schemeSpaceMap r') (schemeSpaceMap l) hk)

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **The statement of Stacks 05ZC from
`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`** — the case of a cartesian square of
schemes of the site.  That input is proved (through
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`), and the tag is registered on the
unconditional `AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isPullback`.

The étale localization is carried out here and nothing of it is assumed: a tower of étale charts
of the cartesian square (Stacks 02X1, twice) leaves a cartesian square of chart schemes and a
*surjective* étale chart of `X'`, and
`AlgebraicGeometry.Space.isIso_of_isIso_chartComparison` identifies the restriction of `c_{g'}`
to that chart with the comparison map of the chart square and descends invertibility back. -/
theorem isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare
    (hscheme : IsSchemeSquareDifferentialsIso B S hS) (g' : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback g' p' p g)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c) : IsIso c := by
  obtain ⟨C⟩ := exists_baseChangeChartTower B S hS X.2 Y.2 Y.2 Y'.2
    (IsPullback.of_id_snd (f := g.hom)) (AlgebraicSpaces.isPullback_hom B S hS h)
  have hcomm : (ObjectProperty.homMk C.cU : schemeSpace _ ⟶ X') ≫ p' =
      schemeSpaceMap C.fU ≫ (ObjectProperty.homMk C.cV : schemeSpace _ ⟶ Y') :=
    ObjectProperty.hom_ext _ C.cUsnd
  have hcommU : (ObjectProperty.homMk C.u : schemeSpace _ ⟶ X) ≫ p =
      schemeSpaceMap C.α ≫ (ObjectProperty.homMk C.v : schemeSpace _ ⟶ Y) :=
    ObjectProperty.hom_ext _ C.commF.symm
  have hk : schemeSpaceMap C.qU ≫ schemeSpaceMap C.α =
      schemeSpaceMap C.fU ≫ schemeSpaceMap C.pV :=
    ObjectProperty.hom_ext _ (by
      change yoneda.map C.qU ≫ yoneda.map C.α = yoneda.map C.fU ≫ yoneda.map C.pV
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map (pullback.condition (f := C.α) (g := C.pV)))
  have htop : (ObjectProperty.homMk C.cU : schemeSpace _ ⟶ X') ≫ g' =
      schemeSpaceMap C.qU ≫ (ObjectProperty.homMk C.u : schemeSpace _ ⟶ X) :=
    ObjectProperty.hom_ext _ C.cUfst
  exact isIso_of_isIso_chartComparison B S hS g' p p'
    (ObjectProperty.homMk C.u) (schemeSpaceMap C.α) (ObjectProperty.homMk C.v)
    (ObjectProperty.homMk C.cU) (schemeSpaceMap C.fU) (ObjectProperty.homMk C.cV)
    (schemeSpaceMap C.qU) (schemeSpaceMap C.pV)
    (isEtale_of_presheaf_etale B S hS C.uEtale) (isEtale_of_presheaf_etale B S hS C.vEtale)
    (isEtale_of_presheaf_etale B S hS C.cUEtale) (isEtale_of_presheaf_etale B S hS C.cVEtale)
    C.cUSurjective hcommU hcomm hk htop hc
    (hscheme _ _ _ _ C.qU C.α C.fU C.pV hk C.isPullbackX)

/-- **The statement of Stacks 05ZD from
`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`.**  The tag is registered on the
unconditional `AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback`.

`AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback` reduces the direct-sum assertion to
Stacks 05ZC at the two orientations of the cartesian square, by the transitivity sequence of
Stacks 05Z8; each of those is
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare`.  The
bespoke chartwise form of Morphisms, Lemma 01V1 is not used. -/
theorem isIso_biprodDesc_of_isPullback_of_schemeSquare
    (hscheme : IsSchemeSquareDifferentialsIso B S hS) {W T : AlgebraicSpaces B S hS}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T) (h : IsPullback p q f g)
    (a : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b) :
    IsIso (biprod.desc a b) :=
  isIso_biprodDesc_of_isPullback B S hS p q f g h a b ha hb
    (fun _ hc => isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare B S hS hscheme
      q p g f h.flip hc)
    (fun _ hc => isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare B S hS hscheme
      p q f g h hc)

end AlgebraicGeometry.Space

end
