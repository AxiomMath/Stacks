module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparisonMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale

/-!
# The comparison map of differentials along an étale morphism is an isomorphism

Stacks 04CX attaches to a commutative square with top edge `f : X' ⟶ X` and left edge
`p' : X' ⟶ Y'` a comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}`, uniquely characterized by
carrying `f^*d_{X/Y}(t)` to `d_{X'/Y'}(f♯ t)`
(`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` and
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`).  Stacks 04CU says that for an étale
`a : U ⟶ X` the restriction of `Ω_{X/Y}` to the small étale site of `U` is `Ω_{U/Y}`, and
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` proves it.

This file identifies the two: **the identification of Stacks 04CU is the comparison map of
Stacks 04CX for the square whose top edge is `a` and whose bottom edge is the identity of `Y`**.
Consequently that comparison map is an isomorphism — the clause of Stacks 04CU that the
étale-local statements of this development consume, so that they need not carry it as an
`IsIso` hypothesis.

## Main results

* The forward map of the étale-source localization of Stacks 04CU has the characterizing
  property of Stacks 04CX: this is the base's
  `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMapEtale.lean`, which the results
  below consume.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale`: **any comparison map of
  Stacks 04CX along an étale morphism, over a fixed base, is an isomorphism.**  The left edge is
  taken as a morphism `p'` together with an equality `a ≫ f = p'`, so that the statement applies
  at whatever spelling of the composite a caller has.

The instance at `AlgebraicGeometry.Space.pullbackDifferentialsMap`, the first map of the
transitivity sequence of Stacks 05Z8, is the base's
`AlgebraicGeometry.Space.isIso_pullbackDifferentialsMap_of_isEtale` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleSourceComparisonMap.lean`, which
this module re-exports.

## Attribute

`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale` carries `@[stacks 04CU]`.
Stacks 04CU asserts the identification `Ω_{X/Y}|_{U_étale} = Ω_{U/V}`, and that identification is
the canonical one — in the source it *is* the comparison map of a square with étale vertical
arrows, not some isomorphism chosen by hand.  The declarations already registered for the tag
exhibit an isomorphism built here:
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` and
`AlgebraicGeometry.Space.universalDerivation_etaleSourceLocalizationHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleSourceLocalization.lean`, and
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleLocalization.lean`, the last of
which is the full square with both vertical arrows étale.  None of them says that the canonical
map of Stacks 04CX is the invertible one, which is the clause registered here.

The base's `AlgebraicGeometry.Space.isIso_pullbackDifferentialsMap_of_isEtale` is that same
clause instantiated at one named map.

## The "in particular" clause is not available

The final sentence of Stacks 04CU — that for `U`, `V` *schemes* the identification above agrees
with the usual Zariski sheaf of differentials of the morphism of schemes `U ⟶ V` — is **not
proved in this development**, and nothing here claims it.  It is the invertibility clause of
Stacks 04CS.  This development has the comparison map of Stacks 04CS,
`AlgebraicGeometry.SmallEtale.differentialsComparison`, with its compatibility with the universal
derivations, its uniqueness and its naturality, but no proof that it is an isomorphism; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentials.lean`, which
record what that proof still needs.  The statement wanted is the hypothesis `hschemeChart` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsQuasicoherent.lean`, which carries it
rather than assuming any part of Stacks 04CU proper.

## Implementation notes

The identification of the forward map of Stacks 04CU with a comparison map of Stacks 04CX is the
base's `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`; an
earlier, independent computation of the same fact on a local section (through the untransported
adjunction `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` and the three
remaining bijections of `AlgebraicGeometry.Space.derivationEtalePullbackEquiv`) was deleted in
its favour, together with its helper lemmas.  What is left here is the uniqueness of the
comparison map, `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`, applied against it.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), the clause
  `a^{-1}𝒪_X = 𝒪_U` for an étale `a`.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `a^* ⊣ a_*` and its two spellings.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pullbackAdjPushforwardModules
  inverseImageDerivationEquiv derivationSheafHom
  derivationSheafHom_inverseImageDerivationEquiv)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### Stacks 04CU as the comparison map of Stacks 04CX -/

/-- **The comparison map of Stacks 04CX along an étale morphism is an isomorphism.**  By
uniqueness of the comparison map it is the identification of Stacks 04CU,
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`.

The left edge of the square is taken as a morphism `p' : U ⟶ Y` together with an equality
`a ≫ f = p'`, so that the statement applies at whatever spelling of the composite a caller
has. -/
@[stacks 04CU "the identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}` is the canonical one: every
  comparison map of 04CX along an étale `a : U ⟶ X`, for a square whose bottom edge is an
  identity, is an isomorphism"]
theorem isIso_of_isSheafOfDifferentialsMap_etale (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (f : X ⟶ Y) (p' : U ⟶ Y) (hp' : a ≫ f = p')
    {c : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS a f p' c) : IsIso c := by
  subst hp'
  rw [eq_of_isSheafOfDifferentialsMap B S hS a f (a ≫ f) hc
    (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS a ha f)]
  exact (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).isIso_hom

end AlgebraicGeometry.Space

end
