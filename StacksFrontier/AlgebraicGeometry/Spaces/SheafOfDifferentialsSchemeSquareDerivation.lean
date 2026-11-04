module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapDerivationCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The last input of Stacks 05ZC and 05ZD, restated with no inverse image of modules in it

**`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction`, the form this file puts that
input in, is proved**, as `AlgebraicGeometry.Space.schemeSquareDerivationRestriction` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`, so the
two conditional statements at the end of this file are unconditional there and that is where the
two tags are registered.  Everything below about why *this* shape of the input is the tractable
one is what the proof then confirmed: no inverse image of modules occurs in it, so the
compatibility of Stacks 03LC (1) with the universal derivations — named as absent in the next
paragraph, and still absent — was never needed.

`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChangeChartReduction.lean` is the
single statement to which Stacks 05ZC and Stacks 05ZD are reduced: for a cartesian square of
schemes of the big fppf site over `S`, read as a square of *represented* algebraic spaces, the
comparison map of Stacks 04CX is an isomorphism.

That statement is about the inverse image `(k)^*Ω_{U/V}` of modules on the small étale site, and
the route to it through the invertibility clause of Stacks 04CS
(`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`) needs the base change
`(k^*𝓕)^a ≅ ε_k^*(𝓕^a)` of **Stacks 03LC (1)** — either
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` or its spaces-side form
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — to be **compatible with the
universal derivations**.  No such compatibility is in the tree.  What pins that base change is the
conjugacy `AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv` of the
two composite adjunctions round the square of ringed sites, read on sections over the open `⊤` by
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_inv_unit_sections_top`.

That base change is not itself beyond computation, and saying why is worth the space, both sides
of it being left adjoints: a comparison of two left adjoints of one right adjoint is
`CategoryTheory.Adjunction.leftAdjointUniq`, and Mathlib's
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` computes it through the transposes —
with `CategoryTheory.Adjunction.homEquiv_naturality_right` it gives
`adj₁.homEquiv (e.hom.app x ≫ q) = adj₂.homEquiv q`.  So such a comparison is computable in
principle, and the conjugacy named above is a second description of this one.  What is missing is
the compatibility statement itself, not a way of writing the isomorphism down.

This file replaces that input by one in which **no inverse image of modules occurs**.  By
`AlgebraicGeometry.Space.isIso_of_bijective_restrictDerivation` the comparison map of a
commutative square is invertible exactly when restriction of derivations along its top edge is
bijective, and restriction of derivations is built from the *direct* image `k_*` and the
structure map `k♯` alone.  For the two routes round the square of small étale ringed sites of a
morphism of schemes of the site the direct images are compared by
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which is assembled from
`SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂` — no adjoint-uniqueness
step — and the corresponding comparison of restrictions to the small Zariski site is *computed*
over the opens of the base by
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`.

## Main definitions

* `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction`: for a cartesian square of
  schemes of the site, read as represented algebraic spaces, restriction of derivations along the
  top edge is a bijection on every `𝒪`-module of the small étale site of the source.

## Main results

* `AlgebraicGeometry.Space.isSchemeSquareDifferentialsIso_of_derivationRestriction`: **it implies
  `AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`**, hence Stacks 05ZC and Stacks 05ZD
  through the chart reduction already in the tree.
* `AlgebraicGeometry.Space.isSchemeSquareDerivationRestriction_of_differentialsIso`: the
  converse, so the two inputs are interchangeable and nothing is lost by carrying the
  derivation-restriction form.
* `Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_derivationRestriction` and
  `AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback_of_derivationRestriction`:
  **Stacks 05ZC and Stacks 05ZD from the derivation-restriction form alone** — which is proved,
  so the unconditional forms are
  `AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isPullback` and
  `AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback`.

## Implementation notes

The cartesianness hypothesis is the one of
`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`: cartesianness of the square of
*schemes* underlying the four morphisms, which is what Morphisms, Lemma 01V0 is stated for and
what the chart tower of
`AlgebraicGeometry.Space.exists_baseChangeChartTower` delivers.  It is not used in this file —
the two implications below are formal — and is carried only so that the two statements quantify
over the same squares.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The one input of Stacks 05ZC and Stacks 05ZD, with no inverse image of modules in it.**
For morphisms `k : U' ⟶ U`, `r : U ⟶ V`, `r' : U' ⟶ V'`, `l : V' ⟶ V` of schemes of the big fppf
site over `S` forming a commutative square whose underlying square of schemes is cartesian,
restriction of derivations along `k` — the passage from a map `Ω_{U'/V'} ⟶ C` of `𝒪_{U'}`-modules
on the small étale site to the `V`-derivation `k_*(d_{U'/V'} ∘ -) ∘ k♯` of `𝒪_U` — is a bijection
for every `C`.

By `AlgebraicGeometry.Space.isIso_of_bijective_restrictDerivation` this is equivalent to
`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`, and unlike that form it mentions only
the direct image of modules and the structure map. -/
abbrev IsSchemeSquareDerivationRestriction : Prop :=
  ∀ (U V U' V' : BigFppfOver B S hS) (k : U' ⟶ U) (r : U ⟶ V) (r' : U' ⟶ V') (l : V' ⟶ V)
    (hk : schemeSpaceMap k ≫ schemeSpaceMap r = schemeSpaceMap r' ≫ schemeSpaceMap l),
    IsPullback ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map r')
        ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map l) →
      ∀ C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2,
        Function.Bijective (restrictDerivation B S hS (schemeSpaceMap k) (schemeSpaceMap r)
          (schemeSpaceMap r') (schemeSpaceMap l) hk C)

/-- **The derivation-restriction form implies the invertibility form.**  Each instance is
`AlgebraicGeometry.Space.isIso_of_bijective_restrictDerivation`. -/
theorem isSchemeSquareDifferentialsIso_of_derivationRestriction
    (h : IsSchemeSquareDerivationRestriction B S hS) : IsSchemeSquareDifferentialsIso B S hS :=
  fun U V U' V' k r r' l hk hcart ↦
    isIso_of_bijective_restrictDerivation B S hS (schemeSpaceMap k) (schemeSpaceMap r)
      (schemeSpaceMap r') (schemeSpaceMap l) hk (h U V U' V' k r r' l hk hcart)

/-- **The invertibility form implies the derivation-restriction form.**  Each instance is
`AlgebraicGeometry.Space.bijective_restrictDerivation_of_isIso`, so nothing is lost by carrying
the derivation-restriction form instead. -/
theorem isSchemeSquareDerivationRestriction_of_differentialsIso
    (h : IsSchemeSquareDifferentialsIso B S hS) : IsSchemeSquareDerivationRestriction B S hS :=
  fun U V U' V' k r r' l hk hcart C ↦
    bijective_restrictDerivation_of_isIso B S hS (schemeSpaceMap k) (schemeSpaceMap r)
      (schemeSpaceMap r') (schemeSpaceMap l) hk (h U V U' V' k r r' l hk hcart) C

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **Stacks 05ZC**, from `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` alone.
The étale localization is
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare` and
nothing of it is assumed.

That hypothesis is proved, as
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`, so the unconditional form of the
tag — which is where it is registered — is
`AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`. -/
theorem isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_derivationRestriction
    (hscheme : IsSchemeSquareDerivationRestriction B S hS) (g' : X' ⟶ X) (p' : X' ⟶ Y')
    (p : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback g' p' p g)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c) : IsIso c :=
  isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_schemeSquare B S hS
    (isSchemeSquareDifferentialsIso_of_derivationRestriction B S hS hscheme) g' p' p g h hc

/-- **Stacks 05ZD**, from `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` alone.
That hypothesis is proved, as
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`, so the unconditional form of the
tag — which is where it is registered — is
`AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`. -/
theorem isIso_biprodDesc_of_isPullback_of_derivationRestriction
    (hscheme : IsSchemeSquareDerivationRestriction B S hS) {W T : AlgebraicSpaces B S hS}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T) (h : IsPullback p q f g)
    (a : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b) :
    IsIso (biprod.desc a b) :=
  isIso_biprodDesc_of_isPullback_of_schemeSquare B S hS
    (isSchemeSquareDifferentialsIso_of_derivationRestriction B S hS hscheme) p q f g h a b ha hb

end AlgebraicGeometry.Space

end
