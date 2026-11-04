module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparisonMap
import StacksCore.Tactic.StacksAttribute

/-!
# Monomorphy of the comparison map of Stacks 05Z8 on a square of étale charts

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` and let

```
U --ψ--> V
|        |
a        b
v        v
X --f--> Y
```

be a commutative square whose vertical arrows are étale.  The first map of the transitivity
sequence of Stacks 05Z8 is the comparison map `c_f : f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of Stacks 04CX, and
`AlgebraicGeometry.Space.mono_of_mono_modulePullback_chart` reduces its monomorphy to the
monomorphy of its restriction `a^*c_f` along a surjective étale chart `a`.  This file carries
that restriction across the square: `a^*c_f` is a monomorphism exactly when the comparison map
`c_ψ : ψ^*Ω_{V/Z} ⟶ Ω_{U/Z}` of the chart morphism is.

## Main results

* `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_right`: being a comparison map of
  Stacks 04CX is transported along an equality of the *left* edges of the square, the companion
  of `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_left` for the upper edge.
* `AlgebraicGeometry.Space.mono_map_iff_of_isSheafOfDifferentialsMap`: for two stacked squares
  with upper edges `g` and `f` whose *lower* comparison map `c_g` is invertible, monomorphy of
  `g^*c_f` is monomorphy of the comparison map of the outer square.
* `AlgebraicGeometry.Space.mono_iff_of_isSheafOfDifferentialsMap`: the same with the roles
  exchanged — when `c_f` is invertible, monomorphy of `c_g` is monomorphy of the comparison map
  of the outer square.
* `AlgebraicGeometry.Space.mono_map_pullbackDifferentialsMap_iff_of_etaleChart`: **the
  reduction**, `Mono (a^*c_f) ↔ Mono c_ψ`.

## The proof

Both sides are compared with the comparison map of the *outer* square, the one with upper edge
`a ≫ f = ψ ≫ b` and left edge `ψ ≫ b ≫ g`, through the composition law of Stacks 05Z7 in the
form `AlgebraicGeometry.Space.eq_comp_of_isSheafOfDifferentialsMap`:

* factoring the outer square through `X` gives `c = (a^*c_f) ≫ c_a` up to the comparison of
  inverse images, and `c_a` is invertible because `a` is étale;
* factoring it through `V` gives `c = (ψ^*c_b) ≫ c_ψ`, and `ψ^*c_b` is invertible because `b`
  is étale.

The two outer comparison maps so produced differ only in how their upper edge is spelled, `a ≫ f`
against `ψ ≫ b`, and `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_left` identifies
them up to an `eqToHom`.  The left edge is spelled once, as `ψ ≫ b ≫ g`, for both; that is what
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_right` and
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale` are for, the invertible
comparison maps `c_a` and `c_b` arriving with the left edge in the spellings `a ≫ f ≫ g` and
`b ≫ g` respectively.

## What this does not do

It does not reduce the monomorphy of `c_ψ` any further.  The chart morphism `ψ` is a morphism of
*schemes* of the site, and the corresponding statement for schemes is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmoothAffineLocally`.
Crossing between the two needs two things, of which only one is here.

* The *exactness* of the functor that crosses is available: the associated-module functor of
  Stacks 03DU (4) is left exact by Stacks 08H8, in the form of the instance
  `AlgebraicGeometry.Space.preservesFiniteLimits_representedAssociatedModule`
  (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModuleEtalePullback.lean`), from
  which preservation of monomorphisms is immediate.  So a monomorphism of Zariski modules on the
  chart scheme does become one on the small étale site.  That module is *not* imported here: it
  sits downstream of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparison.lean`, hence
  downstream of the consumer of this file.
* What is missing is the *naturality* of the identification of Stacks 04CS,
  `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso`, for the comparison maps: that
  identification is a family of isomorphisms of objects, and no declaration in this development
  relates `AlgebraicGeometry.Space.representedAssociatedModule` to
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap`.  Without it the scheme-level
  comparison map and `c_ψ` are two unrelated morphisms between identified objects.  See the
  section *What else is carried, and why none of it is this statement* of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparison.lean`.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7), the comparison maps of
  two stacked squares compose.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), étale localization of
  the sheaf of differentials.
* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8), the transitivity
  sequence of relative differentials.
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8), exactness of the
  associated-module functor of the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ChartMono

variable {X Y Z X' Y' X'' Y'' U V : AlgebraicSpaces B S hS}

/-- Being a comparison map of Stacks 04CX for a square depends on the left edge only through its
value, so it transports along an equality of left edges.  This is the companion of
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_left`, which transports along an
equality of the upper edges. -/
theorem IsSheafOfDifferentialsMap.congr_right {g : X' ⟶ X} {p : X ⟶ Y} {p' p₁ : X' ⟶ Y'}
    {c : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g p p' c) (h : p' = p₁) :
    IsSheafOfDifferentialsMap B S hS g p p₁
      (c ≫ eqToHom (congrArg (fun r : X' ⟶ Y' =>
        sheafOfDifferentials B S hS r) h)) := by
  subst h
  simpa using hc

/-- **Monomorphy of the restricted comparison map, read on the outer square.**  For two stacked
commutative squares with upper edges `g : X'' ⟶ X'` and `f : X' ⟶ X` whose lower comparison map
`c_g` is invertible, the restriction `g^*c_f` of the upper comparison map is a monomorphism
exactly when the comparison map of the outer square is.

By Stacks 05Z7 in the form `AlgebraicGeometry.Space.eq_comp_of_isSheafOfDifferentialsMap` the
outer comparison map is `g^*c_f` followed by `c_g`, up to the invertible comparison of inverse
images of Stacks 03LU. -/
theorem mono_map_iff_of_isSheafOfDifferentialsMap (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {c : (modulePullback B S hS (g ≫ f)).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p''}
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hc : IsSheafOfDifferentialsMap B S hS (g ≫ f) p p'' c)
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) (hcg : IsIso cg) :
    Mono ((modulePullback B S hS g).map cf) ↔ Mono c := by
  have := hcg
  rw [eq_comp_of_isSheafOfDifferentialsMap B S hS f g p p' p'' hc hf hg,
    mono_comp_iff_of_isIso]
  refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
  · have := hm
    infer_instance
  · have := hm
    exact mono_of_mono _ cg

/-- **Monomorphy of the lower comparison map, read on the outer square.**  For two stacked
commutative squares with upper edges `g : X'' ⟶ X'` and `f : X' ⟶ X` whose upper comparison map
`c_f` is invertible, the lower comparison map `c_g` is a monomorphism exactly when the comparison
map of the outer square is.

This is `AlgebraicGeometry.Space.mono_map_iff_of_isSheafOfDifferentialsMap` with the roles of the
two inner squares exchanged: the invertible factor is now the restriction `g^*c_f`, an inverse
image of an isomorphism. -/
theorem mono_iff_of_isSheafOfDifferentialsMap (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {c : (modulePullback B S hS (g ≫ f)).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p''}
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hc : IsSheafOfDifferentialsMap B S hS (g ≫ f) p p'' c)
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) (hcf : IsIso cf) :
    Mono cg ↔ Mono c := by
  have := hcf
  have : IsIso ((modulePullback B S hS g).map cf) := inferInstance
  rw [eq_comp_of_isSheafOfDifferentialsMap B S hS f g p p' p'' hc hf hg,
    mono_comp_iff_of_isIso, mono_comp_iff_of_isIso]

/-- The comparison map `pullbackDifferentialsMap` is the comparison map of Stacks 04CX of its
square. -/
private theorem isSheafOfDifferentialsMap_pullbackDifferentialsMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsSheafOfDifferentialsMap B S hS f g (f ≫ g) (pullbackDifferentialsMap B S hS f g) :=
  isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f g (f ≫ g) (𝟙 Z) (by simp)

/-- **The chart reduction for the first map of the transitivity sequence of Stacks 05Z8.**  Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces and let `a : U ⟶ X`, `b : V ⟶ Y` be
étale with `ψ ≫ b = a ≫ f`.  The restriction along `a` of the comparison map
`c_f : f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` is a monomorphism exactly when the comparison map
`c_ψ : ψ^*Ω_{V/Z} ⟶ Ω_{U/Z}` of the chart morphism is.

Both are compared with the comparison map of the outer square, whose upper edge is
`a ≫ f = ψ ≫ b` and whose left edge is `ψ ≫ b ≫ g`: through `X` by
`AlgebraicGeometry.Space.mono_map_iff_of_isSheafOfDifferentialsMap`, the invertible factor being
`c_a` because `a` is étale, and through `V` by
`AlgebraicGeometry.Space.mono_iff_of_isSheafOfDifferentialsMap`, the invertible factor being
`c_b` because `b` is étale.  The two readings of the outer comparison map differ only in the
spelling of its upper edge, which
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap.congr_left` reconciles. -/
theorem mono_map_pullbackDifferentialsMap_iff_of_etaleChart (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : U ⟶ X) (b : V ⟶ Y) (ψ : U ⟶ V) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hsq : ψ ≫ b = a ≫ f) :
    Mono ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS f g)) ↔
      Mono (pullbackDifferentialsMap B S hS ψ (b ≫ g)) := by
  have hleft : a ≫ f ≫ g = ψ ≫ b ≫ g := by
    rw [← Category.assoc, ← hsq, Category.assoc]
  -- The comparison map of the outer square, factored through `X` and factored through `V`.
  have hcX := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS (a ≫ f) g (ψ ≫ b ≫ g)
    (𝟙 Z) (by simp [hleft])
  have hcV := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS (ψ ≫ b) g (ψ ≫ b ≫ g)
    (𝟙 Z) (by simp)
  have hca := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a (f ≫ g) (ψ ≫ b ≫ g)
    (𝟙 Z) (by simp [hleft])
  -- `c_a` is invertible because `a` is étale, and `c_b` because `b` is.
  have h1 := mono_map_iff_of_isSheafOfDifferentialsMap B S hS f a g (f ≫ g) (ψ ≫ b ≫ g) hcX
    (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS f g) hca
    (isIso_of_isSheafOfDifferentialsMap_of_isEtale B S hS a ha (f ≫ g) _ hleft hca)
  have h3 := mono_iff_of_isSheafOfDifferentialsMap B S hS b ψ g (b ≫ g) (ψ ≫ b ≫ g) hcV
    (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS b g)
    (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS ψ (b ≫ g))
    (isIso_pullbackDifferentialsMap_of_isEtale B S hS b hb g)
  -- The two readings of the outer comparison map agree up to an `eqToHom`.
  have hkey := eq_of_isSheafOfDifferentialsMap B S hS (a ≫ f) g (ψ ≫ b ≫ g) hcX
    (IsSheafOfDifferentialsMap.congr_left B S hS hcV hsq)
  rw [h1, h3, hkey, mono_comp_iff_of_isIso]

end ChartMono

end AlgebraicGeometry.Space

end
