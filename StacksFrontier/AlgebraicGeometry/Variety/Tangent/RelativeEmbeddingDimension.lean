module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.NoetherNormalization
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.EmbeddingDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified

/-!
# Embedding dimension of a morphism

A morphism `f : X ⟶ S` *has embedding dimension at most `e`* if every point of `X` has an open
neighbourhood which, over `S`, is a closed subscheme of a scheme smooth over `S` of relative
dimension `e`. This is the relative form of the notion "embedding dimension" that the crystalline
chapter uses for a morphism `X → S₀`, where the pointwise notions already in the library are
attached to a scheme over a field.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE`: the bound above.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasEmbeddingDimensionLE_of_isClosedImmersion`: a closed immersion
  into a scheme smooth of relative dimension `e` over `S` bounds the embedding dimension by `e`.
* `AlgebraicGeometry.SmoothOfRelativeDimension.hasEmbeddingDimensionLE`: a morphism smooth of
  relative dimension `e` has embedding dimension at most `e`.
* `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_hasEmbeddingDimensionLE`: a morphism of
  bounded embedding dimension is locally of finite type.
* `AlgebraicGeometry.Scheme.Hom.hasEmbeddingDimensionLE_of_finrank_dottedTangentArrow`: a morphism
  locally of finite type whose relative tangent spaces all have dimension `e` has embedding
  dimension at most `e`; this is Tag 0CBL, and it is the link with the pointwise notion.
* `AlgebraicGeometry.Scheme.Hom.hasEmbeddingDimensionLE_of_embeddingDimension`: the same statement
  over a field, phrased with `AlgebraicGeometry.Scheme.Hom.embeddingDimension` of Tag 0C2H.
* `AlgebraicGeometry.injective_tangentMap_of_isClosedImmersion` and
  `AlgebraicGeometry.exists_injective_tangentMap_of_hasEmbeddingDimensionLE`: the opposite
  comparison, as far as it is available here — the relative tangent space at a point injects into
  the relative tangent space, at the image point, of the ambient smooth scheme.

## Which definition this is, and why it is the source's

The Stacks Project does not define embedding dimension for a morphism. Varieties, Section 0C2G
defines it for a scheme over a field, at a point: Definition 0C1Q as `dim_k 𝔪_x/𝔪_x²` at a closed
point over an algebraically closed field, and Definition 0C2H, for arbitrary `k` and `x`, as
`dim_{κ(x)} T_{X/k, x}`. Discussing the latter choice, Section 0C2G lists as a third candidate
"the smallest integer `d ≥ 0` such that there exists an open neighbourhood `U ⊂ X` of `x` and a
closed immersion `U → Y` where `Y` is a smooth variety of dimension `d` over `k`", calls it the
geometric definition, says that it "corresponds most closely to the geometric intuition the phrase
embedding dimension invokes", and records that it agrees with Definition 0C2H by Lemma 0CBL.

The integer `e` of Remark 07MR — "`X/S₀` has embedding dimension `e`" — is used there only through
that third description, with the ground field replaced by the base: the hints to 07MR compute
`Ru_{X/S, *}F` by "a de Rham complex constructed using an embedding of `X` into a smooth scheme of
dimension `e` over `S` (see Lemma 07LH)", and Lemma 07LH is exactly the affine form of such an
embedding, a factorization `A → P' → C` with `A → P'` smooth and `P' → C` surjective. So the
definition formalized here is that third, geometric description, relativized from a ground field to
a base scheme and from "dimension `d`" to "relative dimension `e`".

Two further choices are forced by the way 07MR uses the notion, and are visible in the name. The
predicate is a *bound* rather than a minimum, because 07MR uses `e` only through the vanishing of
the de Rham complex in degrees `> e`; and the embedding is required only *locally on `X`*, as in
the Stacks text, because that is what the local computation of `Ru_{X/S, *}F` needs.

## What is and is not proved

This module is an *input* to Remark 07MR, not a formalization of it: 07MR concludes that
`H^i(Cris(X/S), F)` vanishes for `i > d + e` and for `i > q + e`, and those conclusions need the
cohomological backbone the chapter does not yet have — the computation of crystalline cohomology by
the de Rham complex of a smooth embedding (Lemma 07LH, which rests on Proposition 07LG), the
alternating Čech complex of Remark 07MN, and the comparison `H^i(Cris(X/S), F) = H^i(X_{Zar},
Ru_{X/S, *}F)`. Accordingly nothing here carries the tag 07MR.

Of the comparison with the pointwise notion only one direction is proved here, and it is the one
Tag 0CBL supplies: if the relative tangent spaces of a morphism locally of finite type all have
dimension `e`, then the morphism has embedding dimension at most `e`. What is proved here of the
converse bound — that embedding dimension at most `e` makes every relative tangent space at most
`e`-dimensional — is the geometric half, which needs no rank computation: the tangent space of
`X/S` at a point of such a neighbourhood injects into the tangent space of the ambient smooth
scheme, because a closed immersion is unramified (Tag 02GC) and the tangent map of an unramified
morphism is injective (Tag 0B2G).

The rank computation that half wants is *not* missing from the library, contrary to what this
module documentation claimed before: `SmoothOfRelativeDimension` is related to the rank of the
differentials at the level of schemes by
`Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials` of
`StacksFrontier/AlgebraicGeometry/Different/TheDifferent/SmoothFormula.lean`, and
`StacksFrontier/AlgebraicGeometry/Variety/Tangent/RelativeEmbeddingDimensionForms.lean` draws the
two pointwise consequences from it —
`AlgebraicGeometry.Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension`, that the
relative tangent spaces of the *ambient* smooth scheme are `e`-dimensional, and
`AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension`,
that its relative differential forms vanish above degree `e`. What the converse at `X` itself
still needs is the transport of the dimension along the closed immersion of
`AlgebraicGeometry.exists_injective_tangentMap_of_hasEmbeddingDimensionLE`, whose source and
target tangent spaces sit over the two residue fields of a closed immersion rather than over one
field, together with the invariance of the relative tangent space under restriction to an open.

## Implementation notes

The tangent map of Tag 0B2F is available at a point only when the residue-field homomorphism there
is an isomorphism, which for a closed immersion holds because it is surjective on stalks;
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks` is therefore declared as
a local instance, so that the statements below carry no residue-field hypothesis.

In `AlgebraicGeometry.exists_injective_tangentMap_of_hasEmbeddingDimensionLE` the point of the
neighbourhood is quantified over, together with the equation saying that it lies over the given
point of `X`, rather than written as the pair of the point and its membership: the carrier of an
open subscheme is only definitionally the subtype, and instance search does not unfold it, so the
residue-field instance above is not found at a point presented in that way.

## References

* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 0B2F](https://stacks.math.columbia.edu/tag/0B2F)
* [Stacks Project, Tag 0C2G](https://stacks.math.columbia.edu/tag/0C2G)
* [Stacks Project, Tag 0CBL](https://stacks.math.columbia.edu/tag/0CBL)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks

/-- A morphism `f : X ⟶ S` **has embedding dimension at most `e`** if every point of `X` has an
open neighbourhood `U` admitting a closed immersion over `S` into a scheme smooth over `S` of
relative dimension `e`. See the module documentation for why this is the notion that Remark 07MR
means by "`X/S₀` has embedding dimension `e`". -/
def Scheme.Hom.HasEmbeddingDimensionLE {X S : Scheme.{u}} (f : X ⟶ S) (e : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (Y : Scheme.{u}) (i : U.toScheme ⟶ Y) (g : Y ⟶ S),
    IsClosedImmersion i ∧ SmoothOfRelativeDimension e g ∧ i ≫ g = U.ι ≫ f

/-- A scheme which is a closed subscheme of a scheme smooth of relative dimension `e` over `S` has
embedding dimension at most `e` over `S`. -/
theorem Scheme.Hom.hasEmbeddingDimensionLE_of_isClosedImmersion {X Y S : Scheme.{u}} (i : X ⟶ Y)
    (g : Y ⟶ S) (e : ℕ) [IsClosedImmersion i] [SmoothOfRelativeDimension e g] :
    (i ≫ g).HasEmbeddingDimensionLE e := by
  intro x
  have : IsIso (⊤ : X.Opens).ι := ⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩
  exact ⟨⊤, TopologicalSpace.Opens.mem_top x, Y, (⊤ : X.Opens).ι ≫ i, g, inferInstance,
    inferInstance, Category.assoc _ _ _⟩

/-- A morphism smooth of relative dimension `e` has embedding dimension at most `e`: it is a closed
subscheme of itself. -/
theorem SmoothOfRelativeDimension.hasEmbeddingDimensionLE {X S : Scheme.{u}} (f : X ⟶ S) (e : ℕ)
    [SmoothOfRelativeDimension e f] : f.HasEmbeddingDimensionLE e := by
  simpa using Scheme.Hom.hasEmbeddingDimensionLE_of_isClosedImmersion (𝟙 X) f e

/-- **A morphism of bounded embedding dimension is locally of finite type.** Locally the source is
a closed subscheme of a smooth scheme over the base, and both a closed immersion and a smooth
morphism are locally of finite type; local finite type is local on the source. -/
theorem Scheme.Hom.locallyOfFiniteType_of_hasEmbeddingDimensionLE {X S : Scheme.{u}} (f : X ⟶ S)
    (e : ℕ) (hf : f.HasEmbeddingDimensionLE e) : LocallyOfFiniteType f := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  choose U hU Y i g hi hg hig using hf
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x : X ↦ U x) ?_ fun x ↦ ?_
  · rw [eq_top_iff]
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hU z⟩
  · rw [← hig x]
    have := hi x
    have := hg x
    have : Smooth (g x) := SmoothOfRelativeDimension.smooth e (g x)
    infer_instance

/-- **The pointwise bound gives the relative bound.** If `f` is locally of finite type and all its
relative tangent spaces have dimension `e`, then `f` has embedding dimension at most `e`. This is
Tag 0CBL: near each point such a morphism factors as a closed immersion into a scheme smooth of
relative dimension `e` over an affine open of the base. -/
theorem Scheme.Hom.hasEmbeddingDimensionLE_of_finrank_dottedTangentArrow {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ x : X, Module.finrank (X.residueField x) (DottedTangentArrow f x) = e) :
    f.HasEmbeddingDimensionLE e := by
  intro x
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f x) (U := ⊤)
      (TopologicalSpace.Opens.mem_top _)
  obtain ⟨U, hxU, hUW, D, j, g, hj, hg, hjg⟩ :=
    exists_closedImmersion_smoothFactorization f x ⟨W, hW⟩ hxW e
      ((finrank_relativeCotangentSpace_eq_finrank_dottedTangentArrow f x).trans (he x))
  refine ⟨U.1, hxU, D, j, g ≫ W.ι, hj, ?_, ?_⟩
  · have := hg
    have h : SmoothOfRelativeDimension (e + 0) (g ≫ W.ι) := inferInstance
    rwa [Nat.add_zero] at h
  · rw [← Category.assoc, hjg, Scheme.Hom.resLE_comp_ι]

/-- **The pointwise bound gives the relative bound, over a field.** A scheme locally of finite type
over a field all of whose embedding dimensions in the sense of Tag 0C2H equal `e` has embedding
dimension at most `e` as a morphism. -/
theorem Scheme.Hom.hasEmbeddingDimensionLE_of_embeddingDimension (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ x : X, Scheme.Hom.embeddingDimension k f x = e) :
    f.HasEmbeddingDimensionLE e :=
  f.hasEmbeddingDimensionLE_of_finrank_dottedTangentArrow e he

/-- **The tangent map of a closed immersion is injective.** A closed immersion is unramified
(Tag 02GC), so its tangent map at every point is injective (Tag 0B2G). -/
theorem injective_tangentMap_of_isClosedImmersion {X Y S : Scheme.{u}} (i : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (x : X) (h : i ≫ q = p) [IsClosedImmersion i] :
    Function.Injective (tangentMap i p q h x) :=
  (injective_tangentMap_iff_unramifiedAt i p q x h).mpr (Unramified.unramifiedAt (f := i) x)

/-- **The relative bound embeds the tangent spaces in those of a smooth scheme.** If `f` has
embedding dimension at most `e` then each point of `X` has an open neighbourhood `U` which is a
closed subscheme of a scheme `Y` smooth of relative dimension `e` over `S`, in such a way that the
relative tangent space of `U/S` at the point injects into the relative tangent space of `Y/S` at
its image. Bounding the latter by `e` is the step that is not available; see the module
documentation. -/
theorem exists_injective_tangentMap_of_hasEmbeddingDimensionLE {X S : Scheme.{u}} (f : X ⟶ S)
    (e : ℕ) (hf : f.HasEmbeddingDimensionLE e) (x : X) :
    ∃ (U : X.Opens) (Y : Scheme.{u}) (i : U.toScheme ⟶ Y) (g : Y ⟶ S) (y : U.toScheme)
      (_ : U.ι.base y = x) (_ : IsClosedImmersion i) (_ : SmoothOfRelativeDimension e g)
      (h : i ≫ g = U.ι ≫ f),
      Function.Injective (tangentMap i (U.ι ≫ f) g h y) := by
  obtain ⟨U, hx, Y, i, g, hi, hg, hig⟩ := hf x
  exact ⟨U, Y, i, g, ⟨x, hx⟩, rfl, hi, hg, hig,
    injective_tangentMap_of_isClosedImmersion i (U.ι ≫ f) g ⟨x, hx⟩ hig⟩

end AlgebraicGeometry

end
