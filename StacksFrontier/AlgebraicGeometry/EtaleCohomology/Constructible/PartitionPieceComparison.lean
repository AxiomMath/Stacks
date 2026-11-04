module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedComparison

/-!
# Comparing the pieces of a set-level partition along an inclusion of subsets

`AlgebraicGeometry.ConstructibleStratification.partitionPiece B X T hT` is the object of the big
étale site realising a locally closed subset `T` of `X` as a scheme, namely the reduced induced
scheme on `T`. This file transports the comparison morphism of reduced induced schemes,
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison`, into the site:
for `T₁ ⊆ T₀` there is a morphism of pieces over `X`.

What this is for. A Noetherian induction over the strata of a constructible stratification
produces, from a piece `T₀`, a further shrunk piece `T₁ ⊆ T₀`; a scheme `W` trivialising some
datum over the piece on `T₀` lives *étale* over `partitionPiece B X T₀`, and to use it over `T₁`
it has to be base changed. The base change cannot be taken over `X`, because the structure
morphism of a piece is an immersion and not étale, so it has to be taken along a morphism of
pieces — which is what this file supplies.

## Main results

* `AlgebraicGeometry.ConstructibleStratification.partitionComparison`: **the comparison morphism**
  `partitionPiece B X T₁ hT₁ ⟶ partitionPiece B X T₀ hT₀` attached to an inclusion `T₁ ⊆ T₀` of
  locally closed subsets of `X`.
* `AlgebraicGeometry.ConstructibleStratification.partitionComparison_inclusion` and
  `.map_partitionComparison`: the comparison morphism commutes with the structure morphisms of
  the two pieces, and is the reduced induced comparison morphism underneath.
* `AlgebraicGeometry.ConstructibleStratification.partitionComparison_self` and
  `.partitionComparison_comp`: the comparison morphisms are functorial in the subset.
* `AlgebraicGeometry.ConstructibleStratification.isImmersion_partitionComparison` and
  `.range_partitionComparison`: the comparison morphism is an immersion whose image is the
  preimage of the smaller subset.

## Implementation notes

The underlying category of a `AlgebraicGeometry.BigEtaleSite` is a full subcategory of schemes,
so its inclusion is fully faithful and a morphism of pieces is exactly a morphism of the
underlying schemes. Everything here is therefore `AlgebraicGeometry.BigEtaleSite.inclusion`
applied to, or reflected from, the corresponding statement about reduced induced schemes, and the
properties of morphisms are stated for the morphism of schemes `B.inclusion.map _`, matching the
fields of `AlgebraicGeometry.ConstructibleStratification`.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

namespace ConstructibleStratification

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (T₁ T₀ : Set X.obj)
  (hT₁ : IsLocallyClosed T₁) (hT₀ : IsLocallyClosed T₀) (hsub : T₁ ⊆ T₀)

/-- **The comparison morphism of partition pieces along an inclusion of locally closed subsets.**
For `T₁ ⊆ T₀` locally closed in `X`, the piece realising `T₁` maps to the piece realising `T₀`,
compatibly with their structure morphisms to `X`. -/
def partitionComparison : partitionPiece B X T₁ hT₁ ⟶ partitionPiece B X T₀ hT₀ :=
  B.inclusion.preimage (reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub)

/-- The morphism of schemes underlying the comparison morphism of pieces is the comparison
morphism of reduced induced schemes. -/
theorem map_partitionComparison :
    B.inclusion.map (partitionComparison B X T₁ T₀ hT₁ hT₀ hsub) =
      reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub :=
  B.inclusion.map_preimage _

/-- **The comparison morphism commutes with the structure morphisms of the two pieces.** -/
@[reassoc (attr := simp)]
theorem partitionComparison_inclusion :
    partitionComparison B X T₁ T₀ hT₁ hT₀ hsub ≫ partitionInclusion B X T₀ hT₀ =
      partitionInclusion B X T₁ hT₁ :=
  B.inclusion.map_injective <| by
    rw [Functor.map_comp, map_partitionComparison, map_partitionInclusion,
      map_partitionInclusion]
    exact reducedInducedComparison_inclusion T₁ T₀ hT₁ hT₀ hsub

/-- The comparison morphism does not move points of `X`. -/
@[simp]
theorem map_partitionInclusion_partitionComparison
    (x : B.inclusion.obj (partitionPiece B X T₁ hT₁)) :
    B.inclusion.map (partitionInclusion B X T₀ hT₀)
        (B.inclusion.map (partitionComparison B X T₁ T₀ hT₁ hT₀ hsub) x) =
      B.inclusion.map (partitionInclusion B X T₁ hT₁) x := by
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, partitionComparison_inclusion]

/-- The comparison morphism along the identity inclusion is the identity. -/
@[simp]
theorem partitionComparison_self (T : Set X.obj) (hT : IsLocallyClosed T) :
    partitionComparison B X T T hT hT subset_rfl = 𝟙 (partitionPiece B X T hT) :=
  B.inclusion.map_injective <| by
    rw [CategoryTheory.Functor.map_id, map_partitionComparison]
    exact reducedInducedComparison_self T hT

/-- The comparison morphisms compose. -/
@[simp]
theorem partitionComparison_comp (T₂ : Set X.obj) (hT₂ : IsLocallyClosed T₂) (hsub' : T₂ ⊆ T₁) :
    partitionComparison B X T₂ T₁ hT₂ hT₁ hsub' ≫ partitionComparison B X T₁ T₀ hT₁ hT₀ hsub =
      partitionComparison B X T₂ T₀ hT₂ hT₀ (hsub'.trans hsub) :=
  B.inclusion.map_injective <| by
    rw [Functor.map_comp, map_partitionComparison, map_partitionComparison,
      map_partitionComparison]
    exact reducedInducedComparison_comp T₁ T₀ hT₁ hT₀ hsub T₂ hT₂ hsub'

/-- **The comparison morphism of pieces is an immersion.** -/
instance isImmersion_partitionComparison :
    IsImmersion (B.inclusion.map (partitionComparison B X T₁ T₀ hT₁ hT₀ hsub)) := by
  rw [map_partitionComparison]
  exact isImmersion_reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub

/-- The image of the comparison morphism of pieces is the preimage of the smaller subset under
the structure morphism of the larger piece. -/
theorem range_partitionComparison :
    Set.range (B.inclusion.map (partitionComparison B X T₁ T₀ hT₁ hT₀ hsub)).base =
      (B.inclusion.map (partitionInclusion B X T₀ hT₀)).base ⁻¹' T₁ := by
  rw [map_partitionComparison, map_partitionInclusion]
  exact range_reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub

end ConstructibleStratification

end AlgebraicGeometry

end
