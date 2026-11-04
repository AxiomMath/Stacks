module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ReducedInduced
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedIrreducible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the reduced induced scheme on a locally closed subset

A locally closed subset `T` of a scheme `X` carries the reduced induced scheme structure
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme`, immersed in `X`
with image `T`. This file turns that construction into a functor of `T`: for `T₁ ⊆ T₀` there is a
unique morphism `reducedInducedScheme T₁ ⟶ reducedInducedScheme T₀` over `X`, and it is again an
immersion.

The input is the universal property of the reduced induced structure,
`AlgebraicGeometry.exists_lift_reducedInduced`: a morphism *from a reduced scheme* whose image
lies in `T` factors through the reduced induced scheme on `T`. Reducedness of the source is what
makes the factorization exist — the identity of `Spec k[x]/(x²)` maps onto the reduced point of
the affine line and does not factor through it — and it is available here because the reduced
induced scheme is itself reduced. The factorization is unique because the canonical immersion is
a monomorphism, so the comparison morphisms compose and the comparison of `T` with itself is the
identity.

## Main results

* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedLift` and
  `.reducedInducedLift_inclusion`, `.reducedInducedLift_unique`: the universal property of the
  reduced induced scheme on a locally closed subset, as a chosen morphism with its factorization
  and the uniqueness of that factorization.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison`: **the
  comparison morphism** `reducedInducedScheme T₁ ⟶ reducedInducedScheme T₀` attached to an
  inclusion `T₁ ⊆ T₀` of locally closed subsets of `X`.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison_inclusion`
  and `.reducedInducedInclusion_reducedInducedComparison`: the comparison morphism commutes with
  the canonical immersions into `X`, as an equation of morphisms and pointwise.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison_self` and
  `.reducedInducedComparison_comp`: the comparison morphisms are functorial in `T`.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.range_reducedInducedComparison` and
  `.isImmersion_reducedInducedComparison`: the comparison morphism is an immersion with image the
  preimage of `T₁`.

## Implementation notes

Only `T₁ ⊆ T₀` is required, with both subsets locally closed in the *ambient* scheme `X`; local
closedness of `T₁` inside `T₀` is a consequence rather than a hypothesis, and is what
`isImmersion_reducedInducedComparison` records.

`reducedInducedLift` is defined by choice from the existence statement
`AlgebraicGeometry.exists_lift_reducedInduced` rather than by rebuilding the two halves of the
factorization. Nothing is lost: `reducedInducedLift_unique` shows the lift is the only morphism
over `X`, so every property of it is a property of any construction of it, and the functoriality
lemmas below are proved from uniqueness alone.

## References

* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

namespace Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

variable {X : Scheme.{u}}

/-- The reduced induced scheme on a locally closed subset is reduced: it is the subscheme cut out
by a vanishing ideal sheaf. -/
@[ega "I 5.2.1" "existence", ega "I 5.5.4" "more general"]
instance isReduced_reducedInducedScheme (T : Set X) (hT : IsLocallyClosed T) :
    IsReduced (reducedInducedScheme T hT) :=
  inferInstanceAs (IsReduced
    (Scheme.IdealSheafData.vanishingIdeal (reducedInducedClosed T hT)).subscheme)

/-- The canonical morphism of the reduced induced scheme on a locally closed subset is a
preimmersion, hence a monomorphism: it is a closed immersion followed by an open immersion. -/
instance isPreimmersion_reducedInducedInclusion (T : Set X) (hT : IsLocallyClosed T) :
    IsPreimmersion (reducedInducedInclusion T hT) :=
  inferInstanceAs (IsPreimmersion
    ((reducedInducedIdealSheaf T hT).subschemeι ≫ (reducedInducedOpen T hT).ι))

section Lift

variable {Y : Scheme.{u}} [IsReduced Y] (T : Set X) (hT : IsLocallyClosed T) (f : Y ⟶ X)
  (hf : Set.range f ⊆ T)

/-- **The universal property of the reduced induced scheme on a locally closed subset.** A
morphism `f` from a reduced scheme whose image lies in `T` factors through the reduced induced
scheme on `T`; this is the factorization. -/
noncomputable def reducedInducedLift : Y ⟶ reducedInducedScheme T hT :=
  (exists_lift_reducedInduced T hT f hf).choose

/-- The lift `reducedInducedLift T hT f hf` composed with the canonical immersion into `X` is `f`.
-/
@[reassoc (attr := simp)]
theorem reducedInducedLift_inclusion :
    reducedInducedLift T hT f hf ≫ reducedInducedInclusion T hT = f :=
  (exists_lift_reducedInduced T hT f hf).choose_spec

/-- The canonical immersion sends the image of a point `y` under the lift to `f y`. -/
@[simp]
theorem reducedInducedInclusion_reducedInducedLift (y : Y) :
    reducedInducedInclusion T hT (reducedInducedLift T hT f hf y) = f y := by
  rw [← Scheme.Hom.comp_apply, reducedInducedLift_inclusion]

/-- The factorization of the universal property is the only morphism over `X`: the canonical
immersion is a monomorphism. -/
theorem reducedInducedLift_unique (g : Y ⟶ reducedInducedScheme T hT)
    (hg : g ≫ reducedInducedInclusion T hT = f) : g = reducedInducedLift T hT f hf :=
  (cancel_mono (reducedInducedInclusion T hT)).mp
    (hg.trans (reducedInducedLift_inclusion T hT f hf).symm)

end Lift

section Comparison

variable (T₁ T₀ : Set X) (hT₁ : IsLocallyClosed T₁) (hT₀ : IsLocallyClosed T₀) (hsub : T₁ ⊆ T₀)

/-- **The comparison morphism of reduced induced schemes along an inclusion of locally closed
subsets.** For `T₁ ⊆ T₀` locally closed in `X`, the reduced induced scheme on `T₁` maps to the
reduced induced scheme on `T₀`, compatibly with the canonical immersions into `X`. -/
noncomputable def reducedInducedComparison :
    reducedInducedScheme T₁ hT₁ ⟶ reducedInducedScheme T₀ hT₀ :=
  reducedInducedLift T₀ hT₀ (reducedInducedInclusion T₁ hT₁)
    ((range_inclusion T₁ hT₁).subset.trans hsub)

/-- **The comparison morphism commutes with the canonical immersions into the ambient scheme.** -/
@[reassoc (attr := simp)]
theorem reducedInducedComparison_inclusion :
    reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub ≫ reducedInducedInclusion T₀ hT₀ =
      reducedInducedInclusion T₁ hT₁ :=
  reducedInducedLift_inclusion T₀ hT₀ _ _

/-- The comparison morphism does not move points of the ambient scheme. -/
@[simp]
theorem reducedInducedInclusion_reducedInducedComparison (x : reducedInducedScheme T₁ hT₁) :
    reducedInducedInclusion T₀ hT₀ (reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub x) =
      reducedInducedInclusion T₁ hT₁ x :=
  reducedInducedInclusion_reducedInducedLift T₀ hT₀ _ _ x

/-- The comparison morphism is the only morphism of reduced induced schemes over `X`. -/
theorem reducedInducedComparison_unique
    (g : reducedInducedScheme T₁ hT₁ ⟶ reducedInducedScheme T₀ hT₀)
    (hg : g ≫ reducedInducedInclusion T₀ hT₀ = reducedInducedInclusion T₁ hT₁) :
    g = reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub :=
  reducedInducedLift_unique T₀ hT₀ _ _ g hg

/-- The comparison morphism along the identity inclusion is the identity. -/
@[simp]
theorem reducedInducedComparison_self (T : Set X) (hT : IsLocallyClosed T) :
    reducedInducedComparison T T hT hT subset_rfl = 𝟙 (reducedInducedScheme T hT) :=
  (reducedInducedComparison_unique T T hT hT subset_rfl _ (Category.id_comp _)).symm

/-- The comparison morphisms compose. -/
@[simp]
theorem reducedInducedComparison_comp (T₂ : Set X) (hT₂ : IsLocallyClosed T₂) (hsub' : T₂ ⊆ T₁) :
    reducedInducedComparison T₂ T₁ hT₂ hT₁ hsub' ≫
        reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub =
      reducedInducedComparison T₂ T₀ hT₂ hT₀ (hsub'.trans hsub) :=
  reducedInducedComparison_unique T₂ T₀ hT₂ hT₀ (hsub'.trans hsub) _ <| by
    rw [Category.assoc, reducedInducedComparison_inclusion, reducedInducedComparison_inclusion]

/-- The image of the comparison morphism is the preimage of the smaller subset. In particular the
reduced induced scheme on `T₁` is a locally closed subspace of the reduced induced scheme on
`T₀`. -/
theorem range_reducedInducedComparison :
    Set.range (reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub) =
      reducedInducedInclusion T₀ hT₀ ⁻¹' T₁ := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro x ⟨y, rfl⟩
    rw [Set.mem_preimage, reducedInducedInclusion_reducedInducedComparison]
    exact (range_inclusion T₁ hT₁).subset ⟨y, rfl⟩
  · obtain ⟨y, hy⟩ := (range_inclusion T₁ hT₁).ge hx
    refine ⟨y, (isEmbedding_reducedInducedInclusion T₀ hT₀).injective ?_⟩
    rw [reducedInducedInclusion_reducedInducedComparison]
    exact hy

/-- **The comparison morphism is an immersion.** -/
instance isImmersion_reducedInducedComparison :
    IsImmersion (reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub) := by
  have : IsImmersion (reducedInducedComparison T₁ T₀ hT₁ hT₀ hsub ≫
      reducedInducedInclusion T₀ hT₀) := by
    rw [reducedInducedComparison_inclusion]
    exact inferInstanceAs (IsImmersion
      ((reducedInducedIdealSheaf T₁ hT₁).subschemeι ≫ (reducedInducedOpen T₁ hT₁).ι))
  exact IsImmersion.of_comp _ (reducedInducedInclusion T₀ hT₀)

end Comparison

end Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

end
