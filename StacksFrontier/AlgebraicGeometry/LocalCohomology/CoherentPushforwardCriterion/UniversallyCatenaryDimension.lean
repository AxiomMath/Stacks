module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCompletionDimension
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Stalk
public import StacksFrontier.RingTheory.FormalFibres.SerreConditionOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kollár's criterion on a universally catenary scheme with `(S₁)` formal fibres

On a locally Noetherian, universally catenary scheme whose local rings along the complement have
formal fibres satisfying `(S₁)`, the associated-prime condition of [Stacks, Tag 0BK3] collapses
to a bound on the dimension of the local ring itself: coherence of the direct image of a
coherent module along an open immersion is equivalent to the closure of each associated point
having dimension at least two at each omitted specialization.

## Main results

* `AlgebraicGeometry.two_le_ringKrullDim_quotient_completedStalk_iff_two_le_ringKrullDim_stalk`:
  the pointwise collapse of clause (2) of [Stacks, Tag 0BK3] to `2 ≤ dim(𝒪_{closure {x}, z})`.
* `AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`:
  **[Stacks, Tag 0AWB]**, with the hypotheses the source gives it.

## Implementation notes

The local ring `A = 𝒪_{closure {x}, z}` of the reduced closure of a point is a Noetherian local
domain and a quotient of `𝒪_{X, z}`, which is universally catenary by
`Scheme.isUniversallyCatenary_iff_stalk_isUniversallyCatenary` and has `(S₁)` formal fibres by
hypothesis. Both properties descend along the surjection of stalks, and
`le_ringKrullDim_quotient_adicCompletion_iff_of_surjective` then identifies the dimension of
every associated quotient of `A^∧` with `dim(A)`.

The biconditional of [Stacks, Tag 0BK3] that the collapse is applied to is
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`, which is why this
module imports the assembled criterion. The two statements are
spelled differently — `j.opensRange` for `Set.range j.base`, and `Scheme.completedLocalRing` for
the adic completion of the stalk at its maximal ideal — but both differences are reducible, so
the criterion rewrites the goal with no bridging lemma.

## References

* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0AW6](https://stacks.math.columbia.edu/tag/0AW6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing
open Stacks.LocalCohomology (isCoherent_pushforward_iff_forall_two_le_ringKrullDim)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The local ring of the reduced closure of a point of a locally Noetherian, universally
catenary scheme is a Noetherian local domain, and it is again universally catenary because it is
a quotient of the local ring of the ambient scheme. -/
theorem isDomain_isNoetherianRing_isUniversallyCatenary_stalk_vanishingIdeal_closure
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : Scheme.IsUniversallyCatenary X) (x : X)
    (y : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme) :
    IsDomain ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk y) ∧
      IsNoetherianRing ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk y) ∧
      Ring.IsUniversallyCatenary (X.presheaf.stalk
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι y)) := by
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure _
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  exact ⟨inferInstance, inferInstance,
    (Scheme.isUniversallyCatenary_iff_stalk_isUniversallyCatenary X).mp hX _⟩

/-- **The pointwise collapse of clause (2) of [Stacks, Tag 0BK3].** Let `X` be locally Noetherian
and universally catenary, let `x` be a point of `X` and let `y` be a point of the reduced closure
of `{x}` whose local ring in `X` has `(S₁)` formal fibres. Then every associated prime `𝔭` of the
completion `𝒪^∧_{closure {x}, y}` satisfies `dim(𝒪^∧_{closure {x}, y} / 𝔭) ≥ 2` exactly when
`dim(𝒪_{closure {x}, y}) ≥ 2`. -/
theorem two_le_ringKrullDim_quotient_completedStalk_iff_two_le_ringKrullDim_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : Scheme.IsUniversallyCatenary X) (x : X)
    (y : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme)
    (hFibres : ∀ q : PrimeSpectrum (X.presheaf.stalk
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι y)),
      HasSerreCondition (X.completedLocalRing ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set X))).subschemeι y)
        ⊗[X.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set X))).subschemeι y)]
          q.asIdeal.ResidueField) 1) :
    (∀ p : Ideal ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme.completedLocalRing y),
      IsAssociatedPrimeStacks ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subscheme.completedLocalRing y)
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subscheme.completedLocalRing y) p →
        2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subscheme.completedLocalRing y ⧸ p)) ↔
      2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk y) := by
  obtain ⟨hDom, hNoeth, hUC⟩ :=
    isDomain_isNoetherianRing_isUniversallyCatenary_stalk_vanishingIdeal_closure hX x y
  have := hDom
  have := hNoeth
  exact le_ringKrullDim_quotient_adicCompletion_iff_of_surjective
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.stalkMap y).hom)
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.stalkMap_surjective y) hUC hFibres 2

/-- **[Stacks, Tag 0AWB].** Let `j : U ⟶ X` be an open immersion with `X` locally Noetherian and
universally catenary, and suppose the formal fibres of `𝒪_{X, z}` satisfy `(S₁)` for every point
`z` outside `U`. For a coherent `𝒪_U`-module `ℱ`, the direct image `j_* ℱ` is coherent exactly
when `dim(𝒪_{closure {x}, z}) ≥ 2` for every associated point `x` of `ℱ` and every point `z` of
the reduced closure of `{j x}` lying outside `U`.

The associated-prime criterion of [Stacks, Tag 0BK3] is supplied by
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`, and
`two_le_ringKrullDim_quotient_completedStalk_iff_two_le_ringKrullDim_stalk` collapses its
condition pointwise to the dimension of the local ring itself. -/
@[stacks 0AWB, ega "IV 5.11.4" "(ii)"]
theorem isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    {F : U.Modules} [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∉ j.opensRange →
      ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent ↔
      ∀ x : U, x ∈ Stacks.Divisors.associatedPoints F →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subschemeι y ∉ j.opensRange →
          2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j x} : Set X))).subscheme.presheaf.stalk y) := by
  rw [isCoherent_pushforward_iff_forall_two_le_ringKrullDim j F]
  refine forall_congr' fun x => forall_congr' fun _ => forall_congr' fun y =>
    forall_congr' fun hy => ?_
  exact two_le_ringKrullDim_quotient_completedStalk_iff_two_le_ringKrullDim_stalk hX (j x) y
    (hFibres _ hy)

end AlgebraicGeometry

end
