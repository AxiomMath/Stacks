module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CompletedStalkAssociatedDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCompletionObstruction

/-!
# Clause (2) of Tag 0BK3 at every point, with its own dimension bound

Let `j : U ⟶ X` be an open immersion of locally Noetherian schemes with complement `Z`, let `F`
be a quasi-coherent `𝒪_U`-module and let `x` be a point of `U`. Clause (2) of
[Stacks, Tag 0BK3] reads: for every `x ∈ Ass(F)`, every `z ∈ Z ∩ closure {x}` and every
associated prime `𝔭` of the completion `𝒪^∧_{closure {x}, z}` one has
`dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) ≥ 2`.

The existing site `not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk`, in this same
namespace, states the implication (1) ⇒ (2) in contrapositive form at a single triple and with
`dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) = 1` rather than the `≤ 1` that negating clause (2) gives. This
file removes both restrictions: the dimension hypothesis becomes `≤ 1`, which is what the
negation of the clause supplies, and the conclusion is then run in the forward direction, so
that the dimension bound is asserted at *every* triple at once rather than one being fixed in
advance.

The remaining distance to the unqualified implication is the monomorphism
`φ : i_{x,*} 𝒪_{W_x} ⟶ F`, which stands in for the source's hypothesis `x ∈ Ass(F)`; the module
documentation of `PointClosureAssociatedPoints`, in the same directory, records what is still
missing there.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.CoherentPushforwardCriterion`.

* `not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk_le_one`: the contrapositive at
  a single triple, for an associated quotient of dimension *at most* one.
* `two_le_ringKrullDim_quotient_completedStalk_of_isCoherent_pushforward`: clause (2) of
  [Stacks, Tag 0BK3] itself — coherence of `j_* F` forces
  `dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) ≥ 2` at every `(x, z, 𝔭)`.

## Implementation notes

The dimension hypothesis is weakened by a case split on whether `𝔭` is the maximal ideal of
`𝒪^∧_{closure {x}, z}`, the two cases being genuinely different.

If it is not, then `one_le_ringKrullDim_quotient_of_ne_maximalIdeal` gives
`1 ≤ dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭)`, so `≤ 1` is in fact `= 1` and the existing form of the
statement applies verbatim; nothing about the geometry is re-examined.

If it is, the hypothesis `𝔭 ∈ Ass(𝒪^∧_{closure {x}, z})` is already contradictory and coherence
of `j_* F` is never used. What is needed is that `z` is not the generic point of
`closure {j x}`, which holds because the generic point is `j x`, a point of the image of `j`,
while `z` is assumed outside it. That is supplied in the form
`not_isAssociatedPrimeStacks_maximalIdeal_completedStalk` consumes — a nonempty open of
`closure {j x}` missing `z` — by the open immersion `j'` of `W_x` into `closure {j x}` given by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure`: its image
contains the image of the generic point of `W_x`, and misses `z` because a point of that image
has image in `X` lying in the image of `j`.

The step from `¬ (d ≤ 1)` to `2 ≤ d` for `d : WithBot ℕ∞` is `Order.succ_le_of_lt`.

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

/-- **[Stacks, Tag 0BK3], the implication (1) ⇒ (2), in contrapositive form at a single point,
for an associated quotient of dimension at most one.** Let `j : U ⟶ X` be an open immersion of
schemes with `X` locally Noetherian, let `F` be a quasi-coherent `𝒪_U`-module and let `x` be a
point of `U`. Suppose there is a monomorphism `i_{x,*} 𝒪_{W_x} ⟶ F`, and suppose `z` is a point
of the reduced closure of `{j x}` whose image in `X` lies outside `U` such that the completion
`𝒪^∧_{closure {x}, z}` has an associated prime `𝔭` with
`dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) ≤ 1`. Then `j_* F` is not coherent.

This is the failure of clause (2) of the source at `x` and `z` obstructing clause (1), with the
dimension hypothesis exactly as the negation of that clause delivers it. The monomorphism still
replaces the source's `x ∈ Ass(F)`. -/
@[stacks 0BK3 "(1) implies (2), contrapositive at one point, given a monomorphism from \
the structure sheaf of the point closure", ega "IV 5.11.4" "necessity"]
theorem not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk_le_one {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (x : U)
    {F : U.Modules} [F.IsQuasicoherent]
    (φ : pointClosureStructureSheaf x ⟶ F) [Mono φ]
    {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set X)))
    (z : I.subscheme) (hz : I.subschemeι z ∉ j.opensRange)
    {p : PrimeSpectrum (I.subscheme.completedLocalRingCat z)}
    (hp : IsAssociatedPrimeStacks (I.subscheme.completedLocalRingCat z)
      (I.subscheme.completedLocalRingCat z) p.asIdeal)
    (hdim : ringKrullDim (I.subscheme.completedLocalRingCat z ⧸ p.asIdeal) ≤ 1) :
    ¬ ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  subst hI
  have := p.isPrime
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure _
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure _
  rcases eq_or_ne p.asIdeal (maximalIdeal ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme.completedLocalRingCat z)) with hmax | hmax
  · -- The maximal ideal is never associated: `z` is not the generic point of `closure {j x}`.
    obtain ⟨j', hj', comm⟩ := Scheme.IdealSheafData.exists_isOpenImmersion_pointClosure j x
    have := hj'
    have hzV : z ∉ j'.opensRange := by
      rintro ⟨w, hw⟩
      refine hz ?_
      have hcomm : (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({j x} : Set X))).subschemeι (j' w) =
          j ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subschemeι w) := by
        simpa using congrArg (fun g : _ ⟶ X => g.base w) comm
      rw [← hw, hcomm]
      exact ⟨_, rfl⟩
    have : Nonempty j'.opensRange.toScheme :=
      ⟨⟨j' (genericPoint (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme), ⟨_, rfl⟩⟩⟩
    exact absurd (hmax ▸ hp) (not_isAssociatedPrimeStacks_maximalIdeal_completedStalk hzV)
  · exact not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk j x φ rfl z hz hp
      (le_antisymm hdim (one_le_ringKrullDim_quotient_of_ne_maximalIdeal p.asIdeal hmax))

/-- **[Stacks, Tag 0BK3], the implication (1) ⇒ (2).** Let `j : U ⟶ X` be an open immersion of
schemes with `X` locally Noetherian and let `F` be a quasi-coherent `𝒪_U`-module whose direct
image `j_* F` is coherent. Then for every point `x` of `U` admitting a monomorphism
`i_{x,*} 𝒪_{W_x} ⟶ F`, every point `z` of the reduced closure of `{j x}` whose image in `X` lies
outside `U`, and every associated prime `𝔭` of the completion `𝒪^∧_{closure {x}, z}`, one has
`dim(𝒪^∧_{closure {x}, z} ⧸ 𝔭) ≥ 2`.

This is clause (2) of the source, asserted at every triple rather than at one fixed in advance,
and with the source's own dimension bound. The monomorphism replaces the source's
`x ∈ Ass(F)`, which enters the argument only through the map it produces; it is the one
hypothesis of the source's statement that is not yet discharged. -/
@[stacks 0BK3 "(1) implies (2), given a monomorphism from the structure sheaf of the point \
closure", ega "IV 7.2.3" "b) => c)", ega "IV 5.11.4" "necessity", ega "IV 7.2.2" "a) => b)"]
theorem two_le_ringKrullDim_quotient_completedStalk_of_isCoherent_pushforward
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    {F : U.Modules} [F.IsQuasicoherent]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) :
    ∀ (x : U) (φ : pointClosureStructureSheaf x ⟶ F), Mono φ →
      ∀ I : X.IdealSheafData,
        I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set X)) →
        ∀ z : I.subscheme, I.subschemeι z ∉ j.opensRange →
          ∀ p : PrimeSpectrum (I.subscheme.completedLocalRingCat z),
            IsAssociatedPrimeStacks (I.subscheme.completedLocalRingCat z)
              (I.subscheme.completedLocalRingCat z) p.asIdeal →
            2 ≤ ringKrullDim (I.subscheme.completedLocalRingCat z ⧸ p.asIdeal) := by
  intro x φ hφ I hI z hz p hp
  have := hφ
  have key : ¬ ringKrullDim (I.subscheme.completedLocalRingCat z ⧸ p.asIdeal) ≤ 1 := fun hdim =>
    not_isCoherent_pushforward_of_isAssociatedPrime_completedStalk_le_one j x φ hI z hz hp hdim hF
  exact Order.succ_le_of_lt (not_le.mp key)

end Stacks.AlgebraicGeometry.CoherentPushforwardCriterion

end
