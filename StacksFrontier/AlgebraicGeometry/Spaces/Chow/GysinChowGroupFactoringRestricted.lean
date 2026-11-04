module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoringCanonical

/-!
# The Gysin factoring assertion reduced to a vanishing on the restricted locus

In the situation of Stacks 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be as in
Definition 0ER1.  **Stacks 0ERA** asserts that the Gysin homomorphism of Stacks 0ER1 factors
through rational equivalence, giving `i^* : CH_{k+1}(X) ⟶ CH_k(E)`;
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoringCanonical` reduces that
assertion, at the canonical embeddings of Stacks 0ENK on both sides, to the single hypothesis
`hgys` about one member `V ⊆ X` of the presenting family of a cycle rationally equivalent to
zero: that `i^*((i_V)_* d)` is *presented* as a locally finite sum of principal divisor cycles
over integral closed subspaces of `E` lying in `i^{-1}|V|`.

This file lowers that hypothesis to the form in which the source's two cases produce it.  The
source does not produce a presentation; it produces an equality in a Chow group of the locus
`E ∩ V`, by Lemma 0ER5 at `i_V : V ⟶ X` followed by Lemma 0ER9 (case `E ≠ V`) or Lemma 0EQY
(case `E = V`).  An equality with zero in `CH_k(E ∩ V)` says exactly that a cycle on `E ∩ V` is
rationally equivalent to zero there, and
`exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward`
turns that into a presentation on `E` whose members lie in `|E ∩ V|`.  So the presentation is a
consequence, not an extra obligation, and the remaining input is a vanishing on a closed subspace
of `E` contained in `i^{-1}|V|`.

## Main results

* `gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_restrictedRationalEquivalence`:
  the Gysin cycle map carries cycles rationally equivalent to zero at the canonical embeddings to
  cycles rationally equivalent to zero at the canonical embeddings, as soon as for one integral
  closed subspace `V ⊆ X` of δ-dimension `k + 2` and one principal divisor cycle `d` on `V` at
  the canonical embeddings there are a closed subspace `F ⊆ E` with `|F| ⊆ i^{-1}|V|` and a cycle
  `γ ∈ Z_k(F)` rationally equivalent to zero at the canonical embeddings with
  `i^*((i_V)_* d) = (i_F)_* γ`.

## Implementation notes

### The hypothesis in the source's proof

The hypothesis is the conjunction of the two things the source's proof of the reduced case
delivers:

* the comparison `i^*(i_V)_* = (i_F)_*(i_F')^*` of Lemma 0ER5 applied to the closed immersion
  `i_V : V ⟶ X`, which rewrites `i^*((i_V)_* d)` as a pushforward from the locus
  `F = E ∩ V ⊆ E`, whence the containment `|F| ⊆ i^{-1}|V|`;
* the vanishing of the class of `(i_F')^* d` in `CH_k(F)`, which is Lemma 0ER9 when `F ≠ V` —
  there `(i_F')^* div_V(f) = c₁(𝒪_F) ∩ [F]_{n-1}` and capping with the trivial invertible module
  is zero, `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_tensorUnit_eq_zero` — and
  Lemma 0EQY when `F = V`, where the vanishing is
  `canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
  at exactly the predicate the hypothesis receives.

Both are stated in a Chow group, which is where the source states them, and that is the point of
this reduction: the presentation-level hypothesis `hgys` of
`gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor`
cannot be read off either of them directly, whereas the vanishing can.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E k)

/-- **The factoring assertion of Stacks 0ERA follows from a vanishing on the restricted locus.**
Suppose that for every integral closed subspace `V ⊆ X` of δ-dimension `k + 2` and every
`(k+1)`-cycle `d` on `V` which is a principal divisor cycle in the canonical reading of part (1)
of Stacks 0EQ6, there are a closed subspace `F ⊆ E` whose point set lies in `i^{-1}|V|` and a
`k`-cycle `γ` on `F`, rationally equivalent to zero on `F` in the canonical reading, with

`i^*((i_V)_* d) = (i_F)_* γ`.

Then the Gysin cycle map carries every cycle rationally equivalent to zero on `X` at the
canonical embeddings to a cycle rationally equivalent to zero on `E` at the canonical embeddings.
-/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_restrictedRationalEquivalence
    (hres : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ p) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d →
          ∃ (F : ClosedSubspaces D.site D.base D.base_mem E.1.toFunctor)
            (γ : CycleGroup D (F.1.ι ≫ (E.1.ι ≫ p)) k),
            subspacePointSet D.site D.base D.base_mem E.1.toFunctor F.1 ⊆
                pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
                  subspacePointSet D.site D.base D.base_mem X V.subspace ∧
              IsRationallyEquivalentToZeroCanonical.{v} D (F.1.ι ≫ (E.1.ι ≫ p))
                  (isGood_ι_of_isClosedSubspace D (E.1.ι ≫ p) hE F.1 F.2) k γ ∧
                gysinCycleMap D p E hE k rule
                    (integralClosedSubspacePushforward D p hp V (k + 1) d) =
                  cycleGroupClosedPushforward D hE.1 F.2.1
                    (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) F.2.2 (E.1.ι ≫ p) hE.2.2
                    (F.1.ι ≫ (E.1.ι ≫ p)) rfl k γ) :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule := by
  refine gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor
    D p hp E hE k rule fun V hVdim d hd => ?_
  obtain ⟨F, γ, hFsub, hγ, hgys⟩ := hres V hVdim d hd
  obtain ⟨K, U, hUfin, e, hUsub, hUdim, hUprin, hsum⟩ :=
    exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward
      D (E.1.ι ≫ p) hE F.1 F.2 k hγ
  exact ⟨K, U, hUfin, e, fun l => (hUsub l).trans hFsub, hUdim, hUprin, hgys.trans hsum⟩

end AlgebraicGeometry.Space

end
