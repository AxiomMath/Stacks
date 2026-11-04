module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSectionCanonical

/-!
# Capping a principal divisor with the first Chern class, in the Chow group at the canonical
embeddings

In Situation 0EDT let `X/B` be good and **integral** with `dim_δ(X) = n`, let `ℒ` be an
invertible `𝒪_X`-module and let `f ∈ R(X)^*`.  Then

`c₁(ℒ) ∩ div(f) = 0`  in  `CH_{n-2}(X)`,

with `CH_{n-2}(X)` the Chow group `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6
read at the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisor` proves the same
vanishing in `AlgebraicGeometry.Space.chowGroup`, the quotient by the cycles rationally
equivalent to zero in the reading in which those embeddings are quantified existentially with no
compatibility condition.  That quotient is in general a proper quotient of the source's
`CH_{n-2}(X)`, so the vanishing there is weaker.  It is also not enough for the factoring
statements of Stacks 0EQY and Stacks 0ERA: the cycle whose cap product has to be killed is a
summand of a cycle rationally equivalent to zero, and if rational equivalence is read with the
embeddings quantified then the summand is a principal divisor only for *some* family of ring
maps, for which no rescaling
(`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`,
whose hypothesis is discharged only at the canonical embedding) and hence no reduction to a
difference of Weil divisors is available.  Descending from
`AlgebraicGeometry.Space.chowGroupCanonical` is the route that does work, and it needs the
conclusion in `AlgebraicGeometry.Space.chowGroupCanonical` as well; that is what this file
supplies.

## Main results

* `Space.canonicalFirstChernCapCanonical_canonicalDivisorCycleAt_tensorUnit_eq_zero`:
  `c₁(ℒ) ∩ div_{𝒪_X}(σ) = 0` for a regular meromorphic section `σ` of the structure sheaf.
* `Space.canonicalFirstChernCapCanonical_canonicalPrincipalDivisorCycleAt_eq_zero`:
  `c₁(ℒ) ∩ div(f) = 0`.
* `Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`:
  the same for any cycle which is a principal divisor in the canonical reading of part (1) of
  Stacks 0EQ6 — the form in which the summands of a rational equivalence of
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical` arrive.

## Implementation notes

The three proofs are those of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisor` with Stacks 0EQX and
Stacks 0EQK taken in their canonical form,
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_divisor_comm` and
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_tensorUnit_eq_zero`.  The presentation
of `div(f)` as a difference of Weil divisors of two regular meromorphic sections of `𝒪_X` is an
identity of *cycles*, `AlgebraicGeometry.Space.exists_canonicalPrincipalDivisorCycleAt_eq_sub`,
so it is reused unchanged.

No tag is registered here.  Stacks 0EQY asks for the factorization on a good — not necessarily
integral — algebraic space and for an arbitrary cycle rationally equivalent to zero; what is
proved here is the case its proof reduces to.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQX](https://stacks.math.columbia.edu/tag/0EQX)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] modulesMonoidalCategory

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)

/-- **`c₁(ℒ) ∩ div_{𝒪_X}(σ) = 0` in the Chow group at the canonical embeddings.**  For `X/B`
good and integral with `dim_δ(X) = n`, `ℒ` invertible and `σ` a regular meromorphic section of
the structure sheaf `𝒪_X`.

The source's own final step: pick a nonzero meromorphic section `t` of `ℒ` (Stacks 0EPQ); Stacks
0EQX at the canonical embeddings gives `c₁(ℒ) ∩ div_{𝒪_X}(σ) = c₁(𝒪_X) ∩ div_ℒ(t)`, and Stacks
0EQK at the canonical embeddings makes that zero. -/
theorem canonicalFirstChernCapCanonical_canonicalDivisorCycleAt_tensorUnit_eq_zero
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) σ)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX L hL (n - 2)
      (canonicalDivisorCycleAt D sX hX hint
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
        (isInvertibleModule_tensorUnit hX) σ hσ
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) = 0 := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  obtain ⟨t, ht⟩ :=
    exists_meromorphicSection_ne_zero D.site D.base D.base_mem hX.1 hint hN L hL
  have hσ0 : σ ≠ 0 := ne_zero_of_isRegularMeromorphicSection D.site D.base D.base_mem hX.1 hint
    hN (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) σ hσ
  exact (canonicalFirstChernCapCanonical_divisor_comm D sX hX hint
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (isInvertibleModule_tensorUnit hX) σ L hL hσ0 t ht hn).trans
    (canonicalFirstChernCapCanonical_tensorUnit_eq_zero hX (n - 2) _)

/-- **`c₁(ℒ) ∩ div(f) = 0` in the Chow group at the canonical embeddings**, for `X/B` good and
integral with `dim_δ(X) = n`, `ℒ` an invertible `𝒪_X`-module and `f ∈ R(X)^*`.

`div(f)` is the difference of the Weil divisors of two regular meromorphic sections of `𝒪_X`
(`AlgebraicGeometry.Space.exists_canonicalPrincipalDivisorCycleAt_eq_sub`, an identity of
cycles), and the cap product kills each of them. -/
theorem canonicalFirstChernCapCanonical_canonicalPrincipalDivisorCycleAt_eq_zero
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX L hL (n - 2)
      (canonicalPrincipalDivisorCycleAt D sX hX hint f
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) = 0 := by
  obtain ⟨σ, τ, hσ, hτ, heq⟩ := exists_canonicalPrincipalDivisorCycleAt_eq_sub D sX hX hint f
    (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)
  rw [heq, map_sub,
    canonicalFirstChernCapCanonical_canonicalDivisorCycleAt_tensorUnit_eq_zero D sX hX hint L hL σ
      hσ hn,
    canonicalFirstChernCapCanonical_canonicalDivisorCycleAt_tensorUnit_eq_zero D sX hX hint L hL τ
      hτ hn,
    sub_zero]

/-- **The cap product of Stacks 0EQJ kills a principal divisor cycle on a good integral algebraic
space, in the Chow group at the canonical embeddings.**  If `X/B` is good and integral with
`dim_δ(X) = n` and `c ∈ Z_{n-1}(X)` is a principal divisor cycle in the canonical reading of
part (1) of Stacks 0EQ6, then `c₁(ℒ) ∩ c = 0` in `CH_{n-2}(X)`.

This is the input the proof of Stacks 0EQY needs on each member `W_j` of the family presenting a
rational equivalence of `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`: that
predicate hands over exactly `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood` on each
`W_j`, which is what is asked for here, and the conclusion is in the Chow group the same
predicate defines. -/
theorem canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (c : CycleGroup D sX (n - 2 + 1))
    (hc : IsPrincipalDivisorCycleOfGood D sX hX hint (n - 2 + 1) c) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX L hL (n - 2) c = 0 := by
  obtain ⟨g, hg, hcoe⟩ := hc
  rw [show c = canonicalPrincipalDivisorCycleAt D sX hX hint hg.unit
      (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn) from Subtype.ext hcoe]
  exact canonicalFirstChernCapCanonical_canonicalPrincipalDivisorCycleAt_eq_zero D sX hX hint L hL
    _ hn

end AlgebraicGeometry.Space

end
