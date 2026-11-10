module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RegularMeromorphicSectionDivisorLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularMeromorphicSectionNeZero

/-!
# The Weil divisor associated to an invertible sheaf on an integral good space

In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)` and let `ℒ` be an
invertible `𝒪_X`-module. **Stacks 0EQE** defines

1. for a nonzero meromorphic section `s` of `ℒ`, the *Weil divisor associated to `s`*, the
   `(n-1)`-cycle `div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z]` of Stacks 0EPU, which is an `(n-1)`-cycle
   because a prime divisor has δ-dimension `n - 1` (Stacks 0EPZ);
2. the *Weil divisor associated to `ℒ`*, `c₁(ℒ) ∩ [X] = [div_ℒ(s)] ∈ CH_{n-1}(X)` for any
   nonzero meromorphic section `s`, which is well defined by Stacks 0EPT.

Both are stated under exactly those hypotheses, with the following ingredients:

* `ord_{Z,ℒ}(s)` is read at the generator `s_ξ` of `ℒ` at the generic point of `Z` that Stacks
  0EPR constructs, `AlgebraicGeometry.Space.canonicalLocalRatioFamily`, and the three
  ring-theoretic properties of `𝒪^h_{X,ξ}` it needs are those of Stacks 0ENK, proved from
  integrality and local Noetherianity;
* local finiteness of the prime divisors with `ord_{Z,ℒ}(s) ≠ 0` is Stacks 0EPS for the section
  `s`, `AlgebraicGeometry.Space.locallyFinite_canonicalDivisorCoefficients_ne_zero`;
* the dimension function of Stacks 0EDN is
  `AlgebraicGeometry.Space.exists_dimensionFunction_deltaValue_of_isGood`;
* `CH_{n-1}(X)` is the Chow group `AlgebraicGeometry.Space.chowGroup` of Stacks 0EQ6;
* the class of `div_ℒ(s)` does not depend on `s`: two nonzero meromorphic sections differ by an
  invertible rational function `f` (Stacks 0EPT,
  `AlgebraicGeometry.Space.exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul`), so
  their divisors differ by `div(f)`, which is rationally equivalent to zero
  (`isRationallyEquivalentToZero_of_coe_eq_canonicalPrincipalCycleCoefficients`).

The hypothesis on the section is the source's, `s ≠ 0`. The order of vanishing of Stacks 0EPR
and Stacks 0EPS, 0EPT are stated for *regular* meromorphic sections, those for which
multiplication `𝒦_X ⟶ 𝒦_X(ℒ)` by the section is injective; on a locally Noetherian integral
space these are exactly the nonzero ones,
`AlgebraicGeometry.Space.isRegularMeromorphicSection_iff_ne_zero`, which is the identification
the source makes through Stacks 0ENA.

## Main definitions

* `AlgebraicGeometry.Space.sectionWeilDivisor`: **Stacks 0EQE, part (1)**, `div_ℒ(s)` in
  `Z_{n-1}(X)`.
* `AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf`: **Stacks 0EQE, part (2)**,
  `c₁(ℒ) ∩ [X] ∈ CH_{n-1}(X)`.

## Main results

* `AlgebraicGeometry.Space.sectionWeilDivisor_apply_toIntegralClosedSubspace`: the coefficient
  of `div_ℒ(s)` at a prime divisor `Z` is `ord_{Z,ℒ}(s)`.
* `AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`: **Stacks 0EQE, part (2)**,
  `c₁(ℒ) ∩ [X]` is the class of `div_ℒ(s)` for *every* nonzero meromorphic section `s`.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)

/-- The coefficients `Z ↦ ord_{Z,ℒ}(s)` of the Weil divisor of a meromorphic section `s` of an
invertible module on an integral good space, indexed by the integral closed subspaces of `X`
(zero away from the prime divisors), the order of vanishing being read at the generators `s_ξ`
of Stacks 0EPR. -/
def invertibleDivisorCoefficients
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).nontrivial
  letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).isNoetherianRing
  letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).krullDimLE
  divisorCycleCoefficients D sX hX hint.2.1 L s
    (canonicalLocalRatioFamily D.site D.base D.base_mem hX.1 hint.2.1 L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX))

/-- A nonzero meromorphic section of an invertible module on an integral good space is regular. -/
private theorem isRegularMeromorphicSection_of_ne_zero
    (hint : IsIntegralSpace D.site D.base D.base_mem X) (hL : IsInvertibleSheaf D sX hX L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) (hs : s ≠ 0) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s :=
  (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hX.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s).2 hs

/-- For a nonzero meromorphic section `s`, the coefficients of `div_ℒ(s)` form an `(n-1)`-cycle
on `X`. -/
theorem invertibleDivisorCoefficients_mem_cyclesOfDimension {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0) :
    invertibleDivisorCoefficients D sX hX hint L hL s ∈ cyclesOfDimension D sX (n - 1) := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  let E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint hN
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue_of_isGood D sX hX
  exact divisorCycleCoefficients_mem_cyclesOfDimension D sX hX hint.2.1 L s _
    (locallyFinite_canonicalDivisorCoefficients_ne_zero D.site D.base D.base_mem hX.1 hint.2.1
      hint hN L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s
      (isRegularMeromorphicSection_of_ne_zero D sX hX L hint hL s hs))
    hint d hd hn

/-- **Stacks 0EQE, part (1).** In Situation 0EDT let `X/B` be good, let `X` be integral with
`n = dim_δ(X)` and let `ℒ` be an invertible `𝒪_X`-module. The *Weil divisor associated to a
nonzero meromorphic section `s` of `ℒ`*, the `(n-1)`-cycle

  `div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z] ∈ Z_{n-1}(X)`,

the sum over the prime divisors `Z` of `X`, `ord_{Z,ℒ}(s)` being the order of vanishing of
Stacks 0EPR (`AlgebraicGeometry.Space.sectionWeilDivisor_apply_toIntegralClosedSubspace`). -/
@[stacks 0EQE "part (1): div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z] as an element of Z_{n-1}(X), for X/B \
good and integral with n = dim_δ(X), ℒ invertible and s a nonzero meromorphic section; \
ord_{Z,ℒ}(s) at the generators of Stacks 0EPR, local finiteness by Stacks 0EPS for the section s, \
the δ-dimension n-1 of a prime divisor by Stacks 0EPZ with the dimension function of Stacks \
0EDN, and the properties of the henselian local rings by Stacks 0ENK, all proved"]
def sectionWeilDivisor {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0) :
    CycleGroup D sX (n - 1) :=
  ⟨invertibleDivisorCoefficients D sX hX hint L hL s,
    invertibleDivisorCoefficients_mem_cyclesOfDimension D sX hX hint L hL hn s hs⟩

/-- The coefficients of `div_ℒ(s)`. -/
@[simp]
theorem coe_sectionWeilDivisor {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0) :
    (sectionWeilDivisor D sX hX hint L hL hn s hs :
        IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) =
      invertibleDivisorCoefficients D sX hX hint L hL s :=
  rfl

/-- **Stacks 0EQE, part (1), the coefficients.** The coefficient of `div_ℒ(s)` at a prime
divisor `Z` is the order of vanishing `ord_{Z,ℒ}(s)` of Stacks 0EPR, read at the generator
`s_ξ` that Stacks 0EPR constructs at the generic point of `Z`. -/
theorem sectionWeilDivisor_apply_toIntegralClosedSubspace {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0)
    (Z : PrimeDivisor D.site D.base D.base_mem X) :
    letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).nontrivial
    letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).isNoetherianRing
    letI := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)).krullDimLE
    (sectionWeilDivisor D sX hX hint L hL hn s hs).1
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem hX.1 hint.2.1 Z L s
        (canonicalLocalRatioFamily D.site D.base D.base_mem hX.1 hint.2.1 L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) Z) :=
  let E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  have := E.nontrivial
  have := E.isNoetherianRing
  have := E.krullDimLE
  divisorCycleCoefficients_toIntegralClosedSubspace D sX hX hint.2.1 L s _ Z

/-- The divisors of two nonzero meromorphic sections of `ℒ` have the same class in
`CH_{n-1}(X)`. -/
theorem chowClass_sectionWeilDivisor_eq {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s s' : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0)
    (hs' : s' ≠ 0) :
    chowClass.{v} D sX hX (n - 1) (sectionWeilDivisor D sX hX hint L hL hn s hs) =
      chowClass.{v} D sX hX (n - 1) (sectionWeilDivisor D sX hX hint L hL hn s' hs') := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  let E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint hN
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨f, hf⟩ := exists_units_rationalFunctions_canonicalLocalRatio_eq_emb_mul D.site D.base
    D.base_mem hX.1 hint.2.1 hint hN L hLm s s'
    (isRegularMeromorphicSection_of_ne_zero D sX hX L hint hL s hs)
    (isRegularMeromorphicSection_of_ne_zero D sX hX L hint hL s' hs')
  refine (chowClass_eq_iff_rationallyEquivalent.{v} D sX hX (n - 1) _ _).2 ?_
  refine isRationallyEquivalentToZero_of_coe_eq_canonicalPrincipalCycleCoefficients D sX hX hint
    hn f _ (funext fun Z => ?_)
  change divisorCycleCoefficients D sX hX hint.2.1 L s _ Z -
    divisorCycleCoefficients D sX hX hint.2.1 L s' _ Z = _
  rw [divisorCycleCoefficients_sub_divisorCycleCoefficients D sX hX hint.2.1 L s s' _
    E.emb f
    (fun W => f.isUnit.map _) hf Z]
  rfl

/-- **Stacks 0EQE, part (2).** In Situation 0EDT let `X/B` be good, let `X` be integral with
`n = dim_δ(X)` and let `ℒ` be an invertible `𝒪_X`-module. The *Weil divisor associated to `ℒ`*,

  `c₁(ℒ) ∩ [X] = class of div_ℒ(s) ∈ CH_{n-1}(X)`,

for the nonzero meromorphic section `s` of `ℒ` of Stacks 0EPQ
(`AlgebraicGeometry.Space.regularMeromorphicSection`); the class does not depend on the choice
of `s` (`AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`). -/
@[stacks 0EQE "part (2): c₁(ℒ) ∩ [X] = the class of div_ℒ(s) in CH_{n-1}(X) = Z_{n-1}(X)/∼_rat \
(Stacks 0EQ6), for a nonzero meromorphic section s of ℒ, which exists by Stacks 0EPQ; it is \
the class of div_ℒ(s) for every nonzero s by chowClass_sectionWeilDivisor"]
def weilDivisorOfInvertibleSheaf {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    chowGroup.{v} D sX hX (n - 1) :=
  chowClass.{v} D sX hX (n - 1)
    (sectionWeilDivisor D sX hX hint L hL hn
      (regularMeromorphicSection D.site D.base D.base_mem hX.1 hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL))
      ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hX.1 hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) _).1
        (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hX.1 hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL))))

/-- **Stacks 0EQE, part (2), well-definedness.** `c₁(ℒ) ∩ [X]` is the class of `div_ℒ(s)` in
`CH_{n-1}(X)` for *every* nonzero meromorphic section `s` of `ℒ`. -/
@[stacks 0EQE "part (2), well-definedness: the class of div_ℒ(s) in CH_{n-1}(X) is \
c₁(ℒ) ∩ [X] for every nonzero meromorphic section s, by Stacks 0EPT, the principal divisor \
div(f) of the ratio being rationally equivalent to zero in the sense of Stacks 0EQ6"]
theorem chowClass_sectionWeilDivisor {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : s ≠ 0) :
    chowClass.{v} D sX hX (n - 1) (sectionWeilDivisor D sX hX hint L hL hn s hs) =
      weilDivisorOfInvertibleSheaf.{v} D sX hX hint L hL hn :=
  chowClass_sectionWeilDivisor_eq D sX hX hint L hL hn s _ hs _

end AlgebraicGeometry.Space

end
