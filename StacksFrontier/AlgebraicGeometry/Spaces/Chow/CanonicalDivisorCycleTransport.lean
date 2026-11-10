module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SectionOrderTransport

/-!
# The Weil divisor of a meromorphic section along isomorphisms

In Situation 0EDT let `X/B` be good and integral of δ-dimension `n`, let `ℒ` be an invertible
`𝒪_X`-module and `s` a regular meromorphic section of `ℒ`, with Weil divisor
`div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z] ∈ Z_{n-1}(X)` of Stacks 0EQE, part (1), at the canonical ratios
of Stacks 0EPR (`AlgebraicGeometry.Space.canonicalDivisorCycle`). This file records that the
cycle is unchanged by the two operations that identify one presentation of `(X, ℒ, s)` with
another:

* an isomorphism of modules `α : ℒ ≅ ℒ'` carries `s` to `α(s)` with `div_{ℒ'}(α(s)) = div_ℒ(s)`;
* an isomorphism of algebraic spaces `φ : X ≅ X'` carries the divisor of the pullback `φ^*s'` of
  a regular meromorphic section `s'` of an invertible `𝒪_{X'}`-module `ℒ'` to the divisor of
  `s'`: `φ_* div_{φ^*ℒ'}(φ^*s') = div_{ℒ'}(s')`.

Both are coefficientwise consequences of the invariance of the order of vanishing (names below
are in the namespace `AlgebraicGeometry.Space`),
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap_of_iso` and
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_pullbackMeromorphicSection_of_iso`.

## Main results

* `canonicalDivisorCycle_sectionsMap_of_iso`: the Weil divisor is invariant under an isomorphism
  of modules.
* `cycleClosedPushforward_canonicalDivisorCycle_pullbackMeromorphicSection_of_iso`: the
  pushforward of the divisor of a pulled-back section along an isomorphism of algebraic spaces
  is the divisor of the section.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sX' : X' ⟶ D.space) (hX' : D.IsGood sX')
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (hint' : IsIntegralSpace D.site D.base D.base_mem X')

/-- The generic Henselian local rings of the prime divisors of a good integral space are
nontrivial, Noetherian and of Krull dimension at most one. -/
private theorem generic_henselian_local_rings
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X) :
    (∀ W : PrimeDivisor D.site D.base D.base_mem X, Nontrivial ↥(W.genericHenselianLocalRing
      D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem X, IsNoetherianRing ↥(W.genericHenselianLocalRing
      D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem X, Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing
      D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX))) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX),
    fun W => W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX),
    fun W => W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)⟩

/-- **The Weil divisor of a section is invariant under an isomorphism of modules.** For an
isomorphism `α : ℒ ≅ ℒ'` of invertible modules on a good integral algebraic space and a regular
meromorphic section `s` of `ℒ`, the Weil divisor of `α(s)` is the Weil divisor of `s`. -/
theorem canonicalDivisorCycle_sectionsMap_of_iso
    (L L' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (hL' : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L') (α : L ≅ L')
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalDivisorCycle D sX hX hint L' hL'
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap D.site D.base D.base_mem X hX.1
          α.hom) s)
        (isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem X hX.1 α s hs)
        hn =
      canonicalDivisorCycle D sX hX hint L hL s hs hn := by
  obtain ⟨_, _, _⟩ := generic_henselian_local_rings D sX hX hint
  refine Subtype.ext (funext fun Z => ?_)
  change divisorCycleCoefficients D sX hX _ L' _ _ Z = divisorCycleCoefficients D sX hX _ L s _ Z
  unfold divisorCycleCoefficients
  split_ifs with h
  · exact PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap_of_iso
      D.site D.base D.base_mem (X := ⟨X, hX.1⟩) (isDecentSpace_of_isGood D sX hX) _ hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L L' hL hL' α s hs
  · rfl

/-- **The Weil divisor of a section along an isomorphism of algebraic spaces.** Let
`φ : X ≅ X'` be an isomorphism of good integral algebraic spaces of δ-dimension `n`, `ℒ'` an
invertible `𝒪_{X'}`-module and `s'` a regular meromorphic section of `ℒ'`. Then `φ` carries the
Weil divisor of the pullback `φ^*s'`, a regular meromorphic section of `φ^*ℒ'`, to the Weil
divisor of `s'`:

`φ_* div_{φ^*ℒ'}(φ^*s') = div_{ℒ'}(s')`. -/
theorem cycleClosedPushforward_canonicalDivisorCycle_pullbackMeromorphicSection_of_iso
    (φ : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅ ⟨X', hX'.1⟩)
    (M' : Modules.{u, u} D.site D.base D.base_mem X' hX'.1)
    (hM' : IsInvertibleModule (B := D.site) ⟨X', hX'.1⟩ M')
    (s' : MeromorphicSection.{u, u} D.site D.base D.base_mem X' hX'.1 M')
    (hs' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X' hX'.1 M' s') {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hn' : deltaDimensionClosed D sX' hX' Set.univ isClosed_univ = (n : EInt)) :
    cycleClosedPushforward D hX'.1 hX.1 (isDecentSpace_of_isGood D sX' hX')
        (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom.hom)
        (canonicalDivisorCycle D sX hX hint ((modulePullback D.site D.base D.base_mem φ.hom).obj M')
          (modulePullbackInvertible φ.hom M' hM')
          (pullbackMeromorphicSection D.site D.base D.base_mem φ.hom M'
            (pullbacksMeromorphicSections_of_iso D.site D.base D.base_mem φ) s')
          (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem φ.hom
            (pullbacksMeromorphicSections_of_iso D.site D.base D.base_mem φ) M'
            (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM') s' hs') hn).1 =
      (canonicalDivisorCycle D sX' hX' hint' M' hM' s' hs' hn').1 := by
  obtain ⟨_, _, _⟩ := generic_henselian_local_rings D sX hX hint
  obtain ⟨_, _, _⟩ := generic_henselian_local_rings D sX' hX' hint'
  let e : X ≅ X' := (ObjectProperty.ι _).mapIso φ
  funext Z'
  obtain ⟨Z, rfl⟩ := (IntegralClosedSubspace.equivOfIso _ _ _ hX.1 hX'.1
    (isDecentSpace_of_isGood D sX hX) (isDecentSpace_of_isGood D sX' hX') e).surjective Z'
  rw [IntegralClosedSubspace.equivOfIso_apply, cycleClosedPushforward_apply_pushforward,
    ← IntegralClosedSubspace.equivOfIso_apply]
  refine (divisorCycleCoefficients_equivOfIso_of_orderOfVanishingSection_eq D sX hX sX' hX'
    (isDecentSpace_of_isGood D sX hX) (isDecentSpace_of_isGood D sX' hX') e _ _ _ _ _ _
    (fun P P' hP => ?_) Z).symm
  exact (PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_pullbackMeromorphicSection_of_iso
    D.site D.base D.base_mem φ (isDecentSpace_of_isGood D sX hX)
    (isDecentSpace_of_isGood D sX' hX') hint hint'
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX' hX') M' hM' s' hs' P P' hP).symm

end AlgebraicGeometry.Space

end
