module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoChartGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular

/-!
# The Weil divisor of Stacks 0EQE along an isomorphism of good integral spaces

In Situation 0EDT let `e : X ≅ Y` be an isomorphism of good integral algebraic spaces over the
base, let `𝒩` be an invertible `𝒪_Y`-module and let `τ` be a regular meromorphic section of
`𝒩`.  Pushing the Weil divisor `div_{e^*𝒩}(e^*τ) ∈ Z_k(X)` of Stacks 0EQE forward along `e`
gives `div_𝒩(τ) ∈ Z_k(Y)`.

## Main definitions

* `AlgebraicGeometry.Space.algebraicSpacesIsoOfIso`: an isomorphism of functors between
  algebraic spaces, read as an isomorphism in `AlgebraicGeometry.Space.AlgebraicSpaces`.

## Main results

* `AlgebraicGeometry.Space.canonicalDivisorCycleAt_pushforwardOfIso`: the pushforward along `e`
  of `div_{e^*𝒩}(e^*τ)` is `div_𝒩(τ)`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section AlgebraicSpacesIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An isomorphism of functors whose two sides are algebraic spaces, read as an isomorphism of
the corresponding objects of `AlgebraicGeometry.Space.AlgebraicSpaces`. -/
def algebraicSpacesIsoOfIso (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (e : X ≅ Y) : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ≅ ⟨Y, hY⟩ :=
  ObjectProperty.isoMk _ e

/-- The underlying morphism of functors of `AlgebraicGeometry.Space.algebraicSpacesIsoOfIso` is
the one it was built from. -/
@[simp]
theorem algebraicSpacesIsoOfIso_hom_hom (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ Y) :
    (algebraicSpacesIsoOfIso B S hS hX hY e).hom.hom = e.hom :=
  rfl

/-- Reading `AlgebraicGeometry.Space.algebraicSpacesIsoOfIso` back as an isomorphism of functors
returns the isomorphism it was built from. -/
theorem mapIso_algebraicSpacesIsoOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ Y) :
    (ObjectProperty.ι (IsAlgebraicSpace B S hS)).mapIso
        (algebraicSpacesIsoOfIso B S hS hX hY e) = e :=
  rfl

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ Y)
    (M : Modules.{u, u} B S hS Y hY)
    (hM : IsInvertibleModule (⟨Y, hY⟩ : AlgebraicSpaces B S hS) M)
    (τ : MeromorphicSection.{u, u} B S hS Y hY M)

include hM in
/-- The inverse image `e^*𝒩` of an invertible module along an isomorphism of algebraic spaces, as
an invertible module (Stacks 0B8P). -/
theorem isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso :
    IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS)
      ((modulePullback B S hS (algebraicSpacesIsoOfIso B S hS hX hY e).hom).obj M) :=
  modulePullbackInvertible (algebraicSpacesIsoOfIso B S hS hX hY e).hom M hM

include hX hY in
/-- An isomorphism of algebraic spaces pulls back meromorphic sections, being flat. -/
theorem pullbacksMeromorphicSections_algebraicSpacesIsoOfIso :
    PullbacksMeromorphicSections B S hS e.hom :=
  pullbacksMeromorphicSections_of_flat B S hS e.hom
    (isFlat_of_isEtale B S hS
      (isEtale_hom_of_isIso B S hS (algebraicSpacesIsoOfIso B S hS hX hY e).hom))

include hM in
/-- The inverse image `e^*τ` along an isomorphism of a regular meromorphic section is a regular
meromorphic section (Stacks 0ENC, part (2)). -/
theorem isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
    (hτ : IsRegularMeromorphicSection.{u, u} B S hS Y hY M τ) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX
      ((modulePullback B S hS (algebraicSpacesIsoOfIso B S hS hX hY e).hom).obj M)
      (pullbackMeromorphicSection B S hS (algebraicSpacesIsoOfIso B S hS hX hY e).hom M
        (pullbacksMeromorphicSections_algebraicSpacesIsoOfIso B S hS hX hY e) τ) :=
  isRegularMeromorphicSection_pullbackMeromorphicSection B S hS
    (algebraicSpacesIsoOfIso B S hS hX hY e).hom
    (pullbacksMeromorphicSections_algebraicSpacesIsoOfIso B S hS hX hY e) M hM τ hτ

end AlgebraicSpacesIso

section DivisorCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (e : X ≅ Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)

include hintX hintY in
/-- **The Weil divisor of Stacks 0EQE is carried by an isomorphism of good integral spaces.**  For
`e : X ≅ Y` an isomorphism over the base of good integral algebraic spaces of δ-dimension
`k + 1`, `𝒩` an invertible `𝒪_Y`-module and `τ` a regular meromorphic section of `𝒩`,

`e_*(div_{e^*𝒩}(e^*τ)) = div_𝒩(τ)`   in   `Z_k(Y)`,

at the canonical ratios of Stacks 0EPR on both sides. -/
theorem canonicalDivisorCycleAt_pushforwardOfIso (hcomp : e.hom ≫ sY = sX) {k : ℤ}
    (hkX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hkY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    cycleGroupClosedPushforward D hY.1 hX.1 (isDecentSpace_of_isGood D sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k
        (canonicalDivisorCycleAt D sX hX hintX
          ((modulePullback D.site D.base D.base_mem
            (algebraicSpacesIsoOfIso D.site D.base D.base_mem hX.1 hY.1 e).hom).obj M)
          (isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base
            D.base_mem hX.1 hY.1 e M hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem
            (algebraicSpacesIsoOfIso D.site D.base D.base_mem hX.1 hY.1 e).hom M
            (pullbacksMeromorphicSections_algebraicSpacesIsoOfIso D.site D.base D.base_mem hX.1
              hY.1 e) τ)
          (isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
            D.site D.base D.base_mem hX.1 hY.1 e M hM τ hτ)
          hkX) =
      canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hkY := by
  classical
  have key : ∀ {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sZ : Z ⟶ D.space)
      (hZ : D.IsGood sZ) (hintZ : IsIntegralSpace D.site D.base D.base_mem Z),
      (∀ W : PrimeDivisor D.site D.base D.base_mem Z, Nontrivial ↥(W.genericHenselianLocalRing
        D.site D.base D.base_mem hZ.1 (isDecentSpace_of_isGood D sZ hZ))) ∧
      (∀ W : PrimeDivisor D.site D.base D.base_mem Z, IsNoetherianRing ↥(
        W.genericHenselianLocalRing D.site D.base D.base_mem hZ.1
          (isDecentSpace_of_isGood D sZ hZ))) ∧
      (∀ W : PrimeDivisor D.site D.base D.base_mem Z, Ring.KrullDimLE 1 ↥(
        W.genericHenselianLocalRing D.site D.base D.base_mem hZ.1
          (isDecentSpace_of_isGood D sZ hZ))) := fun sZ hZ hintZ =>
    have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sZ hZ
    ⟨fun W => W.nontrivial_genericHenselianLocalRing _ _ _ _ _ hintZ hN,
      fun W => W.isNoetherianRing_genericHenselianLocalRing _ _ _ _ _ hintZ hN,
      fun W => W.krullDimLE_genericHenselianLocalRing _ _ _ _ _ hintZ hN⟩
  have hdecX := isDecentSpace_of_isGood D sX hX
  have hdecY := isDecentSpace_of_isGood D sY hY
  have hNX := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  obtain ⟨_, _, _⟩ := key sX hX hintX
  obtain ⟨_, _, _⟩ := key sY hY hintY
  refine Subtype.ext (funext fun T => ?_)
  obtain ⟨T₀, rfl⟩ := IntegralClosedSubspace.surjective_pushforward_of_iso D.site D.base
    D.base_mem hX.1 hY.1 hdecX hdecY e T
  change cycleClosedPushforward D hY.1 hX.1 hdecY
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
      (canonicalDivisorCycleAt D sX hX hintX _ _ _ _ hkX).1 _ = _
  rw [cycleClosedPushforward_apply_pushforward]
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 T₀) = 1
  · rw [show T₀ = (T₀.toPrimeDivisor D.site D.base D.base_mem hX.1
          hcod).toIntegralClosedSubspace D.site D.base D.base_mem from
        (IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
          hX.1 T₀ hcod).symm,
      ← PrimeDivisor.toIntegralClosedSubspace_pushforwardOfIso D.site D.base D.base_mem hX.1
        hY.1 hdecY e,
      show (canonicalDivisorCycleAt D sX hX hintX _
            (isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base
            D.base_mem hX.1 hY.1 e M hM) _
            (isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
              D.site D.base D.base_mem hX.1 hY.1 e M hM τ hτ) hkX).1 _ = _ from
        divisorCycleCoefficients_toIntegralClosedSubspace D sX hX hdecX _ _ _ _,
      show (canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hkY).1 _ = _ from
        divisorCycleCoefficients_toIntegralClosedSubspace D sY hY hdecY M τ _ _]
    exact (orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq_unconditional
      D.site D.base D.base_mem hdecX hdecY _
      (algebraicSpacesIsoOfIso D.site D.base D.base_mem hX.1 hY.1 e) hintX hintY hNX hNY M hM τ
      hτ).symm
  · rw [show (canonicalDivisorCycleAt D sX hX hintX _
            (isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base
            D.base_mem hX.1 hY.1 e M hM) _
            (isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
              D.site D.base D.base_mem hX.1 hY.1 e M hM τ hτ) hkX).1 T₀ = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sX hX hdecX _ _ _ hcod,
      show (canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hkY).1 _ = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY hdecY M τ _ (by
          rwa [codimension_integralClosedSubspaceSupport_pushforward_of_iso D.site D.base
            D.base_mem hX.1 hY.1 hdecY e T₀])]

end DivisorCycle

end AlgebraicGeometry.Space

end
