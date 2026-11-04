module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GlobalSectionGenericRestriction

/-!
# The key formula and the refined Gysin maps of two sections

In Situation 0EDT let `W/B` be good and integral with `dim_δ(W) = k + 2`, let `ℒ`, `ℒ'` be
invertible `𝒪_W`-modules with global sections `s`, `s'` and vanishing loci `E = Z(s)`,
`E' = Z(s')`, and let `σ`, `σ'` be regular meromorphic sections of `ℒ`, `ℒ'` which are `s`, `s'`
whenever these are nonzero. Then the two cycles

`(E' → W)_* (i')^* div_ℒ(σ)`  and  `(E → W)_* i^* div_{ℒ'}(σ')`

are rationally equivalent on `W`, through principal divisors on integral closed subspaces of `W`
contained in `E ∩ E'`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `PrimeDivisor.sectionGenerates_of_not_le_vanishingLocus`: a global section generates the
  module at the generic point of a prime divisor off its zero scheme.
* `le_vanishingLocus_of_canonicalDivisorCycle_ne_zero`: the Weil divisor of `σ` is carried by
  `Z(s)`.
* `isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonicalDivisorCycleAt_sub`:
  the comparison above.

## References

* [Stacks Project, Tag 0ERC](https://stacks.math.columbia.edu/tag/0ERC)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe v u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)

/-! ### A global section off its zero scheme -/

section GlobalSection

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)
    (s : L.sections)

include hL in
/-- **A global section generates off its zero scheme.** Let `Z` be a prime divisor of `X` not
contained in `Z(s)`. Then `s` generates `ℒ_ξ` at the generic point `ξ` of `Z`. -/
theorem PrimeDivisor.sectionGenerates_of_not_le_vanishingLocus
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hZ : ¬ (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
      (vanishingLocus D sX hX L s).1) :
    Z.SectionGenerates D sX hX hint L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s) := by
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  set a := Z.globalSectionGerm D.site D.base D.base_mem hX.1 hint.2.1 L hLm s with ha
  have hideal : Ideal.map
      ((Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1).scheme.left.1.presheaf.germ ⊤
        (Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1).point trivial).hom
      (definingIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ (vanishingLocus D sX hX L s)
        (op (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1))) =
      Ideal.span {a} := by
    rw [definingIdealAt_zeroScheme_eq_of_isInvertible D.site D.base D.base_mem ⟨X, hX.1⟩ L s hL
      (Z.genericEtaleChart D.site D.base D.base_mem hX.1 hint.2.1)
      (Z.isAffine_genericChart D.site D.base D.base_mem hX.1 hint.2.1)]
    exact (Z.span_globalSectionGerm_eq_map D.site D.base D.base_mem hX.1 hint.2.1 L hLm s).symm
  have htop : Ideal.span {a} = ⊤ := by
    by_contra hne
    obtain ⟨Zc, hZc⟩ := Z.exists_closedSubspaceComponentImage_of_map_ne_top D sX hX hint
      (vanishingLocus D sX hX L s) (hideal ▸ hne)
    refine hZ ?_
    rw [← hZc]
    exact closedSubspaceComponentImage_le D sX hX (vanishingLocus D sX hX L s) Zc
  have hu : IsUnit a := Ideal.span_singleton_eq_top.1 htop
  refine ⟨stalkToHenselianLocalRing D.site D.base D.base_mem X hX.1
    (Z.genericPoint D.site D.base D.base_mem X) hint.2.1
    (Z.genericChart D.site D.base D.base_mem hX.1 hint.2.1) a, hu.map _, ?_⟩
  exact Z.canonicalGenericRatio_globalSectionMeromorphic D.site D.base D.base_mem hX.1 hint.2.1 L
    hLm hint hN s

include hL in
/-- **The restriction of a section to a subspace off its zero scheme is nonzero.** If an integral
closed subspace `V ⊆ X` is not contained in `Z(s)`, then `s|_V ≠ 0`. -/
theorem modulePullbackSections_ne_zero_of_not_le
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : ¬ V.subspace ≤ (vanishingLocus D sX hX L s).1) :
    modulePullbackSections D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 V.subspace V.isClosedSubspace) L s ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := (modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme D.site D.base
    D.base_mem ⟨X, hX.1⟩ ⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ L hL s
    (closedSubspaceHom D.site D.base D.base_mem hX.1 V.subspace V.isClosedSubspace)).1 h0
  exact hV (Subfunctor.le_of_comp_eq_ι g.hom (congrArg (fun f => f.hom) hg))

variable {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))

/-- A section `σ` equal to `s` unless `Z(s)` is all of `X` generates `ℒ` off `Z(s)`. -/
private theorem sectionGenerates_of_not_le_vanishingLocus_of_eq
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hσs : ¬ (⊤ : Subfunctor X) ≤ (vanishingLocus D sX hX L s).1 →
      σ = globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hZ : ¬ (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
      (vanishingLocus D sX hX L s).1) :
    Z.SectionGenerates D sX hX hint L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ := by
  rw [hσs fun htop => hZ (le_top.trans htop)]
  exact PrimeDivisor.sectionGenerates_of_not_le_vanishingLocus D sX hX hint L hL s Z hZ

include hL in
/-- **The Weil divisor of `σ` is carried by `Z(s)`.** Let `σ` be a regular meromorphic section of
`ℒ` which is `s` unless `Z(s)` is all of `X`. Then every integral closed subspace with a nonzero
coefficient in `div_ℒ(σ)` lies in `Z(s)`. -/
theorem le_vanishingLocus_of_canonicalDivisorCycle_ne_zero
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L σ)
    (hσs : ¬ (⊤ : Subfunctor X) ≤ (vanishingLocus D sX hX L s).1 →
      σ = globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : (canonicalDivisorCycle D sX hX hint L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ hσ hn).1 V ≠ 0) :
    V.subspace ≤ (vanishingLocus D sX hX L s).1 := by
  classical
  by_contra hVE
  refine hV (canonicalDivisorCycle_apply_eq_zero_of_notMem D sX hX hint L _ σ hσ hn
    (Subtype.val : {P : PrimeDivisor D.site D.base D.base_mem X //
      ¬ P.SectionGenerates D sX hX hint L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ} → _)
    (fun P hP => of_not_not fun h => hP ⟨P, h⟩ rfl) V fun i hi => i.2 ?_)
  exact sectionGenerates_of_not_le_vanishingLocus_of_eq D sX hX hint L hL s σ hσs i.1
    (by rw [hi]; exact hVE)

end GlobalSection

/-! ### The Gysin component against the restriction of a chosen generator -/

section GeneratorComparison

variable (M : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hM : IsInvertibleSheaf D sX hX M)
    (t : M.sections) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

open Classical in
/-- **The Gysin component at a prime divisor against the restriction of a generator.** Let `P`
be a prime divisor of the integral space `X` (of δ-dimension `k + 2`) and `w · t_ξ` a generator of
`ℳ_ξ` at its generic point which is `t` itself when `P ⊄ Z(t)`. Then the pushforward of the Gysin
component cycle of `(ℳ, t)` at `P` and the pushforward of `div_{ℳ|_P}((w t_ξ)|_P)` differ by a sum
of canonical principal divisors within `|P|` if `P ⊆ Z(t)`, and agree if `P ⊄ Z(t)`. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_restrictedGeneratorDivisor
    (P : PrimeDivisor D.site D.base D.base_mem X)
    (w : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (hw : ¬ (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
        (vanishingLocus D sX hX M t).1 →
      P.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) M
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
          (globalSectionMeromorphic D.site D.base D.base_mem hX.1 M t) =
        algebraMap ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX))
          (P.genericTotalFractionRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX))
          (w : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX)))) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX M t) k
          (gysinComponentCycle D sX (vanishingLocus D sX hX M t)
            (isGood_vanishingLocus D sX hX M t) k (sectionGysinRule D sX hX M t k hM)
            (P.toIntegralClosedSubspace D.site D.base D.base_mem)) -
        integralClosedSubspacePushforward D sX hX
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
          (P.restrictedGeneratorDivisor D sX hX hint M
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM) hn w))
      (if (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
          (vanishingLocus D sX hX M t).1 then
        subspacePointSet D.site D.base D.base_mem X
          (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace else ∅) := by
  set E := vanishingLocus D sX hX M t with hEdef
  have hE := isGood_vanishingLocus D sX hX M t
  have hMm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  set V := P.toIntegralClosedSubspace D.site D.base D.base_mem with hVdef
  have hVg := isGood_integralClosedSubspace D sX hX V
  have hP : deltaDimension D sX V = k + 1 :=
    (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn P).trans (add_sub_cancel_right _ _)
  have hk' := deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn P
  by_cases hPE : V.subspace ≤ E.1
  · rw [if_pos hPE, gysinComponentCycle_of_le D sX E hE k _ hP hPE,
      closedSubspaceCyclePushforward_containedPushforward D sX hX E k hE hPE, ← map_sub,
      ← one_smul ℤ (_ - _)]
    exact isCycleFamilySumWithin_integralClosedSubspacePushforward D sX hX
      k V (P := canonicalPrincipalDivisors D sX hX k)
      ((exists_zsmul_sub_canonicalDivisorCycleAt_eq D _ (isGood_integralClosedSubspace D sX hX V)
        V.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hMm V)
        (restrictedSectionOfIntegralClosedSubspace D sX hX M hM V)
        (P.henselianUnitRestriction D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) M hMm w)
        (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hVg.1
          V.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hVg) _
          (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D sX hX M hM V))
        (P.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) M hMm w) hk' 1).elim
        fun g hg => ⟨hk', g, hg⟩)
  · rw [if_neg hPE]
    suffices hEq : closedSubspaceCyclePushforward D sX hX E k
          (gysinComponentCycle D sX E hE k (sectionGysinRule D sX hX M t k hM) V) =
        integralClosedSubspacePushforward D sX hX V k
          (P.restrictedGeneratorDivisor D sX hX hint M hMm hn w) by
      rw [hEq, sub_self]
      exact isCycleFamilySumWithin_zero D sX hX k _
    have hur := P.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict D.site D.base
      D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hint M hMm t w (hw hPE)
    have ht0 := modulePullbackSections_ne_zero_of_not_le D sX hX M hM t V hPE
    have hZ : vanishingLocus D (V.subspace.ι ≫ sX) hVg (P.restrictModule D.site D.base D.base_mem
        hX.1 M) (modulePullbackSections D.site D.base D.base_mem
          (P.inclusion D.site D.base D.base_mem hX.1) M t) =
        ⟨E.1.preimage V.subspace.ι, isClosedSubspace_preimage D.site D.base D.base_mem
          V.subspace.ι E.1 hX.1 V.isClosedSubspace.1 E.2⟩ :=
      zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hX.1⟩
        ⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ M hM t
        (P.inclusion D.site D.base D.base_mem hX.1)
    have h0EQF := cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt D
      (V.subspace.ι ≫ sX) hVg V.isIntegralSpace (P.restrictModule D.site D.base D.base_mem hX.1 M)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hMm V) ht0 hk'
    have hd := deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D sX hX E V hVg
      k hP hPE
    have hd' : deltaDimensionSubspace D (V.subspace.ι ≫ sX) hVg
        (vanishingLocus D (V.subspace.ι ≫ sX) hVg (P.restrictModule D.site D.base D.base_mem hX.1 M)
          (modulePullbackSections D.site D.base D.base_mem
            (P.inclusion D.site D.base D.base_mem hX.1) M t)).1
        (vanishingLocus D (V.subspace.ι ≫ sX) hVg (P.restrictModule D.site D.base D.base_mem hX.1 M)
          (modulePullbackSections D.site D.base D.base_mem
            (P.inclusion D.site D.base D.base_mem hX.1) M t)).2 ≤ (k : EInt) := by
      rwa [hZ]
    have hcongr := closedSubspaceCycle_congr D (V.subspace.ι ≫ sX) hVg (congrArg Subtype.val hZ)
      _ _ k hd' hd
    have hsec : ∀ (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
        hVg.1 (P.restrictModule D.site D.base D.base_mem hX.1 M)) (_ : τ = τ') hτ hτ',
        canonicalDivisorCycleAt D (V.subspace.ι ≫ sX) hVg V.isIntegralSpace _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hMm V) τ hτ hk' =
          canonicalDivisorCycleAt D (V.subspace.ι ≫ sX) hVg V.isIntegralSpace _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hMm V) τ' hτ' hk' := by
      rintro τ _ rfl _ _
      rfl
    rw [gysinComponentCycle_of_not_le D sX E hE k _ hP hPE]
    show closedSubspaceCyclePushforward D sX hX E k
      (gysinIntersectionCycle D sX hX E hE k V hP hPE) = _
    rw [← integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle
      D sX hX E hE V hVg k hP hPE, ← hcongr]
    have hreg := P.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem
      hX.1 (isDecentSpace_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) M hMm w
    have hgen : P.restrictedGeneratorDivisor D sX hX hint M hMm hn w =
        canonicalDivisorCycleAt D (V.subspace.ι ≫ sX) hVg V.isIntegralSpace _
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hMm V)
          (P.henselianUnitRestriction D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX)
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) M hMm w) hreg hk' := rfl
    rw [hgen, ← hsec _ _ hur.symm (hur ▸ hreg) hreg]
    exact congrArg _ (Subtype.ext h0EQF)

/-- The Gysin component comparison at a prime divisor `P`, scaled by an integer `c` which vanishes
unless `P ⊆ F`, within any `S` containing `|P|` whenever `P ⊆ Z(t) ∩ F`. -/
private theorem isCanonicallyRationallyEquivalentToZeroWithin_zsmul_gysinComponentCycle_sub
    (P : PrimeDivisor D.site D.base D.base_mem X)
    (w : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (hw : ¬ (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
        (vanishingLocus D sX hX M t).1 →
      P.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) M
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
          (globalSectionMeromorphic D.site D.base D.base_mem hX.1 M t) =
        algebraMap ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX))
          (P.genericTotalFractionRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX))
          (w : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX))))
    (c : ℤ) (F : Subfunctor X)
    (hc : c ≠ 0 → (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤ F)
    (S : Set (points D.site D.base D.base_mem X))
    (hS : (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
        (vanishingLocus D sX hX M t).1 →
      (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤ F →
      subspacePointSet D.site D.base D.base_mem X
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ⊆ S) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (c • (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX M t) k
          (gysinComponentCycle D sX (vanishingLocus D sX hX M t)
            (isGood_vanishingLocus D sX hX M t) k (sectionGysinRule D sX hX M t k hM)
            (P.toIntegralClosedSubspace D.site D.base D.base_mem)) -
        integralClosedSubspacePushforward D sX hX
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
          (P.restrictedGeneratorDivisor D sX hX hint M
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM) hn w))) S := by
  by_cases h0 : c = 0
  · rw [h0, zero_smul]
    exact isCycleFamilySumWithin_zero D sX hX k _
  have h :=
    isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_restrictedGeneratorDivisor
      D sX hX hint M hM t hn P w hw
  refine (h.zsmul neg_mem_canonicalPrincipalDivisors _).mono ?_
  split_ifs with hPE
  · exact hS hPE (hc h0)
  · exact Set.empty_subset _

end GeneratorComparison

/-! ### A cycle map of a kernel against a family of divisors -/

section FamilyComparison

/-- **A cycle map of a kernel on a cycle carried by a family, termwise.** Let `Φ` be the cycle
map of a kernel `K` on `X` (along the identity) and `β` a cycle whose coefficients vanish off an
injective locally finite family `{V_i}`. If each `β(V_i) · (K(V_i) - (V_i)_* d_i)` is canonically
rationally equivalent to zero within `S_i ⊆ |V_i|`, then so is
`Φ(β) - ∑ (V_i)_*(β(V_i) · d_i)` within `⋃ S_i`. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_sub_cycleFamilySum {a k : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sX k}
    {K : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sX k}
    (hΦ : IsCycleMapOfKernel D sX sX id Φ K) (β : CycleGroup D sX a) {I : Type w}
    (V : I → IntegralClosedSubspace D.site D.base D.base_mem X) (hVinj : Function.Injective V)
    (hVfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem X (V i).subspace)
    (hβ : ∀ Z, β.1 Z ≠ 0 → ∃ i, V i = Z) (d : ∀ i, CycleGroup D ((V i).subspace.ι ≫ sX) k)
    (S : I → Set (points D.site D.base D.base_mem X))
    (hS : ∀ i, S i ⊆ subspacePointSet D.site D.base D.base_mem X (V i).subspace)
    (h : ∀ i, IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (β.1 (V i) • (K (V i) - integralClosedSubspacePushforward D sX hX (V i) k (d i))) (S i)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max w v} D sX hX k
      (Φ β - cycleFamilySum D sX hX V hVfin k fun i => β.1 (V i) • d i) (⋃ i, S i) := by
  refine isCycleFamilySumWithin_finsum D sX hX k S (hVfin.subset hS) _ h
    fun Z => ?_
  show (Φ β).1 Z - (cycleFamilySum D sX hX V hVfin k fun i => β.1 (V i) • d i).1 Z = _
  rw [hΦ.apply, cycleFamilySum_apply,
    finsum_eq_finsum_comp_of_support_subset_range hVinj (g := fun Z' => β.1 Z' * (K Z').1 Z)
      (fun Z' hZ' => hβ Z' (left_ne_zero_of_mul hZ')),
    ← finsum_sub_distrib ((hΦ.finite_support β Z).preimage hVinj.injOn)
      (finite_support_cycleFamilyCoeff D sX hX V hVfin k _ Z)]
  refine finsum_congr fun i => ?_
  simp only [map_zsmul, AddSubgroup.coe_zsmul, AddSubgroup.coe_sub, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, mul_sub]

end FamilyComparison

/-! ### The key formula with the Gysin maps of two sections -/

section KeyFormulaGysin

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (hL : IsInvertibleSheaf D sX hX L)
    (s : L.sections) (L' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL' : IsInvertibleSheaf D sX hX L') (s' : L'.sections) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

/-- **The key formula for the refined Gysin maps of two sections, on an integral space.** In
Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = k + 2`, let
`(ℒ, s)`, `(ℒ', s')` be pairs as in Stacks 0ER1 with `E = Z(s)`, `E' = Z(s')`, and let `σ`, `σ'`
be regular meromorphic sections of `ℒ`, `ℒ'` which are `s`, `s'` unless `E`, resp. `E'`, is all
of `X`. Then

`(E' → X)_* (i')^* div_ℒ(σ) - (E → X)_* i^* div_{ℒ'}(σ')`

is a sum of canonical principal divisors on integral closed subspaces of `|E| ∩ |E'|`. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonicalDivisorCycleAt_sub
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L σ)
    (hσs : ¬ (⊤ : Subfunctor X) ≤ (vanishingLocus D sX hX L s).1 →
      σ = globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
    (σ' : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L')
    (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L' σ')
    (hσs' : ¬ (⊤ : Subfunctor X) ≤ (vanishingLocus D sX hX L' s').1 →
      σ' = globalSectionMeromorphic D.site D.base D.base_mem hX.1 L' s') :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sX hX k
      (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L' s') k
          (gysinCycleMap D sX (vanishingLocus D sX hX L' s') (isGood_vanishingLocus D sX hX L' s')
            k (sectionGysinRule D sX hX L' s' k hL')
            (canonicalDivisorCycleAt D sX hX hint L
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) σ hσ hn)) -
        closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) k
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
            (sectionGysinRule D sX hX L s k hL)
            (canonicalDivisorCycleAt D sX hX hint L'
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL') σ' hσ' hn)))
      (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 ∩
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L' s').1) := by
  classical
  have hLm : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hL'm : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L' :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL'
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  set E := vanishingLocus D sX hX L s with hEdef
  set E' := vanishingLocus D sX hX L' s' with hE'def
  have hE := isGood_vanishingLocus D sX hX L s
  have hE' := isGood_vanishingLocus D sX hX L' s'
  let I := {P : PrimeDivisor D.site D.base D.base_mem X //
    ¬ (P.SectionGenerates D sX hX hint L hLm σ ∧ P.SectionGenerates D sX hX hint L' hL'm σ')}
  let Zf : I → PrimeDivisor D.site D.base D.base_mem X := Subtype.val
  let Zf' := fun i : I => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem
  have hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Zf' i).subspace :=
    locallyFinite_primeDivisor_not_sectionGenerates D sX hX hint L hLm σ hσ L' hL'm σ' hσ'
  have hinj : Function.Injective Zf := Subtype.val_injective
  have hinj' : Function.Injective Zf' :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hinj
  have hcov : ∀ P : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ P) →
      P.SectionGenerates D sX hX hint L hLm σ ∧ P.SectionGenerates D sX hX hint L' hL'm σ' := by
    exact fun P hP => of_not_not fun h => hP ⟨P, h⟩ rfl
  let v : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ := fun i =>
    if h : (Zf i).SectionGenerates D sX hX hint L hLm σ then h.choose_spec.1.unit else 1
  let w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ := fun i =>
    if h : (Zf i).SectionGenerates D sX hX hint L' hL'm σ' then h.choose_spec.1.unit else 1
  have hv : ∀ i, (Zf i).SectionGenerates D sX hX hint L hLm σ →
      (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          L hLm hint hN σ =
        algebraMap _ _ ((v i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) := by
    intro i h
    simp only [v, dif_pos h, IsUnit.unit_spec]
    exact h.choose_spec.2
  have hw : ∀ i, (Zf i).SectionGenerates D sX hX hint L' hL'm σ' →
      (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          L' hL'm hint hN σ' =
        algebraMap _ _ ((w i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) := by
    intro i h
    simp only [w, dif_pos h, IsUnit.unit_spec]
    exact h.choose_spec.2
  have hratio1 : ∀ (P : PrimeDivisor D.site D.base D.base_mem X)
      (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hMm : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ M)
      (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M)
      (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M τ)
      (u₀ : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)))ˣ),
      P.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) M
          hMm hint hN τ = algebraMap _ _ (u₀ : ↥(P.genericHenselianLocalRing D.site D.base
            D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX))) →
        P.sectionRatio D sX hX hint M hMm τ hτ u₀ = 1 := by
    intro P M hMm τ hτ u₀ hu
    have hmul := P.sectionRatio_mul D sX hX hint M hMm τ hτ u₀
    rw [hu] at hmul
    have hU : IsUnit (algebraMap ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)) (P.genericTotalFractionRing D.site D.base D.base_mem
          hX.1 (isDecentSpace_of_isGood D sX hX))
        (u₀ : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) := u₀.isUnit.map _
    refine Units.val_eq_one.mp (hU.mul_left_inj.mp ?_)
    rwa [one_mul]
  have hcoefgen : ∀ (i : I) (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hMm : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ M)
      (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M)
      (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M τ)
      (u₀ : (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)))ˣ),
      (canonicalDivisorCycleAt D sX hX hint M hMm τ hτ hn).1 (Zf' i) =
      have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
        W.isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
      have := (Zf i).krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint hN
      have := (Zf i).nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint hN
      (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        ((Zf i).sectionRatio D sX hX hint M hMm τ hτ u₀ : _) (Units.isUnit _) := by
    intro i M hMm τ hτ u₀
    obtain ⟨hfu, hα⟩ := orderOfVanishingSection_canonical_eq_ord D sX hX hint M hMm τ hτ (Zf i)
      _ u₀.isUnit _ ((Zf i).sectionRatio_mul D sX hX hint M hMm τ hτ u₀)
    show (canonicalDivisorCycle D sX hX hint M hMm τ hτ hn).1
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) = _
    rw [canonicalDivisorCycle_apply_primeDivisor, hα]
  have hgenE : ∀ i, ¬ (Zf' i).subspace ≤ E.1 →
      (Zf i).SectionGenerates D sX hX hint L hLm σ :=
    fun i => sectionGenerates_of_not_le_vanishingLocus_of_eq D sX hX hint L hL s σ hσs (Zf i)
  have hgenE' : ∀ i, ¬ (Zf' i).subspace ≤ E'.1 →
      (Zf i).SectionGenerates D sX hX hint L' hL'm σ' :=
    fun i => sectionGenerates_of_not_le_vanishingLocus_of_eq D sX hX hint L' hL' s' σ' hσs'
      (Zf i)
  have hcoefE : ∀ i, (canonicalDivisorCycleAt D sX hX hint L hLm σ hσ hn).1 (Zf' i) ≠ 0 →
      (Zf' i).subspace ≤ E.1 :=
    fun i => le_vanishingLocus_of_canonicalDivisorCycle_ne_zero D sX hX hint L hL s hn σ hσ hσs
      (Zf' i)
  have hcoefE' : ∀ i, (canonicalDivisorCycleAt D sX hX hint L' hL'm σ' hσ' hn).1 (Zf' i) ≠ 0 →
      (Zf' i).subspace ≤ E'.1 :=
    fun i => le_vanishingLocus_of_canonicalDivisorCycle_ne_zero D sX hX hint L' hL' s' hn σ' hσ'
      hσs' (Zf' i)
  have hwE' : ∀ i, ¬ (Zf' i).subspace ≤ E'.1 →
      (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          L' hL'm hint hN (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L' s') =
        algebraMap _ _ ((w i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) := by
    intro i hPE
    have h := hw i (hgenE' i hPE)
    rwa [hσs' fun htop => hPE (le_top.trans htop)] at h
  have hvE : ∀ i, ¬ (Zf' i).subspace ≤ E.1 →
      (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          L hLm hint hN (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s) =
        algebraMap _ _ ((v i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) := by
    intro i hPE
    have h := hv i (hgenE i hPE)
    rwa [hσs fun htop => hPE (le_top.trans htop)] at h
  let S : I → Set (points D.site D.base D.base_mem X) := fun i =>
    subspacePointSet D.site D.base D.base_mem X E.1 ∩
      subspacePointSet D.site D.base D.base_mem X E'.1 ∩
        subspacePointSet D.site D.base D.base_mem X (Zf' i).subspace
  have hS : ∀ i, S i ⊆ subspacePointSet D.site D.base D.base_mem X (Zf' i).subspace :=
    fun i => Set.inter_subset_right
  have hSE : ∀ i, (Zf' i).subspace ≤ E.1 → (Zf' i).subspace ≤ E'.1 →
      subspacePointSet D.site D.base D.base_mem X (Zf' i).subspace ⊆ S i := fun i h h' =>
    Set.subset_inter (Set.subset_inter (subspacePointSet_mono_of_le D h)
      (subspacePointSet_mono_of_le D h')) subset_rfl
  have hΦ' := (isCycleMapOfKernel_gysinCycleMap D sX E' hE' k
    (sectionGysinRule D sX hX L' s' k hL')).closedPushforward hX.1 E'.2.1
    (isDecentSpace_of_isGood D sX hX) E'.2.2 hX.2.2 rfl (π' := id) rfl
  have hΦ := (isCycleMapOfKernel_gysinCycleMap D sX E hE k
    (sectionGysinRule D sX hX L s k hL)).closedPushforward hX.1 E.2.1
    (isDecentSpace_of_isGood D sX hX) E.2.2 hX.2.2 rfl (π' := id) rfl
  have hβgen : ∀ (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hMm : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ M)
      (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M)
      (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M τ),
      (∀ P, (∀ i, Zf i ≠ P) → P.SectionGenerates D sX hX hint M hMm τ) →
      ∀ Z, (canonicalDivisorCycleAt D sX hX hint M hMm τ hτ hn).1 Z ≠ 0 → ∃ i, Zf' i = Z := by
    intro M hMm τ hτ hP Z hZ
    by_contra h
    push Not at h
    exact hZ (canonicalDivisorCycle_apply_eq_zero_of_notMem D sX hX hint M hMm τ hτ hn Zf hP Z h)
  have h₁ := isCanonicallyRationallyEquivalentToZeroWithin_sub_cycleFamilySum.{v} D sX hX hΦ'
    (canonicalDivisorCycleAt D sX hX hint L hLm σ hσ hn) Zf' hinj' hfin
    (hβgen L hLm σ hσ fun P hP => (hcov P hP).1)
    (fun i => (Zf i).restrictedGeneratorDivisor D sX hX hint L' hL'm hn (w i)) S hS
    (fun i => isCanonicallyRationallyEquivalentToZeroWithin_zsmul_gysinComponentCycle_sub
      D sX hX hint L' hL' s' hn (Zf i) (w i) (hwE' i) _ E.1 (hcoefE i) (S i)
      fun hPE' hPE => hSE i hPE hPE')
  have h₂ := isCanonicallyRationallyEquivalentToZeroWithin_sub_cycleFamilySum.{v} D sX hX hΦ
    (canonicalDivisorCycleAt D sX hX hint L' hL'm σ' hσ' hn) Zf' hinj' hfin
    (hβgen L' hL'm σ' hσ' fun P hP => (hcov P hP).2)
    (fun i => (Zf i).restrictedGeneratorDivisor D sX hX hint L hLm hn (v i)) S hS
    (fun i => isCanonicallyRationallyEquivalentToZeroWithin_zsmul_gysinComponentCycle_sub
      D sX hX hint L hL s hn (Zf i) (v i) (hvE i) _ E'.1 (hcoefE' i) (S i)
      fun hPE hPE' => hSE i hPE hPE')
  have hone : ∀ i, canonicalPrincipalDivisorCycleAt D _
      (isGood_integralClosedSubspace D sX hX (Zf' i)) (Zf' i).isIntegralSpace 1
        (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn (Zf i)) = 0 := by
    intro i
    have hz := canonicalPrincipalDivisorCycleAt_zpow D _ (isGood_integralClosedSubspace D sX
      hX (Zf' i)) (Zf' i).isIntegralSpace 1 0
      (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn (Zf i))
    rwa [zpow_zero, zero_smul] at hz
  have htame : ∀ i, IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (integralClosedSubspacePushforward D sX hX (Zf' i) k
        ((Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i) (w i)))
      (S i) := by
    intro i
    have hcyc : (Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i)
        (w i) = canonicalPrincipalDivisorCycleAt D _
          (isGood_integralClosedSubspace D sX hX (Zf' i)) (Zf' i).isIntegralSpace
          ((Zf i).keyFormulaTameSymbol D sX hX hint L hLm σ hσ L' hL'm σ' hσ' (v i) (w i))
          (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn (Zf i)) := rfl
    by_cases hg : (Zf i).SectionGenerates D sX hX hint L hLm σ ∨
        (Zf i).SectionGenerates D sX hX hint L' hL'm σ'
    · have hsym : (Zf i).keyFormulaTameSymbol D sX hX hint L hLm σ hσ L' hL'm σ' hσ' (v i)
          (w i) = 1 := by
        have := (Zf i).isLocalRing_genericHenselianLocalRing D sX hX
        have := (Zf i).isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
        unfold PrimeDivisor.keyFormulaTameSymbol
        rcases hg with hg | hg
        · rw [hratio1 _ _ _ _ _ _ (hv i hg), Stacks.Chow.TameSymbol.one_left, map_one]
        · rw [hratio1 _ _ _ _ _ _ (hw i hg), Stacks.Chow.TameSymbol.one_right, map_one]
      have h0 : (Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i)
          (w i) = 0 := by
        rw [hcyc, hsym]
        exact hone i
      rw [h0, map_zero]
      exact isCycleFamilySumWithin_zero D sX hX k _
    push Not at hg
    have hPE : (Zf' i).subspace ≤ E.1 := of_not_not fun h => hg.1 (hgenE i h)
    have hPE' : (Zf' i).subspace ≤ E'.1 := of_not_not fun h => hg.2 (hgenE' i h)
    exact (isCycleFamilySumWithin_integralClosedSubspacePushforward D sX hX
      k (Zf' i) (P := canonicalPrincipalDivisors D sX hX k) ⟨_, _, hcyc⟩).mono (hSE i hPE hPE')
  have h₃ := isCycleFamilySumWithin_finsum.{u, v, u + 1} D sX hX k S
    (hfin.subset hS)
    (fun i => integralClosedSubspacePushforward D sX hX (Zf' i) k
      ((Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i) (w i)))
    htame
    (α := cycleFamilySum D sX hX Zf' hfin k fun i =>
      (Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i) (w i))
    (fun Z => cycleFamilySum_apply D sX hX Zf' hfin k _ Z)
  have hkey := keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn
    Zf v w hfin hinj hcov
  have hfam : (cycleFamilySum D sX hX Zf' hfin k fun i =>
        (canonicalDivisorCycleAt D sX hX hint L hLm σ hσ hn).1 (Zf' i) •
          (Zf i).restrictedGeneratorDivisor D sX hX hint L' hL'm hn (w i)) -
      (cycleFamilySum D sX hX Zf' hfin k fun i =>
        (canonicalDivisorCycleAt D sX hX hint L' hL'm σ' hσ' hn).1 (Zf' i) •
          (Zf i).restrictedGeneratorDivisor D sX hX hint L hLm hn (v i)) =
      cycleFamilySum D sX hX Zf' hfin k fun i =>
        (Zf i).keyFormulaTameCycle D sX hX hint L hLm σ hσ L' hL'm σ' hσ' hn (v i) (w i) := by
    rw [← cycleFamilySum_sub]
    refine Eq.trans ?_ hkey
    refine congrArg (cycleFamilySum D sX hX Zf' hfin k) (funext fun i => ?_)
    rw [hcoefgen i L hLm σ hσ (v i), hcoefgen i L' hL'm σ' hσ' (w i)]
    rfl
  have hsplit : ∀ a b c d : CycleGroup D sX k, a - b = (a - c) - (b - d) + (c - d) :=
    fun a b c d => by abel
  rw [hsplit _ _ _ _, hfam]
  exact ((h₁.sub h₂ neg_mem_canonicalPrincipalDivisors).add h₃).mono
    (Set.iUnion_subset fun _ => Set.inter_subset_left)

end KeyFormulaGysin

end AlgebraicGeometry.Space

end
