module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalPrincipalDivisorUnits
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleMapOfKernelFamilySum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GlobalSectionGenericRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinPushforwardRule

/-!
# The refined Gysin map commutes with the cap product by a first Chern class

In Situation 0EDT let `X/B` be good, let `(ℒ, s, i : E → X)` be a triple as in Stacks 0ER1, so
that `E = Z(s)` is the zero scheme of a global section `s` of an invertible module `ℒ`, and let
`𝒩` be an invertible `𝒪_X`-module. Stacks 0ERB says that the refined Gysin map
`i^* : CH_{k+2}(X) → CH_{k+1}(E)` commutes with capping by the first Chern class of `𝒩`:

`i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α` in `CH_k(E)`.

Both sides are induced by maps on cycles which preserve rational equivalence, so it suffices to
treat `α = [W]` for one integral closed subspace `W ⊆ X` of δ-dimension `k + 2`. In either case
`i^*[W]` is the pushforward of the Weil divisor of a regular meromorphic section `σ` of `ℒ|_W`:
if `W ⊆ E` it is `c₁(ℒ|_W) ∩ [W]`, and if `W ⊄ E` it is `[Z(s|_W)]` with `σ = s|_W`. The key
formula of Stacks 0EQV on `W`, applied to `σ` and to a regular meromorphic section of `𝒩|_W`,
writes the difference of the two sides as a locally finite sum of principal divisors on integral
closed subspaces of `X`. When `W ⊆ E` each of them lies in `E`; when `W ⊄ E`, at a prime divisor
of `W` not contained in `E` the section `s|_W` generates `ℒ`, so its tame symbol term vanishes,
and the remaining terms lie in `E`. They are therefore principal divisors on `E`, and every
principal divisor used is a canonical one, taken at the embeddings of Stacks 0ENK. The case
`W ⊆ E` is the commutativity of first Chern classes on `W`, a special case of Stacks 0ER9.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction_globalSectionGerm`: the generator
  `v · s_ξ` given by the germ of a global section `s` restricts to `s|_Z`.
* `isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub`: the statement
  for `α = [W]`, at the level of cycles, with the rational equivalence supported in `i⁻¹|W|`.
* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_firstChernCapCycleMap`: Stacks 0ERB,
  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α` in `CH_k(E)`, the Chow group of Stacks 0EQ6 at the
  canonical embeddings of Stacks 0ENK.
* `AlgebraicGeometry.Space.sectionRefinedGysin_firstChernCapCycleMap`: its image in the coarser
  quotient `AlgebraicGeometry.Space.chowGroup`.

## Implementation notes

The statement is made on a `(k+2)`-cycle `α` representing a class of `CH_{k+2}(X)`: the left side
is the refined Gysin map applied to the cycle `c₁(𝒩) ∩ α` of Stacks 0EQJ at the canonical
choices, and on the right `i^*α` is the cycle of Stacks 0ER1 at its canonical rule. Since every
class is represented by a cycle and both operations are well defined on classes, this is the
statement on Chow groups.

## References

* [Stacks Project, Tag 0ERB](https://stacks.math.columbia.edu/tag/0ERB)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section GlobalSectionGerm

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- **The restriction of `v · s_ξ` for the germ `v` of a global section is the restriction of the
global section.** If the germ `a ∈ 𝒪_{U, u}` of a global section `s` of `ℒ` against the chosen
generator `s_ξ` at the generic point `ξ` of `Z` is a unit, then the generator `v · s_ξ` of `ℒ_ξ`,
with `v` the image of `a` in `𝒪^h_{X, ξ}`, has restriction `(v · s_ξ)|_Z` of Section 0EQU equal
to the restriction `s|_Z` of the global section. Unlike
`PrimeDivisor.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict` this needs neither
`X` integral nor the ratio of Stacks 0EPR. -/
theorem PrimeDivisor.henselianUnitRestriction_globalSectionGerm (s : L.sections)
    (hu : IsUnit (Z.globalSectionGerm B S hS hX hdec L hL s)) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isLocalHom_stalkToGenericHenselianLocalRing B S hS hX hdec
    Z.henselianUnitRestriction B S hS hX hdec hN L hL
        (Units.map (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
          (Z.genericChart B S hS hX hdec)).toMonoidHom hu.unit) =
      globalSectionMeromorphic B S hS Z.closed.1 (Z.restrictModule B S hS hX L)
        (modulePullbackSections B S hS (Z.inclusion B S hS hX) L s) := by
  rw [Z.henselianUnitRestriction_map B S hS hX hdec hN L hL hu.unit, IsUnit.unit_spec,
    Z.globalSectionMeromorphic_restrict_eq_genericRestrictionOf B S hS hX hdec hN L hL s]

end GlobalSectionGerm

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L) (s : L.sections)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

section TameSymbol

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M σ)
    (M' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M')
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M')
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M' τ)
    {k : ℤ} (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

/-- **The tame symbol of a generator against itself vanishes.** If the generator `v · s_ξ` of
`ℳ_ξ` at the generic point of a prime divisor `P` is `σ` itself, i.e. `σ = 1 · (v s_ξ)`, then
`∂_B(1, g) = 1` and the principal divisor of the tame symbol of the key formula at `P` is zero. -/
theorem PrimeDivisor.keyFormulaTameCycle_eq_zero_of_sectionRatio_eq_one
    (P : PrimeDivisor D.site D.base D.base_mem Y)
    (v w : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY)))ˣ)
    (h1 : P.sectionRatio D sY hY hintY M hM σ hσ v = 1) :
    P.keyFormulaTameCycle D sY hY hintY M hM σ hσ M' hM' τ hτ hn v w = 0 := by
  have h : P.keyFormulaTameSymbol D sY hY hintY M hM σ hσ M' hM' τ hτ v w = 1 := by
    have := P.isLocalRing_genericHenselianLocalRing D sY hY
    have := P.isNoetherianRing_genericHenselianLocalRing_of_isGood D sY hY hintY
    unfold PrimeDivisor.keyFormulaTameSymbol
    simp only [h1, Stacks.Chow.TameSymbol.one_left, map_one]
  unfold PrimeDivisor.keyFormulaTameCycle
  rw [h]
  exact canonicalPrincipalDivisorCycleAt_one D _ _ _ _

end TameSymbol

section GlobalSection

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M) (t : M.sections)
    (P : PrimeDivisor D.site D.base D.base_mem Y)

/-- **A global section generates where it does not vanish to positive order.** If the order of
vanishing of a nonzero global section `t` of an invertible module along a prime divisor `P` is
zero, its germ against the generator `s_ξ` at the generic point of `P` is a unit. -/
theorem PrimeDivisor.isUnit_globalSectionGerm_of_orderOfVanishingSection_eq_zero
    (ht : t ≠ 0) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (h0 : (canonicalDivisorCycleAt D sY hY hintY M hM
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M t)
      ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) M hM _).2
        (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hY.1 M hM ht)) hk).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) = 0) :
    IsUnit (P.globalSectionGerm D.site D.base D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY)
      M hM t) := by
  have hdec := isDecentSpace_of_isGood D sY hY
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have := P.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec hintY hNY
  have := P.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec hintY hNY
  have := P.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec hintY hNY
  let := henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY.1 (P.genericPoint _ _ _ Y)
    hdec
  have := P.isLocalHom_stalkToGenericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec
  have hreg := (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY hNY M
    hM _).2 (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hY.1 M hM ht)
  have hratio := P.canonicalGenericRatio_globalSectionMeromorphic D.site D.base D.base_mem hY.1 hdec
    M hM hintY hNY t
  have hu := P.isUnit_canonicalGenericRatio D.site D.base D.base_mem hY.1 hdec M hM hintY hNY _ hreg
  rw [hratio] at hu
  have hr := Stacks.Chow.mem_nonZeroDivisors_of_isUnit_algebraMap hu
  rw [canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor] at h0
  unfold orderOfVanishingSection at h0
  rw [P.ord_congr D.site D.base D.base_mem hY.1 hdec _ hu
      ((P.coe_canonicalLocalRatio D.site D.base D.base_mem hY.1 hdec M hM hintY hNY _ hreg).trans
        hratio),
    P.ord_algebraMap D.site D.base D.base_mem hY.1 hdec _ hr] at h0
  have hord : Ring.ord _ (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY.1
      (P.genericPoint _ _ _ Y) hdec (P.genericChart D.site D.base D.base_mem hY.1 hdec)
      (P.globalSectionGerm D.site D.base D.base_mem hY.1 hdec M hM t)) = 0 :=
    (ENat.toNat_eq_zero.1 (by exact_mod_cast h0)).resolve_right (Ring.ord_ne_top hr)
  unfold Ring.ord at hord
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hord
  exact isUnit_of_map_unit _ _ hord

/-- **The ratio of a global section against its own germ is `1`.** If the germ of a global
section `t` against `s_ξ` at the generic point of `P` is a unit `a`, then `t = 1 · (a s_ξ)`: the
ratio of Section 0EQU for the generator `a · s_ξ` of `ℳ_ξ` is `1`. -/
theorem PrimeDivisor.sectionRatio_globalSectionMeromorphic_eq_one (ht : t ≠ 0)
    (hu : IsUnit (P.globalSectionGerm D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) M hM t)) :
    P.sectionRatio D sY hY hintY M hM (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M t)
        ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) M hM _).2
          (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hY.1 M hM ht))
        (Units.map (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY.1
          (P.genericPoint _ _ _ Y) (isDecentSpace_of_isGood D sY hY)
          (P.genericChart D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY))).toMonoidHom
          hu.unit) = 1 := by
  unfold PrimeDivisor.sectionRatio
  rw [mul_inv_eq_one]
  refine Units.ext ?_
  rw [IsUnit.unit_spec, Units.coe_map, Units.coe_map, IsUnit.unit_spec]
  exact P.canonicalGenericRatio_globalSectionMeromorphic D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) M hM hintY
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) t

end GlobalSection

omit L hL s N hN in
/-- **`[P ×_W (W ×_X E)]_k` and `[P' ×_X E]_k` have the same pushforward to `X`.** Let `W ⊆ X`
be an integral closed subspace, `P ⊆ W` an integral closed subspace with image `P' ⊆ X` of
δ-dimension `k + 1`, and `E ⊆ X` a closed subspace not containing `P'`. The inverse image of
`W ×_X E` in `P` and the inverse image of `E` in `P'` are both `P ×_X E`, identified over `X`
through `P ≅ P'`, so their `k`-cycles of Stacks 0EE9 have the same pushforward to `X`. -/
theorem integralClosedSubspacePushforward_closedSubspaceCycle_preimage_preimage_eq (k : ℤ)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hP : deltaDimension D sX
      (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P) =
      k + 1)
    (hPE : ¬ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).subspace ≤
      E.1)
    (hd : deltaDimensionSubspace D (P.subspace.ι ≫ W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        P) ((E.1.preimage W.subspace.ι).preimage P.subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem P.subspace.ι _
        (isGood_integralClosedSubspace D sX hX W).1 P.isClosedSubspace.1
        (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1 hX.1
          W.isClosedSubspace.1 E.2)) ≤ (k : EInt)) :
    integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) P k
          (closedSubspaceCycle D (P.subspace.ι ≫ W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W) P)
            ((E.1.preimage W.subspace.ι).preimage P.subspace.ι) _ k hd)) =
      integralClosedSubspacePushforward D sX hX
        (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P) k
        (closedSubspaceCycle D
          ((closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX _)
          (E.1.preimage
            (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).subspace.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem _ E.1 hX.1
            (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
              P).isClosedSubspace.1 E.2) k
          (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D sX hX E _
            (isGood_integralClosedSubspace D sX hX _) k hP hPE)) := by
  have hdec := isDecentSpace_of_isGood D sX hX
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hPg := isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg P
  let e := IntegralClosedSubspace.isoPushforward hX.1 W.isClosedSubspace.1 hdec
    W.isClosedSubspace.2 P
  have he : e.hom ≫ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
      P).subspace.ι = P.subspace.ι ≫ W.subspace.ι :=
    IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 W.isClosedSubspace.1 hdec
      W.isClosedSubspace.2 P
  have hl : IsClosedImmersion D.site D.base D.base_mem (P.subspace.ι ≫ W.subspace.ι) :=
    isClosedImmersion_comp D.site D.base D.base_mem _ _ P.isClosedSubspace.2 W.isClosedSubspace.2
  -- the inverse image of `E` in `P`, along `P ≅ P' → X`
  have hY : (E.1.preimage W.subspace.ι).preimage P.subspace.ι =
      E.1.preimage (e.symm.inv ≫ (closedSubspaceComponentImage D sX hX W.subspace
        W.isClosedSubspace P).subspace.ι) := by
    rw [Iso.symm_inv, he]
    rfl
  have hYc : IsClosedSubspace D.site D.base D.base_mem (E.1.preimage (e.symm.inv ≫
      (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).subspace.ι)) :=
    hY ▸ isClosedSubspace_preimage D.site D.base D.base_mem P.subspace.ι _ hWg.1
      P.isClosedSubspace.1 (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι E.1
        hX.1 W.isClosedSubspace.1 E.2)
  have hd' :
      deltaDimensionSubspace D (P.subspace.ι ≫ W.subspace.ι ≫ sX) hPg _ hYc ≤ (k : EInt) := by
    convert hd using 2
    exact hY.symm
  rw [closedSubspaceCycle_congr D _ hPg hY _ hYc k hd hd']
  have hcomp := cycleGroupClosedPushforward_cycleGroupClosedPushforward D hX.1
    W.isClosedSubspace.1 P.isClosedSubspace.1 hdec (isDecentSpace_of_isGood D _ hWg) rfl
    P.isClosedSubspace.2 W.isClosedSubspace.2 hl sX hX.2.2 (W.subspace.ι ≫ sX) hWg.2.2
    (P.subspace.ι ≫ W.subspace.ι ≫ sX) rfl rfl (Category.assoc _ _ _) k
    (closedSubspaceCycle D (P.subspace.ι ≫ W.subspace.ι ≫ sX) hPg _ hYc k hd')
  refine hcomp.trans ?_
  exact cycleGroupClosedPushforward_closedSubspaceCycle_eq_of_iso D sX hX hl
    (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).isClosedSubspace.2
    _ hPg _ (isGood_integralClosedSubspace D sX hX _) (Category.assoc _ _ _) rfl _ hYc _ _
    (Subfunctor.preimageIsoPreimageComp e.symm _ E.1)
    (by rw [← Category.assoc, Subfunctor.preimageIsoPreimageComp_hom_comp_ι, Category.assoc,
      Iso.symm_inv, he]) k hd' _

/-- The image in `X` of an integral closed subspace `P` of `W ⊆ X` lies in a closed subspace `E`
once all points of `P` map into `E`. -/
private theorem closedSubspaceComponentImage_le_of_subset_preimage
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (h : subspacePointSet D.site D.base D.base_mem W.subspace.toFunctor P.subspace ⊆
      pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1) :
    (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace P).subspace ≤ E.1 := by
  refine le_of_subspacePointSet_subset_of_integral D hX.1 _ E.2 _ ?_
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  rintro _ ⟨x, hx, rfl⟩
  exact h hx

/-- **The restricted generator of `ℒ|_W` at a prime divisor off `Z(s)`.** Let `W ⊆ X` be an
integral closed subspace not contained in `E = Z(s)`, of δ-dimension `k + 2`, and `P` a prime
divisor of `W` whose image `P' ⊆ X` has δ-dimension `k + 1` and is not contained in `E`. If the
germ `a` of `s|_W` against `s_ξ` at the generic point of `P` is a unit, then the restriction
`(a s_ξ)|_P` of Section 0EQU is `(s|_W)|_P`, and its Weil divisor pushes forward to the component
`[P' ×_X E]_k` of `i_* i^*` at `P'`. -/
theorem integralClosedSubspacePushforward_restrictedGeneratorDivisor_of_isUnit (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
    (hP : deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
      (P.toIntegralClosedSubspace D.site D.base D.base_mem)) = k + 1)
    (hPE : ¬ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
        (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
          (vanishingLocus D sX hX L s).1)
    (hu : IsUnit (P.globalSectionGerm D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1
      (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX W))
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W)
      (integralClosedSubspaceRestrictSection D sX hX L s W))) :
    integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W)
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
          (P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
            (integralClosedSubspaceRestrict D sX hX L W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
              (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) hn
            (Units.map (stalkToHenselianLocalRing D.site D.base D.base_mem W.subspace.toFunctor
              (isGood_integralClosedSubspace D sX hX W).1 (P.genericPoint _ _ _ _)
              (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX W))
              (P.genericChart D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W).1
                (isDecentSpace_of_isGood D _
                  (isGood_integralClosedSubspace D sX hX W)))).toMonoidHom
              hu.unit))) =
      integralClosedSubspacePushforward D sX hX (closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)) k
        (sectionGysinPushforwardRule D sX hX L hL s k _ hP) := by
  have hdec := isDecentSpace_of_isGood D sX hX
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hLWs := isInvertibleSheaf_integralClosedSubspaceRestrict D sX hX L hL W
  -- the zero scheme of `s|_W` is `W ×_X Z(s)`
  have hZ : vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
      (integralClosedSubspaceRestrictSection D sX hX L s W) =
      ⟨(vanishingLocus D sX hX L s).1.preimage W.subspace.ι,
        isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
          (vanishingLocus D sX hX L s).1 hX.1 W.isClosedSubspace.1
          (vanishingLocus D sX hX L s).2⟩ :=
    zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hX.1⟩
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ L hL s
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)
  have hPZ : ¬ (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace ≤
      (vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
        (integralClosedSubspaceRestrictSection D sX hX L s W)).1 := by
    rw [hZ]
    intro hle
    refine hPE (closedSubspaceComponentImage_le_of_subset_preimage D sX hX _ W _ ?_)
    rw [← subspacePointSet_preimage]
    exact subspacePointSet_mono_of_le D hle
  have hPk : deltaDimension D (W.subspace.ι ≫ sX)
      (P.toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1 := by
    rw [← deltaDimension_closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace]
    exact hP
  have h0EQF := closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt D
    (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W) hLWs
    (integralClosedSubspaceRestrictSection D sX hX L s W) k hPk hPZ
  have hGR := P.henselianUnitRestriction_globalSectionGerm D.site D.base D.base_mem hWg.1
    (isDecentSpace_of_isGood D _ hWg) (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg)
    (integralClosedSubspaceRestrict D sX hX L W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W)
    (integralClosedSubspaceRestrictSection D sX hX L s W) hu
  have hsub : (vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
      (integralClosedSubspaceRestrictSection D sX hX L s W)).1.preimage
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι =
      ((vanishingLocus D sX hX L s).1.preimage W.subspace.ι).preimage
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι := by
    rw [hZ]
  have hd : deltaDimensionSubspace D
      ((P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫
      W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem))
      (((vanishingLocus D sX hX L s).1.preimage W.subspace.ι).preimage
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem _ _ hWg.1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
        (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι _ hX.1
          W.isClosedSubspace.1 (vanishingLocus D sX hX L s).2)) ≤ (k : EInt) := by
    convert deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D
      (W.subspace.ι ≫ sX) hWg
      (vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
        (integralClosedSubspaceRestrictSection D sX hX L s W))
      (P.toIntegralClosedSubspace D.site D.base D.base_mem)
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg _) k hPk hPZ using 2
    exact hsub.symm
  have e1 : P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) hn
      (Units.map (stalkToHenselianLocalRing D.site D.base D.base_mem W.subspace.toFunctor
        hWg.1 (P.genericPoint _ _ _ _) (isDecentSpace_of_isGood D _ hWg)
        (P.genericChart D.site D.base D.base_mem hWg.1
          (isDecentSpace_of_isGood D _ hWg))).toMonoidHom
        hu.unit) =
      closedSubspaceCycle D ((P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫
        W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg
          (P.toIntegralClosedSubspace D.site D.base D.base_mem))
        (((vanishingLocus D sX hX L s).1.preimage W.subspace.ι).preimage
          (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι) _ k hd := by
    have t1 : P.restrictModule D.site D.base D.base_mem hWg.1
        (integralClosedSubspaceRestrict D sX hX L W) =
        integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX) hWg
          (integralClosedSubspaceRestrict D sX hX L W)
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) := rfl
    have t2 : modulePullbackSections D.site D.base D.base_mem
        (P.inclusion D.site D.base D.base_mem hWg.1)
        (integralClosedSubspaceRestrict D sX hX L W)
        (integralClosedSubspaceRestrictSection D sX hX L s W) =
        integralClosedSubspaceRestrictSection D (W.subspace.ι ≫ sX) hWg
          (integralClosedSubspaceRestrict D sX hX L W)
          (integralClosedSubspaceRestrictSection D sX hX L s W)
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) := rfl
    refine Eq.trans (canonicalDivisorCycleAt_congr_section D _ _ _ _ _
      (hGR ▸ P.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem hWg.1
        (isDecentSpace_of_isGood D _ hWg)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg)
        (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) _) _ hGR) ?_
    refine Eq.trans ?_ (closedSubspaceCycle_congr D _ _ hsub
      (isClosedSubspace_preimage D.site D.base D.base_mem
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι _ hWg.1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
        (vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
          (integralClosedSubspaceRestrictSection D sX hX L s W)).2) _ k
      (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D
        (W.subspace.ι ≫ sX) hWg
        (vanishingLocus D (W.subspace.ι ≫ sX) hWg (integralClosedSubspaceRestrict D sX hX L W)
          (integralClosedSubspaceRestrictSection D sX hX L s W))
        (P.toIntegralClosedSubspace D.site D.base D.base_mem)
        (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg _) k hPk hPZ) hd)
    exact h0EQF.symm
  rw [e1, sectionGysinPushforwardRule_of_not_le D sX hX L hL s k hP hPE]
  exact integralClosedSubspacePushforward_closedSubspaceCycle_preimage_preimage_eq D sX hX k
    (vanishingLocus D sX hX L s) W _ hP hPE hd

/-- **A cap product of the pushforward of a Weil divisor on an integral closed subspace, over the
prime divisors carrying it.** Let `W ⊆ X` be an integral closed subspace of δ-dimension `k + 2`,
`τ` a regular meromorphic section of an invertible `𝒪_W`-module `ℳ`, and `{P_i}` an injective
family of prime divisors of `W` outside of which `τ` generates `ℳ`, whose images `P'_i ⊆ X` form
a locally finite family. For any component rule `c₁` of Stacks 0EQJ on `X`,

`c₁ ∩ (W → X)_* div_ℳ(τ) = ∑_i ord_{P_i}(τ) · (c₁ ∩ [P'_i])`. -/
theorem firstChernCapCycleMap_integralClosedSubspacePushforward_canonicalDivisorCycleAt {k : ℤ}
    {I : Type*} (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (M : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1)
    (hM : IsInvertibleModule (B := D.site)
      ⟨W.subspace.toFunctor, (isGood_integralClosedSubspace D sX hX W).1⟩ M)
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 M τ)
    (hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (chern : FirstChernComponentCycleRule D sX k)
    (Zf : I → PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
    (hinj : Function.Injective Zf)
    (hcov : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor, (∀ i, Zf i ≠ P) →
      P.SectionGenerates D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        W.isIntegralSpace M hM τ)
    (hfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem X
      (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)).subspace)
    (hdim : ∀ i, deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)) = k + 1) :
    firstChernCapCycleMap D sX hX k chern (integralClosedSubspacePushforward D sX hX W (k + 1)
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace M hM τ hτ hn)) =
      cycleFamilySum D sX hX (fun i => closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)) hfin k
        fun i => (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace M hM τ hτ hn).1
            ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) • chern _ (hdim i) := by
  have hdec := isDecentSpace_of_isGood D sX hX
  have himg := IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1
    W.isClosedSubspace.1 hdec W.isClosedSubspace.2
  have hinj' : Function.Injective fun i => closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) :=
    himg.comp ((PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp
      hinj)
  rw [firstChernCapCycleMap_eq_cycleFamilySum D sX hX k chern _ _ hinj' hfin hdim]
  · refine congrArg _ (funext fun i => ?_)
    rw [show (integralClosedSubspacePushforward D sX hX W (k + 1)
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace M hM τ hτ hn)).1 (closedSubspaceComponentImage D sX hX W.subspace
            W.isClosedSubspace ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)) = _ from
      cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1 hdec
        W.isClosedSubspace.2 _ _]
  · intro V hV
    by_cases hex : ∃ V₀, closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace V₀ = V
    · obtain ⟨V₀, rfl⟩ := hex
      have hV₀ : (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace M hM τ hτ hn).1 V₀ ≠ 0 := by
        rwa [show (integralClosedSubspacePushforward D sX hX W (k + 1)
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
            W.isIntegralSpace M hM τ hτ hn)).1 (closedSubspaceComponentImage D sX hX W.subspace
              W.isClosedSubspace V₀) = _ from
          cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1 hdec
            W.isClosedSubspace.2 _ _] at hV
      by_contra hall
      push Not at hall
      refine hV₀ ?_
      rw [canonicalDivisorCycleAt_coe]
      exact canonicalDivisorCycle_apply_eq_zero_of_notMem D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace M hM τ hτ hn Zf hcov V₀
        fun i h => hall i (congrArg _ h)
    · exact absurd (cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1 hdec
        W.isClosedSubspace.2 _ V fun V₀ h => hex ⟨V₀, h⟩) hV

/-- **One summand of the key formula on `W`, read on `X`.** Let `W ⊆ X` be an integral closed
subspace of δ-dimension `k + 2`, `σ` a regular meromorphic section of `ℒ|_W`, `t = t_W` the
regular meromorphic section of `𝒩|_W` of the cap product, and `P` a prime divisor of `W` with
image `P' ⊆ X`, with the generator `v · s_ξ` of `ℒ_ξ` and the generator `s_ξ` of `𝒩_ξ` at its
generic point. The `P`-summand `D_P - T_P` of the key formula (its divisor cycle minus its tame
cycle), pushed to `X`, is the pushforward of a cycle `c'` on `P'`, and with
`a = ord_P(t)`, `b = ord_P(σ)` the cycle

`a · (i_* i^*)[P'] - b · (c₁(𝒩) ∩ [P']) + c'`

on `P'` is a principal divisor when `P' ⊆ Z(s)`, and is zero when `P' ⊄ Z(s)` provided the
generator `v · s_ξ` is `σ` itself and its restriction to `P` is the component of `i_* i^*`. -/
theorem exists_keyFormula_pushforward_component (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 (integralClosedSubspaceRestrict D sX hX L W))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ σ)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
    (vP : (↥(P.genericHenselianLocalRing D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1
      (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX W))))ˣ)
    (hP : deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
      (P.toIntegralClosedSubspace D.site D.base D.base_mem)) = k + 1)
    (hvP : ¬ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
        (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
          (vanishingLocus D sX hX L s).1 →
      P.sectionRatio D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ vP = 1 ∧
      integralClosedSubspacePushforward D sX hX W k
          (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W)
            (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
            (P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
              (integralClosedSubspaceRestrict D sX hX L W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) hn vP)) =
        integralClosedSubspacePushforward D sX hX (closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)) k
          (sectionGysinPushforwardRule D sX hX L hL s k _ hP)) :
    ∃ c' : CycleGroup D ((closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
        (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace.ι ≫ sX) k,
      integralClosedSubspacePushforward D sX hX (closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)) k c' =
        integralClosedSubspacePushforward D sX hX W k
          (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W)
            (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
            (P.keyFormulaDivisorCycle D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
                (integralClosedSubspaceRestrict D sX hX L W)
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                  (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ
                (integralClosedSubspaceRestrict D sX hX N W)
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
                (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
                (isRegularMeromorphicSection_componentMeromorphicSection sX hX
                  (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn vP 1 -
              P.keyFormulaTameCycle D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
                (integralClosedSubspaceRestrict D sX hX L W)
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                  (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ
                (integralClosedSubspaceRestrict D sX hX N W)
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
                (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
                (isRegularMeromorphicSection_componentMeromorphicSection sX hX
                  (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn vP 1)) ∧
      ((closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
          (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
          (vanishingLocus D sX hX L s).1 →
        ∃ h : (rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX
            (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
              (P.toIntegralClosedSubspace D.site D.base D.base_mem))).1)ˣ,
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
              (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
              (isRegularMeromorphicSection_componentMeromorphicSection sX hX
                (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
              (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
              sectionGysinPushforwardRule D sX hX L hL s k _ hP -
            (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ hn).1
              (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
              canonicalFirstChernRule D sX hX N hN k _ hP + c' =
            canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX _)
              (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
                (P.toIntegralClosedSubspace D.site D.base D.base_mem)).isIntegralSpace h
              (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX, hP])) ∧
      (¬ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
          (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
          (vanishingLocus D sX hX L s).1 →
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
              (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
              (isRegularMeromorphicSection_componentMeromorphicSection sX hX
                (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
              (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
              sectionGysinPushforwardRule D sX hX L hL s k _ hP -
            (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ hn).1
              (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
              canonicalFirstChernRule D sX hX N hN k _ hP + c' = 0) := by
  classical
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hint := W.isIntegralSpace
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hdecW := isDecentSpace_of_isGood D _ hWg
  have hNW' := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg
  have := fun P' : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
    P'.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hWg.1 hdecW hint hNW'
  have := fun P' : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
    P'.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hWg.1 hdecW hint hNW'
  have := fun P' : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
    P'.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hWg.1 hdecW hint hNW'
  have hPk : deltaDimensionClosed D
      ((P.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫
      W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem)) Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) :=
    deltaDimensionClosed_univ_toIntegralClosedSubspace D (W.subspace.ι ≫ sX) hWg hint hn P
  have hPk' : deltaDimensionClosed D ((closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX, hP]
  -- the restricted generator of `𝒩` at `P`, read on `P'`
  obtain ⟨τ', hτ', hτ⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
    W.subspace W.isClosedSubspace N hN (integralClosedSubspaceRestrict D sX hX N W) rfl
    (P.toIntegralClosedSubspace D.site D.base D.base_mem) _
    (P.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem hWg.1 hdecW
      hNW' (integralClosedSubspaceRestrict D sX hX N W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) 1) hPk hPk'
  -- the restricted generator of `ℒ` at `P`, read on `P'`
  obtain ⟨κ', hκ', hκ⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
    W.subspace W.isClosedSubspace L hLm (integralClosedSubspaceRestrict D sX hX L W) rfl
    (P.toIntegralClosedSubspace D.site D.base D.base_mem) _
    (P.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem hWg.1 hdecW
      hNW' (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) vP) hPk hPk'
  -- the tame symbol at `P`, read on `P'`
  obtain ⟨_, ⟨hPk'', θ', rfl⟩, hθ⟩ :=
    exists_cycleGroupClosedPushforward_integralClosedSubspacePushforward_eq (hX := hX)
    (W.subspace.ι ≫ sX) hWg W.isClosedSubspace.2 rfl
    (P.toIntegralClosedSubspace D.site D.base D.base_mem) ⟨hPk, P.keyFormulaTameSymbol D
      (W.subspace.ι ≫ sX) hWg hint (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ
      (integralClosedSubspaceRestrict D sX hX N W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W) vP 1, rfl⟩
  -- the two orders of vanishing
  obtain ⟨hft, hat⟩ := orderOfVanishingSection_canonical_eq_ord D (W.subspace.ι ≫ sX) hWg hint
    (integralClosedSubspaceRestrict D sX hX N W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
    (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W) P _ (1 : _ˣ).isUnit _
    (P.sectionRatio_mul D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX N W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W) 1)
  obtain ⟨hfs, has⟩ := orderOfVanishingSection_canonical_eq_ord D (W.subspace.ι ≫ sX) hWg hint
    (integralClosedSubspaceRestrict D sX hX L W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ P _ vP.isUnit _
    (P.sectionRatio_mul D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ vP)
  let P' := closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
    (P.toIntegralClosedSubspace D.site D.base D.base_mem)
  have hτW : integralClosedSubspacePushforward D sX hX W k
      (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
        (P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX N W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) hn 1)) =
      integralClosedSubspacePushforward D sX hX P' k
        (canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
          P'.isIntegralSpace (integralClosedSubspaceRestrict D sX hX N P')
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN P') τ' hτ' hPk') := hτ
  have hκW : integralClosedSubspacePushforward D sX hX W k
      (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
        (P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) hn vP)) =
      integralClosedSubspacePushforward D sX hX P' k
        (canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
          P'.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L P')
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm P') κ' hκ' hPk') := hκ
  have hθW : integralClosedSubspacePushforward D sX hX W k
      (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
        (P.keyFormulaTameCycle D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ
          (integralClosedSubspaceRestrict D sX hX N W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
          (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
          (isRegularMeromorphicSection_componentMeromorphicSection sX hX
            (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn vP 1)) =
      integralClosedSubspacePushforward D sX hX P' k
        (canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
          P'.isIntegralSpace θ' hPk') := hθ
  have hcs : (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) = _ :=
    (canonicalDivisorCycle_apply_primeDivisor D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn P).trans has
  have hct : (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX N W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) = _ :=
    (canonicalDivisorCycle_apply_primeDivisor D (W.subspace.ι ≫ sX) hWg hint
      (integralClosedSubspaceRestrict D sX hX N W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn P).trans hat
  refine ⟨(canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
      canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P') P'.isIntegralSpace
        (integralClosedSubspaceRestrict D sX hX N P')
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN P') τ' hτ' hPk' -
    (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX N W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
        (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
        (isRegularMeromorphicSection_componentMeromorphicSection sX hX
          (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) •
      canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P') P'.isIntegralSpace
        (integralClosedSubspaceRestrict D sX hX L P')
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm P') κ' hκ' hPk' -
    canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
      P'.isIntegralSpace θ' hPk', ?_, ?_, ?_⟩
  · rw [hcs, hct, map_sub, map_sub, map_sub, map_sub, ← hθW, PrimeDivisor.keyFormulaDivisorCycle]
    refine congrArg (· - _) ?_
    rw [map_sub (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k),
      map_sub (integralClosedSubspacePushforward D sX hX W k),
      map_zsmul (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k),
      map_zsmul (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX) hWg
        (P.toIntegralClosedSubspace D.site D.base D.base_mem) k)]
    refine congrArg₂ (· - ·) ?_ ?_
    · rw [map_zsmul (integralClosedSubspacePushforward D sX hX W k), hτW]
      exact map_zsmul _ _ _
    · rw [map_zsmul (integralClosedSubspacePushforward D sX hX W k), hκW]
      exact map_zsmul _ _ _
  · intro hPE
    rw [sectionGysinPushforwardRule_of_le D sX hX L hL s k hP hPE,
      restrictedDivisorCycle_eq_canonicalDivisorCycleAt D sX hX L hL k hP]
    obtain ⟨h1, eh1⟩ := exists_zsmul_sub_canonicalDivisorCycleAt_eq D _
      (isGood_integralClosedSubspace D sX hX P') P'.isIntegralSpace
      (integralClosedSubspaceRestrict D sX hX L P')
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm P')
      (restrictedSectionOfIntegralClosedSubspace D sX hX L hL P') κ'
      (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX P').1 P'.isIntegralSpace
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (P'.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX P'))
        _ (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D sX hX L hL P'))
      hκ' hPk'
      ((canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX N W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
        (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
        (isRegularMeromorphicSection_componentMeromorphicSection sX hX
          (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem))
    obtain ⟨h2, eh2⟩ := exists_zsmul_sub_canonicalDivisorCycleAt_eq D _
      (isGood_integralClosedSubspace D sX hX P') P'.isIntegralSpace
      (integralClosedSubspaceRestrict D sX hX N P')
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN P')
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN P') τ'
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN P') hτ' hPk'
      ((canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
        (P.toIntegralClosedSubspace D.site D.base D.base_mem))
    refine ⟨h1 * h2⁻¹ * θ'⁻¹, ?_⟩
    rw [canonicalPrincipalDivisorCycleAt_mul, canonicalPrincipalDivisorCycleAt_mul,
      canonicalPrincipalDivisorCycleAt_inv, canonicalPrincipalDivisorCycleAt_inv, ← eh1, ← eh2]
    have hrule : canonicalFirstChernRule D sX hX N hN k P' hP =
        canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P') P'.isIntegralSpace
          (integralClosedSubspaceRestrict D sX hX N P')
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN P')
          (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN P')
          (isRegularMeromorphicSection_componentMeromorphicSection sX hX
            (subspaceDivisorSetupOfIsGood D sX hX) N hN P') hPk' := rfl
    rw [hrule, smul_sub, smul_sub]
    abel
  · intro hPE
    obtain ⟨hr1, hr2⟩ := hvP hPE
    have hb0 : (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) = 0 := by
      rw [hcs]
      have h1 : ((P.sectionRatio D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ vP :
            (P.genericTotalFractionRing D.site D.base D.base_mem hWg.1 hdecW)ˣ) :
          P.genericTotalFractionRing D.site D.base D.base_mem hWg.1 hdecW) = 1 := by
        rw [hr1, Units.val_one]
      rw [P.ord_congr D.site D.base D.base_mem hWg.1 hdecW hfs isUnit_one h1]
      exact P.ord_one D.site D.base D.base_mem hWg.1 hdecW
    have hθ0 : canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
        P'.isIntegralSpace θ' hPk' = 0 := by
      apply integralClosedSubspacePushforward_injective D sX hX P' k
      rw [← hθW,
        PrimeDivisor.keyFormulaTameCycle_eq_zero_of_sectionRatio_eq_one D _ hWg hint _ _ σ hσ
          _ _ _ _ hn P vP 1 hr1, map_zero, map_zero, map_zero]
    have hκρ : canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX P')
        P'.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L P')
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm P') κ' hκ' hPk' =
        sectionGysinPushforwardRule D sX hX L hL s k P' hP := by
      apply integralClosedSubspacePushforward_injective D sX hX P' k
      rwa [← hκW]
    rw [hb0, hθ0, ← hκρ, zero_smul, zero_smul, sub_zero, zero_sub, sub_zero]
    abel

/-- **The case of one integral closed subspace, from a section of `ℒ|_W` presenting `i^*[W]`.**
Let `W ⊆ X` be an integral closed subspace of δ-dimension `k + 2` and `σ` a regular meromorphic
section of `ℒ|_W` with `(W → X)_* div_{ℒ|_W}(σ) = i_* i^*[W]`. Suppose that at every prime
divisor `P` of `W` whose image `P' ⊆ X` is not contained in `Z(s)` a generator `v_P · s_ξ` of
`ℒ_ξ` is chosen which is `σ` itself and whose restriction to `P` pushes forward to `i_* i^*[P']`.
Then `i^*(c₁(𝒩) ∩ [W]) - c₁(i^*𝒩) ∩ i^*[W]` is rationally equivalent to zero on `Z(s)`, within
`i⁻¹|W|`.

This is the key formula on `W` for `σ` and `t_W`, read on `X` summand by summand
(`AlgebraicGeometry.Space.exists_keyFormula_pushforward_component`); the summands at prime
divisors of `W` contained in `Z(s)` and the comparison of `c₁(𝒩) ∩ -` on `Z(s)` and on `X`
(`exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`) are
principal divisors on integral closed subspaces of `X` contained in `Z(s)`, which are read on
`Z(s)` by `AlgebraicGeometry.Space.exists_closedSubspaceCyclePushforward_eq_cycleFamilySum`. -/
theorem isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub_of_section
    (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1 + 1)
    (hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 (integralClosedSubspaceRestrict D sX hX L W))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ σ)
    (hσW : integralClosedSubspacePushforward D sX hX W (k + 1)
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ hn) =
      closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) (k + 1)
        (gysinComponentCycle D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
          (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL) W))
    (v : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      (↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX W).1
        (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX W))))ˣ)
    (hv : ∀ (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
      (hP : deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace
        W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)) = k + 1),
      ¬ (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
          (P.toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
          (vanishingLocus D sX hX L s).1 →
      P.sectionRatio D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) σ hσ (v P) = 1 ∧
      integralClosedSubspacePushforward D sX hX W k
          (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W)
            (P.toIntegralClosedSubspace D.site D.base D.base_mem) k
            (P.restrictedGeneratorDivisor D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
              (integralClosedSubspaceRestrict D sX hX L W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L
                (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) hn (v P))) =
        integralClosedSubspacePushforward D sX hX (closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace (P.toIntegralClosedSubspace D.site D.base D.base_mem)) k
          (sectionGysinPushforwardRule D sX hX L hL s k _ hP)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D
      ((vanishingLocus D sX hX L s).1.ι ≫ sX) (isGood_vanishingLocus D sX hX L s) k
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (sectionGysinRule D sX hX L s k hL)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            W) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinComponentCycle D sX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL)
            W))
      (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (vanishingLocus D sX hX L s).1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hint := W.isIntegralSpace
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hE := isGood_vanishingLocus D sX hX L s
  -- the family of prime divisors of the key formula on `W`
  let I := {P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor //
    ¬ (P.SectionGenerates D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ ∧
      P.SectionGenerates D (W.subspace.ι ≫ sX) hWg hint
        (integralClosedSubspaceRestrict D sX hX N W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
        (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W))}
  have hfinW : LocallyFinite fun i : I => subspacePointSet D.site D.base D.base_mem
      W.subspace.toFunctor ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem).subspace :=
    locallyFinite_primeDivisor_not_sectionGenerates D (W.subspace.ι ≫ sX) hWg hint _
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ _
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) _
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
  have hinj : Function.Injective fun i : I => i.1 := Subtype.val_injective
  have hcov : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      (∀ i : I, i.1 ≠ P) →
        P.SectionGenerates D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ ∧
        P.SectionGenerates D (W.subspace.ι ≫ sX) hWg hint
          (integralClosedSubspaceRestrict D sX hX N W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
          (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W) :=
    fun P hP => Classical.byContradiction fun h => hP ⟨P, h⟩ rfl
  have hfinX : LocallyFinite fun i : I => subspacePointSet D.site D.base D.base_mem X
      (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
        ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend
      (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
        W.isClosedSubspace.2) (e := id) (fun i hi => absurd rfl (hi i))
      (fun i => (IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem
        hX.1 W.isClosedSubspace.1 hdec W.isClosedSubspace.2 _).le) hfinW
  have hdimX : ∀ i : I, deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)) = k + 1 :=
    fun i => by
      rw [deltaDimension_closedSubspaceComponentImage]
      exact (deltaDimension_toIntegralClosedSubspace D (W.subspace.ι ≫ sX) hWg hint
        (deltaDimensionFunction D (W.subspace.ι ≫ sX) hWg)
        (deltaDimensionFunction_apply D (W.subspace.ι ≫ sX) hWg) hn i.1).trans
        (add_sub_cancel_right _ _)
  -- the summands of the key formula, read on `X`
  choose c' hc'eq hc'E hc'nE using fun i : I =>
    exists_keyFormula_pushforward_component D sX hX L hL s N hN k W hn σ hσ i.1 (v i.1)
      (hdimX i) (hv i.1 (hdimX i))
  -- `i_* i^*(c₁(𝒩) ∩ [W])` over the family
  have hS1 : closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) k
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) hE k (sectionGysinRule D sX hX L s k hL)
        (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
          W)) =
      cycleFamilySum D sX hX (fun i : I => closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)) hfinX k
        fun i => (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
            (integralClosedSubspaceRestrict D sX hX N W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
            (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
            (isRegularMeromorphicSection_componentMeromorphicSection sX hX
              (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
            ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem) •
          sectionGysinPushforwardRule D sX hX L hL s k _ (hdimX i) := by
    rw [closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule,
      firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + 1) _ hW]
    exact firstChernCapCycleMap_integralClosedSubspacePushforward_canonicalDivisorCycleAt D sX hX W
      _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) _
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn _ (fun i : I => i.1) hinj
      (fun P hP => (hcov P hP).2) hfinX hdimX
  -- `c₁(𝒩) ∩ i_* i^*[W]` over the family
  have hS2 : firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
      (closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) (k + 1)
        (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hE (k + 1)
          (sectionGysinRule D sX hX L s (k + 1) hL) W)) =
      cycleFamilySum D sX hX (fun i : I => closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)) hfinX k
        fun i => (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
            (integralClosedSubspaceRestrict D sX hX L W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
            ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem) •
          canonicalFirstChernRule D sX hX N hN k _ (hdimX i) := by
    rw [← hσW]
    exact firstChernCapCycleMap_integralClosedSubspacePushforward_canonicalDivisorCycleAt D sX hX W
      _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn _
      (fun i : I => i.1) hinj (fun P hP => (hcov P hP).1) hfinX hdimX
  -- the key formula on `W`, read on `X`
  have hKF := keyFormulaDivisorSum_eq_keyFormulaTameSum D (W.subspace.ι ≫ sX) hWg hint
    (integralClosedSubspaceRestrict D sX hX L W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ
    (integralClosedSubspaceRestrict D sX hX N W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
    (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn (fun i : I => i.1) (fun i => v i.1)
    (fun _ => 1) hfinW hinj hcov
  unfold keyFormulaDivisorSum keyFormulaTameSum at hKF
  have hS3 : cycleFamilySum D sX hX (fun i : I => closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)) hfinX k c' =
      0 := by
    rw [← integralClosedSubspacePushforward_cycleFamilySum D sX hX W _ hfinW hfinX _ c'
      (fun i => (hc'eq i).symm), cycleFamilySum_sub, hKF, sub_self, map_zero]
  -- the cap product on `Z(s)` against the cap product on `X`
  obtain ⟨hk2, g2, hS4⟩ :=
    exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum
    D sX hX (vanishingLocus D sX hX L s) N hN
    (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hE (k + 1)
      (sectionGysinRule D sX hX L s (k + 1) hL) W)
  -- the families on `X`
  have hadd : ∀ {J : Type (u + 1)} (V : J → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hV : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X (V j).subspace)
      (x y : ∀ j, CycleGroup D ((V j).subspace.ι ≫ sX) k),
      cycleFamilySum D sX hX V hV k (fun j => x j + y j) =
        cycleFamilySum D sX hX V hV k x + cycleFamilySum D sX hX V hV k y := by
    intro J V hV x y
    have h := cycleFamilySum_sub D sX hX V hV k (fun j => x j + y j) y
    simp only [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  have hΔ : closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) k
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) hE k (sectionGysinRule D sX hX L s k hL)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            W) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hE k
          (canonicalFirstChernRule D _ hE
            ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hE (k + 1)
            (sectionGysinRule D sX hX L s (k + 1) hL) W)) =
      cycleFamilySum D sX hX (fun i : I => closedSubspaceComponentImage D sX hX W.subspace
          W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)) hfinX k
        (fun i => (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
            (integralClosedSubspaceRestrict D sX hX N W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
            (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
            (isRegularMeromorphicSection_componentMeromorphicSection sX hX
              (subspaceDivisorSetupOfIsGood D sX hX) N hN W) hn).1
            ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem) •
          sectionGysinPushforwardRule D sX hX L hL s k _ (hdimX i) -
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg hint
            (integralClosedSubspaceRestrict D sX hX L W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) σ hσ hn).1
            ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem) •
          canonicalFirstChernRule D sX hX N hN k _ (hdimX i) + c' i) +
      cycleFamilySum D sX hX (fun V : {V : IntegralClosedSubspace D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).1.toFunctor // (gysinComponentCycle D sX
            (vanishingLocus D sX hX L s) hE (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL)
              W).1 V ≠ 0} => closedSubspaceComponentImage D sX hX (vanishingLocus D sX hX L s).1
            (vanishingLocus D sX hX L s).2 V.1)
        (locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX _ _) k
        (fun V => canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX _)
          (closedSubspaceComponentImage D sX hX (vanishingLocus D sX hX L s).1
            (vanishingLocus D sX hX L s).2 V.1).isIntegralSpace (g2 V) (hk2 V)) := by
    rw [hadd, cycleFamilySum_sub, ← hS1, ← hS2, hS3, add_zero, map_sub, ← hS4]
    abel
  -- only the summands at prime divisors with image in `Z(s)` remain
  rw [cycleFamilySum_eq_cycleFamilySum_subtype D sX hX _ hfinX _ _
    (fun i : I => (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
      ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
        (vanishingLocus D sX hX L s).1) fun i hi => hc'nE i hi] at hΔ
  choose h hh using hc'E
  -- the subspaces of `X` contained in `Z(s)`, read on `Z(s)`
  choose V' hV' using fun j : {i : I // (closedSubspaceComponentImage D sX hX W.subspace
      W.isClosedSubspace ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)).subspace ≤
        (vanishingLocus D sX hX L s).1} =>
    exists_closedSubspaceComponentImage_eq_of_mem D sX hX (vanishingLocus D sX hX L s).1
      (vanishingLocus D sX hX L s).2 _
      (subspacePointSet_mono_of_le D j.2 ⟨_, rfl⟩)
  obtain ⟨hA, hkA, g', hcast⟩ :=
    exists_cycleFamilySum_canonicalPrincipalDivisorCycleAt_eq_of_forall_eq
    D sX hX (fun j => closedSubspaceComponentImage D sX hX (vanishingLocus D sX hX L s).1
      (vanishingLocus D sX hX L s).2 (V' j)) _ hV'
    (hfinX.comp_injective Subtype.val_injective) (fun j => h j.1 j.2)
    (fun j => by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX, hdimX j.1])
  -- the rational equivalences on `Z(s)`
  obtain ⟨β₁, hβ₁, hR₁⟩ :=
    exists_closedSubspaceCyclePushforward_eq_cycleFamilySum.{u, v, u + 1} D sX hX
    (vanishingLocus D sX hX L s) V' hA g' hkA
    (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
      (vanishingLocus D sX hX L s).1.ι ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace)
    (fun j x hx => by
      have hx' : pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (vanishingLocus D sX hX L s).1.ι x ∈ subspacePointSet D.site D.base D.base_mem X
            (closedSubspaceComponentImage D sX hX (vanishingLocus D sX hX L s).1
              (vanishingLocus D sX hX L s).2 (V' j)).subspace := by
        rw [IntegralClosedSubspace.subspacePointSet_pushforward]
        exact ⟨x, hx, rfl⟩
      rw [hV' j, IntegralClosedSubspace.subspacePointSet_pushforward] at hx'
      obtain ⟨y, -, hy⟩ := hx'
      exact ⟨y, hy⟩)
  obtain ⟨β₂, hβ₂, hR₂⟩ :=
    exists_closedSubspaceCyclePushforward_eq_cycleFamilySum.{u, v, u + 1} D sX hX
      (vanishingLocus D sX hX L s)
      (fun V : {V : IntegralClosedSubspace D.site D.base D.base_mem
        (vanishingLocus D sX hX L s).1.toFunctor // (gysinComponentCycle D sX
          (vanishingLocus D sX hX L s) hE (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL) W).1 V ≠
            0} => V.1)
      (locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX (vanishingLocus D sX hX L s)
        (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hE (k + 1)
          (sectionGysinRule D sX hX L s (k + 1) hL) W)) g2 hk2
      (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
        (vanishingLocus D sX hX L s).1.ι ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace)
      (fun V => subspacePointSet_subset_of_gysinComponentCycle_ne_zero D sX
        (vanishingLocus D sX hX L s) hE (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL) W V.1 V.2)
  have hβ : gysinCycleMap D sX (vanishingLocus D sX hX L s) hE k
        (sectionGysinRule D sX hX L s k hL)
        (firstChernComponentCycle D sX hX (k + 1)
          (canonicalFirstChernRule D sX hX N hN (k + 1)) W) -
      firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX) hE k
        (canonicalFirstChernRule D _ hE
          ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
          (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
        (gysinComponentCycle D sX (vanishingLocus D sX hX L s) hE (k + 1)
          (sectionGysinRule D sX hX L s (k + 1) hL) W) = β₁ + β₂ := by
    refine injective_cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1
      hdec (vanishingLocus D sX hX L s).2.2 sX hX.2.2 _ rfl k
      (?_ : closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) k _ =
        closedSubspaceCyclePushforward D sX hX (vanishingLocus D sX hX L s) k _)
    rw [hΔ, map_add, hβ₁, hβ₂, hcast]
    exact congrArg (· + _) (congrArg _ (funext fun j => hh j.1 j.2))
  rw [hβ]
  exact hR₁.add hR₂


/-- **The case of one integral closed subspace.** For every integral closed subspace `W ⊆ X`,
the cycle `i^*(c₁(𝒩) ∩ [W]) - c₁(i^*𝒩) ∩ i^*[W]` on `Z(s)` is rationally equivalent to zero
within `i⁻¹|W|`, the cap products taken at the canonical choices of Stacks 0EQJ and `i^*` at the
canonical rule of Stacks 0ER1. -/
theorem isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D
      ((vanishingLocus D sX hX L s).1.ι ≫ sX) (isGood_vanishingLocus D sX hX L s) k
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (sectionGysinRule D sX hX L s k hL)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            W) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinComponentCycle D sX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL)
            W))
      (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (vanishingLocus D sX hX L s).1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hWg := isGood_integralClosedSubspace D sX hX W
  by_cases hW : deltaDimension D sX W = k + 1 + 1
  swap
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX (k + 1) _ hW, map_zero,
      gysinComponentCycle_of_deltaDimension_ne D sX _ _ (k + 1) _ hW, map_zero, sub_zero]
    exact isCycleFamilySumWithin_zero D _ _ k _
  have hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) hWg Set.univ isClosed_univ =
      ((k + 1 + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
  have hWX := closedSubspaceCyclePushforward_gysinComponentCycle_sectionGysinRule D sX hX L hL s
    (k + 1) W
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + 1) _ hW] at hWX
  by_cases hWE : W.subspace ≤ (vanishingLocus D sX hX L s).1
  · refine isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub_of_section
      D sX hX L hL s N hN k W hW hn (restrictedSectionOfIntegralClosedSubspace D sX hX L hL W)
      (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hWg.1
        W.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _
        (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D sX hX L hL W))
      ?_ (fun _ => 1) ?_
    · rw [hWX, sectionGysinPushforwardRule_of_le D sX hX L hL s (k + 1) hW hWE,
        restrictedDivisorCycle_eq_canonicalDivisorCycleAt D sX hX L hL (k + 1) hW]
    · intro P hP hPE
      exact absurd (closedSubspaceComponentImage_le_of_subset_preimage D sX hX _ W _
        fun x _ => subspacePointSet_mono_of_le D hWE ⟨x, rfl⟩) hPE
  · have hsW := integralClosedSubspaceRestrictSection_ne_zero_of_not_le D sX hX L hL s hWE
    refine isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub_of_section
      D sX hX L hL s N hN k W hW hn
      (globalSectionMeromorphic D.site D.base D.base_mem hWg.1
        (integralClosedSubspaceRestrict D sX hX L W)
        (integralClosedSubspaceRestrictSection D sX hX L s W))
      ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hWg.1 W.isIntegralSpace
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) _).2
        (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hWg.1 _
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) hsW))
      ?_ (fun P => if h : IsUnit (P.globalSectionGerm D.site D.base D.base_mem hWg.1
          (isDecentSpace_of_isGood D _ hWg) (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W)
          (integralClosedSubspaceRestrictSection D sX hX L s W)) then
        Units.map (stalkToHenselianLocalRing D.site D.base D.base_mem W.subspace.toFunctor hWg.1
          (P.genericPoint _ _ _ _) (isDecentSpace_of_isGood D _ hWg)
          (P.genericChart D.site D.base D.base_mem hWg.1
            (isDecentSpace_of_isGood D _ hWg))).toMonoidHom
          h.unit else 1) ?_
    · rw [hWX, sectionGysinPushforwardRule_of_not_le D sX hX L hL s (k + 1) hW hWE,
        closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt D sX hX L hL s
          (k + 1)
          hW hWE]
    · intro P hP hPE
      have hPk : deltaDimension D (W.subspace.ι ≫ sX)
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1 := by
        rw [← deltaDimension_closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace]
        exact hP
      have h0 : (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace
          (integralClosedSubspaceRestrict D sX hX L W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W)
          (globalSectionMeromorphic D.site D.base D.base_mem hWg.1
            (integralClosedSubspaceRestrict D sX hX L W)
            (integralClosedSubspaceRestrictSection D sX hX L s W))
          ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hWg.1 W.isIntegralSpace
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) _).2
            (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hWg.1 _
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W) hsW)) hn).1
          (P.toIntegralClosedSubspace D.site D.base D.base_mem) = 0 := by
        rw [← closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt D sX hX L hL s
          (k + 1) hW hWE]
        by_contra hne
        have hsub := subspacePointSet_subset_of_closedSubspaceCycle_ne_zero D (W.subspace.ι ≫ sX)
          hWg _ _ (k + 1) _ _ hne
        refine hPE (closedSubspaceComponentImage_le_of_subset_preimage D sX hX _ W _ ?_)
        rw [← subspacePointSet_preimage]
        exact hsub
      have hu := P.isUnit_globalSectionGerm_of_orderOfVanishingSection_eq_zero D (W.subspace.ι ≫ sX)
        hWg W.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W)
        (integralClosedSubspaceRestrictSection D sX hX L s W) hsW hn h0
      rw [dite_eq_left hu]
      exact ⟨P.sectionRatio_globalSectionMeromorphic_eq_one D (W.subspace.ι ≫ sX) hWg
        W.isIntegralSpace (integralClosedSubspaceRestrict D sX hX L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hLm W)
        (integralClosedSubspaceRestrictSection D sX hX L s W) hsW hu,
        integralClosedSubspacePushforward_restrictedGeneratorDivisor_of_isUnit D sX hX L hL s k W
          hn P hP hPE hu⟩

/-- **Stacks 0ERB.** In Situation 0EDT let `X/B` be good, let `(ℒ, s, i : E → X)` be a triple as
in Stacks 0ER1 and let `𝒩` be an invertible `𝒪_X`-module. For every `(k+2)`-cycle `α` on `X`,

`i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α` in `CH_k(E)`.

Here `i^*` is the refined Gysin map of Stacks 0ER1 on cycles,
`AlgebraicGeometry.Space.gysinCycleMap` at the rule `AlgebraicGeometry.Space.sectionGysinRule`;
both cap products are the cycle-level operations of Stacks 0EQJ at the canonical choices,
`AlgebraicGeometry.Space.firstChernCapCycleMap` at
`AlgebraicGeometry.Space.canonicalFirstChernRule`; and the classes are taken in `CH_k(E)` of
Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`, whose rational equivalences are sums of
principal divisors at the canonical embeddings of Stacks 0ENK. As every class of `CH_{k+2}(X)` is
the class of a cycle, this is the identity of the source on representatives.

The two composites are cycle maps of kernels, and on each `[W]` their difference is a sum of
canonical principal divisors lying over `|W|`
(`isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub`); the general
case is Stacks 0EQ8 (`AlgebraicGeometry.Space.isCycleFamilySumWithin_sub_of_isCycleMapOfKernel`).
-/
@[stacks 0ERB "i^*(c₁(N) ∩ α) = c₁(i^*N) ∩ i^*α in CH_k(E), for every (k+2)-cycle α on X \
representing a class of CH_{k+2}(X); i^* is the refined Gysin map of Stacks 0ER1 on cycles \
(gysinCycleMap at sectionGysinRule), both cap products the cycle-level operations of Stacks 0EQJ \
at the canonical choices, the classes taken in the Chow group of Stacks 0EQ6 at the canonical \
embeddings of Stacks 0ENK (chowGroupCanonical); nothing carried"]
theorem chowClassCanonical_gysinCycleMap_firstChernCapCycleMap (k : ℤ)
    (α : CycleGroup D sX (k + 1 + 1)) :
    chowClassCanonical.{max (u + 1) v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) k
        (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (sectionGysinRule D sX hX L s k hL)
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            α)) =
      chowClassCanonical.{max (u + 1) v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) k
        (firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL) α)) := by
  have hA := (isCycleMapOfKernel_firstChernCapCycleMap D sX hX (k + 1)
    (canonicalFirstChernRule D sX hX N hN (k + 1))).comp
    (isCycleMapOfKernel_gysinCycleMap D sX (vanishingLocus D sX hX L s)
      (isGood_vanishingLocus D sX hX L s) k (sectionGysinRule D sX hX L s k hL))
  have hB := (isCycleMapOfKernel_gysinCycleMap D sX (vanishingLocus D sX hX L s)
      (isGood_vanishingLocus D sX hX L s) (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL)).comp
    (isCycleMapOfKernel_firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
      (isGood_vanishingLocus D sX hX L s) k
      (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
        ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
        (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k))
  have h := IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical
    (isCycleFamilySumWithin_sub_of_isCycleMapOfKernel _ (isGood_vanishingLocus D sX hX L s)
      neg_mem_canonicalPrincipalDivisors
      (continuous_pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.ι) hA hB
      (isRationallyEquivalentToZeroWithin_gysinCycleMap_firstChernComponentCycle_sub.{u, v} D sX
        hX L hL s N hN k) α)
  rw [← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff]
  exact h

/-- Stacks 0ERB in the Chow group `AlgebraicGeometry.Space.chowGroup`, whose rational
equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially, with `i^*` read through
`AlgebraicGeometry.Space.sectionRefinedGysin`: the image of
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_firstChernCapCycleMap` under the
comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem sectionRefinedGysin_firstChernCapCycleMap (k : ℤ) (α : CycleGroup D sX (k + 1 + 1)) :
    sectionRefinedGysin.{max (u + 1) v} D sX hX L s k hL
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1)) α) =
      canonicalFirstChernCap.{u, max (u + 1) v} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s)
        ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
        (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k
        (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
          (k + 1) (sectionGysinRule D sX hX L s (k + 1) hL) α) := by
  rw [sectionRefinedGysin_apply D sX hX L s k hL _ |>.1]
  exact congrArg (chowGroupCanonicalToChowGroup.{max (u + 1) v} D _
    (isGood_vanishingLocus D sX hX L s) k)
    (chowClassCanonical_gysinCycleMap_firstChernCapCycleMap D sX hX L hL s N hN k α)

end AlgebraicGeometry.Space

end
