module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCapCommutativity

/-!
# The cap product with a first Chern class along the inclusion of a closed subspace

In Situation 0EDT let `X/B` be good, `i : Y → X` the inclusion of a closed subspace and `𝒩` an
invertible `𝒪_X`-module. For a `(k+1)`-cycle `β = ∑ n_V [V]` on `Y`, the cycles
`c₁(𝒩) ∩ i_*β` and `i_*(c₁(𝒩|_Y) ∩ β)` of Stacks 0EQJ at the canonical choices differ, summand by
summand, by the difference of the Weil divisors of two regular meromorphic sections of `𝒩|_{V'}`
on the image `V' ⊆ X` of `V`. By Stacks 0EPT that difference is a canonical principal divisor on
`V'`, so the two cycles differ by an explicit locally finite sum of principal divisors on
integral closed subspaces of `X` contained in `Y`. This is Stacks 0EQT for a closed immersion,
with the rational equivalence made explicit.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`:
  the difference as a locally finite sum of differences of Weil divisors.
* `exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`:
  the difference as a locally finite sum of canonical principal divisors.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- Taking the image in `X` of an integral closed subspace of `Y ⊆ X` is injective. -/
private theorem injective_closedSubspaceComponentImage :
    Function.Injective (closedSubspaceComponentImage D sX hX Y.1 Y.2) :=
  IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 Y.2.1
    (D.isDecentSpace_of_isGood sX hX) Y.2.2

/-- The images in `X` of the integral closed subspaces occurring in a cycle on a closed subspace
`Y ⊆ X` form a locally finite family. -/
theorem locallyFinite_closedSubspaceComponentImage_of_ne_zero {k : ℤ}
    (β : CycleGroup D (Y.1.ι ≫ sX) k) :
    LocallyFinite fun V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
        β.1 V ≠ 0} => subspacePointSet D.site D.base D.base_mem X
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).subspace := by
  refine ((closedSubspaceCyclePushforward D sX hX Y k β).2.1.comp_injective
    ((injective_closedSubspaceComponentImage D sX hX Y).comp Subtype.val_injective)).subset
    fun V => ?_
  simp only [Function.comp_apply,
    closedSubspaceCyclePushforward_apply_closedSubspaceComponentImage, ite_eq_right V.2,
    subset_refl]

/-- **The cap product along the inclusion of a closed subspace, at the level of cycles.** Let
`Y ⊆ X` be a closed subspace with inclusion `i`, `c₁ ∩ -` on `X` and `c₁' ∩ -` on `Y` cap
products of Stacks 0EQJ given by component rules, and `β = ∑ n_V [V]` a `(k+1)`-cycle on `Y`. If
for each `V` occurring in `β` the cycle `n_V (c₁ ∩ [V'] - i_*(c₁' ∩ [V]))` on `X`, `V' ⊆ X` the
image of `V`, is the pushforward of a cycle `c_V` on `V'`, then

`c₁ ∩ i_*β - i_*(c₁' ∩ β) = ∑_V (V' → X)_* c_V`

in `Z_k(X)`. -/
theorem firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum {k : ℤ}
    (chern : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D (Y.1.ι ≫ sX) k)
    (β : CycleGroup D (Y.1.ι ≫ sX) (k + 1))
    (c : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor // β.1 V ≠ 0},
      CycleGroup D ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).subspace.ι ≫ sX) k)
    (hc : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor // β.1 V ≠ 0},
      integralClosedSubspacePushforward D sX hX
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1) k (c V) =
      β.1 V.1 • (firstChernComponentCycle D sX hX k chern
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1) -
        closedSubspaceCyclePushforward D sX hX Y k (firstChernComponentCycle D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) k chernY V.1))) :
    firstChernCapCycleMap D sX hX k chern (closedSubspaceCyclePushforward D sX hX Y (k + 1) β) -
        closedSubspaceCyclePushforward D sX hX Y k (firstChernCapCycleMap D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) k chernY β) =
      cycleFamilySum D sX hX (fun V : {V : IntegralClosedSubspace D.site D.base D.base_mem
          Y.1.toFunctor // β.1 V ≠ 0} => closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)
        (locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y β) k c := by
  classical
  have hYg := isGood_closedSubspace D sX hX Y
  let img := closedSubspaceComponentImage D sX hX Y.1 Y.2
  have himg : Function.Injective img := injective_closedSubspaceComponentImage D sX hX Y
  let push := fun j : ℤ => closedSubspaceCyclePushforward D sX hX Y j
  have hpush : ∀ (j : ℤ) (γ : CycleGroup D (Y.1.ι ≫ sX) j) V, (push j γ).1 (img V) = γ.1 V :=
    fun j γ V => closedSubspaceCyclePushforward_apply_closedSubspaceComponentImage D sX hX Y γ V
  have hpush0 : ∀ (j : ℤ) (γ : CycleGroup D (Y.1.ι ≫ sX) j) Z, (∀ V, img V ≠ Z) →
      (push j γ).1 Z = 0 := fun j γ Z hZ =>
    closedSubspaceCyclePushforward_apply_of_forall_ne D sX hX Y γ Z hZ
  refine Subtype.ext (funext fun Z => ?_)
  have hreindex : ∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem X,
      (push (k + 1) β).1 Z' * (firstChernComponentCycle D sX hX k chern Z').1 Z =
      ∑ᶠ V, β.1 V * (firstChernComponentCycle D sX hX k chern (img V)).1 Z := by
    rw [finsum_eq_finsum_comp_of_support_subset_range himg]
    · simp only [hpush]
    · intro Z' hZ'
      by_contra hne
      refine hZ' ?_
      change (push (k + 1) β).1 Z' * _ = 0
      rw [hpush0 _ _ Z' fun V hV => hne ⟨V, hV⟩, zero_mul]
  have hfinX : Function.HasFiniteSupport fun V =>
      β.1 V * (firstChernComponentCycle D sX hX k chern (img V)).1 Z := by
    refine ((hasFiniteSupport_firstChernCapCoeff D sX hX k chern (push (k + 1) β) Z).preimage
      himg.injOn).subset fun V hV => ?_
    simpa only [Function.mem_support, Set.mem_preimage, hpush] using hV
  have hrhs : (cycleFamilySum D sX hX (fun V : {V : IntegralClosedSubspace D.site D.base
      D.base_mem Y.1.toFunctor // β.1 V ≠ 0} => img V.1)
      (locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y β) k c).1 Z =
      ∑ᶠ V, β.1 V * ((firstChernComponentCycle D sX hX k chern (img V)).1 Z -
        (push k (firstChernComponentCycle D (Y.1.ι ≫ sX) hYg k chernY V)).1 Z) := by
    rw [cycleFamilySum_apply]
    let g : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor → ℤ := fun V =>
      β.1 V * ((firstChernComponentCycle D sX hX k chern (img V)).1 Z -
        (push k (firstChernComponentCycle D (Y.1.ι ≫ sX) hYg k chernY V)).1 Z)
    have hg : ∀ j : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
        β.1 V ≠ 0}, (integralClosedSubspacePushforward D sX hX (img j.1) k (c j)).1 Z = g j.1 := by
      intro j
      rw [hc j]
      change (β.1 j.1 • (firstChernComponentCycle D sX hX k chern (img j.1) -
        push k (firstChernComponentCycle D (Y.1.ι ≫ sX) hYg k chernY j.1))).1 Z = _
      simp [g, mul_sub]
    rw [finsum_congr hg, finsum_subtype_eq_finsum_cond fun V => β.1 V ≠ 0]
    refine finsum_congr fun V => ?_
    rw [finsum_eq_if]
    split_ifs with h
    · rfl
    · simp only [not_not.1 h, zero_mul]
  rw [hrhs]
  change (firstChernCapCycleMap D sX hX k chern (push (k + 1) β)).1 Z -
      (push k (firstChernCapCycleMap D (Y.1.ι ≫ sX) hYg k chernY β)).1 Z = _
  rw [firstChernCapCycleMap_apply, hreindex]
  by_cases hZ : ∃ V₀, img V₀ = Z
  · obtain ⟨V₀, rfl⟩ := hZ
    rw [hpush, firstChernCapCycleMap_apply,
      ← finsum_sub_distrib hfinX
        (hasFiniteSupport_firstChernCapCoeff D (Y.1.ι ≫ sX) hYg k chernY β V₀)]
    refine finsum_congr fun V => ?_
    rw [hpush, mul_sub]
  · rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]
    refine finsum_congr fun V => ?_
    rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQT for the inclusion of a closed subspace, at the canonical choices, with the
rational equivalence made explicit.** Let `i : Y → X` be the inclusion of a closed subspace and
`𝒩` an invertible `𝒪_X`-module. For every `(k+1)`-cycle `β = ∑ n_V [V]` on `Y`,

`c₁(𝒩) ∩ i_*β - i_*(c₁(𝒩|_Y) ∩ β) = ∑_V (V' → X)_* div(g_V)`

in `Z_k(X)`, the sum running over the `V` occurring in `β`, `V' ⊆ X` the image of `V`, and the
`g_V` invertible rational functions on the `V'`: at each `V` the two component cycles are Weil
divisors of two regular meromorphic sections of `𝒩|_{V'}` (Stacks 0EPT). The cap products are
those of Stacks 0EQJ at the canonical choices and the principal divisors those of Stacks 0EQ6 at
the canonical embeddings of Stacks 0ENK. -/
theorem exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum
    {k : ℤ} (β : CycleGroup D (Y.1.ι ≫ sX) (k + 1)) :
    ∃ (hk : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
          β.1 V ≠ 0}, deltaDimensionClosed D
          ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1))
          Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
      (g : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
          β.1 V ≠ 0}, (rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D
          sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)).1)ˣ),
      firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (closedSubspaceCyclePushforward D sX hX Y (k + 1) β) -
        closedSubspaceCyclePushforward D sX hX Y k (firstChernCapCycleMap D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) k (canonicalFirstChernRule D (Y.1.ι ≫ sX)
            (isGood_closedSubspace D sX hX Y) (closedSubspaceModuleRestrict D sX hX N Y)
            (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
              N hN) k) β) =
      cycleFamilySum D sX hX (fun V : {V : IntegralClosedSubspace D.site D.base D.base_mem
          Y.1.toFunctor // β.1 V ≠ 0} => closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)
        (locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y β) k
        fun V => canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1))
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).isIntegralSpace (g V) (hk V) := by
  have hYg := isGood_closedSubspace D sX hX Y
  have hNY := modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
    N hN
  have hdimV : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
      β.1 V ≠ 0}, deltaDimension D (Y.1.ι ≫ sX) V.1 = k + 1 := fun V => β.2.2 V.1 V.2
  have hkY : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
      β.1 V ≠ 0}, deltaDimensionClosed D (V.1.subspace.ι ≫ Y.1.ι ≫ sX)
        (isGood_integralClosedSubspace D (Y.1.ι ≫ sX) hYg V.1) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt) := fun V => by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D (Y.1.ι ≫ sX) hYg, hdimV V]
  have hk : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
      β.1 V ≠ 0}, deltaDimensionClosed D
        ((closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1))
        Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := fun V =>
    (deltaDimensionClosed_univ_closedSubspace_component D sX hX Y.1 Y.2 V.1).symm.trans (hkY V)
  have hcomp : ∀ V : {V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor //
      β.1 V ≠ 0}, ∃ g : (rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace
        D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)).1)ˣ,
      integralClosedSubspacePushforward D sX hX
          (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1) k
          (canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1))
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).isIntegralSpace g (hk V)) =
        β.1 V.1 • (firstChernComponentCycle D sX hX k (canonicalFirstChernRule D sX hX N hN k)
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1) -
          closedSubspaceCyclePushforward D sX hX Y k (firstChernComponentCycle D (Y.1.ι ≫ sX)
            hYg k (canonicalFirstChernRule D (Y.1.ι ≫ sX) hYg
              (closedSubspaceModuleRestrict D sX hX N Y) hNY k) V.1)) := by
    intro V
    obtain ⟨σ, hσ, hσeq⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
      Y.1 Y.2 N hN (closedSubspaceModuleRestrict D sX hX N Y) rfl V.1 _
      (isRegularMeromorphicSection_componentMeromorphicSection (Y.1.ι ≫ sX) hYg
        (subspaceDivisorSetupOfIsGood D (Y.1.ι ≫ sX) hYg) (closedSubspaceModuleRestrict D sX hX N Y)
        hNY V.1) (hkY V) (hk V)
    obtain ⟨g, hg⟩ := exists_zsmul_sub_canonicalDivisorCycleAt_eq D _
      (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1))
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1).isIntegralSpace _
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)) σ
      (isRegularMeromorphicSection_componentMeromorphicSection sX hX
        (subspaceDivisorSetupOfIsGood D sX hX) N hN
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V.1)) hσ (hk V) (β.1 V.1)
    refine ⟨g, ?_⟩
    rw [← hg, firstChernComponentCycle_of_deltaDimension_eq D sX hX k _
        (by rw [deltaDimension_closedSubspaceComponentImage]; exact hdimV V),
      firstChernComponentCycle_of_deltaDimension_eq D (Y.1.ι ≫ sX) hYg k _ (hdimV V)]
    rw [map_zsmul, map_sub]
    exact congrArg (β.1 V.1 • ·) (congrArg₂ (· - ·) rfl hσeq.symm)
  choose g hg using hcomp
  exact ⟨hk, g, firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum D sX hX Y
    _ _ β _ hg⟩

end AlgebraicGeometry.Space

end
