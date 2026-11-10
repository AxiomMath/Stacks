module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSides

/-!
# Proper pushforward and the cap product, up to canonical rational equivalence

In Situation 0EDT let `X/B` and `Y/B` be good, `p : X → Y` proper over `B` and `ℒ` an invertible
`𝒪_Y`-module. Stacks 0EQT asserts that for `α ∈ Z_{k+1}(X)`

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `CH_k(Y)`.

The source writes `α = ∑ n_W [W]`, sets `W' ⊆ Y` the closure of the image of `W`, and replaces
`p` by `∐ W → ∐ W'`; this reduces the lemma to an integral `W` with `α = [W]` and the proper
dominant morphism `p|_W : W → W'`, where it is Stacks 0EQS. This file carries out that reduction
for the rational equivalence by canonical principal divisors of
`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`, for arbitrary component
rules of Stacks 0EQJ on `X` and on `Y`, among them the canonical ones
`AlgebraicGeometry.Space.canonicalFirstChernRule` of `p^*ℒ` and of `ℒ`.

* Both sides of the identity are coefficientwise `∑_W n_W φ(W)` and `∑_W n_W ψ(W)` with
  `φ(W) = p_*(c₁(p^*ℒ) ∩ [W])` and `ψ(W) = deg(W/W') · (c₁(ℒ) ∩ [W'])`, both supported in `|W'|`.
  As the `|W'|` for the `W` occurring in `α` form a locally finite family (Stacks 0ENZ), if every
  `φ(W) - ψ(W)` is a sum of canonical principal divisors on subspaces of `|W'|`, so is the
  difference of the two sides (Stacks 0EQ8).
* On `W` the component cycle `c₁(p^*ℒ) ∩ [W]` is the pushforward of a cycle on `W`, and pushing
  it forward along `W → X → Y` is pushing it forward along `W → W' → Y` (Stacks 0EP2,
  `AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq`).
  Hence `φ(W) - ψ(W)` is the pushforward along `W' → Y` of the difference of the two sides of
  Stacks 0EQT for `p|_W : W → W'` and the cycle `[W]`, and a sum of canonical principal divisors
  on `W'` pushes forward to one on `Y`.

So Stacks 0EQT, up to canonical rational equivalence, follows from its case of a proper dominant
morphism of integral spaces and the fundamental cycle, which is Stacks 0EQS.

## Main results

* `isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_component`:
  the reduction to `α = [W]`.
* `isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_comp_ι_eq`:
  the reduction to the component morphisms `p|_W : W → W'`.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k)

include hX hY hpB hp

/-- **Stacks 0EQT up to canonical rational equivalence, from the case `α = [W]`.** Let
`p : X → Y` be proper over `B` and let `c₁ ∩ -` on `X` and on `Y` be cap products of Stacks 0EQJ
given by component rules. Suppose that for every integral closed subspace `W ⊆ X` of δ-dimension
`k + 1`, with `W' ⊆ Y` the closure of the image of `W`, the cycle

`p_*(c₁ ∩ [W]) - deg(W/W') · (c₁ ∩ [W'])`

is a sum of canonical principal divisors on integral closed subspaces of `W'`. Then for every
`(k+1)`-cycle `α` on `X` the cycle `p_*(c₁ ∩ α) - c₁ ∩ p_*α` is a sum of canonical principal
divisors on integral closed subspaces contained in the union of the closures of the images of
the `W` occurring in `α`.

The two sides are coefficientwise `∑_W α(W) φ(W)` and `∑_W α(W) ψ(W)`
(`AlgebraicGeometry.Space.properPushforward_firstChernCapCoeff`,
`AlgebraicGeometry.Space.firstChernCapCoeff_properPushforward`), and the closures of the images
of the `W` occurring in `α` form a locally finite family by Stacks 0ENZ, so the locally finite
sums of Stacks 0EQ8 apply. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_component
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX W = k + 1 →
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sY hY k
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
            (firstChernComponentCycle D sX hX k chernX W) -
          properCycleDegree D sX hX sY hY p W •
            firstChernComponentCycle D sY hY k chernY
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) p W))
        (subspacePointSet D.site D.base D.base_mem Y
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W).subspace))
    (α : CycleGroup D sX (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) -
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α))
      (⋃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        closure (pointsMap D.site D.base D.base_mem X p '' cycleSupportFamily D α.1 W)) := by
  classical
  set W' := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p with hW'
  have hlf := (locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp.2.1.2
    (cycleSupportFamily D α.1) (isClosed_cycleSupportFamily D sX hX α.1) α.2.1).1
  refine isCycleFamilySumWithin_finsum D sY hY k _ hlf
    (fun W => α.1 W • (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernComponentCycle D sX hX k chernX W) -
      properCycleDegree D sX hX sY hY p W • firstChernComponentCycle D sY hY k chernY (W' W)))
    (fun W => ?_) fun T => ?_
  · by_cases hW : α.1 W = 0
    · rw [hW, zero_smul]
      exact isCycleFamilySumWithin_zero D sY hY k _
    · rw [closure_image_cycleSupportFamily D sY hY p α.1 hW]
      exact (h W (α.2.2 W hW)).zsmul neg_mem_canonicalPrincipalDivisors _
  · have hfin₁ : Function.HasFiniteSupport fun W => α.1 W *
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W)).1 T := by
      refine ((finite_properPushforwardFirstChernCapSupport D hX hY hpB hp k chernX α T).image
        Prod.fst).subset fun W hW => ?_
      have hne : α.1 W * (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W)).1 T ≠ 0 := hW
      rw [properPushforward_apply] at hne
      obtain ⟨Z, hZ⟩ : ∃ Z, (firstChernComponentCycle D sX hX k chernX W).1 Z *
          properCycleMult D sX hX sY hY p Z T ≠ 0 := by
        by_contra hall
        exact right_ne_zero_of_mul hne (finsum_eq_zero_of_forall_eq_zero fun Z =>
          not_not.1 (not_exists.1 hall Z))
      refine ⟨(W, Z), ?_, rfl⟩
      change α.1 W * (firstChernComponentCycle D sX hX k chernX W).1 Z *
        properCycleMult D sX hX sY hY p Z T ≠ 0
      rw [mul_assoc]
      exact mul_ne_zero (left_ne_zero_of_mul hne) hZ
    have hfin₂ : Function.HasFiniteSupport fun W => α.1 W *
        (properCycleDegree D sX hX sY hY p W *
          (firstChernComponentCycle D sY hY k chernY (W' W)).1 T) := by
      refine ((finite_firstChernCapProperPushforwardSupport D hX hY hpB hp k chernY α T).image
        Prod.fst).subset fun W hW => ?_
      have hne : α.1 W * (properCycleDegree D sX hX sY hY p W *
          (firstChernComponentCycle D sY hY k chernY (W' W)).1 T) ≠ 0 := hW
      have hmult : properCycleMult D sX hX sY hY p W (W' W) =
          properCycleDegree D sX hX sY hY p W := by
        unfold properCycleMult
        rw [ite_eq_left rfl]
      refine ⟨(W, W' W), ?_, rfl⟩
      change α.1 W * properCycleMult D sX hX sY hY p W (W' W) *
        (firstChernComponentCycle D sY hY k chernY (W' W)).1 T ≠ 0
      rw [hmult, mul_assoc]
      exact hne
    change (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernCapCycleMap D sX hX k chernX α)).1 T -
      (firstChernCapCycleMap D sY hY k chernY
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)).1 T = _
    rw [properPushforward_firstChernCapCoeff D hX hY hpB hp k chernX α T,
      firstChernCapCoeff_properPushforward D hX hY hpB hp k chernY α T,
      ← finsum_sub_distrib hfin₁ hfin₂]
    refine finsum_congr fun W => ?_
    rw [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul, AddSubgroup.coe_sub, Pi.sub_apply,
      AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul, mul_sub]

/-- **Stacks 0EQT up to canonical rational equivalence, from the component morphisms.** Let
`p : X → Y` be proper over `B` and let `c₁ ∩ -` on `X` and on `Y` be cap products of Stacks 0EQJ
given by component rules. Suppose that for every integral closed subspace `W ⊆ X` of δ-dimension
`k + 1`, every integral closed subspace `W' ⊆ Y` and every dominant `g : W → W'` over `p` — the
component morphism of Stacks 0EEG, which is proper — the cycle

`g_*(c₁ ∩ [W]) - deg(W/W') · (c₁ ∩ [W'])` on `W'`

is a sum of canonical principal divisors on `W'`, the component cycles being those on `W` and on
`W'` themselves (`AlgebraicGeometry.Space.chernComponentCycleOrZero`). This is Stacks 0EQT for the
proper dominant morphism `g` of integral spaces and the cycle `[W]`, that is, Stacks 0EQS. Then
for every `(k+1)`-cycle `α` on `X`

`p_*(c₁ ∩ α) - c₁ ∩ p_*α`

is a locally finite sum of canonical principal divisors on integral closed subspaces of `Y`, so
that `p_*(c₁ ∩ α)` and `c₁ ∩ p_*α` have the same class in the Chow group of Stacks 0EQ6 at the
canonical embeddings of Stacks 0ENK.

The component cycle of `W` on `X` is the pushforward of the one on `W`, and pushing it forward
along `W → X → Y` is pushing it forward along `W → W' → Y`
(`AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq`),
so the difference for `[W]` on `Y` is the pushforward along `W' → Y` of the difference on `W'`,
and the reduction to `α = [W]` applies. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_comp_ι_eq
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1)
      (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
      (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
      (_hdom : IsDominant D.site D.base D.base_mem g),
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (W'.subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY W') k
        (properCyclePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) (W'.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY W')
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k (chernX W hW) -
          properCycleDegree D sX hX sY hY p W • chernComponentCycleOrZero D sY k chernY W')
        Set.univ)
    (α : CycleGroup D sX (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) -
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α))
      Set.univ := by
  refine IsCycleFamilySumWithin.mono
    (isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_component
      D hX hY hpB hp k chernX chernY (fun W hW => ?_) α) (Set.subset_univ _)
  obtain ⟨g, hg⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem
    hY.1 (D.isDecentSpace_of_isGood sY hY) p W
  have hdom := IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base
    D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p W g hg
  generalize IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W = W' at g hg hdom ⊢
  have hW'good := isGood_integralClosedSubspace D sY hY W'
  rw [firstChernComponentCycle_eq_pushforward D sX hX k chernX W,
    firstChernComponentCycle_eq_pushforward D sY hY k chernY W',
    properCyclePushforward_integralClosedSubspacePushforward_of_comp_ι_eq D hX hY hpB hp.2.1.2 W W'
      hg (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k,
    chernComponentCycleOrZero_of_deltaDimension_eq D sX k chernX hW, ← map_zsmul, ← map_sub]
  have hc := (h W hW W' g hg hdom).closedPushforward (hX := hY) (W'.subspace.ι ≫ sY) hW'good
    W'.isClosedSubspace.2 rfl
  rw [Set.image_univ] at hc
  exact hc

end AlgebraicGeometry.Space

end
