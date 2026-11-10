module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# The projection formula of Stacks 0EQT reduced to one integral closed subspace, up to rational
equivalence

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be proper over `B` and let
`α ∈ Z_{k+1}(X)`. For two component rules of Stacks 0EQJ, `c₁(𝒩) ∩ -` on `X` and `c₁(ℒ) ∩ -` on
`Y`, the *defect* at an integral closed subspace `W ⊆ X` is the `k`-cycle

`p_*(c₁(𝒩|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`

on `Y`, where `W'` is the closure of the image of `|W|` and `deg(W/W')` the degree of Stacks
0EP1, part (1). This file proves that `p_*(c₁(𝒩) ∩ α) - c₁(ℒ) ∩ p_*α` is rationally equivalent
to zero, at the canonical embeddings of Stacks 0ENK, as soon as every integer multiple of every
defect is rationally equivalent to zero by integral closed subspaces of `Y` lying in `W'`.

This is the passage of the source's proof of Stacks 0EQT from an arbitrary cycle to a single
integral closed subspace, read in the Chow group. The commutator is the locally finite sum of
the multiples `α(W) · (defect at W)`, by the two coefficient expansions of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap`; the carriers `|W'|`
form a locally finite family by Stacks 0ENZ; and Stacks 0EQ8 at the canonical embeddings
(`AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_finsum`) assembles the summands.

A defect can be read on `W'` itself: it is the pushforward along `W' → Y` of
`g_*(c₁(𝒩|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])` for the component morphism
`g : W ⟶ W'` of Stacks 0EEG (`AlgebraicGeometry.Space.properPushforwardChernDefect_eq`), and a
cycle on `W'` rationally equivalent to zero pushes forward to one rationally equivalent to zero
inside `|W'|`.

## Main definitions

* `properPushforwardChernDefect`: the defect at `W`.

## Main results

* `isRationallyEquivalentToZeroCanonical_properPushforward_firstChernCapCycleMap_sub`:
  the reduction.
* `isRationallyEquivalentToZeroWithinCanonical_zsmul_properPushforwardChernDefect`:
  the reduction of a defect to the subspace `W'`.

## References

* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Defect

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k)

/-- **The defect of the projection formula at one integral closed subspace.** For `W ⊆ X`, the
`k`-cycle `p_*(c₁(𝒩|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])` on `Y`, where `W'` is the
closure of the image of `|W|` and `deg(W/W')` the degree of Stacks 0EP1, part (1). -/
def properPushforwardChernDefect (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    CycleGroup D sY k :=
  properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
      (firstChernComponentCycle D sX hX k chernX W) -
    properCycleDegree D sX hX sY hY p W •
      firstChernComponentCycle D sY hY k chernY
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W)

/-- The coefficient of a cycle scaled by an integer is the scaled coefficient. -/
theorem zsmul_cycleGroup_apply {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (s : Z ⟶ D.space) (n : ℤ) (c : CycleGroup D s n) (a : ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem Z) : (a • c).1 T = a * c.1 T := by
  change a • c.1 T = a * c.1 T
  rw [zsmul_eq_mul, Int.cast_id]

include hX hY hpB hp

/-- At a fixed integral closed subspace `T ⊆ Y` only finitely many `W ⊆ X` with `α(W) ≠ 0`
contribute to the coefficient of `p_*(c₁(𝒩) ∩ α)` at `T`. -/
theorem finite_support_properPushforwardFirstChernCapTerm (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem X => α.1 W *
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernComponentCycle D sX hX k chernX W)).1 T).Finite := by
  refine ((finite_properPushforwardFirstChernCapSupport D hX hY hpB hp k chernX α T).image
    Prod.fst).subset fun W hW => ?_
  have hW' : α.1 W * (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      (firstChernComponentCycle D sX hX k chernX W).1 Z *
        properCycleMult D sX hX sY hY p Z T) ≠ 0 := hW
  obtain ⟨Z, hZ⟩ : ∃ Z, (firstChernComponentCycle D sX hX k chernX W).1 Z *
      properCycleMult D sX hX sY hY p Z T ≠ 0 := by
    by_contra h
    push Not at h
    exact hW' (by rw [finsum_eq_zero_of_forall_eq_zero h, mul_zero])
  refine ⟨(W, Z), ?_, rfl⟩
  change α.1 W * (firstChernComponentCycle D sX hX k chernX W).1 Z *
    properCycleMult D sX hX sY hY p Z T ≠ 0
  rw [mul_assoc]
  exact mul_ne_zero (left_ne_zero_of_mul hW') hZ

/-- At a fixed integral closed subspace `T ⊆ Y` only finitely many `W ⊆ X` with `α(W) ≠ 0`
contribute to the coefficient of `c₁(ℒ) ∩ p_*α` at `T`. -/
theorem finite_support_firstChernCapProperPushforwardTerm (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem X => α.1 W *
      (properCycleDegree D sX hX sY hY p W *
        (firstChernComponentCycle D sY hY k chernY
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W)).1 T)).Finite := by
  refine ((finite_firstChernCapProperPushforwardSupport D hX hY hpB hp k chernY α T).image
    Prod.fst).subset fun W hW => ?_
  refine ⟨(W, IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W), ?_, rfl⟩
  have hmult : properCycleMult D sX hX sY hY p W (IntegralClosedSubspace.closureImage D.site
        D.base D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p W) =
      properCycleDegree D sX hX sY hY p W := by
    unfold properCycleMult
    split_ifs with h
    · rfl
    · exact absurd rfl h
  change α.1 W * properCycleMult D sX hX sY hY p W _ * _ ≠ 0
  rw [hmult, mul_assoc]
  exact hW

/-- **The commutator of `p_*` and the cap product, as a sum of defects.** The coefficient of
`p_*(c₁(𝒩) ∩ α) - c₁(ℒ) ∩ p_*α` at an integral closed subspace `T ⊆ Y` is the `α`-weighted sum
over `W ⊆ X` of the coefficient at `T` of the defect at `W`. -/
theorem properPushforward_firstChernCapCycleMap_sub_apply (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) -
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W *
        (properPushforwardChernDefect D hX hY hpB hp k chernX chernY W).1 T := by
  change (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α)).1 T -
        (firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)).1 T = _
  rw [properPushforward_firstChernCapCoeff D hX hY hpB hp k chernX α T,
    firstChernCapCoeff_properPushforward D hX hY hpB hp k chernY α T,
    ← finsum_sub_distrib (finite_support_properPushforwardFirstChernCapTerm D hX hY hpB hp k
      chernX α T) (finite_support_firstChernCapProperPushforwardTerm D hX hY hpB hp k chernY α T)]
  refine finsum_congr fun W => ?_
  change _ = α.1 W * ((properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
      (firstChernComponentCycle D sX hX k chernX W)).1 T -
    (properCycleDegree D sX hX sY hY p W • firstChernComponentCycle D sY hY k chernY
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W)).1 T)
  rw [zsmul_cycleGroup_apply, mul_sub]

/-- **The reduction of Stacks 0EQT to a single integral closed subspace, in the Chow group.**
If for every integral closed subspace `W ⊆ X` of δ-dimension `k + 1` every integer multiple of
the defect at `W` is rationally equivalent to zero, at the canonical embeddings of Stacks 0ENK,
by integral closed subspaces of `Y` lying in the closure `W'` of the image of `|W|`, then for
every `(k + 1)`-cycle `α` on `X` the cycle `p_*(c₁(𝒩) ∩ α) - c₁(ℒ) ∩ p_*α` is rationally
equivalent to zero.

The carriers `|W'|` form a locally finite family as `W` ranges over the subspaces occurring in
`α`, by Stacks 0ENZ (`AlgebraicGeometry.Space.locallyFinite_closure_image_pointsMap`), and the
commutator is coefficientwise the sum of the multiples `α(W) · (defect at W)`
(`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_sub_apply`), so Stacks 0EQ8 at
the canonical embeddings applies. -/
theorem isRationallyEquivalentToZeroCanonical_properPushforward_firstChernCapCycleMap_sub
    (hdefect : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D sX W = k + 1 → ∀ a : ℤ,
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sY hY k
        (a • properPushforwardChernDefect D hX hY hpB hp k chernX chernY W)
        (subspacePointSet D.site D.base D.base_mem Y
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W).subspace))
    (α : CycleGroup D sX (k + 1)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) -
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)) := by
  classical
  let J := {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0}
  have hlf := (locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp.2.1.2
    (fun j : J => subspacePointSet D.site D.base D.base_mem X j.1.subspace)
    (fun j => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 j.1)
    (locallyFinite_cycleSupport α)).1
  have hE : (fun j : J => closure (pointsMap D.site D.base D.base_mem X p ''
      subspacePointSet D.site D.base D.base_mem X j.1.subspace)) = fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p j.1).subspace :=
    funext fun j => (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base
      D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p j.1).symm
  rw [hE] at hlf
  refine isRationallyEquivalentToZeroCanonical_finsum.{u + 1} D sY hY k (J := J)
    (fun j => α.1 j.1 • properPushforwardChernDefect D hX hY hpB hp k chernX chernY j.1)
    _ hlf (fun j => hdefect j.1 (α.2.2 j.1 j.2) (α.1 j.1)) fun T => ?_
  rw [properPushforward_firstChernCapCycleMap_sub_apply D hX hY hpB hp k chernX chernY α T]
  rw [finsum_congr fun j : J => zsmul_cycleGroup_apply D sY k _ _ T]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun W => α.1 W * (properPushforwardChernDefect D hX hY hpB hp k chernX chernY W).1 T)
    (fun W => α.1 W ≠ 0)).symm
  refine finsum_congr fun W => ?_
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul, finsum_eq_if, ite_eq_right (not_not.2 rfl)]
  · rw [finsum_eq_if, ite_eq_left hW]

/-- **A defect read on the closure of the image.** For `W ⊆ X` with closure `W'` of the image of
`|W|` and the component morphism `g : W ⟶ W'` of Stacks 0EEG, the defect at `W` is the
pushforward along `W' → Y` of the `k`-cycle

`g_*(c₁(𝒩|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`

on `W'`, the component cycles being extended by zero off δ-dimension `k + 1`. This is the square
`p_* i_* = i'_* g_*` of Stacks 0EP2,
`AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward_closureImage`. -/
theorem properPushforwardChernDefect_eq (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (g : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W).subspace.toFunctor)
    (hg : g ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι = W.subspace.ι ≫ p) :
    properPushforwardChernDefect D hX hY hpB hp k chernX chernY W =
      integralClosedSubspacePushforward D sY hY
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W) k
        (subspaceProperCyclePushforward D sX hX sY hY hpB hp W _ g hg k
            (chernComponentCycleOrZero D sX k chernX W) -
          properCycleDegree D sX hX sY hY p W •
            chernComponentCycleOrZero D sY k chernY
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) p W)) := by
  rw [properPushforwardChernDefect, firstChernComponentCycle_eq_pushforward D sX hX k chernX W,
    properCyclePushforward_integralClosedSubspacePushforward_closureImage D sX hX sY hY hpB hp W _
      g hg k, firstChernComponentCycle_eq_pushforward D sY hY k chernY, map_sub, map_zsmul]

/-- **A defect is rationally equivalent to zero inside `W'` once its reading on `W'` is.** If,
for the component morphism `g : W ⟶ W'` of Stacks 0EEG, the cycle
`g_*(c₁(𝒩|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])` on `W'` is rationally equivalent to
zero at the canonical embeddings of Stacks 0ENK, then every integer multiple of the defect at
`W` is rationally equivalent to zero by integral closed subspaces of `Y` lying in `W'`: the
pushforward along the closed immersion `W' → Y` carries the presenting family into `|W'|`
(`exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward`). -/
theorem isRationallyEquivalentToZeroWithinCanonical_zsmul_properPushforwardChernDefect
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (g : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) p W).subspace.toFunctor)
    (hg : g ≫ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι = W.subspace.ι ≫ p)
    (h : IsRationallyEquivalentToZeroCanonical.{u + 1} D
      ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY _) k
      (subspaceProperCyclePushforward D sX hX sY hY hpB hp W _ g hg k
          (chernComponentCycleOrZero D sX k chernX W) -
        properCycleDegree D sX hX sY hY p W •
          chernComponentCycleOrZero D sY k chernY
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) p W)))
    (a : ℤ) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sY hY k
      (a • properPushforwardChernDefect D hX hY hpB hp k chernX chernY W)
      (subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p W).subspace) := by
  have ha := (rationalEquivalencesCanonical.{u + 1} D _
      (isGood_integralClosedSubspace D sY hY _) k).zsmul_mem h a
  obtain ⟨K, U, hUfin, e, hsub, hdim, hprin, hsum⟩ :=
    exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward D sY hY
      _ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).isClosedSubspace k ha
  refine ⟨K, U, hUfin, e, hsub, hdim, hprin, ?_⟩
  rw [properPushforwardChernDefect_eq D hX hY hpB hp k chernX chernY W g hg, ← map_zsmul]
  exact hsum

end Defect

end AlgebraicGeometry.Space

end
