module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# Flat pullback of a rational equivalence to zero, given Stacks 0EQA

In Situation 0EDT let `X, Y/B` be good and let `f : X ⟶ Y` be flat of relative dimension `r`.
Stacks 0EQB says that `α ∼_rat β` in `Z_m(Y)` gives `f^*α ∼_rat f^*β` in `Z_n(X)` for `m + r = n`.
This file proves it under the hypothesis that, for every integral closed subspace `V ⊆ Y` of
δ-dimension `m + 1` and every principal divisor `d` on `V`, the flat pullback `g^*d` along the
projection `g : V ×_Y X ⟶ V` is rationally equivalent to zero on `V ×_Y X` (Stacks 0EQA). Along the
way it shows that the proper pushforward of Stacks 0EP1 along the inclusion of a closed subspace is
the pushforward with which rational equivalence is written, and that
`f^*((i_V)_* d) = (i_{V'})_*(g^* d)` for the inverse image `V' = V ×_Y X` of Stacks 083Q.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackChowMap_of_flatPullbackBaseChange`: the induced
  homomorphism `CH_m(Y) → CH_n(X)`, given Stacks 0EQA.

## Main results

* `AlgebraicGeometry.Space.properCyclePushforward_ι_eq_cycleGroupClosedPushforward`: the proper
  pushforward of Stacks 0EP1 along the inclusion of a closed subspace is the pushforward with
  which rational equivalence is written.
* `AlgebraicGeometry.Space.flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward`:
  `f^*((i_V)_* d) = (i_{V'})_*(g^*d)` for `V' = V ×_Y X`.
* `Space.exists_cycleFamilySum_flatPullbackMap_integralClosedSubspacePushforward`:
  given Stacks 0EQA on `V ×_Y X`, `f^*((i_V)_* d)` is a locally finite sum of principal divisors
  on integral closed subspaces of `X` lying over `|V|`.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_flatPullbackBaseChange`
  and
  `AlgebraicGeometry.Space.rationallyEquivalent_flatPullbackMap_of_flatPullbackBaseChange`:
  flat pullback preserves rational equivalence, given Stacks 0EQA.

## References

* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Proper pushforward along the inclusion of a closed subspace -/

section Inclusion

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

/-- The degree of Stacks 0EP1 along the inclusion of a closed subspace is `1` at every integral
closed subspace of it. -/
theorem properCycleDegree_ι_eq_one_of_isClosedSubspace
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    properCycleDegree D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) sX hX Y.ι V = 1 := by
  have hdim : deltaDimension D sX (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hX.1 (D.isDecentSpace_of_isGood sX hX) Y.ι V) =
      deltaDimension D (Y.ι ≫ sX) V := by
    rw [IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1
      hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 V]
    exact IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V
  have hone : functionFieldDegree D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) sX hX Y.ι V = 1 :=
    IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX)
      (isDecentSpace_of_isGood D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY)) hY.2 V
  rw [properCycleDegree, ite_eq_left hdim, hone, Nat.cast_one]

open scoped Classical in
/-- The multiplicity of Stacks 0EP1 along the inclusion of a closed subspace is the indicator of
the image. -/
theorem properCycleMult_ι_of_isClosedSubspace
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleMult D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) sX hX Y.ι V Z =
      if IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 V = Z then 1 else 0 := by
  rw [properCycleMult, properCycleDegree_ι_eq_one_of_isClosedSubspace D sX hX Y hY V,
    IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V]

/-- The coefficients of the two pushforwards along the inclusion of a closed subspace agree: both
carry the coefficient at an integral closed subspace of `Y` to the coefficient at its image
in `X`, and vanish at an integral closed subspace of `X` which is not such an image. -/
theorem properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward_of_isClosedSubspace
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCyclePushforwardCoeff D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) sX hX
        Y.ι β Z =
      cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 β Z := by
  by_cases hex : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V = Z
  · obtain ⟨V₀, rfl⟩ := hex
    rw [cycleClosedPushforward_apply_pushforward, properCyclePushforwardCoeff]
    refine (finsum_eq_single _ V₀ ?_).trans ?_
    · intro V hV
      rw [properCycleMult_ι_of_isClosedSubspace D sX hX Y hY V, ite_eq_right fun h => hV
        (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 h), mul_zero]
    · rw [properCycleMult_ι_of_isClosedSubspace D sX hX Y hY V₀, ite_eq_left rfl, mul_one]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 β Z fun V hV => hex ⟨V, hV⟩,
      properCyclePushforwardCoeff]
    refine finsum_eq_zero_of_forall_eq_zero fun V => ?_
    rw [properCycleMult_ι_of_isClosedSubspace D sX hX Y hY V, ite_eq_right fun h => hex ⟨V, h⟩,
      mul_zero]

/-- The proper pushforward of Stacks 0EP1 along the inclusion of a closed subspace is the
pushforward with which rational equivalence is written. -/
theorem properCyclePushforward_ι_eq_cycleGroupClosedPushforward (k : ℤ)
    (c : CycleGroup D (Y.ι ≫ sX) k) :
    properCyclePushforward D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) sX hX
        (f := Y.ι) rfl
        (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem hY.2) k c =
      cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k c :=
  Subtype.ext (funext fun Z =>
    properCyclePushforwardCoeff_ι_eq_cycleClosedPushforward_of_isClosedSubspace D sX hX Y hY c.1 Z)

end Inclusion

/-! ### The inverse image of an integral closed subspace as a cartesian square -/

section BaseChange

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y)

include hX hY in
/-- The inverse image `V ×_Y X` of an integral closed subspace of `Y` is good over the base. -/
theorem isGood_ι_preimage_integralClosedSubspace :
    D.IsGood ((V.subspace.preimage f).ι ≫ sX) :=
  isGood_ι_of_isClosedSubspace D sX hX _
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V)

include hbase in
/-- The projection `g : V ×_Y X ⟶ V` of Stacks 083Q is a morphism over the base. -/
theorem fromPreimage_comp_ι_comp :
    V.subspace.fromPreimage f ≫ (V.subspace.ι ≫ sY) = (V.subspace.preimage f).ι ≫ sX := by
  rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, hbase]

include hX hY hbase hflat hr in
/-- The projection `g : V ×_Y X ⟶ V` is flat of relative dimension `r`. -/
theorem isFlat_and_hasRelativeDimension_fromPreimage :
    IsFlat D.site D.base D.base_mem (V.subspace.fromPreimage f) ∧
      HasRelativeDimension r D.site D.base D.base_mem (V.subspace.fromPreimage f) :=
  (isFlat_and_hasRelativeDimension_of_isPullback D
    ((V.subspace.preimage f).ι ≫ sX)
    (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
    (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V) sX hX sY hY
    (fromPreimage_comp_ι_comp D sX sY f hbase V) hbase
    (Subfunctor.isPullback_preimage f V.subspace) r hflat hr).2

include hbase hflat hr in
/-- For an integral closed subspace `V ⊆ Y` and a cycle `d ∈ Z_m(V)`,

`f^*((i_V)_* d) = (i_{V'})_*(g^* d)`   in `Z_n(X)`,   `m + r = n`,

where `V' = V ×_Y X` is the inverse image of Stacks 083Q, `i_{V'} : V' ⟶ X` its inclusion and
`g : V' ⟶ V` the projection. -/
theorem flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward
    (m n : ℤ) (hmn : m + (r : ℤ) = n) (d : CycleGroup D (V.subspace.ι ≫ sY) m) :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (integralClosedSubspacePushforward D sY hY V m d) =
      cycleGroupClosedPushforward D hX.1
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V).1
        (D.isDecentSpace_of_isGood sX hX)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V).2 sX hX.2.2
        ((V.subspace.preimage f).ι ≫ sX) rfl n
        (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
          (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
          (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
          (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
          (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
          m n hmn d) := by
  have hpre := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V
  rw [← properCyclePushforward_ι_eq_integralClosedSubspacePushforward D sY hY V m d,
    ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sX hX
      (V.subspace.preimage f) hpre n _]
  exact flatPullback_properPushforward_unconditional D
    ((V.subspace.preimage f).ι ≫ sX)
    (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
    (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V) sX hX sY hY
    (fromPreimage_comp_ι_comp D sX sY f hbase V) rfl rfl hbase r hflat hr
    (Subfunctor.isPullback_preimage f V.subspace)
    (isProper_of_isClosedImmersion D.site D.base D.base_mem V.isClosedSubspace.1 hY.1
      V.subspace.ι V.isClosedSubspace.2) m n hmn d

end BaseChange

/-! ### The summand half of Stacks 0EQB, given Stacks 0EQA -/

section Summand

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- Let `V ⊆ Y` be an integral closed subspace and `d ∈ Z_m(V)`. If the flat pullback `g^*d` along
the projection `g : V ×_Y X ⟶ V` is rationally equivalent to zero on `V ×_Y X`, then
`f^*((i_V)_*d)` is the sum of Stacks 0EQ6, part (1), over a locally finite family of integral
closed subspaces of `X` of δ-dimension `n + 1` whose point sets lie in `|f|^{-1}(|V|)`, with
principal divisors as summands. -/
theorem exists_cycleFamilySum_flatPullbackMap_integralClosedSubspacePushforward
    (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (d : CycleGroup D (V.subspace.ι ≫ sY) m)
    (hEQA : IsRationallyEquivalentToZero.{v} D ((V.subspace.preimage f).ι ≫ sX)
      (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V) n
      (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
        (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
        (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
        m n hmn d)) :
    ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hUfin : LocallyFinite fun l : K =>
        subspacePointSet D.site D.base D.base_mem X (U l).subspace)
      (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) n),
      (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
          pointsMap D.site D.base D.base_mem X f ⁻¹'
            subspacePointSet D.site D.base D.base_mem Y V.subspace) ∧
        (∀ l, deltaDimension D sX (U l) = n + 1) ∧
          (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) n (e l)) ∧
            flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
                (integralClosedSubspacePushforward D sY hY V m d) =
              cycleFamilySum D sX hX U hUfin n e := by
  obtain ⟨K, U, hUfin, e, hsub, hdim, hprin, heq⟩ :=
    exists_cycleFamilySum_subset_of_isRationallyEquivalentToZero_closedPushforward.{v} D sX hX
      (V.subspace.preimage f) (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V)
      n hEQA
  refine ⟨K, U, hUfin, e, fun l => (hsub l).trans
    (subspacePointSet_preimage D.site D.base D.base_mem f V.subspace).subset, hdim, hprin, ?_⟩
  rwa [flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sX hX sY hY f
    hbase r hflat hr V m n hmn d]

/-- The flat pullback of an `m`-cycle rationally equivalent to zero on `Y` is rationally equivalent
to zero on `X`, given that for every integral closed subspace `V ⊆ Y` of δ-dimension `m + 1` and
every principal divisor `d` on `V` the flat pullback of `d` along the projection `V ×_Y X ⟶ V` is
rationally equivalent to zero on `V ×_Y X` (Stacks 0EQA). -/
theorem isRationallyEquivalentToZero_flatPullbackMap_of_flatPullbackBaseChange (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hEQA : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          IsRationallyEquivalentToZero.{v} D ((V.subspace.preimage f).ι ≫ sX)
            (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V) n
            (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
              (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
              (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
              (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
              m n hmn d))
    {α : CycleGroup D sY m} (hα : IsRationallyEquivalentToZero.{v} D sY hY m α) :
    IsRationallyEquivalentToZero.{v} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) :=
  isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor.{v} D sX hX sY hY f hbase r
    hflat hr m n hmn
    (fun V hVdim d hd =>
      exists_cycleFamilySum_flatPullbackMap_integralClosedSubspacePushforward.{v} D sX hX sY hY f
        hbase r hflat hr m n hmn V d (hEQA V hVdim d hd))
    hα

/-- In Situation 0EDT let `X, Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r`, and
let `α ∼_rat β` be rationally equivalent `m`-cycles on `Y`. Given Stacks 0EQA on the base changes
`V ×_Y X`, as in
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_flatPullbackBaseChange`,
`f^*α ∼_rat f^*β` as `n`-cycles on `X`, where `m + r = n`. -/
theorem rationallyEquivalent_flatPullbackMap_of_flatPullbackBaseChange (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hEQA : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          IsRationallyEquivalentToZero.{v} D ((V.subspace.preimage f).ι ≫ sX)
            (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V) n
            (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
              (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
              (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
              (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
              m n hmn d))
    {α β : CycleGroup D sY m} (h : RationallyEquivalent.{v} D sY hY m α β) :
    RationallyEquivalent.{v} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α)
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn β) :=
  rationallyEquivalent_cycleHom.{v} D sX hX sY hY m n
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)
    (fun _ hγ => isRationallyEquivalentToZero_flatPullbackMap_of_flatPullbackBaseChange.{v} D sX
      hX sY hY f hbase r hflat hr m n hmn hEQA hγ) h

/-- The flat pullback `f^* : CH_m(Y) → CH_n(X)` on the Chow groups of Stacks 0EQ6, part (4), for
`m + r = n`, given Stacks 0EQA on the base changes `V ×_Y X`. -/
def flatPullbackChowMap_of_flatPullbackBaseChange (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (hEQA : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          IsRationallyEquivalentToZero.{v} D ((V.subspace.preimage f).ι ≫ sX)
            (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V) n
            (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
              (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
              (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
              (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
              (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
              m n hmn d)) :
    chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n :=
  chowGroupHomOfCycleHom.{v} D sX hX sY hY m n
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)
    fun _ hγ => isRationallyEquivalentToZero_flatPullbackMap_of_flatPullbackBaseChange.{v} D sX hX
      sY hY f hbase r hflat hr m n hmn hEQA hγ

end Summand

end AlgebraicGeometry.Space

end
