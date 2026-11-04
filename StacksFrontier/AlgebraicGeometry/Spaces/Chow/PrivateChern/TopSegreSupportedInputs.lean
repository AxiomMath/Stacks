module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.CapChain
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow

/-!
# The cap product, proper pushforward and flat pullback on subsets

In Situation 0EDT the three compatibilities of the operations on cycles with rational
equivalence — Stacks 0EQY for the cap product with a first Chern class, Stacks 0EQC for proper
pushforward and Stacks 0EQR for the commutation of flat pullback with the cap product — are
proved summand by summand, and each summand `(i_W)_* div(f)` of a rational equivalence is
carried to a cycle rationally equivalent to zero *on a definite subset*: on `|W|` for the cap
product, on the closure of the image of `|W|` for proper pushforward, and on the inverse image of
`|W|` for flat pullback. This file records the resulting forms on subsets, in the language of
`AlgebraicGeometry.Space.RationallyEquivalentOn`.

## Main results

* `rationallyEquivalentOn_of_withinCanonical`: the two spellings of rational equivalence to zero
  on a subset agree.
* `rationallyEquivalentOn_firstChernCapCycleMap`: Stacks 0EQY on subsets.
* `rationallyEquivalentOn_properCyclePushforward`: Stacks 0EQC on subsets.
* `rationallyEquivalentOn_flatPullbackMap_firstChernCapCycleMap`: Stacks 0EQR on subsets.

All of these are in the namespace `AlgebraicGeometry.Space.PrivateChern`.

## References

* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

section Within

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ}

/-- Rational equivalence to zero within `T` at the canonical embeddings is rational equivalence
to zero on `T`. -/
theorem rationallyEquivalentOn_of_withinCanonical {T : Set (points D.site D.base D.base_mem X)}
    {α : CycleGroup D sX k} (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    RationallyEquivalentOn.{v} D sX hX k T α 0 := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hdim, fun j => (hprin j).isPrincipalDivisorCycle, hsub,
    by rw [sub_zero]; exact hsum⟩

/-- Rational equivalence to zero on `T` is rational equivalence to zero within `T` at the
canonical embeddings. -/
theorem withinCanonical_of_rationallyEquivalentOn {T : Set (points D.site D.base D.base_mem X)}
    {α : CycleGroup D sX k} (h : RationallyEquivalentOn.{v} D sX hX k T α 0) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsub, hsum⟩ := h
  rw [sub_zero] at hsum
  exact ⟨J, W, hWfin, c, hsub, hdim, fun j => (hprin j).isPrincipalDivisorCycleOfGood D
    (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace, hsum⟩

end Within

/-! ### Stacks 0EQY on subsets -/

section Cap

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQY on subsets.** The cap product with `c₁(𝒩)` at the canonical choices carries a
cycle rationally equivalent to zero on `T` to a cycle rationally equivalent to zero on `T`. -/
theorem rationallyEquivalentOn_firstChernCapCycleMap (T : Set (points D.site D.base D.base_mem X))
    (k : ℤ) (α : CycleGroup D sX (k + 1))
    (hα : RationallyEquivalentOn.{u + 1} D sX hX (k + 1) T α 0) :
    RationallyEquivalentOn.{u + 1} D sX hX k T
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α) 0 :=
  rationallyEquivalentOn_firstChernCapCycleMap_of_summand.{u + 1} D sX hX k _
    (fun V hV d hd => rationallyEquivalentOn_of_withinCanonical D
      (isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_integralClosedSubspacePushforward
        D sX hX k N hN V d hV (hd.isPrincipalDivisorCycleOfGood D
          (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace))) T α hα

end Cap

/-! ### Stacks 0EQC on subsets -/

section Pushforward

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)

/-- The summand of Stacks 0EQC: the pushforward of a principal divisor on `W` is rationally
equivalent to zero on the closure of the image of `|W|`, witnessed by that closure alone. -/
theorem rationallyEquivalentOn_properCyclePushforward_summand (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D sX W = k + 1)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c) :
    RationallyEquivalentOn.{v} D sY hY k
      (closure (pointsMap D.site D.base D.base_mem X p ''
        subspacePointSet D.site D.base D.base_mem X W.subspace))
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (integralClosedSubspacePushforward D sX hX W k c)) 0 := by
  have hc' := hc.isPrincipalDivisorCycleOfGood D (isGood_integralClosedSubspace D sX hX W)
    W.isIntegralSpace
  obtain ⟨q, hq⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W
  rw [properCyclePushforward_integralClosedSubspacePushforward_closureImage D sX hX sY hY hpB hp
    W _ q hq k c]
  let W' := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W
  have hle : deltaDimension D sY W' ≤ k + 1 := by
    rw [← hW]
    exact IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY p hpB W
  by_cases h1 : deltaDimension D sY W' = k + 1
  · have hprin := isPrincipalDivisorCycleOfGood_subspaceProperCyclePushforward D sX hX sY hY hpB
      hp k W q hq hW h1 c hc'
    refine ⟨PUnit.{v + 1}, fun _ => W', locallyFinite_of_finite _, fun _ => _, fun _ => h1,
      fun _ => hprin.isPrincipalDivisorCycle, fun _ => ?_, ?_⟩
    · rw [IntegralClosedSubspace.subspacePointSet_closureImage]
    · refine Subtype.ext (funext fun Z => ?_)
      rw [sub_zero, cycleFamilySum_apply, finsum_unique]
  · have hzero : subspaceProperCyclePushforward D sX hX sY hY hpB hp W W' q hq k c = 0 := by
      rcases lt_or_eq_of_le (show deltaDimension D sY W' ≤ k by omega) with hlt | heq
      · exact cycleGroup_eq_zero_of_deltaDimension_lt D sY hY W' k hlt _
      · exact subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq D sX hX sY hY hpB hp k
          W q hq hW heq c hc'
    rw [hzero, map_zero]
    exact rationallyEquivalentOn_refl.{v} D sY hY k _ 0

/-- **Stacks 0EQC on subsets.** Proper pushforward carries a cycle rationally equivalent to zero
on `T` to a cycle rationally equivalent to zero on the closure of the image of `T`. -/
theorem rationallyEquivalentOn_properCyclePushforward (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) (α : CycleGroup D sX k)
    (hα : RationallyEquivalentOn.{v} D sX hX k T α 0) :
    RationallyEquivalentOn.{v} D sY hY k (closure (pointsMap D.site D.base D.base_mem X p '' T))
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k α) 0 :=
  rationallyEquivalentOn_properCyclePushforward_of_summand.{v} D sX hX sY hY hpB hp.2.1.2 k
    (fun W hW c hc => rationallyEquivalentOn_properCyclePushforward_summand.{v} D sX hX sY hY hpB
      hp k W hW c hc) T α hα

end Pushforward

/-! ### Stacks 0EQR on subsets -/

section FlatPullback

variable {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **Stacks 0EQR on subsets.** For a `(k + 1)`-cycle `α` on `Y` supported on `T`, the cycle
`f^*(c₁(ℒ) ∩ α) - c₁(f^*ℒ) ∩ f^*α` is rationally equivalent to zero on `|f|^{-1}(T)`, both cap
products at the canonical choices. -/
theorem rationallyEquivalentOn_flatPullbackMap_firstChernCapCycleMap (k : ℤ)
    (T : Set (points D.site D.base D.base_mem Y)) (α : CycleGroup D sY (k + 1))
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T) :
    RationallyEquivalentOn.{u + 1} D sX hX (k + (r : ℤ))
      (pointsMap D.site D.base D.base_mem X f ⁻¹' T)
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
        (firstChernCapCycleMap D sY hY k (canonicalFirstChernRule D sY hY L hL k) α))
      (firstChernCapCycleMap D sX hX (k + (r : ℤ))
        (canonicalFirstChernRule D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩)).obj L)
          (modulePullbackInvertible
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩) L hL) (k + (r : ℤ)))
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
          α)) := by
  classical
  rw [rationallyEquivalentOn_iff_zero]
  let J := {W : IntegralClosedSubspace D.site D.base D.base_mem Y // α.1 W ≠ 0}
  let F : J → CycleGroup D sX (k + (r : ℤ)) := fun j =>
    α.1 j.1 • flatChernDefect D sX hX sY hY f hbase r hflat hr k
      (canonicalFirstChernRule D sY hY L hL k)
      (canonicalFirstChernRule D sX hX
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩)).obj L)
        (modulePullbackInvertible
          (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨Y, hY.1⟩) L hL) (k + (r : ℤ))) j.1 (α.2.2 j.1 j.2)
  refine RationallyEquivalentOn.mono ?_ (rationallyEquivalentOn_of_withinCanonical D
    (isRationallyEquivalentToZeroWithinCanonical_finsum.{u + 1} D sX hX (k + (r : ℤ))
    (J := J) F
    (fun j => pointsMap D.site D.base D.base_mem X f ⁻¹'
      subspacePointSet D.site D.base D.base_mem Y j.1.subspace)
    ((AlgebraicGeometry.Space.locallyFinite_cycleSupport α).preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem f))
    (fun j => isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect D sX hX sY hY f
      hbase r hflat hr L hL k j.1 (α.2.2 j.1 j.2) (α.1 j.1)) fun Z => ?_))
  · exact Set.iUnion_subset fun j => Set.preimage_mono (hαT j.1 j.2)
  · show (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k _ α)).1 Z -
        (firstChernCapCycleMap D sX hX (k + (r : ℤ)) _
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
            α)).1 Z = _
    rw [flatPullbackMap_firstChernCapCycleMap_sub_apply]
    have hj : ∀ j : J, (F j).1 Z =
        α.1 j.1 * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k _ _ j.1 Z :=
      fun j => by
        rw [AddSubgroup.coe_zsmul, Pi.smul_apply, flatChernDefect_apply, smul_eq_mul]
    rw [finsum_congr hj]
    refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
      (f := fun W => α.1 W * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k _ _ W Z)
      (fun W => α.1 W ≠ 0)).symm
    refine finsum_congr fun W => ?_
    by_cases hW : α.1 W = 0
    · rw [hW, zero_mul, finsum_eq_if, if_neg (not_not.2 rfl)]
    · rw [finsum_eq_if, if_pos hW]

end FlatPullback

end AlgebraicGeometry.Space.PrivateChern

end
