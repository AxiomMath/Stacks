module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleProjection
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.GlobalTop

/-!
# The top power of the cap product on a represented projective tower

In Situation 0EDT let `f : P → T` be a proper morphism of schemes of the site, flat of relative
dimension `n`, with `h_P` and `h_T` good, and `ℳ` an invertible `𝒪_{h_P}`-module whose reading
`ℳ_P` on `P` makes `(f, ℳ_P)` a projective tower of fibre dimension `n` locally on `T`. The
iterated cap products of Stacks 0EQJ on `h_P` are read on `P` as the iterated cap products of
Chapter 42 (`AlgebraicGeometry.Space.mk_cycleGroupEquivScheme_firstChernCapPowCycleMap`). If every
point of `T` has relative dimension at most `k`, then Stacks 02TW on `T`, where rational
equivalence of `k`-cycles is equality, gives

`f_*(c₁(ℳ)^n ∩ f^*α) = α`

for every `k`-cycle `α` on `h_T`.

## Main results

* `AlgebraicGeometry.Space.mk_cycleGroupEquivScheme_firstChernCapPowCycleMap`: the powers of the
  cap product on a represented space are the powers of the scheme cap product.
* `Stacks.Chow.eq_zero_of_mem_rationalEquivalences_of_relativeDimension_le`: no nonzero `k`-cycle
  is rationally equivalent to zero on a scheme all of whose points have relative dimension at
  most `k`.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_of_represented`:
  `f_*(c₁(ℳ)^n ∩ f^*α) = α`.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Power

variable (D : BaseSpaceDimensionSituation.{u}) {U : BigFppfOver D.site D.base D.base_mem}
    (sQ : yoneda.obj U ⟶ D.space) (hQ : D.IsGood sQ) {C : Stacks.Chow.ChowSituation.{u}}
    (s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S) [LocallyOfFiniteType s₀]
    (hδ : IsDeltaCompatible D U sQ C s₀)
    (M : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj U) hQ.1)
    (hM : IsInvertibleModule (B := D.site) ⟨yoneda.obj U, hQ.1⟩ M)

/-- The identification of cycle groups along an equality of degrees, read on the scheme. -/
theorem mk_cycleGroupEquivScheme_cycleGroupCast {a b : ℤ} (h : a = b) (γ : CycleGroup D sQ a) :
    (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ b (cycleGroupCast D sQ h γ)) :
        Stacks.Chow.chowGroup C s₀ b) =
      Stacks.Chow.chowGroupCast C s₀ h
        (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ a γ)) := by
  subst h
  rfl

/-- **The powers of the cap product on a represented space are the powers of the scheme cap
product.**  The class in `A_m(U)` of `c₁(ℳ)^s ∩ γ`, the `s`-fold cap product of Stacks 0EQJ at the
canonical choices, read on `U`, is `c₁(ℳ_U)^s ∩ γ`. -/
theorem mk_cycleGroupEquivScheme_firstChernCapPowCycleMap
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem U M)]
    (s : ℕ) (m : ℤ) (γ : CycleGroup D sQ (m + s)) :
    (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ m
        (firstChernCapPowCycleMap D sQ hQ M hM s m γ)) : Stacks.Chow.chowGroup C s₀ m) =
      Stacks.Chow.capPow C s₀ (Stacks.Chow.invCap C s₀
          (representedZariskiModule D.site D.base D.base_mem U M)) s (m + s) m rfl
        (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ (m + s) γ)) := by
  induction s generalizing m with
  | zero =>
    rw [Stacks.Chow.capPow_zero_apply]
    exact mk_cycleGroupEquivScheme_cycleGroupCast D sQ s₀ hδ _ γ
  | succ s ih =>
    rw [Stacks.Chow.capPow_succ_apply']
    change (QuotientAddGroup.mk (cycleGroupEquivScheme sQ s₀ hδ m
        (firstChernCapCycleMap D sQ hQ m (canonicalFirstChernRule D sQ hQ M hM m)
          (firstChernCapPowCycleMap D sQ hQ M hM s (m + 1)
            (cycleGroupCast D sQ (by push_cast; ring) γ)))) : Stacks.Chow.chowGroup C s₀ m) = _
    rw [mk_cycleGroupEquivScheme_firstChernCapCycleMap D sQ hQ s₀ hδ M hM m,
      ← Stacks.Chow.invCap_capOnChow_mk, QuotientAddGroup.mk'_apply, ih (m + 1)]
    congr 1
    rw [mk_cycleGroupEquivScheme_cycleGroupCast D sQ s₀ hδ _ γ, Stacks.Chow.capPow_cast]

end Power

/-! ### Chow groups in the top dimension of a scheme -/

/-- **On a scheme all of whose points have relative dimension at most `k`, no nonzero `k`-cycle
is rationally equivalent to zero**: rational equivalence in degree `k` is carried by integral
closed subschemes of δ-dimension `k + 1`, and there are none. -/
theorem _root_.Stacks.Chow.eq_zero_of_mem_rationalEquivalences_of_relativeDimension_le
    (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    {k : ℤ} (hk : ∀ x, Stacks.Chow.relativeDimension C.dimensionFunction p x ≤ k)
    {α : Stacks.Chow.CycleGroup C p k} (hα : α ∈ Stacks.Chow.rationalEquivalences C p k) :
    α = 0 := by
  obtain ⟨J, W, hW, hDim, -, g, hg⟩ := hα
  have hJ : IsEmpty J := ⟨fun j => by
    have h := hDim j
    rw [Stacks.Chow.schemeDeltaDimension_subschemeι_comp C p (W j) (hW j)] at h
    have := hk (Stacks.Chow.genericPointOf (W j) (hW j))
    have h' := WithBotTop.coe_injective h
    omega⟩
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [hg x, Stacks.Chow.principalDivisorFamilyCoefficient, finsum_of_isEmpty]
  rfl

/-! ### The top power on a represented projective tower -/

section Top

variable (D : BaseSpaceDimensionSituation.{u}) {T P : BigFppfOver D.site D.base D.base_mem}
    (sT : yoneda.obj T ⟶ D.space) (hT : D.IsGood sT) (sP : yoneda.obj P ⟶ D.space)
    (hP : D.IsGood sP) (f : P ⟶ T) (hfB : yoneda.map f ≫ sT = sP)
    (hf : IsQuasiCompact D.site D.base D.base_mem (yoneda.map f)) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem (yoneda.map f))
    (hrel : HasRelativeDimension n D.site D.base D.base_mem (yoneda.map f))
    (M : Modules.{u, u} D.site D.base D.base_mem (yoneda.obj P) hP.1)
    (hM : IsInvertibleModule (B := D.site) ⟨yoneda.obj P, hP.1⟩ M)
    {C : Stacks.Chow.ChowSituation.{u}}
    (s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T ⟶ C.S) [LocallyOfFiniteType s₀]
    [LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ s₀)]
    (hδT : IsDeltaCompatible D T sT C s₀)
    (hδP : IsDeltaCompatible D P sP C ((BigFppfOver.toScheme D.site D.base D.base_mem).map f ≫ s₀))

include hδT hδP in
/-- **The top power on a represented projective tower over a scheme of dimension at most `k`.**
Let `f : P → T` be a proper morphism of schemes of the site, flat of relative dimension `n`,
with `h_P → B`, `h_T → B` good and δ-compatible with a scheme situation `s₀ : T → C.S`, and let
`ℳ` be an invertible module on `h_P` whose reading `ℳ_P` on `P` makes `(f, ℳ_P)` a projective
tower of fibre dimension `n` locally on `T`.  If every point of `T` has relative dimension at
most `k`, then `f_*(c₁(ℳ)^n ∩ f^*α) = α` for every `k`-cycle `α` on `h_T`, the powers of the cap
product being those of Stacks 0EQJ at the canonical choices.

Read on the schemes the cycle is `f_*(c₁(ℳ_P)^n ∩ f^*α)` up to rational equivalence
(`AlgebraicGeometry.Space.mk_cycleGroupEquivScheme_firstChernCapPowCycleMap`), whose class is
the class of `α` by Stacks 02TW for a locally projective tower, and in degree `k` on `T` rational
equivalence is equality. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_of_represented
    [AlgebraicGeometry.IsProper ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj P).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj P).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem P M)]
    (htower : Stacks.Chow.IsLocallyProjectiveTower n
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)
      (representedZariskiModule D.site D.base D.base_mem P M))
    (k : ℤ) (hdimT : ∀ x, Stacks.Chow.relativeDimension C.dimensionFunction s₀ x ≤ k)
    (α : CycleGroup D sT k) :
    properCyclePushforward D sP hP sT hT hfB hf k
      (firstChernCapPowCycleMap D sP hP M hM n k
        (flatPullbackMap D sP hP sT hT (yoneda.map f) hfB n hflat hrel k (k + n) rfl α)) = α := by
  set f₀ := (BigFppfOver.toScheme D.site D.base D.base_mem).map f
  have : LocallyOfFiniteType f₀ := locallyOfFiniteType_of_comp _ s₀
  have : Flat f₀ := (holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
    isEtaleLocalOnSourceAndTarget_flat f).1 hflat
  have hπ := (hasRelativeDimension_yoneda_map_iff D.site D.base D.base_mem f n).1 hrel
  set γ := properCyclePushforward D sP hP sT hT hfB hf k
      (firstChernCapPowCycleMap D sP hP M hM n k
        (flatPullbackMap D sP hP sT hT (yoneda.map f) hfB n hflat hrel k (k + n) rfl α))
  -- the class of the cycle on `T` is the class of `α`
  have hcl : (QuotientAddGroup.mk (cycleGroupEquivScheme sT s₀ hδT k γ) :
      Stacks.Chow.chowGroup C s₀ k) =
      QuotientAddGroup.mk (cycleGroupEquivScheme sT s₀ hδT k α) := by
    have htop := htower.bundleProjection_self C s₀ (f₀ ≫ s₀) rfl hπ k
      (QuotientAddGroup.mk (cycleGroupEquivScheme sT s₀ hδT k α))
    refine Eq.trans ?_ htop
    rw [cycleGroupEquivScheme_properCyclePushforward hP hT hδP hδT f hfB hf rfl k]
    change _ = Stacks.Chow.properChowPushforward C (f₀ ≫ s₀) s₀ f₀ rfl k
      (Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper C (f₀ ≫ s₀) s₀
        f₀ rfl k)
      (Stacks.Chow.capPow C (f₀ ≫ s₀) (Stacks.Chow.invCap C (f₀ ≫ s₀)
          (representedZariskiModule D.site D.base D.base_mem P M)) n (k + n) k (by ring)
        (QuotientAddGroup.mk (Stacks.Chow.flatPullback C (f₀ ≫ s₀) s₀ f₀ rfl n hπ k
          (cycleGroupEquivScheme sT s₀ hδT k α))))
    rw [← cycleGroupEquivScheme_flatPullbackMap hP hT f hfB n hflat hrel hδT hδP k,
      ← mk_cycleGroupEquivScheme_firstChernCapPowCycleMap D sP hP _ hδP M hM n k]
    rfl
  have h0 := Stacks.Chow.eq_zero_of_mem_rationalEquivalences_of_relativeDimension_le C s₀ hdimT
    ((QuotientAddGroup.eq_iff_sub_mem).1 hcl)
  rw [sub_eq_zero] at h0
  exact (cycleGroupEquivScheme sT s₀ hδT k).injective h0

include hδT hδP in
/-- **The top coefficient on a represented projective tower over a scheme of dimension at most
`k`.**  In the situation of
`properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_of_represented`,
for every integral closed subspace `T' ⊆ h_T` of δ-dimension `k` the coefficient of
`f_*(c₁(ℳ)^n ∩ f^*[T'])` at `T'` is `1`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_self_of_represented
    [AlgebraicGeometry.IsProper ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj P).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj P).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem P M)]
    (htower : Stacks.Chow.IsLocallyProjectiveTower n
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map f)
      (representedZariskiModule D.site D.base D.base_mem P M))
    (k : ℤ) (hdimT : ∀ x, Stacks.Chow.relativeDimension C.dimensionFunction s₀ x ≤ k)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj T))
    (hT' : deltaDimension D sT T' = k) :
    (properCyclePushforward D sP hP sT hT hfB hf k
      (firstChernCapPowCycleMap D sP hP M hM n k
        (flatPullbackMap D sP hP sT hT (yoneda.map f) hfB n hflat hrel k (k + n) rfl
          (integralCycle D sT k T' hT')))).1 T' = 1 := by
  rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_of_represented D sT hT sP hP
    f hfB hf n hflat hrel M hM s₀ hδT hδP htower k hdimT, integralCycle_coe,
    integralCycleCoeff_self]

end Top

end AlgebraicGeometry.Space
