module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPowRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSurjectiveAffineFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent

/-!
# The top power of the cap product along a flat proper morphism, over the integral subspaces

Let `π : P → X` be a proper morphism of good algebraic spaces over the base, flat of relative
dimension `n`, and `ℒ` an invertible `𝒪_P`-module. For an integral closed subspace `T ⊆ X` of
δ-dimension `k` the cycle `π_*(c₁(ℒ)^n ∩ π^*[T])` is a multiple `d_T [T]`
(`properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_integralCycle`), and the
identity `π_*(c₁(ℒ)^n ∩ π^*α) = α` of cycles (the top power of Stacks 0ERU) is the assertion
`d_T = 1` for all `T`. The source reduces it to `X = T` by bivariance. Here that reduction is an
exact identity of cycles, with no rational equivalence: along the inclusion of `π^{-1}(T)` the
cap products at the canonical rule on `P` are the cap products at the rule transported to
`π^{-1}(T)` (`cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule`), and flat pullback
and proper pushforward commute with pushforward along closed subspaces.

On `T` itself the comparison of the transported rule with the canonical rule of `ℒ|_{π^{-1}(T)}`
is a rational equivalence, but in the top degree `k = dim_δ(T)` there are no nonzero cycles
rationally equivalent to zero
(`eq_zero_of_isRationallyEquivalentToZeroCanonical_of_forall_deltaDimension_le`). So the
identity of cycles on `X` follows from the identity of classes
`π_{T,*}(c₁(ℒ_T)^n ∩ π_T^*[T]) = [T]` in `CH_k(T)` for every integral closed subspace `T`.

## Main results

* `eq_zero_of_isRationallyEquivalentToZeroCanonical_of_forall_deltaDimension_le`: in the top
  degree a cycle rationally equivalent to zero is zero.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_cycleGroupClosedPushforward`:
  the exact identity along the inclusion of a closed subspace of the base.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_of_forall`: the top
  power of Stacks 0ERU from its class on each integral closed subspace.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

/-! ### Cycles rationally equivalent to zero in the top degree -/

section TopDegree

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **In the top degree a cycle rationally equivalent to zero is zero**: if every integral closed
subspace of `X` has δ-dimension at most `k`, a `k`-cycle rationally equivalent to zero vanishes,
the presenting family being empty. -/
theorem eq_zero_of_isRationallyEquivalentToZeroCanonical_of_forall_deltaDimension_le (k : ℤ)
    (hk : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, deltaDimension D sX W ≤ k)
    {α : CycleGroup D sX k} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    α = 0 := by
  obtain ⟨J, W, hWfin, c, hdim, -, rfl⟩ := hα
  have hJ : IsEmpty J := ⟨fun j => by have := hk (W j); rw [hdim j] at this; omega⟩
  refine Subtype.ext (funext fun Z => ?_)
  exact finsum_of_isEmpty _

/-- In the top degree the class map is injective. -/
theorem eq_of_chowClassCanonical_eq_of_forall_deltaDimension_le (k : ℤ)
    (hk : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, deltaDimension D sX W ≤ k)
    {α β : CycleGroup D sX k}
    (h : chowClassCanonical.{v} D sX hX k α = chowClassCanonical.{v} D sX hX k β) : α = β :=
  sub_eq_zero.1 (eq_zero_of_isRationallyEquivalentToZeroCanonical_of_forall_deltaDimension_le D sX
    hX k hk ((chowClassCanonical_eq_iff_rationallyEquivalentCanonical.{v} D sX hX k α β).1 h))

end TopDegree


/-! ### The base change to a closed subspace of the base -/

section Closed

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (Z : Subfunctor X) (hZ : IsClosedSubspace D.site D.base D.base_mem Z)

include sX hX sP hP hp hZ in
/-- The base change `π^{-1}(Z) → Z` of a proper morphism is proper (Stacks 04WP). -/
theorem isProper_fromPreimage_of_isClosedSubspace :
    IsProper D.site D.base D.base_mem (Z.fromPreimage π) :=
  isProper_of_isPullback'
    (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ).1 hP.1 hZ.1 hX.1
    (Subfunctor.isPullback_preimage π Z).flip hp

/-- **Along the inclusion of a closed subspace `Z ⊆ X`, `π_*(c₁(ℒ)^n ∩ π^*-)` is pushed forward
from `Z`, exactly**: for `β ∈ Z_k(Z)`,
`π_*(c₁(ℒ)^n ∩ π^*(i_*β)) = i_*(π_{Z,*}(c₁(ℒ)^n ∩ π_Z^*β))`, the cap products on `π^{-1}(Z)`
being taken at the rule transported from `P`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_cycleGroupClosedPushforward
    (k : ℤ) (β : CycleGroup D (Z.ι ≫ sX) k) :
    properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl
            (cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hZ.2 sX
              hX.2.2 (Z.ι ≫ sX) rfl k β))) =
      cycleGroupClosedPushforward D hX.1 hZ.1 (D.isDecentSpace_of_isGood sX hX) hZ.2 sX hX.2.2
        (Z.ι ≫ sX) rfl k
        (properCyclePushforward D ((Z.preimage π).ι ≫ sP)
          (isGood_ι_of_isClosedSubspace D sP hP _
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
          (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
          (fromPreimage_comp_structureMorphism D sP sX π hπB Z)
          (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z hZ).2.1.2 k
          (firstChernCapPowCycleMapOfRule D ((Z.preimage π).ι ≫ sP)
            (isGood_ι_of_isClosedSubspace D sP hP _
              (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
            (fun m => closedSubspaceChernRule D sP hP (Z.preimage π)
              (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ) m
              (canonicalFirstChernRule D sP hP L hL m)) n k
            (flatPullbackMap D ((Z.preimage π).ι ≫ sP)
              (isGood_ι_of_isClosedSubspace D sP hP _
                (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
              (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) (Z.fromPreimage π)
              (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
              (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
                hflat hrel).1
              (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
                hflat hrel).2 k (k + n) rfl β))) := by
  have hc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ
  have hcP : IsProper D.site D.base D.base_mem (Z.preimage π).ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem hc.1 hP.1 _ hc.2
  have hZP : IsProper D.site D.base D.base_mem Z.ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem hZ.1 hX.1 _ hZ.2
  have hpZ := isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z hZ
  rw [flatPullbackMap_cycleGroupClosedPushforward D sP hP sX hX π hπB n hflat hrel Z hZ k β,
    ← firstChernCapPowCycleMapOfRule_canonicalFirstChernRule D sP hP L hL n,
    ← cycleGroupClosedPushforward_firstChernCapPowCycleMapOfRule D sP hP (Z.preimage π) hc,
    ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sP hP (Z.preimage π) hc,
    ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sX hX Z hZ,
    properCyclePushforward_comp D _ sP sX _ hP hX rfl hπB hcP hp,
    properCyclePushforward_comp D _ _ sX _ _ hX _ rfl hpZ hZP]
  exact properCyclePushforward_congr D _ _ sX hX (Subfunctor.fromPreimage_ι Z π).symm _ _ _ _ k _

/-- The top power `π_{Z,*}(c₁(ℒ_Z)^n ∩ π_Z^*β)` over a closed subspace `Z ⊆ X` of the base, for
the base change `π_Z : π^{-1}(Z) → Z` and the restriction `ℒ_Z` of `ℒ` to `π^{-1}(Z)`, at the
canonical rule of `ℒ_Z`. -/
def closedBaseChangeTopPowerCycle (k : ℤ) (β : CycleGroup D (Z.ι ≫ sX) k) :
    CycleGroup D (Z.ι ≫ sX) k :=
  properCyclePushforward D ((Z.preimage π).ι ≫ sP)
    (isGood_ι_of_isClosedSubspace D sP hP _
      (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
    (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
    (fromPreimage_comp_structureMorphism D sP sX π hπB Z)
    (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z hZ).2.1.2 k
    (firstChernCapPowCycleMap D ((Z.preimage π).ι ≫ sP)
      (isGood_closedSubspace D sP hP
        ⟨Z.preimage π, isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ⟩)
      (closedSubspaceModuleRestrict D sP hP L
        ⟨Z.preimage π, isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ⟩)
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1 (Z.preimage π)
        (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ)) L hL) n k
      (flatPullbackMap D ((Z.preimage π).ι ≫ sP)
        (isGood_ι_of_isClosedSubspace D sP hP _
          (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
        (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) (Z.fromPreimage π)
        (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
        (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
          hflat hrel).1
        (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
          hflat hrel).2 k (k + n) rfl β))

/-- The transported rule and the canonical rule of `ℒ_Z` give rationally equivalent top powers. -/
theorem chowClassCanonical_closedBaseChangeTopPowerCycle (k : ℤ) (β : CycleGroup D (Z.ι ≫ sX) k) :
    chowClassCanonical.{u + 1} D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) k
        (properCyclePushforward D ((Z.preimage π).ι ≫ sP)
          (isGood_ι_of_isClosedSubspace D sP hP _
            (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
          (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ)
          (fromPreimage_comp_structureMorphism D sP sX π hπB Z)
          (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z hZ).2.1.2 k
          (firstChernCapPowCycleMapOfRule D ((Z.preimage π).ι ≫ sP)
            (isGood_ι_of_isClosedSubspace D sP hP _
              (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
            (fun m => closedSubspaceChernRule D sP hP (Z.preimage π)
              (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ) m
              (canonicalFirstChernRule D sP hP L hL m)) n k
            (flatPullbackMap D ((Z.preimage π).ι ≫ sP)
              (isGood_ι_of_isClosedSubspace D sP hP _
                (isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ))
              (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) (Z.fromPreimage π)
              (fromPreimage_comp_structureMorphism D sP sX π hπB Z) n
              (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
                hflat hrel).1
              (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sP hP sX hX π hπB Z hZ n
                hflat hrel).2 k (k + n) rfl β))) =
      chowClassCanonical.{u + 1} D (Z.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Z hZ) k
        (closedBaseChangeTopPowerCycle D sX hX sP hP π hπB n hflat hrel hp L hL Z hZ k β) := by
  have hc := isClosedSubspace_preimage_of_isClosedSubspace D sP hP sX hX π Z hZ
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical closedBaseChangeTopPowerCycle
  rw [← map_sub]
  refine isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ _ _ _ _
    (isProper_fromPreimage_of_isClosedSubspace D sX hX sP hP π hp Z hZ) k _ ?_
  exact isRationallyEquivalentToZeroCanonical_firstChernCapPowCycleMapOfRule_sub D _ _
    (closedSubspaceModuleRestrict D sP hP L ⟨Z.preimage π, hc⟩)
    (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1 (Z.preimage π) hc)
      L hL) _
    (fun m β' =>
      isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_closedSubspaceChernRule_sub
        D sP hP L hL ⟨Z.preimage π, hc⟩ m β') n k _

end Closed

/-! ### The top power from the integral closed subspaces -/

section Integral

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)

include hX in
/-- The top integral closed subspace of `T` has the δ-dimension of `T`. -/
theorem IntegralClosedSubspace.deltaDimension_top_eq
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D (T.subspace.ι ≫ sX)
        (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
          T.isIntegralSpace) = deltaDimension D sX T := by
  conv_rhs => rw [← IntegralClosedSubspace.pushforward_top_eq D sX hX T]
  rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 T.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2]

variable {P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The top power of Stacks 0ERU from its class over each integral closed subspace.** If for
every integral closed subspace `T ⊆ X` of δ-dimension `k` the class in `CH_k(T)` of
`π_{T,*}(c₁(ℒ_T)^n ∩ π_T^*[T])` is `[T]`, then `π_*(c₁(ℒ)^n ∩ π^*α) = α` for every `k`-cycle `α`
on `X`, as cycles. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_of_forall (k : ℤ)
    (htop : ∀ (T : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hT : deltaDimension D sX T = k),
      chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
          (closedBaseChangeTopPowerCycle D sX hX sP hP π hπB n hflat hrel hp L hL T.subspace
            T.isClosedSubspace k
            (integralCycle D (T.subspace.ι ≫ sX) k
              (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
                T.isIntegralSpace)
              ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT))) =
        chowClassCanonical.{u + 1} D (T.subspace.ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
          (integralCycle D (T.subspace.ι ≫ sX) k
            (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
              T.isIntegralSpace)
            ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT)))
    (α : CycleGroup D sX k) :
    properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl α)) = α := by
  refine (properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_iff D sX hX sP hP
    π hπB hp.2.1.2 n hflat hrel L hL k).2 (fun T hT => ?_) α
  set β := integralCycle D (T.subspace.ι ≫ sX) k
    (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1 T.isIntegralSpace)
    ((IntegralClosedSubspace.deltaDimension_top_eq D sX hX T).trans hT)
  have hβ : integralCycle D sX k T hT = cycleGroupClosedPushforward D hX.1 T.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2 sX hX.2.2 (T.subspace.ι ≫ sX) rfl
      k β := by
    refine Subtype.ext ?_
    rw [cycleGroupClosedPushforward_integralCycle_coe D (T.subspace.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) sX hX
      T.isClosedSubspace.2 rfl k, IntegralClosedSubspace.pushforward_top_eq D sX hX T]
    rfl
  have hw := eq_of_chowClassCanonical_eq_of_forall_deltaDimension_le D (T.subspace.ι ≫ sX)
    (isGood_ι_of_isClosedSubspace D sX hX T.subspace T.isClosedSubspace) k
    (fun V => (IntegralClosedSubspace.deltaDimension_comp_ι_le D sX hX T V).trans hT.le)
    ((chowClassCanonical_closedBaseChangeTopPowerCycle D sX hX sP hP π hπB n hflat hrel hp L hL
      T.subspace T.isClosedSubspace k β).trans (htop T hT))
  rw [hβ,
    properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_cycleGroupClosedPushforward
      D sX hX sP hP π hπB n hflat hrel hp L hL T.subspace T.isClosedSubspace k β, hw, ← hβ,
    integralCycle_coe, integralCycleCoeff_self]

end Integral

end AlgebraicGeometry.Space

end
