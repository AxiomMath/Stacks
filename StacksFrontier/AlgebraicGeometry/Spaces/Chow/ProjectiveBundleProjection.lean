module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleMapOfKernelFamilySum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CyclesIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist

/-!
# Pushing forward the powers of `c₁(𝒪_P(1))` along a projective bundle

In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r = n + 1` and let `(π : P → X, 𝒪_P(1))` be its projective bundle. Stacks 0ERU asserts that for
`α ∈ CH_k(X)` the class `π_*(c₁(𝒪_P(1))^s ∩ π^*α) ∈ CH_{k+n-s}(X)` is `0` for `s < n` and is `α`
for `s = n`.

This file works with cycles. The `s`-fold cap product `c₁(ℒ)^s ∩ - : Z_{m+s}(X) → Z_m(X)` is the
composite of `s` cap products of Stacks 0EQJ at the canonical choices. The flat pullback of
Stacks 0EP8, the cap product and proper pushforward along a quasi-compact morphism all send a
cycle `∑ n_W [W]` to `∑ n_W φ(W)` for a cycle `φ(W)` lying over `W`, so the composite
`f_*(c₁(ℒ)^s ∩ f^*-)` along a flat morphism `f : Y → X` of relative dimension `n` sends `[W]` to a
`(k + n - s)`-cycle all of whose subspaces lie in `W`. As the δ-dimension of an integral closed
subspace of `W` is at most `δ(W) = k`, with equality only for `W` itself:

* for `s < n` the cycle `f_*(c₁(ℒ)^s ∩ f^*α)` is zero, for every invertible `ℒ` on `Y`: this is
  the dimension argument of the source, and it needs neither that `f` is a projective bundle nor
  any property of the cap product beyond where its cycles live;
* for `s = n` the cycle `f_*(c₁(ℒ)^n ∩ f^*[T])` is `d_T [T]` for an integer `d_T`, and
  `f_*(c₁(ℒ)^n ∩ f^*α)` has coefficient `α(T) d_T` at `T`. So the identity
  `f_*(c₁(ℒ)^n ∩ f^*α) = α` of cycles holds for all `α` exactly when `d_T = 1` for every `T`.

## Main definitions

* `AlgebraicGeometry.Space.cycleGroupCast`: the identification `Z_a(X) = Z_b(X)` for `a = b`.
* `AlgebraicGeometry.Space.firstChernCapPowCycleMap`: the `s`-fold cap product
  `c₁(ℒ)^s ∩ - : Z_{m+s}(X) → Z_m(X)` at the canonical choices.
* `AlgebraicGeometry.Space.flatPullbackKernel`: the cycles `f^*[W]`, as the kernel of the flat
  pullback.

## Main results

* `AlgebraicGeometry.Space.deltaDimension_le_and_eq_of_subspacePointSet_subset`: `|T| ⊆ |W|`
  implies `δ(T) ≤ δ(W)`, with equality only for `T = W`.
* `AlgebraicGeometry.Space.isCycleMapOfKernel_flatPullbackMap`,
  `AlgebraicGeometry.Space.IsCycleMapOfKernel.properPushforward` and
  `AlgebraicGeometry.Space.exists_isCycleMapOfKernel_firstChernCapPowCycleMap`: flat pullback,
  proper pushforward and the powers of the cap product are cycle maps of kernels.
* `AlgebraicGeometry.Space.properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero`:
  `f_*(c₁(ℒ)^s ∩ f^*α) = 0` for `s` below the relative dimension.
* `Space.properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_iff`:
  the identity `f_*(c₁(ℒ)^n ∩ f^*α) = α` reduced to the coefficient of `f_*(c₁(ℒ)^n ∩ f^*[T])` at
  `T`.
* `Space.properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_zero`:
  **Stacks 0ERU for `s < n`**, at the level of cycles.

## Implementation notes

The source reduces to `α = [Z]` and then to `X = Z` integral by the bivariance of the operations
(Stacks 0ERM, 0ERN). Here the reduction to `α = [Z]` is the statement that every operation
involved is the cycle map of a kernel lying over the subspaces of `X`
(`AlgebraicGeometry.Space.IsCycleMapOfKernel`), which needs no rational equivalence; for the same
reason the vanishing holds for cycles, not only for their classes. The source's rank `r` is
`n + 1` here: for `r = 0` the statement is empty.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Dimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

include hX in
/-- **The δ-dimension is monotone along inclusions of integral closed subspaces**, and it
determines the subspace among the integral closed subspaces of a given one: if `|T| ⊆ |W|` then
`δ(T) ≤ δ(W)`, with equality only for `T = W`. The generic point of `T` is a specialization of
that of `W`, and the dimension function drops strictly along a nontrivial specialization. -/
theorem deltaDimension_le_and_eq_of_subspacePointSet_subset
    {T W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hTW : subspacePointSet D.site D.base D.base_mem X T.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace) :
    deltaDimension D sX T ≤ deltaDimension D sX W ∧
      (deltaDimension D sX T = deltaDimension D sX W → T = W) := by
  have hT := T.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hW := W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hspec : W.ambientGenericPoint D.site D.base D.base_mem ⤳
      T.ambientGenericPoint D.site D.base D.base_mem :=
    hW.specializes (hTW hT.mem)
  by_cases heq : T.ambientGenericPoint D.site D.base D.base_mem =
      W.ambientGenericPoint D.site D.base D.base_mem
  · have hTW' : T = W :=
      (existsUnique_integralClosedSubspace_isGenericPoint_of_isGood D sX hX
        (W.ambientGenericPoint D.site D.base D.base_mem)).unique (heq ▸ hT) hW
    subst hTW'
    exact ⟨le_rfl, fun _ => rfl⟩
  · have hlt : D.deltaValue sX (T.ambientGenericPoint D.site D.base D.base_mem) <
        D.deltaValue sX (W.ambientGenericPoint D.site D.base D.base_mem) :=
      lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
        (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
          D.isAlgebraicSpace D.quasiSeparated)
        D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2 hspec (Ne.symm heq)
    have hlt' : deltaDimension D sX T < deltaDimension D sX W := hlt
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

end Dimension

section Kernels

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)

/-- The identification `Z_a(X) = Z_b(X)` for `a = b`. -/
def cycleGroupCast {a b : ℤ} (h : a = b) : CycleGroup D sX a →+ CycleGroup D sX b :=
  (AddEquiv.addSubgroupCongr (congrArg (cyclesOfDimension D sX) h)).toAddMonoidHom

/-- The cycle `cycleGroupCast h α` has the same coefficients as `α`. -/
@[simp]
theorem cycleGroupCast_coe {a b : ℤ} (h : a = b) (α : CycleGroup D sX a) :
    (cycleGroupCast D sX h α).1 = α.1 :=
  rfl

/-- The kernel of the identity of `Z_b(X)`: the cycle `[W]` of an integral closed subspace of
δ-dimension `b`, and `0` for the others. -/
def integralCycleOrZero (b : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    CycleGroup D sX b :=
  if hW : deltaDimension D sX W = b then integralCycle D sX b W hW else 0

/-- For `W` of δ-dimension `b`, the coefficient of `integralCycleOrZero b W` at `Z` is the
coefficient of `Z` in `[W]`. -/
theorem integralCycleOrZero_coe_apply {b : ℤ}
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = b) (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (integralCycleOrZero D sX b W).1 Z = integralCycleCoeff D W Z := by
  rw [integralCycleOrZero, dite_eq_left hW, integralCycle_coe]

/-- The identification `Z_a(X) = Z_b(X)` is the cycle map of the kernel `W ↦ [W]` over the
identity. -/
theorem isCycleMapOfKernel_cycleGroupCast {a b : ℤ} (h : a = b) :
    IsCycleMapOfKernel D sX sX id (cycleGroupCast D sX h) (integralCycleOrZero D sX b) where
  apply α Z := by
    rw [cycleGroupCast_coe, finsum_eq_single _ Z fun W hW => ?_]
    · by_cases hZ : α.1 Z = 0
      · rw [hZ, zero_mul]
      · rw [integralCycleOrZero_coe_apply D sX ((α.2.2 Z hZ).trans h), integralCycleCoeff_self,
          mul_one]
    · by_cases hαW : α.1 W = 0
      · rw [hαW, zero_mul]
      · rw [integralCycleOrZero_coe_apply D sX ((α.2.2 W hαW).trans h),
          integralCycleCoeff_eq_zero D W (Ne.symm hW), mul_zero]
  support W Z hZ := by
    by_cases hW : deltaDimension D sX W = b
    · rw [integralCycleOrZero_coe_apply D sX hW] at hZ
      by_cases hZW : Z = W
      · subst hZW
        exact subset_rfl
      · exact absurd (integralCycleCoeff_eq_zero D W hZW) hZ
    · rw [integralCycleOrZero, dite_eq_right hW] at hZ
      exact absurd rfl hZ

variable {D sX} in
/-- **A cycle map of a kernel over the identity raising the dimension is zero.** If
`Φ : Z_a(X) → Z_b(X)` is the cycle map of a kernel lying over the subspaces of `X` along the
identity, and `a < b`, then `Φ = 0`: a subspace `T` occurring in `φ(W)` is contained in `W`,
so `b = δ(T) ≤ δ(W) = a` for `W` occurring in a cycle. -/
theorem IsCycleMapOfKernel.eq_zero_of_lt (hX : D.IsGood sX) {a b : ℤ} (hab : a < b)
    {Φ : CycleGroup D sX a →+ CycleGroup D sX b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sX b}
    (h : IsCycleMapOfKernel D sX sX id Φ φ) (α : CycleGroup D sX a) : Φ α = 0 := by
  refine Subtype.ext (funext fun T => ?_)
  rw [h.apply]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul]
  by_cases hT : (φ W).1 T = 0
  · rw [hT, mul_zero]
  have hle := (deltaDimension_le_and_eq_of_subspacePointSet_subset D sX hX
    (h.support W T hT)).1
  have hTd := (φ W).2.2 T hT
  have hWd := α.2.2 W hW
  omega

variable {D sX} in
/-- **A cycle map of a kernel over the identity preserving the dimension is diagonal.** If
`Φ : Z_a(X) → Z_a(X)` is the cycle map of a kernel lying over the subspaces of `X` along the
identity, the coefficient of `Φ(α)` at `T` is `α(T)` times the coefficient of `φ(T)` at `T`. -/
theorem IsCycleMapOfKernel.apply_eq_mul (hX : D.IsGood sX) {a : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sX a}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sX a}
    (h : IsCycleMapOfKernel D sX sX id Φ φ) (α : CycleGroup D sX a)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Φ α).1 T = α.1 T * (φ T).1 T := by
  rw [h.apply, finsum_eq_single _ T fun W hWT => ?_]
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul]
  by_cases hT : (φ W).1 T = 0
  · rw [hT, mul_zero]
  have h' := deltaDimension_le_and_eq_of_subspacePointSet_subset D sX hX (h.support W T hT)
  exact absurd (h'.2 (((φ W).2.2 T hT).trans (α.2.2 W hW).symm)) (Ne.symm hWT)

variable {D sX} in
/-- On an integral closed subspace `T` of δ-dimension `a`, the kernel of a cycle map over the
identity preserving the dimension is a multiple of `[T]`. -/
theorem IsCycleMapOfKernel.kernel_eq_zsmul (hX : D.IsGood sX) {a : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sX a}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sX a}
    (h : IsCycleMapOfKernel D sX sX id Φ φ) {T : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hT : deltaDimension D sX T = a) :
    φ T = (φ T).1 T • integralCycle D sX a T hT := by
  refine Subtype.ext (funext fun Z => ?_)
  change (φ T).1 Z = (φ T).1 T * integralCycleCoeff D T Z
  by_cases hZT : Z = T
  · subst hZT
    rw [integralCycleCoeff_self, mul_one]
  · rw [integralCycleCoeff_eq_zero D T hZT, mul_zero]
    by_contra hZ
    have h' := deltaDimension_le_and_eq_of_subspacePointSet_subset D sX hX (h.support T Z hZ)
    exact hZT (h'.2 (((φ T).2.2 Z hZ).trans hT.symm))

end Kernels

section FlatPullbackKernel

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The kernel of the flat pullback `Z_m(Y) → Z_n(X)`: the cycle `f^*[W] = [f^{-1}(W)]_n` of
an integral closed subspace of δ-dimension `m`, and `0` for the others. -/
def flatPullbackKernel (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) : CycleGroup D sX n :=
  if hW : deltaDimension D sY W = m then
    cycleGroupCast D sX (by rw [hW, hmn])
      (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W)
  else 0

/-- **The flat pullback of cycles of Stacks 0EP8 is the cycle map of its kernel**, which lies
over the subspaces of `Y` along `|f|`. -/
theorem isCycleMapOfKernel_flatPullbackMap (m n : ℤ) (hmn : m + (r : ℤ) = n) :
    IsCycleMapOfKernel D sY sX (pointsMap D.site D.base D.base_mem X f)
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)
      (flatPullbackKernel D sX hX sY hY f hbase r hflat hr m n hmn) where
  apply α T := by
    rw [flatPullbackMap_apply]
    refine finsum_congr fun W => ?_
    by_cases hW : α.1 W = 0
    · rw [hW, zero_mul, zero_mul]
    · rw [flatPullbackKernel, dite_eq_left (α.2.2 W hW), cycleGroupCast_coe]
      rfl
  support W T hT := by
    by_cases hW : deltaDimension D sY W = m
    · rw [flatPullbackKernel, dite_eq_left hW, cycleGroupCast_coe] at hT
      exact subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
        W T hT
    · rw [flatPullbackKernel, dite_eq_right hW] at hT
      exact absurd rfl hT

end FlatPullbackKernel

section PushforwardKernel

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {f : Y ⟶ X} (hfB : f ≫ sX = sY) (hf : IsQuasiCompact D.site D.base D.base_mem f)

variable {D} in
/-- **Proper pushforward of a cycle map of a kernel.** If `Φ : Z_a(X) → Z_b(Y)` is the cycle
map of a kernel `φ` lying over the subspaces of `X` along `|f|` for a quasi-compact
`f : Y → X` over the base, then `f_* ∘ Φ` is the cycle map of the kernel `W ↦ f_* φ(W)`, which
lies over the subspaces of `X` along the identity: a subspace occurring in `f_* φ(W)` is the
closure of the image of a subspace lying over `|W|`, and `|W|` is closed.

The two sums may be exchanged since a contributing pair `(W, V)` has `W` occurring in the cycle
and containing the generic point of the subspace considered, and `V` among the finitely many
subspaces of `φ(W)` whose image closure is that subspace. -/
theorem IsCycleMapOfKernel.properPushforward {a b : ℤ} {Φ : CycleGroup D sX a →+ CycleGroup D sY b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sY b}
    (h : IsCycleMapOfKernel D sX sY (pointsMap D.site D.base D.base_mem Y f) Φ φ) :
    IsCycleMapOfKernel D sX sX id ((properCyclePushforward D sY hY sX hX hfB hf b).comp Φ)
      fun W => properCyclePushforward D sY hY sX hX hfB hf b (φ W) := by
  have hsupp : ∀ (W T : IntegralClosedSubspace D.site D.base D.base_mem X)
      (V : IntegralClosedSubspace D.site D.base D.base_mem Y), (φ W).1 V ≠ 0 →
      properCycleMult D sY hY sX hX f V T ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X T.subspace ⊆
          subspacePointSet D.site D.base D.base_mem X W.subspace := by
    intro W T V hV hVT
    rw [← ((properCycleMult_ne_zero_iff D sY hY sX hX f V T).1 hVT).1,
      IntegralClosedSubspace.subspacePointSet_closureImage]
    refine closure_minimal ?_ (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 _
      W.isClosedSubspace)
    rintro _ ⟨y, hy, rfl⟩
    exact h.support W V hV hy
  refine ⟨fun α T => ?_, fun W T hT => ?_⟩
  · have hfin : {WV : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem Y |
          α.1 WV.1 * (φ WV.1).1 WV.2 * properCycleMult D sY hY sX hX f WV.2 T ≠ 0}.Finite := by
      refine ((finite_setOf_ne_zero_mem_subspacePointSet D sX α
        (T.ambientGenericPoint D.site D.base D.base_mem)).biUnion fun W _ =>
          (Set.finite_singleton W).prod
            (finite_properCycleFibre D sY hY sX hX hfB hf (φ W).1 (φ W).2.1 T)).subset ?_
      rintro ⟨W, V⟩ hWV
      have hWV' : α.1 W * (φ W).1 V * properCycleMult D sY hY sX hX f V T ≠ 0 := hWV
      have h3 := right_ne_zero_of_mul hWV'
      have h12 := left_ne_zero_of_mul hWV'
      have hTW := hsupp W T V (right_ne_zero_of_mul h12) h3
      refine Set.mem_biUnion (x := W) ⟨left_ne_zero_of_mul h12,
        hTW (T.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).mem⟩
        ⟨rfl, right_ne_zero_of_mul h12,
          ((properCycleMult_ne_zero_iff D sY hY sX hX f V T).1 h3).1⟩
    change (properCyclePushforward D sY hY sX hX hfB hf b (Φ α)).1 T = _
    rw [properPushforward_apply]
    simp_rw [h.apply, finsum_mul]
    rw [finsum_comm_of_finite (fun W V => α.1 W * (φ W).1 V * properCycleMult D sY hY sX hX f V T)
      hfin]
    refine finsum_congr fun W => ?_
    rw [properPushforward_apply, mul_finsum]
    exact finsum_congr fun V => mul_assoc _ _ _
  · rw [properPushforward_apply] at hT
    obtain ⟨V, hV⟩ : ∃ V, (φ W).1 V * properCycleMult D sY hY sX hX f V T ≠ 0 := by
      by_contra hall
      exact hT (finsum_eq_zero_of_forall_eq_zero fun V => not_not.1 (not_exists.1 hall V))
    have hVT := right_ne_zero_of_mul hV
    exact hsupp W T V (left_ne_zero_of_mul hV) hVT

end PushforwardKernel

section Power

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The `s`-fold cap product `c₁(ℒ)^s ∩ - : Z_{m+s}(X) → Z_m(X)` at the level of cycles**: the
composite of `s` cap products of Stacks 0EQJ at the canonical choices. -/
def firstChernCapPowCycleMap : (s : ℕ) → (m : ℤ) → CycleGroup D sX (m + s) →+ CycleGroup D sX m
  | 0, m => cycleGroupCast D sX (by simp)
  | s + 1, m => (firstChernCapCycleMap D sX hX m (canonicalFirstChernRule D sX hX L hL m)).comp
      ((firstChernCapPowCycleMap s (m + 1)).comp (cycleGroupCast D sX (by push_cast; ring)))

/-- The `s`-fold cap product is the cycle map of a kernel lying over the subspaces of `X` along
the identity: so are the cap product (Stacks 0EQJ) and the identifications of cycle groups, and
cycle maps of kernels compose. -/
theorem exists_isCycleMapOfKernel_firstChernCapPowCycleMap (s : ℕ) (m : ℤ) :
    ∃ φ, IsCycleMapOfKernel D sX sX id (firstChernCapPowCycleMap D sX hX L hL s m) φ := by
  induction s generalizing m with
  | zero => exact ⟨_, isCycleMapOfKernel_cycleGroupCast D sX _⟩
  | succ s ih =>
    obtain ⟨φ, hφ⟩ := ih (m + 1)
    exact ⟨_, ((isCycleMapOfKernel_cycleGroupCast D sX _).comp hφ).comp
      (isCycleMapOfKernel_firstChernCapCycleMap D sX hX m _)⟩
end Power

section FlatProperProjection

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : Y ⟶ X) (hfB : f ≫ sX = sY) (hf : IsQuasiCompact D.site D.base D.base_mem f) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The composite `f_*(c₁(ℒ)^s ∩ f^*-)` is the cycle map of a kernel lying over the subspaces of
`X` along the identity. -/
theorem exists_isCycleMapOfKernel_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap
    (s : ℕ) (k m : ℤ) (h : k + n = m + s) :
    ∃ ψ, IsCycleMapOfKernel D sX sX id
      ((properCyclePushforward D sY hY sX hX hfB hf m).comp
        ((firstChernCapPowCycleMap D sY hY L hL s m).comp
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (m + s) h))) ψ := by
  obtain ⟨φ, hφ⟩ := exists_isCycleMapOfKernel_firstChernCapPowCycleMap D sY hY L hL s m
  exact ⟨_, ((isCycleMapOfKernel_flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (m + s)
    h).comp hφ).properPushforward hX hY hfB hf⟩

/-- **The vanishing half of Stacks 0ERU, at the level of cycles and for every flat morphism.**
Let `f : Y → X` be a quasi-compact morphism of good algebraic spaces over the base which is flat
of relative dimension `n`, and let `ℒ` be an invertible `𝒪_Y`-module. For `s < n` and every
`k`-cycle `α` on `X`, the cycle `f_*(c₁(ℒ)^s ∩ f^*α) ∈ Z_{k+n-s}(X)` is zero.

Each integral closed subspace occurring in `f_*(c₁(ℒ)^s ∩ f^*[W])` lies in `W`, and has
δ-dimension `k + n - s > k = δ(W)`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero (s : ℕ)
    (hs : s < n) (k m : ℤ) (h : k + n = m + s) (α : CycleGroup D sX k) :
    properCyclePushforward D sY hY sX hX hfB hf m
        (firstChernCapPowCycleMap D sY hY L hL s m
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (m + s) h α)) = 0 := by
  obtain ⟨ψ, hψ⟩ :=
    exists_isCycleMapOfKernel_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap
      D sX hX sY hY f hfB hf n hflat hrel L hL s k m h
  exact hψ.eq_zero_of_lt hX (by omega) α

/-- **The top power, reduced to one subspace.** For `f` flat of relative dimension `n` and
`α ∈ Z_k(X)`, the coefficient of `f_*(c₁(ℒ)^n ∩ f^*α)` at an integral closed subspace `T` of
δ-dimension `k` is `α(T)` times the coefficient at `T` of `f_*(c₁(ℒ)^n ∩ f^*[T])`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply (k : ℤ)
    (α : CycleGroup D sX k) (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T = k) :
    (properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl α))).1 T =
      α.1 T * (properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl
            (integralCycle D sX k T hT)))).1 T := by
  obtain ⟨ψ, hψ⟩ :=
    exists_isCycleMapOfKernel_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap
      D sX hX sY hY f hfB hf n hflat hrel L hL n k k rfl
  exact (hψ.apply_eq_mul hX α T).trans (by rw [← hψ.apply_integralCycle hT]; rfl)

/-- **The top power on one subspace is a multiple of it**: for an integral closed subspace `T`
of δ-dimension `k`, `f_*(c₁(ℒ)^n ∩ f^*[T]) = d_T [T]` with `d_T` its coefficient at `T`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_integralCycle (k : ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) (hT : deltaDimension D sX T = k) :
    properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl
            (integralCycle D sX k T hT))) =
      (properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl
            (integralCycle D sX k T hT)))).1 T • integralCycle D sX k T hT := by
  obtain ⟨ψ, hψ⟩ :=
    exists_isCycleMapOfKernel_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap
      D sX hX sY hY f hfB hf n hflat hrel L hL n k k rfl
  have h := hψ.apply_integralCycle hT
  exact h.trans ((hψ.kernel_eq_zsmul hX hT).trans (by rw [← h]; rfl))

/-- **The top power is the identity exactly when it is so on each subspace**: the identity
`f_*(c₁(ℒ)^n ∩ f^*α) = α` holds for every `k`-cycle `α` if and only if, for every integral
closed subspace `T` of δ-dimension `k`, the coefficient of `f_*(c₁(ℒ)^n ∩ f^*[T])` at `T` is `1`.
-/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_iff (k : ℤ) :
    (∀ α : CycleGroup D sX k, properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl α)) = α) ↔
      ∀ (T : IntegralClosedSubspace D.site D.base D.base_mem X) (hT : deltaDimension D sX T = k),
        (properCyclePushforward D sY hY sX hX hfB hf k
          (firstChernCapPowCycleMap D sY hY L hL n k
            (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl
              (integralCycle D sX k T hT)))).1 T = 1 := by
  refine ⟨fun h T hT => by rw [h, integralCycle_coe, integralCycleCoeff_self], fun h α => ?_⟩
  refine Subtype.ext (funext fun T => ?_)
  by_cases hα : α.1 T = 0
  · by_cases hT : deltaDimension D sX T = k
    · rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply D sX hX sY hY f
        hfB hf n hflat hrel L hL k α T hT, hα, zero_mul]
    · by_contra hne
      exact hT ((properCyclePushforward D sY hY sX hX hfB hf k
        (firstChernCapPowCycleMap D sY hY L hL n k
          (flatPullbackMap D sY hY sX hX f hfB n hflat hrel k (k + n) rfl α))).2.2 T
            (fun h0 => hne (h0.trans hα.symm)))
  · have hT := α.2.2 T hα
    rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply D sX hX sY hY f
      hfB hf n hflat hrel L hL k α T hT, h T hT, mul_one]

end FlatProperProjection


section ProjectiveBundle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))

/- Stacks 0ERU is completed in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ProjectiveBundleTopPower.lean`: the vanishing below
gives the case `s < n`, and the top power `s = n` is deduced from the reduction below by computing
the coefficient at `T` of `π_*(c₁(𝒪_P(1))^n ∩ π^*[T])`, which is `1`. -/

/-- **Stacks 0ERU, the vanishing.** Let `ℰ` be a finite locally free `𝒪_X`-module of rank `n + 1`
on a good algebraic space `X/B`, and `(π : P → X, 𝒪_P(1))` its projective bundle. For `s < n` and
every `k`-cycle `α` on `X`, the cycle `π_*(c₁(𝒪_P(1))^s ∩ π^*α) ∈ Z_{k+n-s}(X)` is zero; in
particular its class in `CH_{k+n-s}(X)` is zero. Here `π^*` is the flat pullback of cycles
(Stacks 0EP8), `c₁(𝒪_P(1))^s ∩ -` the `s`-fold cap product of Stacks 0EQJ at the canonical choices
and `π_*` the proper pushforward of cycles (Stacks 0EP1). -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_zero
    (s : ℕ) (hs : s < n) (k m : ℤ) (h : k + n = m + s) (α : CycleGroup D sX k) :
    properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
        (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 m
        (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
          (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
          (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) s m
          (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
            (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
            (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
            (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
            (m + s) h α)) = 0 :=
  properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_zero D sX hX _
    (isGood_projectiveBundleProj_comp D sX hX E hfree) _ rfl _ n _ _ _
    (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) s hs k m h α

/-- **Stacks 0ERU, the vanishing, in the Chow group**: for `s < n` the class of
`π_*(c₁(𝒪_P(1))^s ∩ π^*α)` in `CH_{k+n-s}(X)` is zero. -/
theorem chowClass_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle
    (s : ℕ) (hs : s < n) (k m : ℤ) (h : k + n = m + s) (α : CycleGroup D sX k) :
    chowClass.{v} D sX hX m
        (properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
          (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 m
          (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
            (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
            (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) s m
            (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
              (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
              (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
              (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
              (m + s) h α))) = 0 := by
  rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_zero
    D sX hX E hfree n hr s hs k m h α, map_zero]

/-- **Stacks 0ERU, the top power, reduced to one subspace.** For the projective bundle of a module
of rank `n + 1`, the identity `π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α` of `k`-cycles holds for every `α` if
and only if, for every integral closed subspace `T ⊆ X` of δ-dimension `k`, the coefficient of
`π_*(c₁(𝒪_P(1))^n ∩ π^*[T])` at `T` is `1`. That cycle is a multiple of `[T]`
(`Space.properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_integralCycle`).
-/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_self_iff
    (k : ℤ) :
    (∀ α : CycleGroup D sX k,
      properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
          (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 k
          (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
            (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
            (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) n k
            (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
              (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
              (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
              (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
              (k + n) rfl α)) = α) ↔
      ∀ (T : IntegralClosedSubspace D.site D.base D.base_mem X)
        (hT : deltaDimension D sX T = k),
        (properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
          (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 k
          (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
            (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
            (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) n k
            (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
              (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
              (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
              (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
              (k + n) rfl (integralCycle D sX k T hT)))).1 T = 1 :=
  properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_eq_self_iff D sX hX _
    (isGood_projectiveBundleProj_comp D sX hX E hfree) _ rfl _ n _ _ _
    (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) k

end ProjectiveBundle

end AlgebraicGeometry.Space

end
