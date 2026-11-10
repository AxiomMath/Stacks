module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSides
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback

/-!
# Iterated cap products, rational equivalence and base change

In Situation 0EDT let `ℒ` be an invertible module on a good algebraic space. This file collects
the properties of the iterated cap products `c₁(ℒ)^s ∩ -` of Stacks 0EQJ, at the canonical
choices, that the proof of Stacks 0ERU uses to read a coefficient of
`π_*(c₁(ℒ)^n ∩ π^*α)` on smaller spaces.

* Along the inclusion `i : Y → X` of a closed subspace, `c₁(ℒ)^s ∩ i_*β` is
  `i_*(c₁(ℒ|_Y)^s ∩ β + R)` with `R` rationally equivalent to zero on `Y`: the difference at each
  step is a locally finite sum of canonical principal divisors inside `|Y|`, which descends to
  `Y`.
* Along a flat morphism `f`, `f^*(c₁(ℒ)^s ∩ β)` and `c₁(f^*ℒ)^s ∩ f^*β` have the same class in the
  Chow group at the canonical embeddings (Stacks 0EQR iterated).
* A `k`-cycle rationally equivalent to zero on a space with no integral closed subspace of
  δ-dimension `k + 1` is zero.

Consequently, for `π : P → X` proper and flat of relative dimension `n` and an integral closed
subspace `T ⊆ X` of δ-dimension `k`, the coefficient of `π_*(c₁(ℒ)^n ∩ π^*[T])` at `T` is read on
the inverse image `π^{-1}(T) → T`, and then on any étale chart `U → T` without integral closed
subspaces of δ-dimension `k + 1`, at a component of the inverse image of `T`.

## Main results

* `IsCanonicallyRationallyEquivalentToZeroWithin.exists_cycleGroupClosedPushforward_eq`:
  a rational equivalence inside the image of a closed immersion comes from its source.
* `IsRationallyEquivalentToZeroCanonical.eq_zero_of_forall_deltaDimension_ne`:
  no rational equivalence in the top dimension.
* `exists_firstChernCapPowCycleMap_closedSubspaceCyclePushforward_eq`:
  the iterated cap product along the inclusion of a closed subspace.
* `chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap`:
  Stacks 0EQR for the iterated cap product.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_eq_preimage`:
  the top coefficient read on the inverse image of `T`.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_preimageComponent`:
  the top coefficient read on an étale chart.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Within

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQY with a carrier.**  The cap product of Stacks 0EQJ at the canonical choices
carries a `(k+1)`-cycle rationally equivalent to zero within a set `S ⊆ |X|`, at the canonical
embeddings of Stacks 0ENK, to a `k`-cycle rationally equivalent to zero within `S`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.firstChernCap {k : ℤ}
    {S : Set (points D.site D.base D.base_mem X)} {α : CycleGroup D sX (k + 1)}
    (hα : IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + 1) α S) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α) S := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, rfl⟩ := hα
  refine (isRationallyEquivalentToZeroWithinCanonical_finsum D sX hX k
    (fun j => firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
      (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)))
    (fun j => subspacePointSet D.site D.base D.base_mem X (W j).subspace) hWfin
    (fun j =>
isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_integralClosedSubspacePushforward
        D sX hX k N hN (W j) (c j) (hdim j) (hprin j))
    (fun Z => firstChernCapCycleMap_cycleFamilySum_apply D sX hX k _ W hWfin c Z)).mono
    (Set.iUnion_subset hsub)

end Within

/-! ### Descent of a rational equivalence along a closed immersion -/

section ClosedImmersion

variable (D : BaseSpaceDimensionSituation.{u})
    {X T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sT : T ⟶ D.space) (hT : D.IsGood sT) {j : T ⟶ X}
    (hj : IsClosedImmersion D.site D.base D.base_mem j) (hjs : j ≫ sX = sT)

/-- **A rational equivalence inside the image of a closed immersion comes from the source.** Let
`j : T → X` be a closed immersion over the base and `S ⊆ |X|` a set inside the image of `|j|`. A
`k`-cycle on `X` which is a locally finite sum of canonical principal divisors on integral closed
subspaces with point sets in `S` is the pushforward `j_* β` of such a sum `β` on `T`, with point
sets in `|j|⁻¹(S)`: each subspace is the image of one of `T`, and its principal divisor is carried
back along the isomorphism with that image. -/
theorem IsCanonicallyRationallyEquivalentToZeroWithin.exists_cycleGroupClosedPushforward_eq
    {k : ℤ} {α : CycleGroup D sX k} {S : Set (points D.site D.base D.base_mem X)}
    (hS : S ⊆ Set.range (pointsMap D.site D.base D.base_mem T j))
    (h : IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k α S) :
    ∃ β : CycleGroup D sT k,
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sT hT k β
          (pointsMap D.site D.base D.base_mem T j ⁻¹' S) ∧
        cycleGroupClosedPushforward D hX.1 hT.1 (D.isDecentSpace_of_isGood sX hX) hj sX hX.2.2 sT
          hjs k β = α := by
  have hdec := D.isDecentSpace_of_isGood sX hX
  have hTdec := D.isDecentSpace_of_isGood sT hT
  obtain ⟨J, W, hWfin, c, hsub, hcan, rfl⟩ := h
  choose V hV using fun i => IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
    hX.1 hT.1 hdec hTdec hj (W i) ((hsub i).trans hS)
  obtain rfl : W = fun i => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1
      hdec hj (V i) := funext fun i => (hV i).symm
  choose c' hc' heq using fun i =>
    exists_integralClosedSubspacePushforward_eq_cycleGroupClosedPushforward sT hT hj hjs (V i)
      (hcan i)
  have hpts : ∀ i, subspacePointSet D.site D.base D.base_mem T (V i).subspace ⊆
      pointsMap D.site D.base D.base_mem T j ⁻¹'
        subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hT.1 hdec hj
            (V i)).subspace := by
    intro i x hx
    rw [Set.mem_preimage, IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.mem_image_of_mem _ hx
  have hfin : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem T (V i).subspace :=
    (hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem j)).subset hpts
  exact ⟨cycleFamilySum D sT hT V hfin k c',
    ⟨J, V, hfin, c', fun i => (hpts i).trans (Set.preimage_mono (hsub i)), hc', rfl⟩,
    cycleGroupClosedPushforward_cycleFamilySum sT hT hj hjs V hfin hWfin c' c heq⟩

end ClosedImmersion

/-! ### Rational equivalence in the top dimension -/

section TopDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **No rational equivalence in the top dimension.** If no integral closed subspace of `X` has
δ-dimension `k + 1`, then a `k`-cycle rationally equivalent to zero is zero: the presenting
family of Stacks 0EQ6 is empty. -/
theorem IsRationallyEquivalentToZeroCanonical.eq_zero_of_forall_deltaDimension_ne {k : ℤ}
    (hdim : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, deltaDimension D sX W ≠ k + 1)
    {α : CycleGroup D sX k} (h : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    α = 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, -, rfl⟩ := h
  have : IsEmpty J := ⟨fun j => hdim (W j) (hWdim j)⟩
  exact Subtype.ext (funext fun Z => (cycleFamilySum_apply D sX hX W hWfin k c Z).trans
    (finsum_of_isEmpty _))

end TopDimension

/-! ### The cap product along the inclusion of a closed subspace -/

section ClosedSubspace

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQT for the inclusion of a closed subspace, as a pushforward.** For a closed
subspace `i : Y → X` and a `(k+1)`-cycle `β` on `Y`,

`c₁(𝒩) ∩ i_*β = i_*(c₁(𝒩|_Y) ∩ β + R)`

for a `k`-cycle `R` on `Y` rationally equivalent to zero, the cap products being those of
Stacks 0EQJ at the canonical choices on `X` and on `Y`. The difference
`c₁(𝒩) ∩ i_*β - i_*(c₁(𝒩|_Y) ∩ β)` is a locally finite sum of canonical principal divisors on
integral closed subspaces of `X` inside `|Y|`
(`exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum`), hence the
pushforward of such a sum on `Y`. -/
theorem exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_eq {k : ℤ}
    (β : CycleGroup D (Y.1.ι ≫ sX) (k + 1)) :
    ∃ R : CycleGroup D (Y.1.ι ≫ sX) k,
      IsRationallyEquivalentToZeroCanonical.{u + 1} D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) k R ∧
        firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
            (closedSubspaceCyclePushforward D sX hX Y (k + 1) β) =
          closedSubspaceCyclePushforward D sX hX Y k
            (firstChernCapCycleMap D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y) k
              (canonicalFirstChernRule D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
                (closedSubspaceModuleRestrict D sX hX N Y)
                (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1
                  Y.2) N hN) k) β + R) := by
  obtain ⟨hk, g, h⟩ :=
    exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_sub_eq_cycleFamilySum D sX hX Y
      N hN β
  have hwithin : IsCanonicallyRationallyEquivalentToZeroWithin.{u, u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (closedSubspaceCyclePushforward D sX hX Y (k + 1) β) -
        closedSubspaceCyclePushforward D sX hX Y k (firstChernCapCycleMap D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) k (canonicalFirstChernRule D (Y.1.ι ≫ sX)
            (isGood_closedSubspace D sX hX Y) (closedSubspaceModuleRestrict D sX hX N Y)
            (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
              N hN) k) β))
      (Set.range (pointsMap D.site D.base D.base_mem Y.1.toFunctor Y.1.ι)) := by
    rw [h]
    refine ⟨_, _, locallyFinite_closedSubspaceComponentImage_of_ne_zero D sX hX Y β, _,
      fun V => ?_, fun V => ⟨hk V, g V, rfl⟩, rfl⟩
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  obtain ⟨R, hR, hpush⟩ := hwithin.exists_cycleGroupClosedPushforward_eq D sX hX (Y.1.ι ≫ sX)
    (isGood_closedSubspace D sX hX Y) Y.2.2 rfl subset_rfl
  refine ⟨R, hR.isRationallyEquivalentToZeroCanonical, ?_⟩
  rw [map_add]
  exact (eq_add_of_sub_eq' hpush.symm)

/-- Reading a cycle on `Y` in another, equal, degree commutes with pushing it forward to `X`. -/
theorem cycleGroupCast_closedSubspaceCyclePushforward {a b : ℤ} (h : a = b)
    (β : CycleGroup D (Y.1.ι ≫ sX) a) :
    cycleGroupCast D sX h (closedSubspaceCyclePushforward D sX hX Y a β) =
      closedSubspaceCyclePushforward D sX hX Y b (cycleGroupCast D (Y.1.ι ≫ sX) h β) :=
  Subtype.ext rfl

/-- **The `s`-fold cap product along the inclusion of a closed subspace, as a pushforward.** For
a closed subspace `i : Y → X` and an `(m+s)`-cycle `β` on `Y`,

`c₁(𝒩)^s ∩ i_*β = i_*(c₁(𝒩|_Y)^s ∩ β + R)`

for an `m`-cycle `R` on `Y` rationally equivalent to zero, the iterated cap products being those
of Stacks 0EQJ at the canonical choices on `X` and on `Y`. By induction on `s`: each cap product
on `X` of a pushforward is the pushforward of the cap product on `Y` up to a cycle rationally
equivalent to zero on `Y`
(`AlgebraicGeometry.Space.exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_eq`), and
the cap product on `Y` preserves rational equivalence to zero (Stacks 0EQY). -/
theorem exists_firstChernCapPowCycleMap_closedSubspaceCyclePushforward_eq (s : ℕ) (m : ℤ)
    (β : CycleGroup D (Y.1.ι ≫ sX) (m + s)) :
    ∃ R : CycleGroup D (Y.1.ι ≫ sX) m,
      IsRationallyEquivalentToZeroCanonical.{u + 1} D (Y.1.ι ≫ sX)
          (isGood_closedSubspace D sX hX Y) m R ∧
        firstChernCapPowCycleMap D sX hX N hN s m
            (closedSubspaceCyclePushforward D sX hX Y (m + s) β) =
          closedSubspaceCyclePushforward D sX hX Y m
            (firstChernCapPowCycleMap D (Y.1.ι ≫ sX) (isGood_closedSubspace D sX hX Y)
              (closedSubspaceModuleRestrict D sX hX N Y)
              (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1
                Y.2) N hN) s m β + R) := by
  induction s generalizing m with
  | zero =>
    refine ⟨0, isRationallyEquivalentToZeroCanonical_zero D _ _ m, ?_⟩
    rw [add_zero]
    exact Subtype.ext rfl
  | succ s ih =>
    have hYg := isGood_closedSubspace D sX hX Y
    have hNY := modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y.1 Y.2)
      N hN
    have hcast : m + ((s + 1 : ℕ) : ℤ) = m + 1 + (s : ℤ) := by push_cast; ring
    obtain ⟨R₁, hR₁, h₁⟩ := ih (m + 1) (cycleGroupCast D (Y.1.ι ≫ sX) hcast β)
    obtain ⟨R₂, hR₂, h₂⟩ := exists_firstChernCapCycleMap_closedSubspaceCyclePushforward_eq D sX hX
      Y N hN (firstChernCapPowCycleMap D (Y.1.ι ≫ sX) hYg
        (closedSubspaceModuleRestrict D sX hX N Y) hNY s (m + 1)
          (cycleGroupCast D (Y.1.ι ≫ sX) hcast β) + R₁)
    refine ⟨firstChernCapCycleMap D (Y.1.ι ≫ sX) hYg m (canonicalFirstChernRule D (Y.1.ι ≫ sX)
      hYg (closedSubspaceModuleRestrict D sX hX N Y) hNY m) R₁ + R₂,
      isRationallyEquivalentToZeroCanonical_add D _ hYg m
        (isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule D
          (Y.1.ι ≫ sX) hYg m (closedSubspaceModuleRestrict D sX hX N Y) hNY hR₁) hR₂, ?_⟩
    simp only [firstChernCapPowCycleMap, AddMonoidHom.comp_apply]
    rw [cycleGroupCast_closedSubspaceCyclePushforward, h₁, h₂]
    exact congrArg _ ((congrArg (· + R₂) (map_add _ _ _)).trans (add_assoc _ _ _))

end ClosedSubspace

/-! ### Reduction of the top coefficient to the inverse image -/

section Preimage

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP) {π : P ⟶ X}
    (hbase : π ≫ sX = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hr : HasRelativeDimension n D.site D.base D.base_mem π)
    (hproper : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

include hX hP hproper in
/-- **Stacks 0EPD, first assertion, at the inverse image.** The projection
`π^{-1}(T) ⟶ T` of the inverse image of an integral closed subspace along a proper morphism is
proper. -/
theorem isProper_fromPreimage (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsProper D.site D.base D.base_mem (T.subspace.fromPreimage π) :=
  isProper_of_isPullback D.site D.base D.base_mem
    (isClosedSubspace_preimage_integralClosedSubspace D sP hP sX hX π T).1 hP.1
    T.isClosedSubspace.1 hX.1 (Subfunctor.isPullback_preimage π T.subspace).flip hproper

/-- **The top coefficient of `π_*(c₁(ℒ)^n ∩ π^*[T])` is read on the inverse image of `T`.** Let
`π : P → X` be proper and flat of relative dimension `n` between good spaces, `ℒ` an invertible
`𝒪_P`-module and `T ⊆ X` an integral closed subspace of δ-dimension `k`, with inverse image
`P_T = π^{-1}(T)` and projection `π_T : P_T → T`. The coefficient at `T` of the `k`-cycle
`π_*(c₁(ℒ)^n ∩ π^*[T])` on `X` is the coefficient at `T` itself of the `k`-cycle
`π_{T*}(c₁(ℒ|_{P_T})^n ∩ π_T^*[T])` on `T`, the cap products being those of Stacks 0EQJ at the
canonical choices.

By Stacks 0EPD at the inverse image `π^*[T] = i'_*π_T^*[T]`, where `i' : P_T → P` is the
inclusion; the iterated cap product of a pushforward along `i'` is the pushforward of the iterated
cap product on `P_T` up to a cycle `R` on `P_T` rationally equivalent to zero; pushing forward
along `π` is pushing forward along `π_T` and then along `T → X`; and `π_{T*}R` is a `k`-cycle on
`T` rationally equivalent to zero (Stacks 0EQC), hence zero, since no integral closed subspace of
`T` has δ-dimension `k + 1`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_eq_preimage
    (k : ℤ) (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T = k)
    (htop : deltaDimension D (T.subspace.ι ≫ sX)
      (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
        T.isIntegralSpace) = k) :
    (properCyclePushforward D sP hP sX hX hbase hproper.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sX hX π hbase n hflat hr k (k + n) rfl
            (integralCycle D sX k T hT)))).1 T =
      (properCyclePushforward D ((T.subspace.preimage π).ι ≫ sP)
          (isGood_ι_preimage_integralClosedSubspace D sP hP sX hX π T)
          (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T)
          (fromPreimage_comp_ι_comp D sP sX π hbase T)
          (isProper_fromPreimage D sX hX sP hP hproper T).2.1.2 k
          (firstChernCapPowCycleMap D ((T.subspace.preimage π).ι ≫ sP)
            (isGood_ι_preimage_integralClosedSubspace D sP hP sX hX π T)
            (closedSubspaceModuleRestrict D sP hP L ⟨T.subspace.preimage π,
              isClosedSubspace_preimage_integralClosedSubspace D sP hP sX hX π T⟩)
            (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1
              (T.subspace.preimage π)
              (isClosedSubspace_preimage_integralClosedSubspace D sP hP sX hX π T)) L hL) n k
            (flatPullbackMap D ((T.subspace.preimage π).ι ≫ sP)
              (isGood_ι_preimage_integralClosedSubspace D sP hP sX hX π T)
              (T.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX T)
              (T.subspace.fromPreimage π) (fromPreimage_comp_ι_comp D sP sX π hbase T) n
              (isFlat_and_hasRelativeDimension_fromPreimage D sP hP sX hX π hbase n hflat hr T).1
              (isFlat_and_hasRelativeDimension_fromPreimage D sP hP sX hX π hbase n hflat hr T).2
              k (k + n) rfl
              (integralCycle D (T.subspace.ι ≫ sX) k
                (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
                  T.isIntegralSpace) htop)))).1
        (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
          T.isIntegralSpace) := by
  set E : ClosedSubspaces D.site D.base D.base_mem P := ⟨T.subspace.preimage π,
    isClosedSubspace_preimage_integralClosedSubspace D sP hP sX hX π T⟩
  have hTg := isGood_integralClosedSubspace D sX hX T
  have hEg := isGood_closedSubspace D sP hP E
  set top := IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
    T.isIntegralSpace
  have h₁ := flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sP hP sX hX π
    hbase n hflat hr T k (k + n) rfl (integralCycle D (T.subspace.ι ≫ sX) k top htop)
  rw [integralClosedSubspacePushforward_integralCycle_top D sX hX T hT htop] at h₁
  rw [h₁]
  obtain ⟨R, hR, h₂⟩ := exists_firstChernCapPowCycleMap_closedSubspaceCyclePushforward_eq D sP hP E
    L hL n k (flatPullbackMap D ((T.subspace.preimage π).ι ≫ sP) hEg (T.subspace.ι ≫ sX) hTg
      (T.subspace.fromPreimage π) (fromPreimage_comp_ι_comp D sP sX π hbase T) n
      (isFlat_and_hasRelativeDimension_fromPreimage D sP hP sX hX π hbase n hflat hr T).1
      (isFlat_and_hasRelativeDimension_fromPreimage D sP hP sX hX π hbase n hflat hr T).2
      k (k + n) rfl (integralCycle D (T.subspace.ι ≫ sX) k top htop))
  rw [h₂]
  rw [properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq D hP hX hEg hTg E.2.2 rfl
    T.isClosedSubspace.2 rfl (Subfunctor.fromPreimage_ι T.subspace π) hbase hproper.2.1.2
    (fromPreimage_comp_ι_comp D sP sX π hbase T)
    (isProper_fromPreimage D sX hX sP hP hproper T).2.1.2 k]
  have hzero := IsRationallyEquivalentToZeroCanonical.eq_zero_of_forall_deltaDimension_ne D
    (T.subspace.ι ≫ sX) hTg (fun V hV => by
      have hle := (deltaDimension_le_and_eq_of_subspacePointSet_subset D (T.subspace.ι ≫ sX) hTg
        (T := V) (W := top) (fun x _ => by
          rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
          exact Set.mem_univ x)).1
      rw [hV, htop] at hle
      omega)
    (isRationallyEquivalentToZeroCanonical_properCyclePushforward D _ hEg _ hTg
      (fromPreimage_comp_ι_comp D sP sX π hbase T)
      (isProper_fromPreimage D sX hX sP hP hproper T) k R hR)
  rw [map_add, hzero, add_zero]
  refine Eq.trans ?_ (cycleClosedPushforward_apply_pushforward D hX.1 T.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) T.isClosedSubspace.2 _ top)
  rw [IntegralClosedSubspace.pushforward_top_eq D sX hX T]
  rfl

end Preimage

/-! ### Flat pullback of the iterated cap product -/

section FlatPullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (L' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')

/-- **Stacks 0EQR for the iterated cap product.** Let `f : X → Y` be flat of relative dimension
`r` between good spaces, `ℒ` an invertible `𝒪_Y`-module and `ℒ'` an invertible `𝒪_X`-module with
`ℒ' ≅ f^*ℒ`. For an `(m+s)`-cycle `β` on `Y`,

`f^*(c₁(ℒ)^s ∩ β) = c₁(ℒ')^s ∩ f^*β`   in `CH_{m+r}(X)`,

the iterated cap products being those of Stacks 0EQJ at the canonical choices and the Chow group
that of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. By induction on `s`, from
Stacks 0EQR for one cap product, the invariance of the cap product under isomorphisms of
invertible modules, and Stacks 0EQY. -/
theorem chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap
    (e : L' ≅ (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩)).obj L)
    (s : ℕ) (m n : ℤ) (hmn : m + (r : ℤ) = n) (hmn' : m + (s : ℤ) + (r : ℤ) = n + (s : ℤ))
    (β : CycleGroup D sY (m + s)) :
    chowClassCanonical.{u + 1} D sX hX n
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
          (firstChernCapPowCycleMap D sY hY L hL s m β)) =
      chowClassCanonical.{u + 1} D sX hX n
        (firstChernCapPowCycleMap D sX hX L' hL' s n
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (m + s) (n + s) hmn' β)) := by
  induction s generalizing m n with
  | zero => exact congrArg _ (Subtype.ext rfl)
  | succ s ih =>
    subst hmn
    have hcast : m + ((s + 1 : ℕ) : ℤ) = m + 1 + (s : ℤ) := by push_cast; ring
    have hcast' : m + (r : ℤ) + ((s + 1 : ℕ) : ℤ) = m + (r : ℤ) + 1 + (s : ℤ) := by
      push_cast; ring
    simp only [firstChernCapPowCycleMap, AddMonoidHom.comp_apply]
    have h₁ := chowClassCanonical_flatPullbackMap_firstChernCapCycleMap D sX hX sY hY f hbase r
      hflat hr L hL m (firstChernCapPowCycleMap D sY hY L hL s (m + 1)
        (cycleGroupCast D sY hcast β))
    rw [h₁, canonicalFirstChernCapCanonical_congr_iso hX _ L' _ hL' e.symm,
      ← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
      ih (m + 1) (m + (r : ℤ) + 1) (by ring) (by ring) (cycleGroupCast D sY hcast β),
      canonicalFirstChernCapCanonicalChowMap_chowClassCanonical]
    exact congrArg (fun γ => chowClassCanonical.{u + 1} D sX hX (m + (r : ℤ))
      (firstChernCapCycleMap D sX hX (m + (r : ℤ))
        (canonicalFirstChernRule D sX hX L' hL' (m + (r : ℤ)))
        (firstChernCapPowCycleMap D sX hX L' hL' s (m + (r : ℤ) + 1) γ))) (Subtype.ext rfl)

end FlatPullback

/-! ### The top coefficient read on an étale chart -/

section EtaleChart

variable (D : BaseSpaceDimensionSituation.{u})
    {T U P P' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sT : T ⟶ D.space) (hT : D.IsGood sT) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    (sP : P ⟶ D.space) (hP : D.IsGood sP) (sP' : P' ⟶ D.space) (hP' : D.IsGood sP')
    {h : U ⟶ T} (hh : IsEtale D.site D.base D.base_mem h) (hhB : h ≫ sT = sU)
    {π : P ⟶ T} (hπB : π ≫ sT = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hr : HasRelativeDimension n D.site D.base D.base_mem π)
    (hproper : IsProper D.site D.base D.base_mem π)
    {h' : P' ⟶ P} {π' : P' ⟶ U} (sq : IsPullback h' π' π h) (hh'B : h' ≫ sP = sP')
    (hπ'B : π' ≫ sU = sP')
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (L' : Modules.{u, u} D.site D.base D.base_mem P' hP'.1)
    (hL' : IsInvertibleModule (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')

include hh hhB hπB hflat hr hproper sq hh'B in
/-- **The coefficients of `π_*(c₁(ℒ)^n ∩ π^*α)` are read on an étale chart of the base.** Let
`π : P → T` be proper and flat of relative dimension `n` between good spaces, `ℒ` an invertible
`𝒪_P`-module, `h : U → T` étale, `P' = P ×_T U` with projections `h' : P' → P`, `π' : P' → U`,
and `ℒ' ≅ h'^*ℒ`. Suppose no integral closed subspace of `U` has δ-dimension `k + 1`. Then for a
`k`-cycle `α` on `T`, an integral closed subspace `Z ⊆ T` and an irreducible component `Z'` of
`h^{-1}(Z)`, the coefficient of `π_*(c₁(ℒ)^n ∩ π^*α)` at `Z` is the coefficient of
`π'_*(c₁(ℒ')^n ∩ π'^*h^*α)` at `Z'`, the cap products being those of Stacks 0EQJ at the canonical
choices.

The coefficient at `Z` is that of `h^*π_*(c₁(ℒ)^n ∩ π^*α)` at `Z'` (Stacks 0EPY), which is
`π'_*h'^*(c₁(ℒ)^n ∩ π^*α)` by Stacks 0EPD. By Stacks 0EQR for the iterated cap product and
Stacks 0EPA, `h'^*(c₁(ℒ)^n ∩ π^*α)` is rationally equivalent to `c₁(ℒ')^n ∩ π'^*h^*α`, so the two
pushforwards are rationally equivalent `k`-cycles on `U` (Stacks 0EQC), hence equal. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_preimageComponent
    (e : L' ≅ (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk h' : (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P, hP.1⟩)).obj L)
    (k : ℤ)
    (hdimU : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem U,
      deltaDimension D sU W ≠ k + 1)
    (α : CycleGroup D sT k) (Z : IntegralClosedSubspace D.site D.base D.base_mem T)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem h)) :
    (properCyclePushforward D sP hP sT hT hπB hproper.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sT hT π hπB n hflat hr k (k + n) rfl α))).1 Z =
      (properCyclePushforward D sP' hP' sU hU hπ'B
          (isProper_of_isPullback D.site D.base D.base_mem hP'.1 hP.1 hU.1 hT.1 sq
            hproper).2.1.2 k
          (firstChernCapPowCycleMap D sP' hP' L' hL' n k
            (flatPullbackMap D sP' hP' sU hU π' hπ'B n
              (isFlat_and_hasRelativeDimension_of_isPullback D sP' hP' sU hU sP hP sT hT hπ'B hπB
                sq.flip n hflat hr).2.1
              (isFlat_and_hasRelativeDimension_of_isPullback D sP' hP' sU hU sP hP sT hT hπ'B hπB
                sq.flip n hflat hr).2.2 k (k + n) rfl
              (flatPullbackMap D sU hU sT hT h hhB 0
                (isFlat_of_isEtale D.site D.base D.base_mem hh)
                (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem h hT.1 hh) k k
                (by simp) α)))).1
        (Z.preimageComponent D.site D.base D.base_mem h hU.1 (D.isDecentSpace_of_isGood sU hU)
          hT.1 C) := by
  have hhflat := isFlat_of_isEtale D.site D.base D.base_mem hh
  have hhrel := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem h hT.1 hh
  have hh' := isFlat_and_hasRelativeDimension_of_isPullback D sP' hP' sP hP sU hU sT hT hh'B hhB
    sq 0 hhflat hhrel
  have hπ' := isFlat_and_hasRelativeDimension_of_isPullback D sP' hP' sU hU sP hP sT hT hπ'B hπB
    sq.flip n hflat hr
  have hπ'p := isProper_of_isPullback D.site D.base D.base_mem hP'.1 hP.1 hU.1 hT.1 sq hproper
  set Ψ := firstChernCapPowCycleMap D sP hP L hL n k
    (flatPullbackMap D sP hP sT hT π hπB n hflat hr k (k + n) rfl α)
  rw [← IntegralClosedSubspace.flatPullbackMap_apply_preimageComponent D sU hU sT hT hh hhB k k
      (by simp) _ Z C,
    flatPullback_properPushforward_unconditional D sP' hP' sP hP sU hU sT hT hh'B hπ'B hπB hhB 0
      hhflat hhrel sq hproper k k (by simp) Ψ]
  refine congrArg (fun γ : CycleGroup D sU k => γ.1 _) ?_
  have hβ : flatPullbackMap D sP' hP' sP hP h' hh'B 0 hh'.2.1 hh'.2.2 (k + n) (k + n) (by simp)
      (flatPullbackMap D sP hP sT hT π hπB n hflat hr k (k + n) rfl α) =
      flatPullbackMap D sP' hP' sU hU π' hπ'B n hπ'.2.1 hπ'.2.2 k (k + n) rfl
        (flatPullbackMap D sU hU sT hT h hhB 0 hhflat hhrel k k (by simp) α) := by
    have h₁ := flatPullbackMap_comp D sP' hP' sP hP sT hT h' π hh'B hπB 0 n hh'.2.1 hh'.2.2 hflat
      hr k (k + n) (by push_cast; ring)
    have h₂ := flatPullbackMap_comp D sP' hP' sU hU sT hT π' h hπ'B hhB n 0 hπ'.2.1 hπ'.2.2
      hhflat hhrel k (k + n) (by push_cast; ring)
    refine Subtype.ext ?_
    refine (congrArg Subtype.val (DFunLike.congr_fun h₁ α).symm).trans
      ((flatPullbackMap_coe_congr D _ hP' _ hT sq.w _ _ (by omega) _ _ _ _ _ _ _ _
        (by push_cast; ring) (by push_cast; ring) α α rfl).trans
        ((congrArg Subtype.val (DFunLike.congr_fun h₂ α)).trans ?_))
    exact flatPullbackMap_coe_congr D _ hP' _ hU rfl _ _ rfl _ _ _ _ _ _ _ _ (by simp) rfl _ _ rfl
  have hre := chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap D sP' hP' sP hP h' hh'B 0
    hh'.2.1 hh'.2.2 L hL L' hL' e n k k (by simp) (by simp)
    (flatPullbackMap D sP hP sT hT π hπB n hflat hr k (k + n) rfl α)
  rw [hβ, chowClassCanonical_eq_iff_rationallyEquivalentCanonical] at hre
  have hpush := rationallyEquivalentCanonical_properCyclePushforward D sP' hP' sU hU hπ'B hπ'p k hre
  have h0 := IsRationallyEquivalentToZeroCanonical.eq_zero_of_forall_deltaDimension_ne D sU hU
    hdimU hpush
  rw [sub_eq_zero] at h0
  exact h0

end EtaleChart

end AlgebraicGeometry.Space

end
