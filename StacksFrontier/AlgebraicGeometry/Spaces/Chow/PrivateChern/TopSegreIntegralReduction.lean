module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.LocallyFiniteCycleSumCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.LocallyFiniteCycleSumPullback
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.LocallyFiniteCycleSumPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleInjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.RationalEquivalenceOnSubset

/-!
# The top-degree projective bundle identity reduces to integral subspaces

Let `q : Q ⟶ Y` be a proper flat morphism of good algebraic spaces of relative dimension `d`,
`ℒ` an invertible module on `Q`, and `Φ(α) = q_*(c₁(ℒ)^d ∩ q^*α)` the composite of the flat
pullback with the top Segre operation `AlgebraicGeometry.Space.PrivateChern.topSegreCycle`.
If `Φ([Z]) ∼_rat [Z]` on `|Z|` for every integral closed subspace `Z ⊆ Y`, then `Φ(α) ∼_rat α`
for every `k`-cycle `α` on `Y`.

## Main results

All in the namespace `AlgebraicGeometry.Space.PrivateChern`:

* `eq_locallyFiniteCycleSum_integralCycle`: a cycle is the locally finite sum of its terms
  `α_Z [Z]`.
* `iteratedFirstChernCapCycle_locallyFiniteCycleSum_apply`: the iterated cap product commutes with
  locally finite sums, coefficientwise.
* `isRationallyEquivalentToZero_topSegreCycle_flatPullbackMap_sub`: `Φ(α) - α ∼_rat 0` for every
  cycle, from the case of integral closed subspaces with rational equivalence on their point sets.
* `rationallyEquivalentOn_topSegreCycle_flatPullbackMap`: the same on a closed subset `T`, for
  cycles supported on `T`.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### Locally finite sums with different supports -/

section Congr

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    {I : Type v}

/-- A locally finite sum depends only on the summands, not on the chosen supports. -/
theorem locallyFiniteCycleSum_congr (k : ℤ) (T T' : I → Set (points D.site D.base D.base_mem X))
    (hT : LocallyFinite T) (hT' : LocallyFinite T') (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
    (hαT' : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T' i) :
    locallyFiniteCycleSum D sX k T hT α hαT = locallyFiniteCycleSum D sX k T' hT' α hαT' :=
  rfl

/-- Reindexing a locally finite sum along an equality of degrees is the locally finite sum of
the reindexed summands. -/
theorem cycleGroupCast_locallyFiniteCycleSum {a b : ℤ} (h : a = b)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX a)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i) :
    cycleGroupCast D sX h (locallyFiniteCycleSum D sX a T hT α hαT) =
      locallyFiniteCycleSum D sX b T hT (fun i => cycleGroupCast D sX h (α i))
        (fun i Z hZ => hαT i Z hZ) :=
  rfl

end Congr

/-! ### The iterated cap product and locally finite sums -/

section Iterated

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {I : Type v}

/-- The iterated cap product of a cycle supported on `T` is supported on `T`. -/
theorem subspacePointSet_subset_of_iteratedFirstChernCapCycle_ne_zero
    (T : Set (points D.site D.base D.base_mem X)) :
    ∀ (d : ℕ) (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
        (L j)) (k : ℤ) (α : CycleGroup D sX (k + d)),
      (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T) →
      ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (iteratedFirstChernCapCycle D sX hX d L hL k α).1 Z ≠ 0 →
          subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T
  | 0, L, hL, k, α, hα => fun Z hZ => hα Z hZ
  | d + 1, L, hL, k, α, hα => by
    rw [iteratedFirstChernCapCycle_succ]
    exact subspacePointSet_subset_of_iteratedFirstChernCapCycle_ne_zero T d (Fin.init L)
      (fun j => hL _) k _
      (subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sX hX (k + d) _ T _
        (fun Z hZ => hα Z hZ))

/-- The iterated cap product commutes with locally finite sums, coefficientwise. -/
theorem iteratedFirstChernCapCycle_locallyFiniteCycleSum_apply
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T) :
    ∀ (d : ℕ) (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
        (L j)) (k : ℤ) (α : I → CycleGroup D sX (k + d))
      (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
        (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
      (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (iteratedFirstChernCapCycle D sX hX d L hL k
          (locallyFiniteCycleSum D sX (k + d) T hT α hαT)).1 Z =
        ∑ᶠ i, (iteratedFirstChernCapCycle D sX hX d L hL k (α i)).1 Z
  | 0, L, hL, k, α, hαT, Z => rfl
  | d + 1, L, hL, k, α, hαT, Z => by
    have h1 := firstChernCapCycleMap_locallyFiniteCycleSum D sX hX (k + d)
      (canonicalFirstChernRule D sX hX (L (Fin.last d)) (hL _) (k + d)) T hT
      (fun i => cycleGroupCast D sX (by push_cast; ring) (α i)) (fun i Z hZ => hαT i Z hZ)
    have h2 := iteratedFirstChernCapCycle_locallyFiniteCycleSum_apply T hT d (Fin.init L)
      (fun j => hL _) k
      (fun i => firstChernCapCycleMap D sX hX (k + d)
        (canonicalFirstChernRule D sX hX (L (Fin.last d)) (hL _) (k + d))
        (cycleGroupCast D sX (by push_cast; ring) (α i)))
      (fun i => subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sX hX (k + d) _ (T i)
        (cycleGroupCast D sX (by push_cast; ring) (α i)) fun Z hZ => hαT i Z hZ) Z
    rw [iteratedFirstChernCapCycle_succ]
    change (iteratedFirstChernCapCycle D sX hX d (Fin.init L) (fun j => hL _) k
      (firstChernCapCycleMap D sX hX (k + d)
        (canonicalFirstChernRule D sX hX (L (Fin.last d)) (hL _) (k + d))
        (locallyFiniteCycleSum D sX (k + d + 1) T hT
          (fun i => cycleGroupCast D sX (by push_cast; ring) (α i))
          (fun i Z hZ => hαT i Z hZ)))).1 Z = _
    rw [h1, h2]
    rfl

end Iterated

/-! ### A cycle as the sum of its terms -/

section Terms

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (k : ℤ)
    (α : CycleGroup D sX k)

/-- The integral closed subspaces at which a cycle has a nonzero coefficient. -/
abbrev CycleSupport :=
  {Z : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 Z ≠ 0}

variable [Small.{v} (CycleSupport D sX k α)]

/-- The support of a cycle, as a type in the universe of the index families. -/
abbrev SmallCycleSupport := Shrink.{v} (CycleSupport D sX k α)

/-- The term `α_Z [Z]` of a cycle at a member of its support. -/
def cycleTerm (i : SmallCycleSupport.{v} D sX k α) : CycleGroup D sX k :=
  α.1 ((equivShrink _).symm i).1 •
    integralCycle D sX k ((equivShrink _).symm i).1 (α.2.2 _ ((equivShrink _).symm i).2)

/-- The coefficient of the term `α_Z [Z]` at `Z'` is `α_Z` times the coefficient of `[Z]` at
`Z'`. -/
theorem cycleTerm_apply (i : SmallCycleSupport.{v} D sX k α)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (cycleTerm.{v} D sX k α i).1 Z =
      α.1 ((equivShrink _).symm i).1 * integralCycleCoeff D ((equivShrink _).symm i).1 Z :=
  rfl

/-- The term `α_Z [Z]` is supported on `|Z|`. -/
theorem subspacePointSet_subset_of_cycleTerm_ne_zero (i : SmallCycleSupport.{v} D sX k α)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (cycleTerm.{v} D sX k α i).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X ((equivShrink _).symm i).1.subspace := by
  rw [cycleTerm_apply] at hZ
  rw [eq_of_integralCycleCoeff_ne_zero D _ (right_ne_zero_of_mul hZ)]

/-- The point sets of the integral closed subspaces in the support of a cycle form a locally finite
family. -/
theorem locallyFinite_smallCycleSupport :
    LocallyFinite fun i : SmallCycleSupport.{v} D sX k α =>
      subspacePointSet D.site D.base D.base_mem X ((equivShrink _).symm i).1.subspace :=
  (AlgebraicGeometry.Space.locallyFinite_cycleSupport α).comp_injective
    (equivShrink _).symm.injective

/-- A cycle is the locally finite sum `α = ∑_Z α_Z [Z]` of its terms, over the integral closed
subspaces in its support, each term supported on the point set of its subspace. -/
theorem eq_locallyFiniteCycleSum_integralCycle :
    α = locallyFiniteCycleSum D sX k
      (fun i : SmallCycleSupport.{v} D sX k α =>
        subspacePointSet D.site D.base D.base_mem X ((equivShrink _).symm i).1.subspace)
      (locallyFinite_smallCycleSupport.{v} D sX k α) (cycleTerm.{v} D sX k α)
      (subspacePointSet_subset_of_cycleTerm_ne_zero.{v} D sX k α) := by
  classical
  refine Subtype.ext (funext fun Z => ?_)
  rw [locallyFiniteCycleSum_apply]
  by_cases hZ : α.1 Z = 0
  · rw [hZ]
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    rw [cycleTerm_apply]
    by_cases h : Z = ((equivShrink _).symm i).1
    · rw [← h, hZ, zero_mul]
    · rw [integralCycleCoeff_eq_zero D _ h, mul_zero]
  · rw [finsum_eq_single _ (equivShrink _ ⟨Z, hZ⟩) fun i hi => ?_]
    · rw [cycleTerm_apply, Equiv.symm_apply_apply, integralCycleCoeff_self, mul_one]
    · rw [cycleTerm_apply, integralCycleCoeff_eq_zero D _ fun h => hi ?_, mul_zero]
      rw [← Equiv.apply_symm_apply (equivShrink _) i]
      congr 1
      exact Subtype.ext h.symm

end Terms

/-! ### The reduction -/

section Reduction

variable {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sQ : Q ⟶ D.space) (hQ : D.IsGood sQ) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {q : Q ⟶ Y}
    (hq : q ≫ sY = sQ) (hqc : IsQuasiCompact D.site D.base D.base_mem q) (d : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem q)
    (hd : HasRelativeDimension d D.site D.base D.base_mem q)
    (L : Modules.{u, u} D.site D.base D.base_mem Q hQ.1)
    (hL : IsInvertibleModule (⟨Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The composite `Φ(α) = q_*(c₁(ℒ)^d ∩ q^*α)` of a cycle supported on a closed `T ⊆ |Y|` is
supported on `T`. -/
theorem subspacePointSet_subset_of_topSegreCycle_flatPullbackMap_ne_zero (k n : ℤ)
    (hkn : k + (d : ℤ) = n) (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T)
    (α : CycleGroup D sY k)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hZ : (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
      (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α)).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T := by
  have h1 := subspacePointSet_subset_of_flatPullbackMap_ne_zero D sQ hQ sY hY q hq d hflat hd k n
    hkn T α hαT
  have h2 := subspacePointSet_subset_of_iteratedFirstChernCapCycle_ne_zero D sQ hQ
    (pointsMap D.site D.base D.base_mem Q q ⁻¹' T) d (fun _ => L) (fun _ => hL) k
    (cycleGroupCast D sQ hkn.symm (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α))
    (fun W hW => h1 W hW)
  refine (subspacePointSet_subset_of_properCyclePushforward_ne_zero D sQ hQ sY hY hq hqc k _ _
    h2 Z hZ).trans ?_
  exact closure_minimal (Set.image_preimage_subset _ _) hT

/-- `Φ` commutes with locally finite sums of cycles supported on closed sets. -/
theorem topSegreCycle_flatPullbackMap_locallyFiniteCycleSum {I : Type v} (k n : ℤ)
    (hkn : k + (d : ℤ) = n) (T : I → Set (points D.site D.base D.base_mem Y))
    (hTc : ∀ i, IsClosed (T i)) (hT : LocallyFinite T) (α : I → CycleGroup D sY k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T i) :
    topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn
          (locallyFiniteCycleSum D sY k T hT α hαT)) =
      locallyFiniteCycleSum D sY k T hT
        (fun i => topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
          (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i)))
        (fun i => subspacePointSet_subset_of_topSegreCycle_flatPullbackMap_ne_zero D sQ hQ sY hY
          hq hqc d hflat hd L hL k n hkn (T i) (hTc i) (α i) (hαT i)) := by
  set T' := fun i => pointsMap D.site D.base D.base_mem Q q ⁻¹' T i
  have hT' : LocallyFinite T' :=
    hT.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem q)
  have hT'c : ∀ i, IsClosed (T' i) :=
    fun i => (hTc i).preimage (continuous_pointsMap D.site D.base D.base_mem q)
  have h1 := flatPullbackMap_locallyFiniteCycleSum D sQ hQ sY hY q hq d hflat hd k n hkn T hT α
    hαT
  have hβT : ∀ (i : I) (W : IntegralClosedSubspace D.site D.base D.base_mem Q),
      (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i)).1 W ≠ 0 →
        subspacePointSet D.site D.base D.base_mem Q W.subspace ⊆ T' i :=
    fun i => subspacePointSet_subset_of_flatPullbackMap_ne_zero D sQ hQ sY hY q hq d hflat hd k
      n hkn (T i) (α i) (hαT i)
  have hγT : ∀ (i : I) (W : IntegralClosedSubspace D.site D.base D.base_mem Q),
      (iteratedFirstChernCapCycle D sQ hQ d (fun _ => L) (fun _ => hL) k
        (cycleGroupCast D sQ hkn.symm
          (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i)))).1 W ≠ 0 →
        subspacePointSet D.site D.base D.base_mem Q W.subspace ⊆ T' i :=
    fun i => subspacePointSet_subset_of_iteratedFirstChernCapCycle_ne_zero D sQ hQ (T' i) d _ _ k
      (cycleGroupCast D sQ hkn.symm
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i))) fun W hW => hβT i W hW
  have h2 : iteratedFirstChernCapCycle D sQ hQ d (fun _ => L) (fun _ => hL) k
      (cycleGroupCast D sQ hkn.symm
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn
          (locallyFiniteCycleSum D sY k T hT α hαT))) =
      locallyFiniteCycleSum D sQ k T' hT'
        (fun i => iteratedFirstChernCapCycle D sQ hQ d (fun _ => L) (fun _ => hL) k
          (cycleGroupCast D sQ hkn.symm
            (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i)))) hγT := by
    refine Subtype.ext (funext fun W => ?_)
    rw [h1]
    exact iteratedFirstChernCapCycle_locallyFiniteCycleSum_apply D sQ hQ T' hT' d _ _ k
      (fun i => cycleGroupCast D sQ hkn.symm
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (α i)))
      (fun i W hW => hβT i W hW) W
  have h3 := properCyclePushforward_locallyFiniteCycleSum D sQ hQ sY hY hq hqc k T' hT'c hT' _ hγT
  simp only [topSegreCycle, AddMonoidHom.comp_apply]
  rw [h2, h3]
  rfl

/-- Shared proof of the two reductions, for a single cycle `α` supported on `T`. -/
private theorem rationallyEquivalentOn_topSegreCycle_flatPullbackMap_of_hint (k n : ℤ)
    (hkn : k + (d : ℤ) = n) (T : Set (points D.site D.base D.base_mem Y))
    (α : CycleGroup D sY k) [Small.{v} (CycleSupport D sY k α)]
    (hint : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hZ : deltaDimension D sY Z = k),
      subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T →
      RationallyEquivalentOn.{v} D sY hY k (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
        (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
          (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (integralCycle D sY k Z hZ)))
        (integralCycle D sY k Z hZ))
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T) :
    RationallyEquivalentOn.{v} D sY hY k T
      (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α)) α := by
  have hTi : ∀ i : SmallCycleSupport.{v} D sY k α,
      IsClosed (subspacePointSet D.site D.base D.base_mem Y ((equivShrink _).symm i).1.subspace) :=
    fun i => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 _
  have hsum := eq_locallyFiniteCycleSum_integralCycle.{v} D sY k α
  have hre := rationallyEquivalentOn_locallyFiniteCycleSum.{v} D sY hY k T _
    (locallyFinite_smallCycleSupport.{v} D sY k α)
    (fun i => hαT _ ((equivShrink _).symm i).2)
    (fun i => topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
      (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (cycleTerm.{v} D sY k α i)))
    (cycleTerm.{v} D sY k α)
    (fun i => subspacePointSet_subset_of_topSegreCycle_flatPullbackMap_ne_zero D sQ hQ sY hY
      hq hqc d hflat hd L hL k n hkn
      (subspacePointSet D.site D.base D.base_mem Y ((equivShrink _).symm i).1.subspace) (hTi i)
      (cycleTerm.{v} D sY k α i)
      (subspacePointSet_subset_of_cycleTerm_ne_zero.{v} D sY k α i))
    (subspacePointSet_subset_of_cycleTerm_ne_zero.{v} D sY k α) fun i => by
      simpa only [cycleTerm, map_zsmul] using RationallyEquivalentOn.zsmul
        (hint _ (α.2.2 _ ((equivShrink _).symm i).2) (hαT _ ((equivShrink _).symm i).2))
        (α.1 ((equivShrink _).symm i).1)
  rwa [← topSegreCycle_flatPullbackMap_locallyFiniteCycleSum D sQ hQ sY hY hq hqc d hflat hd L hL
    k n hkn _ hTi _ _ (subspacePointSet_subset_of_cycleTerm_ne_zero.{v} D sY k α), ← hsum] at hre

/-- If `Φ([Z]) ∼_rat [Z]` on `|Z|` for every integral closed subspace `Z ⊆ Y` of δ-dimension `k`,
then `Φ(α) - α ∼_rat 0` for every `k`-cycle `α` on `Y`. -/
theorem isRationallyEquivalentToZero_topSegreCycle_flatPullbackMap_sub (k n : ℤ)
    (hkn : k + (d : ℤ) = n)
    [∀ α : CycleGroup D sY k, Small.{v} (CycleSupport D sY k α)]
    (hint : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hZ : deltaDimension D sY Z = k),
      RationallyEquivalentOn.{v} D sY hY k (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
        (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
          (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (integralCycle D sY k Z hZ)))
        (integralCycle D sY k Z hZ))
    (α : CycleGroup D sY k) :
    IsRationallyEquivalentToZero.{v} D sY hY k
      (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α) - α) := by
  exact (rationallyEquivalentOn_topSegreCycle_flatPullbackMap_of_hint.{v} D sQ hQ sY hY hq hqc d
    hflat hd L hL k n hkn Set.univ α (fun Z hZ _ => hint Z hZ) fun _ _ => Set.subset_univ _
    ).rationallyEquivalent D sY hY k _

/-- If `Φ([Z]) ∼_rat [Z]` on `|Z|` for every integral closed subspace `Z` of δ-dimension `k` with
`|Z| ⊆ T`, for a closed `T ⊆ |Y|`, then `Φ(α) ∼_rat α` on `T` for every `k`-cycle `α` supported
on `T`. -/
theorem rationallyEquivalentOn_topSegreCycle_flatPullbackMap (k n : ℤ)
    (hkn : k + (d : ℤ) = n) (T : Set (points D.site D.base D.base_mem Y)) (_hTc : IsClosed T)
    [∀ α : CycleGroup D sY k, Small.{v} (CycleSupport D sY k α)]
    (hint : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hZ : deltaDimension D sY Z = k),
      subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T →
      RationallyEquivalentOn.{v} D sY hY k (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
        (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
          (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn (integralCycle D sY k Z hZ)))
        (integralCycle D sY k Z hZ))
    (α : CycleGroup D sY k)
    (hαT : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T) :
    RationallyEquivalentOn.{v} D sY hY k T
      (topSegreCycle D sQ hQ sY hY hq hqc L hL d k n hkn
        (flatPullbackMap D sQ hQ sY hY q hq d hflat hd k n hkn α)) α := by
  exact rationallyEquivalentOn_topSegreCycle_flatPullbackMap_of_hint.{v} D sQ hQ sY hY hq hqc d
    hflat hd L hL k n hkn T α hint hαT

end Reduction

end AlgebraicGeometry.Space.PrivateChern

end
