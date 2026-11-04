module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreIntegralReduction

/-!
# Iterated cap products along a chain of integral closed subspaces

In Situation 0EDT let `Q/B` be good and `ℒ` invertible on `Q`. This file records three
consequences of the compatibility of the cap product `c₁(ℒ) ∩ -` and of proper pushforward with
rational equivalence *on subsets*, the form in which the proofs of Stacks 0EQY and Stacks 0EQC
produce it: each summand `(i_W)_* div(f)` of a rational equivalence is carried to a cycle
rationally equivalent to zero on `|W|`, respectively on the closure of its image.

* Summing over a witnessing family (Stacks 0EQ8), both operations carry cycles rationally
  equivalent to zero on `T` to cycles rationally equivalent to zero on `T`, respectively on the
  closure of the image of `T`.
* The iterated cap product `c₁(ℒ)^d ∩ -` then does the same.
* **Chains.** If `H_0 ⊆ H_1 ⊆ ⋯ ⊆ H_d` are integral closed subspaces of `Q` with
  `dim_δ(H_i) = m + i` and `c₁(ℒ) ∩ [H_{i+1}] ∼_rat [H_i]` on `|H_{i+1}|` for every `i < d`,
  then `c₁(ℒ)^d ∩ [H_d] ∼_rat [H_0]` on `|H_d|`. This is how the top-degree case of Stacks 0ERU
  is computed: on a projective space bundle the `H_i` are the linear subbundles cut out by
  coordinate sections of `𝒪(1)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_firstChernCapCycleMap_of_summand`
* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_properCyclePushforward_of_summand`
* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_iteratedFirstChernCapCycle`
* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_iteratedFirstChernCapCycle_chain`

## References

* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### A rational equivalence as a locally finite sum -/

section Family

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) {J : Type v}

/-- The sum `∑ (i_j)_* c_j` of a locally finite family of pushforwards is the locally finite
sum of its summands, each supported on the point set of its subspace. -/
theorem cycleFamilySum_eq_locallyFiniteCycleSum
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) :
    cycleFamilySum D sX hX W hWfin k c =
      locallyFiniteCycleSum D sX k (fun j => subspacePointSet D.site D.base D.base_mem X
        (W j).subspace) hWfin (fun j => integralClosedSubspacePushforward D sX hX (W j) k (c j))
        (fun j => subspacePointSet_subset_of_pushforward_ne_zero D sX hX (W j) k (c j)) :=
  rfl

/-- A locally finite sum of zero cycles is zero. -/
theorem locallyFiniteCycleSum_zero (k : ℤ) (T : J → Set (points D.site D.base D.base_mem X))
    (hT : LocallyFinite T)
    (hαT : ∀ (j : J) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (0 : CycleGroup D sX k).1 Z ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T j) :
    locallyFiniteCycleSum D sX k T hT (fun _ => 0) hαT = 0 :=
  Subtype.ext (funext fun _ => finsum_eq_zero_of_forall_eq_zero fun _ => rfl)

/-- A locally finite sum of cycles rationally equivalent to zero on `T j ⊆ T` is rationally
equivalent to zero on `T`. -/
private theorem rationallyEquivalentOn_locallyFiniteCycleSum_zero (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) (Tj : J → Set (points D.site D.base D.base_mem X))
    (hTj : LocallyFinite Tj) (hTjT : ∀ j, Tj j ⊆ T) (α : J → CycleGroup D sX k)
    (hαT : ∀ (j : J) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α j).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ Tj j)
    (h : ∀ j, RationallyEquivalentOn.{v} D sX hX k (Tj j) (α j) 0) :
    RationallyEquivalentOn.{v} D sX hX k T (locallyFiniteCycleSum D sX k Tj hTj α hαT) 0 := by
  have := rationallyEquivalentOn_locallyFiniteCycleSum.{v} D sX hX k T Tj hTj hTjT α (fun _ => 0)
    hαT (fun j Z hZ => absurd rfl hZ) h
  rwa [locallyFiniteCycleSum_zero] at this

end Family

/-! ### From the summands to rational equivalence on subsets -/

section Summand

variable {Q Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sQ : Q ⟶ D.space)
    (hQ : D.IsGood sQ)

/-- **The cap product respects rational equivalence on subsets**, granted that it carries each
summand `(i_W)_* div(f)` to a cycle rationally equivalent to zero on `|W|`. -/
theorem rationallyEquivalentOn_firstChernCapCycleMap_of_summand (k : ℤ)
    (chern : FirstChernComponentCycleRule D sQ k)
    (hsummand : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Q)
      (_ : deltaDimension D sQ W = k + 1 + 1) (c : CycleGroup D (W.subspace.ι ≫ sQ) (k + 1)),
      IsPrincipalDivisorCycle D (W.subspace.ι ≫ sQ) (k + 1) c →
        RationallyEquivalentOn.{v} D sQ hQ k
          (subspacePointSet D.site D.base D.base_mem Q W.subspace)
          (firstChernCapCycleMap D sQ hQ k chern
            (integralClosedSubspacePushforward D sQ hQ W (k + 1) c)) 0)
    (T : Set (points D.site D.base D.base_mem Q)) (α : CycleGroup D sQ (k + 1))
    (hα : RationallyEquivalentOn.{v} D sQ hQ (k + 1) T α 0) :
    RationallyEquivalentOn.{v} D sQ hQ k T (firstChernCapCycleMap D sQ hQ k chern α) 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWT, hsum⟩ := hα
  rw [sub_zero] at hsum
  rw [hsum, cycleFamilySum_eq_locallyFiniteCycleSum, firstChernCapCycleMap_locallyFiniteCycleSum]
  exact rationallyEquivalentOn_locallyFiniteCycleSum_zero D sQ hQ k T _ hWfin hWT
    (fun j => firstChernCapCycleMap D sQ hQ k chern
      (integralClosedSubspacePushforward D sQ hQ (W j) (k + 1) (c j)))
    (fun j => subspacePointSet_subset_of_firstChernCapCycleMap_ne_zero D sQ hQ k chern _ _
      (subspacePointSet_subset_of_pushforward_ne_zero D sQ hQ (W j) (k + 1) (c j)))
    (fun j => hsummand (W j) (hWdim j) (c j) (hWprin j))

variable (sY : Y ⟶ D.space) (hY : D.IsGood sY) {q : Q ⟶ Y} (hq : q ≫ sY = sQ)
    (hqc : IsQuasiCompact D.site D.base D.base_mem q)

/-- **Proper pushforward respects rational equivalence on subsets**, granted that it carries
each summand `(i_W)_* div(f)` to a cycle rationally equivalent to zero on the closure of the
image of `|W|`. -/
theorem rationallyEquivalentOn_properCyclePushforward_of_summand (k : ℤ)
    (hsummand : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Q)
      (_ : deltaDimension D sQ W = k + 1) (c : CycleGroup D (W.subspace.ι ≫ sQ) k),
      IsPrincipalDivisorCycle D (W.subspace.ι ≫ sQ) k c →
        RationallyEquivalentOn.{v} D sY hY k
          (closure (pointsMap D.site D.base D.base_mem Q q ''
            subspacePointSet D.site D.base D.base_mem Q W.subspace))
          (properCyclePushforward D sQ hQ sY hY hq hqc k
            (integralClosedSubspacePushforward D sQ hQ W k c)) 0)
    (T : Set (points D.site D.base D.base_mem Q)) (α : CycleGroup D sQ k)
    (hα : RationallyEquivalentOn.{v} D sQ hQ k T α 0) :
    RationallyEquivalentOn.{v} D sY hY k (closure (pointsMap D.site D.base D.base_mem Q q '' T))
      (properCyclePushforward D sQ hQ sY hY hq hqc k α) 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWT, hsum⟩ := hα
  rw [sub_zero] at hsum
  rw [hsum, cycleFamilySum_eq_locallyFiniteCycleSum,
    properCyclePushforward_locallyFiniteCycleSum D sQ hQ sY hY hq hqc k _
      (fun j => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hQ.1
        (W j))]
  exact rationallyEquivalentOn_locallyFiniteCycleSum_zero D sY hY k
    (closure (pointsMap D.site D.base D.base_mem Q q '' T)) _
    (locallyFinite_closure_image_pointsMap D sQ hQ sY hY hq hqc _
      (fun j => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hQ.1
        (W j)) hWfin).1
    (fun j => closure_mono (Set.image_mono (hWT j)))
    (fun j => properCyclePushforward D sQ hQ sY hY hq hqc k
      (integralClosedSubspacePushforward D sQ hQ (W j) k (c j)))
    (fun j => subspacePointSet_subset_of_properCyclePushforward_ne_zero D sQ hQ sY hY hq hqc k _ _
      (subspacePointSet_subset_of_pushforward_ne_zero D sQ hQ (W j) k (c j)))
    (fun j => hsummand (W j) (hWdim j) (c j) (hWprin j))

end Summand

/-! ### Iterated cap products -/

section Iterated

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- Reindexing along an equality of degrees preserves rational equivalence on subsets. -/
theorem rationallyEquivalentOn_cycleGroupCast {a b : ℤ} (h : a = b)
    (T : Set (points D.site D.base D.base_mem X)) {α β : CycleGroup D sX a}
    (hαβ : RationallyEquivalentOn.{v} D sX hX a T α β) :
    RationallyEquivalentOn.{v} D sX hX b T (cycleGroupCast D sX h α)
      (cycleGroupCast D sX h β) := by
  subst h
  exact hαβ

/-- **Iterated cap products respect rational equivalence on subsets**, as soon as each single
cap product does. -/
theorem rationallyEquivalentOn_iteratedFirstChernCapCycle :
    ∀ (d : ℕ) (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1)
      (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
        (L j)),
      (∀ (j : Fin d) (T : Set (points D.site D.base D.base_mem X)) (k : ℤ)
        (α : CycleGroup D sX (k + 1)),
        RationallyEquivalentOn.{v} D sX hX (k + 1) T α 0 →
          RationallyEquivalentOn.{v} D sX hX k T
            (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX (L j) (hL j) k)
              α) 0) →
      ∀ (T : Set (points D.site D.base D.base_mem X)) (k : ℤ) (α : CycleGroup D sX (k + d)),
        RationallyEquivalentOn.{v} D sX hX (k + d) T α 0 →
          RationallyEquivalentOn.{v} D sX hX k T
            (iteratedFirstChernCapCycle D sX hX d L hL k α) 0
  | 0, L, hL, _, T, k, α, hα => by
    have h := rationallyEquivalentOn_cycleGroupCast.{v} D sX hX
      (show k + ((0 : ℕ) : ℤ) = k by simp) T hα
    rwa [map_zero] at h
  | d + 1, L, hL, hcap, T, k, α, hα => by
    rw [iteratedFirstChernCapCycle_succ]
    refine rationallyEquivalentOn_iteratedFirstChernCapCycle d (Fin.init L)
      (fun j => hL _) (fun j T k α hα => hcap (Fin.castSucc j) T k α hα) T k _ ?_
    simpa using hcap (Fin.last d) T (k + d) _
      (rationallyEquivalentOn_cycleGroupCast.{v} D sX hX (by push_cast; ring) T hα)

/-- If each single cap product respects rational equivalence on `T`, then iterated cap products
carry cycles rationally equivalent on `T` to cycles rationally equivalent on `T`. -/
theorem rationallyEquivalentOn_iteratedFirstChernCapCycle_of_rationallyEquivalentOn
    (d : ℕ) (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (L j))
    (hcap : ∀ (j : Fin d) (T : Set (points D.site D.base D.base_mem X)) (k : ℤ)
      (α : CycleGroup D sX (k + 1)),
      RationallyEquivalentOn.{v} D sX hX (k + 1) T α 0 →
        RationallyEquivalentOn.{v} D sX hX k T
          (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX (L j) (hL j) k)
            α) 0)
    (T : Set (points D.site D.base D.base_mem X)) (k : ℤ) {α β : CycleGroup D sX (k + d)}
    (hαβ : RationallyEquivalentOn.{v} D sX hX (k + d) T α β) :
    RationallyEquivalentOn.{v} D sX hX k T (iteratedFirstChernCapCycle D sX hX d L hL k α)
      (iteratedFirstChernCapCycle D sX hX d L hL k β) := by
  rw [rationallyEquivalentOn_iff_zero, ← map_sub]
  exact rationallyEquivalentOn_iteratedFirstChernCapCycle.{v} D sX hX d L hL hcap T k _
    ((rationallyEquivalentOn_iff_zero.{v} D sX hX _).1 hαβ)

end Iterated

/-! ### Chains -/

section Chain

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **Iterated cap products along a chain.** Let `H_0, …, H_d` be integral closed subspaces of
`X` with `dim_δ(H_i) = m + i`, each point set contained in the next, such that
`c₁(ℒ) ∩ [H_{i+1}] ∼_rat [H_i]` on `|H_{i+1}|` for every `i < d`. If `c₁(ℒ) ∩ -` respects
rational equivalence on subsets, then `c₁(ℒ)^d ∩ [H_d] ∼_rat [H_0]` on `|H_d|`. -/
theorem rationallyEquivalentOn_iteratedFirstChernCapCycle_chain
    (hcap : ∀ (T : Set (points D.site D.base D.base_mem X)) (k : ℤ)
      (α : CycleGroup D sX (k + 1)),
      RationallyEquivalentOn.{v} D sX hX (k + 1) T α 0 →
        RationallyEquivalentOn.{v} D sX hX k T
          (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k) α) 0)
    (m : ℤ) (H : ℕ → IntegralClosedSubspace D.site D.base D.base_mem X) :
    ∀ (d : ℕ) (hdim : ∀ i ≤ d, deltaDimension D sX (H i) = m + i)
      (_ : ∀ i < d, subspacePointSet D.site D.base D.base_mem X (H i).subspace ⊆
        subspacePointSet D.site D.base D.base_mem X (H (i + 1)).subspace)
      (_ : ∀ (i : ℕ) (hi : i < d),
        RationallyEquivalentOn.{v} D sX hX (m + i)
          (subspacePointSet D.site D.base D.base_mem X (H (i + 1)).subspace)
          (firstChernCapCycleMap D sX hX (m + i) (canonicalFirstChernRule D sX hX L hL (m + i))
            (integralCycle D sX (m + i + 1) (H (i + 1))
              (by rw [hdim (i + 1) hi]; push_cast; ring)))
          (integralCycle D sX (m + i) (H i) (hdim i hi.le))),
      RationallyEquivalentOn.{v} D sX hX m
        (subspacePointSet D.site D.base D.base_mem X (H d).subspace)
        (iteratedFirstChernCapCycle D sX hX d (fun _ => L) (fun _ => hL) m
          (integralCycle D sX (m + d) (H d) (hdim d le_rfl)))
        (integralCycle D sX m (H 0) (by simpa using hdim 0 (Nat.zero_le d)))
  | 0, hdim, _, _ => rationallyEquivalentOn_refl.{v} D sX hX m _ _
  | d + 1, hdim, hsub, hstep => by
    have IH := rationallyEquivalentOn_iteratedFirstChernCapCycle_chain hcap m H d
      (fun i hi => hdim i (Nat.le_succ_of_le hi)) (fun i hi => hsub i (Nat.lt_succ_of_lt hi))
      (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    rw [iteratedFirstChernCapCycle_succ]
    have hcast : cycleGroupCast D sX (by push_cast; ring)
        (integralCycle D sX (m + ((d + 1 : ℕ) : ℤ)) (H (d + 1)) (hdim (d + 1) le_rfl)) =
        integralCycle D sX (m + d + 1) (H (d + 1)) (by rw [hdim (d + 1) le_rfl]; push_cast; ring) :=
      Subtype.ext rfl
    rw [hcast]
    exact RationallyEquivalentOn.trans
      (rationallyEquivalentOn_iteratedFirstChernCapCycle_of_rationallyEquivalentOn.{v} D sX hX d
        (Fin.init fun _ => L) (fun _ => hL) (fun _ => hcap) _ m (hstep d (Nat.lt_succ_self d)))
      (RationallyEquivalentOn.mono (hsub d (Nat.lt_succ_self d)) IH)

end Chain

end AlgebraicGeometry.Space.PrivateChern

end
