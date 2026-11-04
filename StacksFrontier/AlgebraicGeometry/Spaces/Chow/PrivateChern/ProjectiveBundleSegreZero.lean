module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleHyperplaneCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleTopSegre
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TopSegreIntegralReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow

/-!
# The Segre operation `t₀` of a projective bundle is the identity

In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`d + 1` and let `(π : P ⟶ X, 𝒪_P(1))` be its projective bundle. The top-degree case of
Stacks 0ERU says that `π_*(c₁(𝒪_P(1))^d ∩ π^*α) = α` for every `α ∈ CH_k(X)`; in the language of
the proof of Stacks 0ERY, the Segre operation `t₀(ℰ)` is the identity of `CH_*(X)`.

On an integral closed subspace `Z ⊆ X` the identity holds on the nose for cycles,
`π_*(c₁(𝒪_P(1))^d ∩ π^*[Z]) = [Z]`, since on étale charts of `X` over which `𝒪_P(1)` has a chain
of sections cutting out hyperplanes it holds up to rational equivalence on `|Z|`. Writing a cycle
as a locally finite sum of integral cycles, the composite differs from the identity by a cycle
rationally equivalent to zero, and the operations on Chow homology are the ones induced on
classes of cycles.

## Main results

All in the namespace `AlgebraicGeometry.Space.PrivateChern`:

* `firstChernCapChow_pow_of_chowClass`: the `m`-th power of the cap product with `c₁(𝒩)` on the
  class of a cycle is the class of the iterated cap product.
* `topSegreCycle_flatPullbackMap_integralCycle_projectiveBundleDatum`:
  `π_*(c₁(𝒪_P(1))^d ∩ π^*[Z]) = [Z]` for every integral closed subspace `Z ⊆ X`.
* `segreCap_zero_projectiveBundleDatum`: `t₀(ℰ) = 1` on `CH_*(X)`.
* `segreCapOfModule_succ_zero`: the same for the Segre operations of a module of positive rank.

## Implementation notes

The Chow groups are those whose rational equivalences are indexed in the universe `u + 1`, the
universe of the compatibilities of the operations on Chow homology.

## References

* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable {D : BaseSpaceDimensionSituation.{u}}

section Iterated

variable {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
  (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
  (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Powers of the cap product with `c₁(𝒩)` on the class of a cycle**:
`c₁(𝒩)^m ∩ [β] = [c₁(𝒩) ∩ ⋯ ∩ c₁(𝒩) ∩ β]` for `β ∈ Z_{k+m}(X)`. -/
theorem firstChernCapChow_pow_of_chowClass : ∀ (m : ℕ) (k : ℤ) (b : CycleGroup D sX (k + m)),
    (HPow.hPow (α := AddMonoid.End (chowHomology.{u, u + 1} D sX hX))
        (firstChernCapChow.{u, u + 1} D sX hX N hN) m)
        (DirectSum.of _ (k + m) (chowClass.{u + 1} D sX hX (k + m) b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k
        (chowClass.{u + 1} D sX hX k
          (iteratedFirstChernCapCycle D sX hX m (fun _ => N) (fun _ => hN) k b))
  | 0, k, b => by
    rw [show HPow.hPow (α := AddMonoid.End (chowHomology.{u, u + 1} D sX hX))
      (firstChernCapChow.{u, u + 1} D sX hX N hN) 0 = 1 from pow_zero _]
    exact of_chowClass_congr D sX hX (by simp) _ _ rfl
  | m + 1, k, b => by
    have h : k + ((m + 1 : ℕ) : ℤ) = k + (m : ℤ) + 1 := by push_cast; ring
    show (HPow.hPow (α := AddMonoid.End (chowHomology.{u, u + 1} D sX hX))
        (firstChernCapChow.{u, u + 1} D sX hX N hN) m)
      (firstChernCapChow.{u, u + 1} D sX hX N hN
        (DirectSum.of _ (k + ((m + 1 : ℕ) : ℤ))
          (chowClass.{u + 1} D sX hX (k + ((m + 1 : ℕ) : ℤ)) b))) = _
    rw [of_chowClass_congr D sX hX h b (cycleGroupCast D sX h b) rfl,
      firstChernCapChow_of_chowClass, firstChernCapChow_pow_of_chowClass m k]
    rfl

end Iterated

variable {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
  (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **The top-degree identity of Stacks 0ERU on integral cycles.** For the projective bundle
`(π : P ⟶ X, 𝒪_P(1))` of a module of rank `d + 1` and an integral closed subspace `Z ⊆ X` of
δ-dimension `k`, `π_*(c₁(𝒪_P(1))^d ∩ π^*[Z]) = [Z]` as cycles. -/
theorem topSegreCycle_flatPullbackMap_integralCycle_projectiveBundleDatum (d : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) (k n : ℤ) (hkn : k + (d : ℤ) = n)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k) :
    topSegreCycle D (projectiveBundleDatum E d hr).toBase (projectiveBundleDatum E d hr).isGood
        sX hX (projectiveBundleDatum E d hr).proj_comp
        (projectiveBundleDatum E d hr).isProper.2.1.2 (projectiveBundleDatum E d hr).twist
        (projectiveBundleDatum E d hr).isInvertible_twist d k n hkn
        (flatPullbackMap D (projectiveBundleDatum E d hr).toBase
          (projectiveBundleDatum E d hr).isGood sX hX (projectiveBundleDatum E d hr).proj
          (projectiveBundleDatum E d hr).proj_comp d (projectiveBundleDatum E d hr).isFlat
          (projectiveBundleDatum E d hr).hasRelativeDimension k n hkn
          (integralCycle D sX k Z hZ)) =
      integralCycle D sX k Z hZ := by
  let := isQuasicoherentOnSite_of_rank E hr
  have hfree := isFiniteLocallyFreeOnSite_of_rank E hr
  have := hasPullbacks_bigFppfOver D.site D.base D.base_mem
  refine topSegreCycle_flatPullbackMap_integralCycle_eq_of_charts D _
    (projectiveBundleDatum E d hr).isGood sX hX _ (projectiveBundleDatum E d hr).isProper d
    (projectiveBundleDatum E d hr).isFlat (projectiveBundleDatum E d hr).hasRelativeDimension _ _
    ?_ k n hkn Z hZ
  intro y
  obtain ⟨Wst, g, α, V0, w0, hWa, hge, hy, hα, hw0, hV0⟩ :=
    exists_affine_etale_chart_hyperplaneChain D E d hr sX hX (𝟙 X) y
  let c0 := (projectiveBundleChartFamily (X := goodSpace hX) E hfree).siteToChart
    (bundleBaseChart (goodSpace hX))
  have hsqT := (IsPullback.of_hasPullback α c0).flip.map yoneda
  have hbig := hsqT.paste_horiz (isPullback_projectiveBundleProj (X := goodSpace hX) E hfree)
  rw [hα, Category.comp_id] at hbig
  have hWg := isGood_of_isEtale_of_isAffine D sX hX hWa g hge
  have hQWa := isAlgebraicSpace_yoneda D.site D.base D.base_mem (pullback α c0)
  have hqWp : IsProper D.site D.base D.base_mem (yoneda.map (pullback.fst α c0)) :=
    isProper_of_isPullback D.site D.base D.base_mem hQWa (projectiveBundleDatum E d hr).isGood.1
      hWg.1 hX.1 hbig (projectiveBundleDatum E d hr).isProper
  have hQWg : D.IsGood (yoneda.map (pullback.fst α c0) ≫ g ≫ sX) :=
    ⟨hQWa, isQuasiSeparated_comp D.site D.base D.base_mem hQWa hWg.1 _ _
        (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hqWp.1) hWg.2.1,
      isLocallyOfFiniteType_comp' D.site D.base D.base_mem _ _ hWg.1 D.isAlgebraicSpace
        hqWp.2.1.1 hWg.2.2⟩
  obtain ⟨-, hfqW, hdqW⟩ := isFlat_and_hasRelativeDimension_of_isPullback D _ hQWg _ hWg _
    (projectiveBundleDatum E d hr).isGood _ hX rfl (projectiveBundleDatum E d hr).proj_comp
    hbig.flip d (projectiveBundleDatum E d hr).isFlat
    (projectiveBundleDatum E d hr).hasRelativeDimension
  have hg'e : IsEtale D.site D.base D.base_mem
      (yoneda.map (pullback.snd α c0) ≫ projectiveBundleChart (X := goodSpace hX) E hfree) :=
    isEtale_of_isPullback D.site D.base D.base_mem _ _ _ _
      (isPullback_homMk D.site D.base D.base_mem hWg.1 (projectiveBundleDatum E d hr).isGood.1
        hX.1 hQWa hbig.flip) hge
  refine ⟨yoneda.obj Wst, yoneda.obj (pullback α c0), g ≫ sX, hWg,
    yoneda.map (pullback.fst α c0) ≫ g ≫ sX, hQWg, g, _, yoneda.map (pullback.fst α c0), hbig,
    rfl, rfl,
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sX) hbig.w).trans (Category.assoc _ _ _)),
    hge, hy, hqWp, hfqW, hdqW, isFlat_of_isEtale D.site D.base D.base_mem hg'e,
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem _
      (projectiveBundleDatum E d hr).isGood.1 hg'e, ?_⟩
  intro k' n' hkn' Z' hZ'
  subst hkn'
  have hcomp : (ObjectProperty.homMk
      (yoneda.map (pullback.snd α c0) ≫ projectiveBundleChart (X := goodSpace hX) E hfree) :
        (⟨yoneda.obj (pullback α c0), hQWg.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨(projectiveBundleDatum E d hr).space, (projectiveBundleDatum E d hr).isGood.1⟩) =
      representedSpaceMap D.site D.base D.base_mem (pullback.snd α c0) ≫
        projectiveBundleAtlas (X := goodSpace hX) E hfree :=
    ObjectProperty.hom_ext _ rfl
  exact rationallyEquivalentOn_topSegreCycle_chartBundle D E hfree d α V0 w0 hw0 hV0 (g ≫ sX)
    hWg _ hQWg rfl hqWp hfqW hdqW _ _
    (eqToIso (congrArg (fun φ => (modulePullback D.site D.base D.base_mem φ).obj
        (projectiveBundleTwist (X := goodSpace hX) E hfree).obj) hcomp) ≪≫
      ((modulePullbackCompIso D.site D.base D.base_mem _ _).app _).symm) k' Z' hZ'

/-- **The Segre operation `t₀` of a projective bundle is the identity** (the top-degree case of
Stacks 0ERU on Chow homology): for the projective bundle `(π : P ⟶ X, 𝒪_P(1))` of a module of
rank `d + 1`, `π_*(c₁(𝒪_P(1))^d ∩ π^*α) = α` for every `α ∈ CH_*(X)`. -/
theorem segreCap_zero_projectiveBundleDatum (d : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) :
    (projectiveBundleDatum E d hr).segreCap.{u, u + 1} 0 = 1 := by
  refine chowHomology_hom_ext D sX hX fun k b => ?_
  have hre := isRationallyEquivalentToZero_topSegreCycle_flatPullbackMap_sub.{u + 1} D
    (projectiveBundleDatum E d hr).toBase (projectiveBundleDatum E d hr).isGood sX hX
    (projectiveBundleDatum E d hr).proj_comp (projectiveBundleDatum E d hr).isProper.2.1.2 d
    (projectiveBundleDatum E d hr).isFlat (projectiveBundleDatum E d hr).hasRelativeDimension
    (projectiveBundleDatum E d hr).twist (projectiveBundleDatum E d hr).isInvertible_twist k
    (k + d) rfl (fun Z hZ => by
      rw [topSegreCycle_flatPullbackMap_integralCycle_projectiveBundleDatum E d hr k (k + d) rfl Z
        hZ]
      exact rationallyEquivalentOn_refl.{u + 1} D sX hX k _ _) b
  rw [ProjectiveBundleDatum.segreCap, Nat.add_zero]
  show (projectiveBundleDatum E d hr).pushforwardChow
      (((projectiveBundleDatum E d hr).twistCap ^ d) ((projectiveBundleDatum E d hr).pullbackChow
        (DirectSum.of _ k (chowClass.{u + 1} D sX hX k b)))) =
    DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k (chowClass.{u + 1} D sX hX k b)
  rw [flatPullbackChow_of_chowClass_eq D _
      (projectiveBundleDatum E d hr).isGood sX hX _ (projectiveBundleDatum E d hr).proj_comp d
      (projectiveBundleDatum E d hr).isFlat (projectiveBundleDatum E d hr).hasRelativeDimension k
      (k + d) rfl b,
    firstChernCapChow_pow_of_chowClass, properPushforwardChow_of,
    chowGroupProperPushforward_chowClass]
  exact congrArg _ ((chowClass_eq_iff_rationallyEquivalent.{u + 1} D sX hX k _ _).2 hre)

/-- **`t₀(ℰ) = 1`** for the Segre operations of a module of positive rank. -/
theorem segreCapOfModule_succ_zero (d : ℕ) (hr : IsFiniteLocallyFreeOfRank D sX hX E (d + 1)) :
    segreCapOfModule.{u, u + 1} E (d + 1) hr 0 = 1 :=
  segreCap_zero_projectiveBundleDatum E d hr

end AlgebraicGeometry.Space.PrivateChern

end
