module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Datum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.RankOne
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological

/-!
# The top identity for projective bundles, and the first Chern class in rank one

`Stacks.Chow.GenuineChern.TopHalf C` is the assertion that, for the projective bundle
`π : P(ℰ) ⟶ X` of every module `ℰ` of constant positive rank `r` on every scheme `X` locally of
finite type over the base,

  `π_*(c₁(𝒪(1))^{r-1} ∩ π^*β) = β`.

Granted it, the pullback to the bundle is injective on Chow groups, and in rank one the Segre
pushforward is the cap with the first Chern class of the module itself.

## Main definitions

* `Stacks.Chow.GenuineChern.TopHalf`: the identity `π_*(c₁(𝒪(1))^{r-1} ∩ π^*β) = β` for every
  projective bundle.

## Main results

* `Stacks.Chow.GenuineChern.pullback_injective`: the pullback to the projective bundle is
  injective on Chow groups.
* `Stacks.Chow.GenuineChern.bundleTwistIsoOfRankOne`: `π^*ℒ ≅ 𝒪(1)` for `ℒ` invertible.
* `Stacks.Chow.GenuineChern.segre_rank_one`: `π_*(c₁(𝒪(1)) ∩ π^*α) = c₁(ℒ) ∩ α` for `ℒ`
  invertible.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02U2](https://stacks.math.columbia.edu/tag/02U2)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- For the projective bundle `π` of every module of constant positive rank `r` on every scheme
locally of finite type over the base, `π_*(c₁(𝒪(1))^{r-1} ∩ π^*β) = β` on Chow groups. -/
def TopHalf : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (k : ℤ)
    (β : chowGroup C sX k),
    haveI := flat_bundleProj E n
    haveI := locallyOfFiniteType_bundleProj E n
    projectiveBundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
        (relativeDimension_bundleProj E n)
        (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
        (bundleTwistCap E C sX) (n + 1 - 1) k β =
      chowGroupCast C sX (by omega) β

variable {C} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)

/-- The pullback to the projective bundle is injective on Chow groups. -/
theorem pullback_injective (H : TopHalf C) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (k : ℤ) :
    haveI := flat_bundleProj E n
    haveI := locallyOfFiniteType_bundleProj E n
    Function.Injective (projectiveBundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl
      (n + 1) (relativeDimension_bundleProj E n)
      (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k) k) :=
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  projectiveBundlePullback_injective C sX _ _ rfl (bundleTwistCap E C sX) (n + 1) _ _
    (H sX E n) k

/-- For an invertible module `ℒ`, the tautological map `π^*ℒ ⟶ 𝒪(1)` of its projective bundle,
as an isomorphism. -/
def bundleTwistIsoOfRankOne
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property E] :
    (Scheme.Modules.pullback (bundleProj E)).obj E ≅ bundleTwist E :=
  haveI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.RelativeProj.relativeProj
        (SymGraded.schemeSheafGradedAlgebra E (bundlePieces E))).scheme.presheaf
      (AlgebraicGeometry.RelativeProj.relativeProj
        (SymGraded.schemeSheafGradedAlgebra E (bundlePieces E))).scheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (AlgebraicGeometry.RelativeProj.relativeProj
        (SymGraded.schemeSheafGradedAlgebra E (bundlePieces E))).toBase).obj E) :=
    isInvertible_presheaf_modulePullback E _
  haveI := Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E (bundlePieces E)
  haveI := isInvertible_presheaf_modulePullback E (bundleProj E)
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).presheaf
      (bundle E).ringCatSheaf.2 (bundleTwist E) := isInvertible_bundleTwist E
  @asIso _ _ _ _ (Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E))
    (Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible _
      (Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)))

/-- For an invertible module `ℒ`, the Segre pushforward is the cap with its first Chern class:
`π_*(c₁(𝒪(1)) ∩ π^*α) = c₁(ℒ) ∩ α`. -/
theorem segre_rank_one (H : TopHalf C)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (0 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property E]
    (k : ℤ) (α : chowGroup C sX k) :
    segre E 0 C sX k α =
      firstChernClassCapChow C (k - 1) sX E (chowGroupCast C sX (by omega) α) := by
  have := flat_bundleProj E 0
  have := locallyOfFiniteType_bundleProj E 0
  have := isInvertible_presheaf_modulePullback E (bundleProj E)
  have h := projectiveBundleProjection_one_eq_of_rank_one C sX (bundleProj E ≫ sX)
    (bundleProj E) rfl (bundleTwistCap E C sX) (relativeDimension_bundleProj E 0)
    (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (H sX E 0) (fun d => firstChernClassCapChow C d sX E) ?_ k α
  · simp only [segre, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    have h' : projectiveBundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl (0 + 1)
        (relativeDimension_bundleProj E 0)
        (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
        (bundleTwistCap E C sX) (0 + 1) k α =
        chowGroupCast C sX (by omega)
          (firstChernClassCapChow C (k - 1) sX E (chowGroupCast C sX (by omega) α)) := h
    rw [h', chowGroupCast_chowGroupCast]
    rfl
  · intro k α d hd y hy
    change firstChernClassCapChow C d (bundleProj E ≫ sX) (bundleTwist E) y ≍ _
    rw [← firstChernClassCapChow_congr C (bundleProj E ≫ sX) d (bundleTwistIsoOfRankOne E)]
    refine (capOnChow_heq C (bundleProj E ≫ sX)
      (invertibleChernCapOperator C (bundleProj E ≫ sX) ((Scheme.Modules.pullback
        (bundleProj E)).obj E) fun k ↦
          firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ _)
      (d₂ := k - 1 + ((0 + 1 - 1 : ℕ) : ℤ)) (by omega)
      (y := chowGroupCast C _ (by omega) y) (chowGroupCast_heq C _ _ y).symm).trans ?_
    refine (flatPullbackChow_firstChernClassCapChow_heq C (bundleProj E ≫ sX) sX (bundleProj E)
      rfl (0 + 1 - 1) (relativeDimension_bundleProj E 0)
      (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k) E
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (Iso.refl _) (k - 1)
      (chowGroupCast C sX (by omega) α) (chowGroupCast C _ (by omega) y) ?_).symm
    refine (chowGroupCast_heq C _ _ y).trans (hy.trans ?_)
    exact flatPullbackChow_heq C (bundleProj E ≫ sX) sX (bundleProj E) rfl (0 + 1 - 1)
      (relativeDimension_bundleProj E 0)
      (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (by omega) (chowGroupCast_heq C sX _ α).symm

end Stacks.Chow.GenuineChern

end
