module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaGeneralSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeGenericFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IsomorphismRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleRankZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat

/-!
# The projective bundle formula

Let `X` be a good algebraic space over the base and `ℰ` a finite locally free `𝒪_X`-module of rank
`r`, with projective bundle `(π : P = 𝐏(ℰ) → X, 𝒪_P(1))`. The map
`⊕_{i=0}^{r-1} CH_{k+i}(X) → CH_{k+r-1}(P)`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`, is bijective
(Stacks 0ERV). In rank `n + 1` it is injective
(`AlgebraicGeometry.Space.injective_bundleFormulaMap_projectiveBundle_of_freeTower`) and
surjective (`AlgebraicGeometry.Space.bundleFormulaSurjective_projectiveBundle_of_freeTower`).

Both halves rest on four inputs: a finite locally free module is free on a nonempty open subspace
(`AlgebraicGeometry.Space.exists_isOpenImmersion_nonempty_iso_freeTower_of_isGood`),
`𝐏(𝒪_U) → U` is an isomorphism (`AlgebraicGeometry.Space.isIso_projectiveBundleProj_of_rank_one`),
and the twist comparison `i^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` along the morphism of projective bundles
of a split quotient (`AlgebraicGeometry.Space.projectiveBundleSplitEpiTwistIso`), which gives both
the twist along the hyperplane at infinity and the invariance of the formula under isomorphisms of
modules. In rank `0` the projective bundle has no points and both sides vanish.

## Main results

* `AlgebraicGeometry.Space.bijective_projectiveBundleFormulaMap`: **Stacks 0ERV**, the map
  `⊕_{i=0}^{r-1} CH_{k+i}(X) → CH_{k+r-1}(𝐏(ℰ))`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`, is bijective
  (`AlgebraicGeometry.Space.projectiveBundleFormulaEquiv`).
* `AlgebraicGeometry.Space.bijective_bundleFormulaMap_projectiveBundle_of_freeTower`
* `AlgebraicGeometry.Space.bijective_bundleFormulaMap_projectiveBundle_of_moduleIso_of_twist`
* `AlgebraicGeometry.Space.bijective_bundleFormulaMap_projectiveBundle_of_twist`
* `AlgebraicGeometry.Space.projectiveBundleFormulaMapOfRank`,
  `AlgebraicGeometry.Space.bijective_projectiveBundleFormulaMapOfRank_zero`,
  `AlgebraicGeometry.Space.bijective_projectiveBundleFormulaMapOfRank_of_twist`: every rank `r`

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1))

/-! ### Rank zero -/

section RankZero

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS Y.1 Y.2) [hF : F.IsQuasicoherentOnSite]
  (hr0 : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) F 0)

include hr0 in
/-- **The projective bundle of a module of rank `0` has no points**: its atlas is surjective on
points, and the presenting chart bundle `𝐏(ℰ|_V)` is the projective bundle of a module of rank `0`
on a scheme, which is empty. -/
theorem isEmpty_points_projectiveBundle_of_rank_zero :
    IsEmpty (points B S hS (projectiveBundle F hr0.isFiniteLocallyFreeOnSite).1) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, -⟩ := surjective_pointsMap_projectiveBundleAtlas F hr0.isFiniteLocallyFreeOnSite x
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (chartBundleModule F (presentationChart (projectiveBundlePresentation Y))) 0 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (chartBundleModuleRestrictIso F _).symm
      (isFiniteLocallyFreeOfRank_restrictToChartScheme B S hS Y F hF 0 hr0 _)
  have he : IsEmpty (chartBundle F (presentationChart (projectiveBundlePresentation Y))) :=
    Stacks.ProjectiveBundleDeRham.isEmpty_projectiveBundle_of_rank_zero _
  exact he.false (pointsToScheme B S hS _ y)

end RankZero

/-- The Chow groups of a space with no points vanish. -/
theorem subsingleton_chowGroupCanonical_of_isEmpty_points
    {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sZ : Z ⟶ D.space)
    (hZ : D.IsGood sZ) (h : IsEmpty (points D.site D.base D.base_mem Z)) (k : ℤ) :
    Subsingleton (chowGroupCanonical.{u + 1} D sZ hZ k) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [CycleGroup.eq_zero_of_isEmpty_points D sZ h a, CycleGroup.eq_zero_of_isEmpty_points D sZ h b]

/-- **The projective bundle formula (Stacks 0ERV)**, from its four inputs. For a finite locally
free module `ℰ` of rank `n + 1` on a good algebraic space `X`, the map
`(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i` from `⊕_{i=0}^{n} CH_{d_i}(X)` to `CH_N(𝐏(ℰ))`, with
`d_i + n = N + i`, is bijective. -/
theorem bijective_bundleFormulaMap_projectiveBundle_of_freeTower
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hbase : ∀ U : AlgebraicSpaces D.site D.base D.base_mem,
      IsIso (@projectiveBundleProj D.site D.base D.base_mem U (freeTower U 0)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U 0))
        (isFiniteLocallyFreeOfRank_freeTower U 0).isFiniteLocallyFreeOnSite).hom)
    (htw : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (m : ℕ),
      Nonempty ((modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion (freeTower U m)
          (isFiniteLocallyFreeOfRank_freeTower U m))).obj
        (projectiveCompletionTwist (freeTower U m) (isFiniteLocallyFreeOfRank_freeTower U m)).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem U (freeTower U m)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U m))
        (isFiniteLocallyFreeOfRank_freeTower U m).isFiniteLocallyFreeOnSite).obj))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Bijective (bundleFormulaMap D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) N d hd) :=
  ⟨injective_bundleFormulaMap_projectiveBundle_of_freeTower D sX hX E n hr hfreeOpen hmod hbase
      htw N d hd,
    bundleFormulaSurjective_projectiveBundle_of_freeTower D sX hX E n hr hfreeOpen hmod hbase htw
      N d hd⟩

/-- **The projective bundle formula (Stacks 0ERV)**, from the two remaining geometric inputs: the
projective bundle formula is invariant under isomorphisms of modules, and
`i^*𝒪_{𝐏(F_m ⊕ 𝒪)}(1) ≅ 𝒪_{𝐏(F_m)}(1)` along the hyperplane at infinity. The freeness on a
nonempty open is `AlgebraicGeometry.Space.exists_isOpenImmersion_nonempty_iso_freeTower_of_isGood`
and `𝐏(𝒪_U) ≅ U` is `AlgebraicGeometry.Space.isIso_projectiveBundleProj_of_rank_one`. -/
theorem bijective_bundleFormulaMap_projectiveBundle_of_moduleIso_of_twist
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (htw : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (m : ℕ),
      Nonempty ((modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion (freeTower U m)
          (isFiniteLocallyFreeOfRank_freeTower U m))).obj
        (projectiveCompletionTwist (freeTower U m) (isFiniteLocallyFreeOfRank_freeTower U m)).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem U (freeTower U m)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U m))
        (isFiniteLocallyFreeOfRank_freeTower U m).isFiniteLocallyFreeOnSite).obj))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Bijective (bundleFormulaMap D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) N d hd) :=
  bijective_bundleFormulaMap_projectiveBundle_of_freeTower D sX hX E n hr
    (fun _ sY hY y F hF => exists_isOpenImmersion_nonempty_iso_freeTower_of_isGood D sY hY y F hF)
    hmod
    (fun U => (ObjectProperty.isIso_hom_iff _).2
      (@isIso_projectiveBundleProj_of_rank_one _ _ _ U (freeTower U 0)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U 0))
        (isFiniteLocallyFreeOfRank_freeTower U 0)
        (isFiniteLocallyFreeOfRank_freeTower U 0).isFiniteLocallyFreeOnSite))
    htw N d hd

/-! ### The two remaining inputs from the twist along a split quotient -/

/-- **The projective bundle formula is invariant under isomorphisms of modules**, granted the
twist comparison `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` along the morphism `φ : 𝐏(ℰ') → 𝐏(ℰ)` of every
split quotient `ℰ → ℰ'`: for `e : ℰ ≅ ℰ'` that morphism is the isomorphism
`AlgebraicGeometry.Space.projectiveBundleIsoOfIso`. -/
theorem projectiveBundleFormulaHolds_of_iso_of_twist
    (htwist : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem)
      (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2) (hF : F.IsQuasicoherentOnSite)
      (hF' : F'.IsQuasicoherentOnSite) (v : F ⟶ F') (σ : F' ⟶ F) (hσ : σ ≫ v = 𝟙 F')
      (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite F)
      (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite F'),
      Nonempty ((modulePullback D.site D.base D.base_mem
          (@projectiveBundleMapOfSplitEpi D.site D.base D.base_mem U F F' hF hF' v σ hσ hfree
            hfree')).obj (@projectiveBundleTwist D.site D.base D.base_mem U F hF hfree).obj ≅
        (@projectiveBundleTwist D.site D.base D.base_mem U F' hF' hfree').obj))
    (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space) (hU : D.IsGood sU)
    (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
    (hF' : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1))
    (e : F ≅ F') (h : ProjectiveBundleFormulaHolds D sU hU F n hF) :
    ProjectiveBundleFormulaHolds D sU hU F' n hF' := by
  have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2 hF
  have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2 hF'
  have : IsIso (projectiveBundleMapOfSplitEpi F F' e.hom e.inv e.inv_hom_id
      hF.isFiniteLocallyFreeOnSite hF'.isFiniteLocallyFreeOnSite).hom :=
    (ObjectProperty.isIso_hom_iff _).2
      (isIso_projectiveBundleMapOfSplitEpi_of_iso F F' e hF.isFiniteLocallyFreeOnSite
        hF'.isFiniteLocallyFreeOnSite)
  obtain ⟨t⟩ := htwist U F F' inferInstance inferInstance e.hom e.inv e.inv_hom_id
    hF.isFiniteLocallyFreeOnSite hF'.isFiniteLocallyFreeOnSite
  exact ProjectiveBundleFormulaHolds.of_iso D sU hU
    (projectiveBundleMapOfSplitEpi F F' e.hom e.inv e.inv_hom_id hF.isFiniteLocallyFreeOnSite
      hF'.isFiniteLocallyFreeOnSite).hom
    (congrArg (fun f => f.hom) (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj F F'
      e.hom e.inv e.inv_hom_id hF.isFiniteLocallyFreeOnSite hF'.isFiniteLocallyFreeOnSite)) t h

/-- **The projective bundle formula (Stacks 0ERV)**, from the twist comparison along split
quotients alone: for every split quotient `v : ℰ → ℰ'` of finite locally free modules on an
algebraic space, `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` along `φ = projectiveBundleMapOfSplitEpi`. It
gives both the twist along the hyperplane at infinity of `𝐏(F_m ⊕ 𝒪)` (the quotient
`F_m ⊕ 𝒪 → F_m`) and the invariance of the formula under isomorphisms of modules. -/
theorem bijective_bundleFormulaMap_projectiveBundle_of_twist
    (htwist : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem)
      (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2) (hF : F.IsQuasicoherentOnSite)
      (hF' : F'.IsQuasicoherentOnSite) (v : F ⟶ F') (σ : F' ⟶ F) (hσ : σ ≫ v = 𝟙 F')
      (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite F)
      (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite F'),
      Nonempty ((modulePullback D.site D.base D.base_mem
          (@projectiveBundleMapOfSplitEpi D.site D.base D.base_mem U F F' hF hF' v σ hσ hfree
            hfree')).obj (@projectiveBundleTwist D.site D.base D.base_mem U F hF hfree).obj ≅
        (@projectiveBundleTwist D.site D.base D.base_mem U F' hF' hfree').obj))
    (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) :
    Function.Bijective (bundleFormulaMap D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) N d hd) :=
  bijective_bundleFormulaMap_projectiveBundle_of_moduleIso_of_twist D sX hX E n hr
    (fun U sU hU F F' hF hF' e h =>
      projectiveBundleFormulaHolds_of_iso_of_twist D n htwist U sU hU F F' hF hF' e h)
    (fun U _ => htwist U _ _ _ _ _ _ _ _ _) N d hd

/-! ### Every rank -/

/-- **The map of the projective bundle formula in every rank `r`**: for a finite locally free
module `ℰ` of rank `r`, the map `(α_i)_{i < r} ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i` from
`∏_{i < r} CH_{d_i}(X)` to `CH_N(𝐏(ℰ))`, with `d_i + (r - 1) = N + i`. In rank `r = n + 1` it is
`AlgebraicGeometry.Space.bundleFormulaMap`; in rank `0` its source is the empty product and it is
zero. For `d_i = k + i` and `N = k + r - 1` it is the map of Stacks 0ERV. -/
def projectiveBundleFormulaMapOfRank (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) :
    (r : ℕ) → (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F r) →
    (N : ℤ) → (d : Fin r → ℤ) → (∀ i : Fin r, d i + ((r : ℤ) - 1) = N + (i : ℕ)) →
    ((∀ i, chowGroupCanonical.{u + 1} D sX hX (d i)) →+
      chowGroupCanonical.{u + 1} D
        ((@projectiveBundleProj D.site D.base D.base_mem X F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
          hF.isFiniteLocallyFreeOnSite).hom ≫ sX)
        (@isGood_projectiveBundleProj_comp D X.1 sX hX F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
            hF.isFiniteLocallyFreeOnSite) N)
  | 0, _, _, _, _ => 0
  | n + 1, hF, N, d, hd =>
    bundleFormulaMap D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX F n hF)
      (@projectiveBundleProj D.site D.base D.base_mem X F
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
          hF.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X F
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF) n hF
        hF.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X F
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF) n hF
        hF.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X F
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
          hF.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X F
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
        hF.isFiniteLocallyFreeOnSite) N d
      (fun i => by have := hd i; push_cast at this; linarith)

/-- **The projective bundle formula in rank `0`**: the projective bundle of a module of rank `0`
has no points, so its Chow groups vanish and the map from the empty product is bijective. -/
theorem bijective_projectiveBundleFormulaMapOfRank_zero
    (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F 0)
    (N : ℤ) (d : Fin 0 → ℤ) (hd : ∀ i : Fin 0, d i + (((0 : ℕ) : ℤ) - 1) = N + (i : ℕ)) :
    Function.Bijective (projectiveBundleFormulaMapOfRank D sX hX F 0 hF N d hd) := by
  have : F.IsQuasicoherentOnSite := (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
  have := subsingleton_chowGroupCanonical_of_isEmpty_points D _
    (@isGood_projectiveBundleProj_comp D X.1 sX hX F
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF) hF.isFiniteLocallyFreeOnSite)
    (isEmpty_points_projectiveBundle_of_rank_zero F hF) N
  exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Stacks 0ERV: the projective space bundle formula, in every rank**, from the twist
comparison along split quotients. For a finite locally free module `ℰ` of rank `r` on a good
algebraic space `X` with projective bundle `(π : P → X, 𝒪_P(1))`, the map
`(α_i)_{i < r} ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i` from `∏_{i < r} CH_{d_i}(X)` to `CH_N(P)`, with
`d_i + (r - 1) = N + i` (in Stacks `d_i = k + i`, `N = k + r - 1`), is bijective. -/
theorem bijective_projectiveBundleFormulaMapOfRank_of_twist
    (htwist : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem)
      (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2) (hF : F.IsQuasicoherentOnSite)
      (hF' : F'.IsQuasicoherentOnSite) (v : F ⟶ F') (σ : F' ⟶ F) (hσ : σ ≫ v = 𝟙 F')
      (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite F)
      (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite F'),
      Nonempty ((modulePullback D.site D.base D.base_mem
          (@projectiveBundleMapOfSplitEpi D.site D.base D.base_mem U F F' hF hF' v σ hσ hfree
            hfree')).obj (@projectiveBundleTwist D.site D.base D.base_mem U F hF hfree).obj ≅
        (@projectiveBundleTwist D.site D.base D.base_mem U F' hF' hfree').obj))
    (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (r : ℕ)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F r)
    (N : ℤ) (d : Fin r → ℤ) (hd : ∀ i : Fin r, d i + ((r : ℤ) - 1) = N + (i : ℕ)) :
    Function.Bijective (projectiveBundleFormulaMapOfRank D sX hX F r hF N d hd) := by
  cases r with
  | zero => exact bijective_projectiveBundleFormulaMapOfRank_zero D sX hX F hF N d hd
  | succ n => exact bijective_bundleFormulaMap_projectiveBundle_of_twist D sX hX F n hF htwist N d _

/-! ### Stacks 0ERV -/

/-- **The map of the projective space bundle formula (Stacks 0ERV).** For a finite locally free
module `ℰ` of rank `r` on a good algebraic space `X` with projective bundle
`(π : P = 𝐏(ℰ) → X, 𝒪_P(1))`, the map
`⊕_{i=0}^{r-1} CH_{k+i}(X) → CH_{k+r-1}(P)`,
`(α_0, …, α_{r-1}) ↦ π^*α_0 + c₁(𝒪_P(1)) ∩ π^*α_1 + … + c₁(𝒪_P(1))^{r-1} ∩ π^*α_{r-1}`
(`AlgebraicGeometry.Space.projectiveBundleFormulaMap_apply`). -/
def projectiveBundleFormulaMap (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (r : ℕ)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F r) (k : ℤ) :
    (∀ i : Fin r, chowGroupCanonical.{u + 1} D sX hX (k + (i : ℕ))) →+ chowGroupCanonical.{u + 1} D
        ((@projectiveBundleProj D.site D.base D.base_mem X F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
          hF.isFiniteLocallyFreeOnSite).hom ≫ sX)
        (@isGood_projectiveBundleProj_comp D X.1 sX hX F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
            hF.isFiniteLocallyFreeOnSite) (k + r - 1) :=
  projectiveBundleFormulaMapOfRank D sX hX F r hF (k + r - 1) (fun i => k + (i : ℕ))
    (fun i => by ring)

/-- **The projective space bundle formula map is the sum of the caps of the pullbacks**: in rank
`n + 1`, `(α_i) ↦ ∑_{i=0}^{n} c₁(𝒪_P(1))^i ∩ π^*α_i`, the pullback
`π^* : CH_{k+i}(X) → CH_{k+i+n}(P)` being the flat pullback of the relative dimension `n` of
`π`. -/
theorem projectiveBundleFormulaMap_apply (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2)
    (n : ℕ) (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F (n + 1)) (k : ℤ)
    (α : ∀ i : Fin (n + 1), chowGroupCanonical.{u + 1} D sX hX (k + (i : ℕ))) :
    projectiveBundleFormulaMap D sX hX F (n + 1) hF k α =
      ∑ i : Fin (n + 1),
        bundleFormulaCap D _ (isGood_projectiveBundleProj_comp_of_rank D sX hX F n hF)
          (@projectiveBundleTwist D.site D.base D.base_mem X F
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
              hF.isFiniteLocallyFreeOnSite).obj
          (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X F
              (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
            hF.isFiniteLocallyFreeOnSite) (i : ℕ) (k + ((n + 1 : ℕ) : ℤ) - 1 + (i : ℕ))
          (k + ((n + 1 : ℕ) : ℤ) - 1) rfl
          (bundleFormulaPull D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX F n hF)
            (@projectiveBundleProj D.site D.base D.base_mem X F
                (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
              hF.isFiniteLocallyFreeOnSite).hom rfl n
            (@isFlat_projectiveBundleProj D.site D.base D.base_mem X F
                (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF) n hF
              hF.isFiniteLocallyFreeOnSite)
            (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X F
                (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF) n hF
              hF.isFiniteLocallyFreeOnSite)
            (k + (i : ℕ)) (k + ((n + 1 : ℕ) : ℤ) - 1 + (i : ℕ)) (by push_cast; ring) (α i)) :=
  rfl

/-- **Stacks 0ERV: the projective space bundle formula.** Let `X` be a good algebraic space over
the base of the theory of cycles, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`(π : P = 𝐏(ℰ) → X, 𝒪_P(1))` its projective bundle. The map
`⊕_{i=0}^{r-1} CH_{k+i}(X) → CH_{k+r-1}(P)`,
`(α_0, …, α_{r-1}) ↦ π^*α_0 + c₁(𝒪_P(1)) ∩ π^*α_1 + … + c₁(𝒪_P(1))^{r-1} ∩ π^*α_{r-1}`,
is an isomorphism. -/
@[stacks 0ERV]
theorem bijective_projectiveBundleFormulaMap
    (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (r : ℕ)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F r) (k : ℤ) :
    Function.Bijective (projectiveBundleFormulaMap D sX hX F r hF k) :=
  bijective_projectiveBundleFormulaMapOfRank_of_twist D sX hX
    (fun U G G' hG hG' v σ hσ hfree hfree' =>
      ⟨@projectiveBundleSplitEpiTwistIso _ _ _ U G G' hG hG' v σ hσ hfree hfree'⟩)
    F r hF _ _ _

/-- **Stacks 0ERV as an isomorphism**:
`⊕_{i=0}^{r-1} CH_{k+i}(X) ≃+ CH_{k+r-1}(𝐏(ℰ))`, `(α_i) ↦ ∑_i c₁(𝒪_P(1))^i ∩ π^*α_i`. -/
def projectiveBundleFormulaEquiv (F : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (r : ℕ)
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) F r) (k : ℤ) :
    (∀ i : Fin r, chowGroupCanonical.{u + 1} D sX hX (k + (i : ℕ))) ≃+ chowGroupCanonical.{u + 1} D
        ((@projectiveBundleProj D.site D.base D.base_mem X F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
          hF.isFiniteLocallyFreeOnSite).hom ≫ sX)
        (@isGood_projectiveBundleProj_comp D X.1 sX hX F
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hF)
            hF.isFiniteLocallyFreeOnSite) (k + r - 1) :=
  AddEquiv.ofBijective (projectiveBundleFormulaMap D sX hX F r hF k)
    (bijective_projectiveBundleFormulaMap D sX hX F r hF k)

end AlgebraicGeometry.Space

end
