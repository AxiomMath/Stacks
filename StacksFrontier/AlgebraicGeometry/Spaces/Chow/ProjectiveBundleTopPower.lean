module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPowerRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedProjectiveBundleTop
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedChowSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistCharts
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRepresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The projective space bundle formula on algebraic spaces: the top power

In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `n + 1` and
`(π : P → X, 𝒪_P(1))` its projective bundle. This file proves Stacks 0ERU: for every `k`-cycle
`α` on `X`,

`π_*(c₁(𝒪_P(1))^s ∩ π^*α)` is `0` for `s < n` and `α` for `s = n`,

the cap products being those of Stacks 0EQJ at the canonical choices, in `Z_{k+n-s}(X)` and so in
the Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. The vanishing for
cycles is proved in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleProjection`.

All names below are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_of_representedChart`:
  the top coefficient through a represented étale chart over a base of dimension `k`.
* `isLocallyProjectiveTower_chartBundleToChart`: a chart bundle with the restriction of `𝒪_P(1)`
  is a projective tower locally on its chart.
* `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_self`:
  `π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α` in `Z_k(X)`.
* The two theorems named `chowClassCanonical_` followed by
  `properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle`, without
  and with the suffix `_eq_zero`: Stacks 0ERU in the Chow group, for `s = n` and `s < n`.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The top coefficient over a base of dimension `k` with a represented étale chart -/

section RepresentedChart

variable (D : BaseSpaceDimensionSituation.{u})
    {T P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sT : T ⟶ D.space) (hT : D.IsGood sT) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    {π : P ⟶ T} (hπB : π ≫ sT = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hr : HasRelativeDimension n D.site D.base D.base_mem π)
    (hproper : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    {R Q : BigFppfOver D.site D.base D.base_mem} {h : yoneda.obj R ⟶ T}
    (hh : IsEtale D.site D.base D.base_mem h) (hR : D.IsGood (h ≫ sT)) (q : Q ⟶ R)
    {h' : yoneda.obj Q ⟶ P} (sq : IsPullback h' (yoneda.map q) π h)
    (hQ : D.IsGood (yoneda.map q ≫ h ≫ sT))

include hh sq hR in
/-- **The top coefficient through a represented étale chart over a base of dimension `k`.** Let
`π : P → T` be proper and flat of relative dimension `n` between good spaces and `ℒ` an
invertible `𝒪_P`-module. Let `h : h_R → T` be étale from a represented good space, with
`P ×_T h_R = h_Q` represented through a morphism of schemes `q : Q → R` which is proper and,
with the reading of `h'^*ℒ` on `Q`, a projective tower of fibre dimension `n` locally on `R`. If
`δ ≤ k` at every point of `h_R`, then for every `k`-cycle `α` on `T` and every integral closed
subspace `Z ⊆ T` whose inverse image in `h_R` is nonempty, the coefficient of
`π_*(c₁(ℒ)^n ∩ π^*α)` at `Z` is the coefficient of `α` at `Z`, the cap products being those of
Stacks 0EQJ at the canonical choices. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_of_representedChart
    [AlgebraicGeometry.IsProper ((BigFppfOver.toScheme D.site D.base D.base_mem).map q)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Q).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Q).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem Q
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk h' : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base
            D.base_mem) ⟶ ⟨P, hP.1⟩)).obj L))]
    (htower : Stacks.Chow.IsLocallyProjectiveTower n
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map q)
      (representedZariskiModule D.site D.base D.base_mem Q
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk h' : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base
            D.base_mem) ⟶ ⟨P, hP.1⟩)).obj L)))
    (k : ℤ) (hdimR : ∀ y : points D.site D.base D.base_mem (yoneda.obj R),
      D.deltaValue (h ≫ sT) y ≤ k)
    (α : CycleGroup D sT k) (Z : IntegralClosedSubspace D.site D.base D.base_mem T)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem h)) :
    (properCyclePushforward D sP hP sT hT hπB hproper.2.1.2 k
        (firstChernCapPowCycleMap D sP hP L hL n k
          (flatPullbackMap D sP hP sT hT π hπB n hflat hr k (k + n) rfl α))).1 Z = α.1 Z := by
  have hh'B : h' ≫ sP = yoneda.map q ≫ h ≫ sT := by
    rw [← hπB, ← Category.assoc, sq.w, Category.assoc]
  have hπ' := isFlat_and_hasRelativeDimension_of_isPullback D _ hQ _ hR sP hP sT hT rfl hπB
    sq.flip n hflat hr
  have hπ'p := isProper_of_isPullback D.site D.base D.base_mem hQ.1 hP.1 hR.1 hT.1 sq hproper
  have hdimW : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj R),
      deltaDimension D (h ≫ sT) W ≠ k + 1 := fun W hW => by
    have := hdimR (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
      (W.genericPoint D.site D.base D.base_mem))
    rw [← deltaDimension, hW] at this
    omega
  let h'A : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨P, hP.1⟩ :=
    ObjectProperty.homMk h'
  have h₁ :=
    properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_preimageComponent D
      sT hT (h ≫ sT) hR sP hP (yoneda.map q ≫ h ≫ sT) hQ hh rfl hπB n hflat hr hproper sq hh'B
      rfl L hL ((modulePullback D.site D.base D.base_mem h'A).obj L)
      (modulePullbackInvertible h'A L hL) (Iso.refl _) k hdimW α Z
  refine (h₁ C).trans ?_
  have hδR := isDeltaCompatible_representedChowSituation D (h ≫ sT) hR
  have hδQ := hδR.comp hR q
  have h₂ := properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_of_represented D
    (h ≫ sT) hR (yoneda.map q ≫ h ≫ sT) hQ q rfl hπ'p.2.1.2 n hπ'.2.1 hπ'.2.2
    ((modulePullback D.site D.base D.base_mem h'A).obj L) (modulePullbackInvertible h'A L hL)
    (C := representedChowSituation D (h ≫ sT) hR)
    (𝟙 ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R)) hδR hδQ htower k
    (fun x => by
      rw [Stacks.Chow.relativeDimension_id, representedChowSituation_dimensionFunction_apply]
      exact hdimR _)
  refine (congrArg (fun γ : CycleGroup D (h ≫ sT) k => γ.1 _) (h₂ _)).trans ?_
  exact IntegralClosedSubspace.flatPullbackMap_apply_preimageComponent D (h ≫ sT) hR sT hT hh rfl
    k k (by simp) α Z C

end RepresentedChart

/-! ### The chart bundles as projective towers -/

section ChartTower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) (n : ℕ)
  (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E (n + 1))

/-- The restriction of `𝒪_P(1)` to a chart bundle `P_V`, read on `P_V`, is the inverse image of
the twist of `Stacks.Chow.bundle (ℰ|_V)` along the comparison of the two presentations of
`𝐏(ℰ|_V)`. -/
theorem nonempty_schemeReading_projectiveBundleTwist_iso {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    letI := isFiniteLocallyFree_chartBundleModule E hfree V
    Nonempty (schemeReading (projectiveBundleTwist E hfree).obj
        (projectiveBundleChartOfHom E hfree m) ≅
      (Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).inv).obj
        (Stacks.Chow.bundleTwist (chartBundleModule E V))) :=
  let := isFiniteLocallyFree_chartBundleModule E hfree V
  ⟨(((Scheme.Modules.pullbackComp (chartBundleChowBundleIso E hfree V).inv
        (chartBundleChowBundleIso E hfree V).hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr (chartBundleChowBundleIso E hfree V).inv_hom_id).app _ ≪≫
      (Scheme.Modules.pullbackId (X := chartBundle E V)).app _).symm ≪≫
    (Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).inv).mapIso
      (projectiveBundleTwistChowIso E hfree V m))⟩

/-- A module on a scheme isomorphic to one invertible in the sense of Stacks is invertible. -/
private theorem isInvertible_of_stacks_isInvertible_of_iso {Y : Scheme.{u}}
    {M N : Scheme.Modules Y}
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property M]
    (e : M ≅ N) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.presheaf _ _).mp
    (Stacks.SheafOfModules.isInvertible_of_iso Y.presheaf _ e)

include hr in
/-- **A chart bundle with the restriction of `𝒪_P(1)` is a projective tower locally on its
chart**, for `ℰ` of rank `n + 1`: it is the projective bundle of Stacks 02TW with its twist,
through the comparison of the two presentations of `𝐏(ℰ|_V)`. -/
theorem isLocallyProjectiveTower_chartBundleToChart {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    Stacks.Chow.IsLocallyProjectiveTower n (chartBundleToChart E V)
      (schemeReading (projectiveBundleTwist E hfree).obj
        (projectiveBundleChartOfHom E hfree m)) := by
  have := isFiniteLocallyFreeOfRank_chartBundleModule E n hr V
  obtain ⟨e⟩ := nonempty_schemeReading_projectiveBundleTwist_iso E hfree m
  exact (Stacks.Chow.isLocallyProjectiveTower_bundle (chartBundleModule E V) n).of_isPullback
    (IsPullback.of_horiz_isIso ⟨by
      rw [← chartBundleChowBundleIso_hom_comp_chartBundleToChart E hfree V, Iso.inv_hom_id_assoc,
        Category.comp_id]⟩) e

/-- **The restriction of `𝒪_P(1)` to a chart bundle is invertible.** -/
theorem isInvertible_schemeReading_projectiveBundleTwist {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (chartBundle E V).sheaf.obj
      (chartBundle E V).ringCatSheaf.property
      (schemeReading (projectiveBundleTwist E hfree).obj
        (projectiveBundleChartOfHom E hfree m)) := by
  let := isFiniteLocallyFree_chartBundleModule E hfree V
  obtain ⟨e⟩ := nonempty_schemeReading_projectiveBundleTwist_iso E hfree m
  have : Stacks.SheafOfModules.IsInvertible
      (Stacks.Chow.bundle (chartBundleModule E V)).presheaf
      (structureSheafRing (Stacks.Chow.bundle (chartBundleModule E V)).toRingedSpace).property
      (Stacks.Chow.bundleTwist (chartBundleModule E V)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (Stacks.Chow.isInvertible_bundleTwist (chartBundleModule E V))
  have : Stacks.SheafOfModules.IsInvertible (chartBundle E V).presheaf
      (structureSheafRing (chartBundle E V).toRingedSpace).property
      ((Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).inv).obj
        (Stacks.Chow.bundleTwist (chartBundleModule E V))) := inferInstance
  exact isInvertible_of_stacks_isInvertible_of_iso e.symm

end ChartTower

/-! ### Representable algebraic spaces on affine schemes -/

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An affine scheme is quasi-separated over the base**, as a representable algebraic space:
its morphism to the terminal object of the site has quasi-compact diagonal. -/
theorem isQuasiSeparatedOver_yoneda_of_isAffine {W : BigFppfOver B S hS}
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsQuasiSeparatedOver B S hS (yoneda.obj W) :=
  (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS
    (Over.mkIdTerminal.isTerminalObj yoneda _) (yoneda.map (Over.mkIdTerminal.from W))).2
    (diagonalProp_quasiCompact_yoneda_map_of_isAffine B S hS _ hW)

end Affine

/-! ### The top power for the projective bundle -/

section ProjectiveBundleTop

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))

/-- For an integral closed subspace `T ⊆ X` of δ-dimension `k`, the coefficient at `T` of
`π_*(c₁(𝒪_P(1))^n ∩ π^*[T])` is `1`. -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_apply_self
    (k : ℤ) (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : deltaDimension D sX T = k) :
    (properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
      (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 k
      (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
        (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
        (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) n k
        (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
          (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
          (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
          (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
          (k + n) rfl (integralCycle D sX k T hT)))).1 T = 1 := by
  have hTg := isGood_integralClosedSubspace D sX hX T
  have htop : deltaDimension D (T.subspace.ι ≫ sX)
      (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
        T.isIntegralSpace) = k :=
    (deltaDimension_top D (T.subspace.ι ≫ sX) hTg T.isIntegralSpace
      (deltaDimensionClosed_univ_integralClosedSubspace D sX hX T)).trans hT
  rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_eq_preimage D sX hX _
    (isGood_projectiveBundleProj_comp D sX hX E hfree) rfl n
    (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
    (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
    (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree) _
    (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) k T hT htop]
  have hP := isGood_projectiveBundleProj_comp D sX hX E hfree
  have hPc := isClosedSubspace_preimage_integralClosedSubspace D _ hP sX hX
    (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom T
  have hPTg := isGood_ι_preimage_integralClosedSubspace D _ hP sX hX
    (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom T
  have hsurj := isSurjective_of_presheafSurjective D.site D.base D.base_mem _
    (surjective_projectiveBundlePresentation (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
  obtain ⟨y, hy⟩ := hsurj (pointsMap D.site D.base D.base_mem _ T.subspace.ι
    (T.genericPoint D.site D.base D.base_mem))
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    (chartScheme (bundleBaseChart (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
      ).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme D.site D.base D.base_mem _ y)) isOpen_univ
  set V := openChart D.site D.base D.base_mem X
    (bundleBaseChart (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)) W with hVdef
  have m := openChartInclusion D.site D.base D.base_mem X
    (bundleBaseChart (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)) W
  have hVaff : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V.obj.left) :=
    isAffine_chartScheme_openChart D.site D.base D.base_mem X _ ⟨W, hW⟩
  obtain ⟨v, hv⟩ : pointsMap D.site D.base D.base_mem _ T.subspace.ι
      (T.genericPoint D.site D.base D.base_mem) ∈
      Set.range (pointsMap D.site D.base D.base_mem (yoneda.obj V.obj.left) V.1.hom) := by
    rw [hVdef, range_pointsMap_openChart]
    exact ⟨y, hyW, hy⟩
  have hg : IsEtale D.site D.base D.base_mem V.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem V.obj.hom).2 V.property
  have chartSq := isPullback_projectiveBundleChartOfHom (X := ⟨X, hX.1⟩) E hfree m
  obtain ⟨R, fst, snd, sqR, hsnd⟩ : ∃ (R : BigFppfOver D.site D.base D.base_mem)
      (fst : yoneda.obj R ⟶ T.subspace.toFunctor) (snd : R ⟶ V.obj.left),
      IsPullback fst (yoneda.map snd) T.subspace.ι V.obj.hom ∧
        AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map snd) :=
    ⟨_, _, _, T.isClosedSubspace.2.rep.isPullback V.obj.hom,
      T.isClosedSubspace.2.property_snd V.obj.hom⟩
  obtain ⟨Q, fst', snd', sqQ, hsnd'⟩ : ∃ (Q : BigFppfOver D.site D.base D.base_mem)
      (fst' : yoneda.obj Q ⟶ (T.subspace.preimage
        (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom).toFunctor)
      (snd' : Q ⟶ (projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).site V),
      IsPullback fst' (yoneda.map snd') (T.subspace.preimage
          (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom).ι
        (projectiveBundleChartOfHom (X := ⟨X, hX.1⟩) E hfree m).hom ∧
        AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map snd') :=
    ⟨_, _, _, hPc.2.rep.isPullback _, hPc.2.property_snd _⟩
  have hw : (fst' ≫ T.subspace.fromPreimage (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom) ≫
      T.subspace.ι = (yoneda.map snd' ≫ yoneda.map
        ((projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).siteToChart V)) ≫ V.obj.hom := by
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, sqQ.w, Category.assoc,
      chartSq.w, Category.assoc]
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : Q ⟶ R, yoneda.map q ≫ fst =
      fst' ≫ T.subspace.fromPreimage (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom ∧
      yoneda.map q ≫ yoneda.map snd = yoneda.map snd' ≫ yoneda.map
        ((projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).siteToChart V) :=
    ⟨yoneda.preimage (sqR.lift _ _ hw), by rw [Functor.map_preimage, sqR.lift_fst],
      by rw [Functor.map_preimage, sqR.lift_snd]⟩
  have sqG : IsPullback fst' (yoneda.map q)
      (T.subspace.fromPreimage (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom) fst := by
    refine IsPullback.of_bot ?_ hq₁.symm sqR
    rw [hq₂, Subfunctor.fromPreimage_ι, ← Functor.map_comp]
    exact sqQ.paste_vert chartSq
  have sqH : IsPullback (yoneda.map snd') (yoneda.map q)
      (yoneda.map ((projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).siteToChart V))
      (yoneda.map snd) := by
    refine IsPullback.of_right ?_ hq₂.symm chartSq
    rw [← sqQ.w, ← sqR.w]
    exact sqG.paste_horiz (Subfunctor.isPullback_preimage _ T.subspace).flip
  have sqHs := AlgebraicGeometry.Stack.ChartBaseChange.isPullback_toScheme_of_isPullback_yoneda sqH
  have hh : IsEtale D.site D.base D.base_mem fst :=
    isEtale_of_isPullback_yoneda D.site D.base D.base_mem sqR.flip hg
  have := hsnd
  have hRaff : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme D.site D.base D.base_mem).map snd)
  have hRalg := isAlgebraicSpace_yoneda D.site D.base D.base_mem R
  have hR : D.IsGood (fst ≫ T.subspace.ι ≫ sX) :=
    ⟨hRalg, isQuasiSeparated_of_isQuasiSeparatedOver D.site D.base D.base_mem
        (isQuasiSeparatedOver_yoneda_of_isAffine hRaff) _,
      isLocallyOfFiniteType_comp D.site D.base D.base_mem hRalg hTg.1 D.isAlgebraicSpace fst _
        (isLocallyOfFiniteType_of_isEtale' D.site D.base D.base_mem fst hh) hTg.2.2⟩
  have hqp : AlgebraicGeometry.IsProper ((BigFppfOver.toScheme D.site D.base D.base_mem).map q) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqHs
      (isProper_chartBundleToChart (X := ⟨X, hX.1⟩) E hfree V)
  have hQalg := isAlgebraicSpace_yoneda D.site D.base D.base_mem Q
  have hQ : D.IsGood (yoneda.map q ≫ fst ≫ T.subspace.ι ≫ sX) :=
    ⟨hQalg, isQuasiSeparated_comp D.site D.base D.base_mem hQalg hRalg _ _
        ((isQuasiSeparated_yoneda_map_iff D.site D.base D.base_mem q).2 inferInstance) hR.2.1,
      isLocallyOfFiniteType_comp D.site D.base D.base_mem hQalg hRalg D.isAlgebraicSpace _ _
        ((isLocallyOfFiniteType_yoneda_map_iff D.site D.base D.base_mem q).2 inferInstance)
        hR.2.2⟩
  have hhom : (ObjectProperty.homMk fst' : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base
        D.base_mem) ⟶ ⟨_, hPTg.1⟩) ≫ closedSubspaceHom D.site D.base D.base_mem hP.1 _ hPc =
      representedSpaceMap D.site D.base D.base_mem snd' ≫
        projectiveBundleChartOfHom (X := ⟨X, hX.1⟩) E hfree m :=
    ObjectProperty.hom_ext _ sqQ.w
  have e : representedZariskiModule D.site D.base D.base_mem Q
      ((modulePullback D.site D.base D.base_mem
        (ObjectProperty.homMk fst' : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base
          D.base_mem) ⟶ ⟨_, hPTg.1⟩)).obj
        (closedSubspaceModuleRestrict D _ hP (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
          ⟨_, hPc⟩)) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme D.site D.base D.base_mem).map snd')).obj
        (schemeReading (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
          (projectiveBundleChartOfHom (X := ⟨X, hX.1⟩) E hfree m)) :=
    (SmallEtale.restrictModule (associatedBigEtaleSite D.site)
        ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Q) Q.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence D.site D.base D.base_mem Q).inverse.mapIso
        ((modulePullbackCompIsoOfEq D.site D.base D.base_mem _ _ hhom).app _)) ≪≫
    (schemeReadingPullbackIso (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
      (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).property snd' rfl).symm
  have htower := (isLocallyProjectiveTower_chartBundleToChart (X := ⟨X, hX.1⟩) E hfree n hr
    m).of_isPullback sqHs e
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Q).sheaf.obj
      ((BigFppfOver.toScheme D.site D.base D.base_mem).obj Q).ringCatSheaf.property
      (representedZariskiModule D.site D.base D.base_mem Q
        ((modulePullback D.site D.base D.base_mem
          (ObjectProperty.homMk fst' : (⟨yoneda.obj Q, hQ.1⟩ : AlgebraicSpaces D.site D.base
            D.base_mem) ⟶ ⟨_, hPTg.1⟩)).obj
          (closedSubspaceModuleRestrict D _ hP (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
            ⟨_, hPc⟩))) := by
    have : Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
          ((projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).site V)).presheaf
        (structureSheafRing ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
          ((projectiveBundleChartFamily (X := ⟨X, hX.1⟩) E hfree).site V)).toRingedSpace).property
        (schemeReading (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
          (projectiveBundleChartOfHom (X := ⟨X, hX.1⟩) E hfree m)) :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_schemeReading_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree m)
    exact isInvertible_of_stacks_isInvertible_of_iso e.symm
  have hdimR : ∀ y : points D.site D.base D.base_mem (yoneda.obj R),
      D.deltaValue (fst ≫ T.subspace.ι ≫ sX) y ≤ k := fun y => by
    have hk : deltaDimensionClosed D (T.subspace.ι ≫ sX) hTg Set.univ isClosed_univ ≤
        ((k : ℤ) : EInt) := by
      rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX T, hT]
    have h₁ := deltaValue_le_add_of_hasRelativeDimension D (fst ≫ T.subspace.ι ≫ sX) hR
      (T.subspace.ι ≫ sX) hTg fst rfl 0
      (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem fst hTg.1 hh) y
    have h₂ := (deltaDimensionClosed_le_coe_iff D (T.subspace.ι ≫ sX) hTg Set.univ isClosed_univ
      k).mp hk (pointsMap D.site D.base D.base_mem _ fst y) (Set.mem_univ _)
    push_cast at h₁
    exact h₁.trans (by simpa using h₂)
  obtain ⟨r, -, -⟩ := exists_points_of_isPullback D.site D.base D.base_mem sqR
    (T.genericPoint D.site D.base D.base_mem) v hv.symm
  have hrmem : r ∈ (IntegralClosedSubspace.top D.site D.base D.base_mem T.isClosedSubspace.1
      T.isIntegralSpace).preimagePointSet D.site D.base D.base_mem fst := by
    change pointsMap D.site D.base D.base_mem _ fst r ∈
      subspacePointSet D.site D.base D.base_mem _ _
    rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
    exact Set.mem_univ _
  have hfl := isFlat_and_hasRelativeDimension_fromPreimage D _ hP sX hX _ rfl n
    (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
    (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) T
  refine (properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_apply_of_representedChart
    D (T.subspace.ι ≫ sX) hTg _ hPTg (fromPreimage_comp_ι_comp D _ sX _ rfl T) n
    hfl.1 hfl.2
    (isProper_fromPreimage D sX hX _ hP (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree) T)
    _ (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hP.1 _ hPc) _
      (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree))
    hh hR q sqG hQ htower k hdimR _ _
    ⟨irreducibleComponent (⟨r, hrmem⟩ : (IntegralClosedSubspace.top D.site D.base D.base_mem
      T.isClosedSubspace.1 T.isIntegralSpace).preimagePointSet D.site D.base D.base_mem fst),
      irreducibleComponent_mem_irreducibleComponents _⟩).trans ?_
  rw [integralCycle_coe, integralCycleCoeff_self]

/-- **Stacks 0ERU, the top power, at the level of cycles.** Let `ℰ` be a finite locally free
`𝒪_X`-module of rank `n + 1` on a good algebraic space `X/B`, and `(π : P → X, 𝒪_P(1))` its
projective bundle. For every `k`-cycle `α` on `X`,

`π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α`   in `Z_k(X)`,

`π^*` being the flat pullback of cycles (Stacks 0EP8), `c₁(𝒪_P(1))^n ∩ -` the `n`-fold cap
product of Stacks 0EQJ at the canonical choices and `π_*` the proper pushforward of cycles
(Stacks 0EP1). -/
theorem properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_self
    (k : ℤ) (α : CycleGroup D sX k) :
    properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
        (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 k
        (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
          (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
          (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) n k
          (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
            (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
            (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
            (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
            (k + n) rfl α)) = α :=
  (properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_self_iff D
    sX hX E hfree n hr k).2
    (fun T hT =>
      properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_apply_self
        D sX hX E hfree n hr k T hT) α

/-- **Stacks 0ERU, the vanishing, in the Chow group at the canonical embeddings.** Let `ℰ` be a
finite locally free `𝒪_X`-module of rank `n + 1` on a good algebraic space `X/B` and
`(π : P → X, 𝒪_P(1))` its projective bundle. For `s < n` and every `k`-cycle `α` on `X`, the class
of `π_*(c₁(𝒪_P(1))^s ∩ π^*α)` in `CH_{k+n-s}(X)` is zero, the Chow group being that of Stacks 0EQ6
at the canonical embeddings of Stacks 0ENK. -/
@[stacks 0ERU "the vanishing for s < r - 1, read on a cycle representing α, in the Chow group of \
Stacks 0EQ6 at the canonical embeddings"]
theorem chowClassCanonical_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_zero
    (s : ℕ) (hs : s < n) (k m : ℤ) (h : k + n = m + s) (α : CycleGroup D sX k) :
    chowClassCanonical.{u + 1} D sX hX m
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

/-- **Stacks 0ERU, the top power, in the Chow group at the canonical embeddings.** Let `ℰ` be a
finite locally free `𝒪_X`-module of rank `n + 1` on a good algebraic space `X/B` and
`(π : P → X, 𝒪_P(1))` its projective bundle. For every `k`-cycle `α` on `X`, the class of
`π_*(c₁(𝒪_P(1))^n ∩ π^*α)` in `CH_k(X)` is the class of `α`, the Chow group being that of
Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. -/
@[stacks 0ERU "the top power s = r - 1, read on a cycle representing α, in the Chow group of \
Stacks 0EQ6 at the canonical embeddings"]
theorem chowClassCanonical_properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle
    (k : ℤ) (α : CycleGroup D sX k) :
    chowClassCanonical.{u + 1} D sX hX k
        (properCyclePushforward D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX rfl
          (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.2 k
          (firstChernCapPowCycleMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree)
            (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj
            (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree) n k
            (flatPullbackMap D _ (isGood_projectiveBundleProj_comp D sX hX E hfree) sX hX
              (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom rfl n
              (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)
              (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree) k
              (k + n) rfl α))) =
      chowClassCanonical.{u + 1} D sX hX k α := by
  rw [properCyclePushforward_firstChernCapPowCycleMap_flatPullbackMap_projectiveBundle_eq_self
    D sX hX E hfree n hr k α]

end ProjectiveBundleTop

end AlgebraicGeometry.Space

end
