module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherenceAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedProjectiveHigherDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Eventual vanishing of the higher direct images of the twists along a projective immersion

Let `D : h_Z ⟶ X ×_S P^n_S` be a closed immersion of algebraic spaces over `S`, as in
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion`, whose source is represented by an object `Z`
of the big fppf site and whose composite with the coordinates is `h_k` for a morphism of the site
`k : Z ⟶ P^n_S`.  Put `ℒ = k^* 𝒪_{P^n_S}(1)` on the scheme underlying `Z` and let `ℒ^d` be its
tensor powers (written `𝒪_Z ⊗ ℒ^{⊗ d}`, the spelling of Stacks 02O1).  Let `q : h_Z ⟶ X` be the
composite of `D` with the projection.

* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.exists_isZero_rightDerived_twistPow`: if `X`
  is quasi-compact and locally Noetherian, there is `d₀` with `R^j q_* (ℒ^d)^a = 0` for all
  `d ≥ d₀` and `j > 0`.  This is Stacks 08AQ for `𝓕 = 𝒪_Z`, in the case the proof of Stacks 08AR
  applies it to: the source's proof checks the vanishing étale locally on `X` (Stacks 071Z) and
  cites Stacks 02O1 over an affine chart.  Here a single affine chart `V ⟶ X` surjective on points
  suffices, restriction along it being faithful; over it the base change of `q` is the
  represented space of an H-projective morphism of schemes `ψ_V : W ⟶ V`
  (`AlgebraicGeometry.Space.ProjectiveSpaceImmersion.exists_chart_isClosedImmersion`), the
  restriction of `(ℒ^d)^a` is `(π^*ℒ^d)^a`, the higher direct images along `h_{ψ_V}` are those of
  schemes by Stacks 071N, and `π^*ℒ` is ample relative to `ψ_V` because it is the pullback of
  `𝒪(1)` along the closed immersion `W ⟶ P^n_V`.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.isCoherent_modulePushforward_twistPow`: if `X`
  is locally Noetherian, `q_* (ℒ^d)^a` is coherent, for every `d`: over each affine chart of `X`
  it is the direct image along the H-projective `ψ_V`, coherent by Stacks 02O4.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space.ProjectiveSpaceImmersion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
  {hP : B.Contains (projectiveSpaceOver n S)} {X : AlgebraicSpaces B S hS} {Z : BigFppfOver B S hS}

/-- The twist `ℒ = k^* 𝒪_{P^n_S}(1)` on the scheme underlying `Z`. -/
def schemeTwist (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) :
    ((BigFppfOver.toScheme B S hS).obj Z).Modules :=
  (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj
    (projectiveSpaceTwistingSheaf n S)

/-- The twist `schemeTwist k` is an invertible module. -/
instance (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) :
    IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Z) (schemeTwist k) :=
  @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
    ((BigFppfOver.toScheme B S hS).map k) (projectiveSpaceTwistingSheaf n S)
    (Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf n S)

/-- The twists `𝒪_Z ⊗ ℒ^{⊗ d}`, in the spelling of Stacks 02O1. -/
def twistPow (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (d : ℕ) :
    ((BigFppfOver.toScheme B S hS).obj Z).Modules :=
  Stacks.RelativeVeryAmple.tensorModules _ (unitModule _)
    (tensorPowModule _ (schemeTwist k) (d : ℤ))

/-- The pullback of the twist along a morphism `π : W ⟶ Z` of schemes, in the spelling of
Stacks 02O1 on `W`. -/
def pullbackTwistPowIso (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) {W : Scheme.{u}}
    (π : W ⟶ (BigFppfOver.toScheme B S hS).obj Z) (d : ℕ) :
    (Scheme.Modules.pullback π).obj (twistPow k d) ≅
      Stacks.RelativeVeryAmple.tensorModules W (unitModule W)
        (tensorPowModule W ((Scheme.Modules.pullback π).obj (schemeTwist k)) (d : ℤ)) :=
  pullbackTensorModulesIso π _ _ ≪≫
    tensorModulesMapIso W (Stacks.RelativeAmple.pullbackUnitModuleIso π)
      (pullbackTensorPowModuleIso π (schemeTwist k) d)

/-- **The scheme-level data over a chart.**  For an étale chart `V` of `X` with affine underlying
scheme, the base change `ψ_V : W ⟶ V` of `q` is H-projective, and the pullback of `ℒ` along
`π : W ⟶ Z` is invertible and ample relative to `ψ_V`. -/
theorem exists_chart_isRelativelyAmple
    (D : ProjectiveSpaceImmersion B S hS n hP ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
    (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (hk : (D.imm ≫ D.coord).hom = yoneda.map k)
    (V : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    ∃ π : D.relativelyRepresentable_hom.pullback V.1.hom ⟶ Z,
      yoneda.map π = D.relativelyRepresentable_hom.fst V.1.hom ∧
      IsProjectiveMorphism
        ((BigFppfOver.toScheme B S hS).map (D.relativelyRepresentable_hom.snd V.1.hom)) ∧
      Stacks.RelativeAmple.IsRelativelyAmple
        ((BigFppfOver.toScheme B S hS).map (D.relativelyRepresentable_hom.snd V.1.hom))
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map π)).obj (schemeTwist k)) := by
  obtain ⟨π, ι, hπ, hι, hι1, hι2⟩ := exists_chart_isClosedImmersion D k hk V
  let T := BigFppfOver.toScheme B S hS
  let V₀ := T.obj V.1.left
  have hproj : IsProjectiveMorphism (T.map (D.relativelyRepresentable_hom.snd V.1.hom)) :=
    ⟨n, ι, hι, hι1⟩
  have hprop := isProper_of_isProjectiveMorphism _ hproj
  refine ⟨π, hπ, hproj, ?_⟩
  -- `π^* ℒ ≅ ι^* 𝒪_{P^n_V}(1)`
  let E : (Scheme.Modules.pullback (projectiveSpaceOverMap n V.1.left.hom.hom)).obj
      (projectiveSpaceTwistingSheaf n S) ≅ projectiveSpaceTwistingSheaf n V₀ :=
    (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n V.1.left.hom.hom)
        (projectiveSpaceOver.toIntegralAtUniverse n S)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd n V.1.left.hom.hom)).app _
  let e : (Scheme.Modules.pullback (T.map π)).obj (schemeTwist k) ≅
      (Scheme.Modules.pullback ι).obj (projectiveSpaceTwistingSheaf n V₀) :=
    (Scheme.Modules.pullbackComp (T.map π) (T.map k)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hι2.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp ι (projectiveSpaceOverMap n V.1.left.hom.hom)).app _).symm ≪≫
      (Scheme.Modules.pullback ι).mapIso E
  exact Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver _ _
    inferInstance ⟨1, le_rfl, n, ι, inferInstance, hι1, ⟨tensorPowModuleOneIso _ _ ≪≫ e⟩⟩

/-- A faithful functor between preadditive categories preserving zero morphisms reflects zero
objects. -/
theorem _root_.CategoryTheory.Functor.isZero_of_isZero_obj_of_faithful_of_preservesZeroMorphisms
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] {A : C} (h : IsZero (F.obj A)) :
    IsZero A :=
  (IsZero.iff_id_eq_zero A).2
    (F.map_injective (by rw [F.map_id, F.map_zero]; exact h.eq_of_src _ _))

/-- **Stacks 08AQ for `𝓕 = 𝒪_Z`, along a projective immersion with represented source.**  If `X`
is quasi-compact and locally Noetherian, there is a `d₀` such that `R^j q_* ((𝒪_Z ⊗ ℒ^{⊗ d})^a)`
vanishes for all `d ≥ d₀` and `j > 0`, where `q = D.hom` and `ℒ = k^* 𝒪_{P^n_S}(1)`.

The vanishing is tested after restriction to one affine chart `V ⟶ X` surjective on points,
which is faithful (`AlgebraicGeometry.Space.faithful_etaleModulePullback`).  There it is
`R^j (h_{ψ_V})_* ((π^*(𝒪_Z ⊗ ℒ^{⊗ d}))^a)` (Stacks 071Z and the compatibility of `(-)^a` with
étale restriction), which is `(R^j ψ_{V*} (𝒪_W ⊗ (π^*ℒ)^{⊗ d}))^a` by Stacks 071N, and that
vanishes for `d ≫ 0` by Stacks 02O1, `π^*ℒ` being ample relative to the H-projective
`ψ_V : W ⟶ V` over the Noetherian affine `V`. -/
theorem exists_isZero_rightDerived_twistPow
    (D : ProjectiveSpaceImmersion B S hS n hP ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
    (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (hk : (D.imm ≫ D.coord).hom = yoneda.map k)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
    have := modulePushforward_additive B S hS D.hom
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ j : ℕ, 0 < j →
      IsZero (((modulePushforward B S hS D.hom).rightDerived j).obj
        ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
          (twistPow k d))) := by
  intro _ _
  let T := BigFppfOver.toScheme B S hS
  have hq := D.relativelyRepresentable_hom
  obtain ⟨U, f, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  let V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, isEtaleChart_of_isEtale B S hS f het⟩
  have : IsAffine (T.obj V.1.left) := hU
  have : IsLocallyNoetherian (T.obj V.1.left) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)
      X.2).1 hXN U f (presheaf_etale_of_isEtale B S hS het)
  have : _root_.AlgebraicGeometry.IsNoetherian (T.obj V.1.left) := ⟨⟩
  obtain ⟨π, hπ, hproj, hample⟩ := exists_chart_isRelativelyAmple D k hk V
  let ψ := hq.snd V.1.hom
  have hψp : _root_.AlgebraicGeometry.IsProper (T.map ψ) := isProper_of_isProjectiveMorphism _ hproj
  have : IsLocallyNoetherian (T.obj (hq.pullback V.1.hom)) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map ψ)
  have : (unitModule (T.obj (hq.pullback V.1.hom))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _
  open Stacks.AlgebraicGeometry in
  obtain ⟨d₀, hd₀⟩ :=
    AmpleTwistAcyclicity.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
      (T.map ψ) (unitModule _) _ hample
  refine ⟨d₀, fun d hd j hj ↦ ?_⟩
  let i : schemeSpace U ⟶ X := ObjectProperty.homMk f
  have hfaith := faithful_etaleModulePullback.{u, u} B S hS U i het hsurj
  have : (etaleModulePullback.{u, u} B S hS i het).IsLeftAdjoint :=
    ⟨_, ⟨etaleModulePullbackAdjunction B S hS i het⟩⟩
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (etaleModulePullback.{u, u} B S hS i het)
  refine CategoryTheory.Functor.isZero_of_isZero_obj_of_faithful_of_preservesZeroMorphisms
    (etaleModulePullback.{u, u} B S hS i het) ?_
  -- the base change of `q` along the chart
  let W := hq.pullback V.1.hom
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS ψ)
  have sq : IsPullback (representedSpaceMap B S hS π) (representedSpaceMap B S hS ψ) D.hom i := by
    refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ ?_) ?_
    · show yoneda.map π ≫ D.hom.hom = yoneda.map ψ ≫ f
      rw [hπ]
      exact hq.w V.1.hom
    · show IsPullback (yoneda.map π) (yoneda.map ψ) D.hom.hom f
      rw [hπ]
      exact hq.isPullback V.1.hom
  -- the restriction of `(𝒪_Z ⊗ ℒ^{⊗ d})^a` to the chart is `(𝒪_W ⊗ (π^*ℒ)^{⊗ d})^a`
  let L' := (Scheme.Modules.pullback (T.map π)).obj (schemeTwist k)
  let FW := Stacks.RelativeVeryAmple.tensorModules (T.obj W) (unitModule (T.obj W))
    (tensorPowModule (T.obj W) L' (d : ℤ))
  have hpow : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj W).presheaf
      (T.obj W).ringCatSheaf.2 (tensorPowModule (T.obj W) L' (d : ℤ)) :=
    isInvertibleModule_tensorPowModule (T.obj W) L' (d : ℤ)
  have hFWcoh : FW.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible (T.obj W)
      (unitModule (T.obj W)) (tensorPowModule (T.obj W) L' (d : ℤ))
  have hz : IsZero (((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerived j).obj
      ((representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).obj FW)) := by
    obtain ⟨e'⟩ := nonempty_rightDerived_modulePushforward_representedSpaceMap_iso B S hS ψ
      inferInstance inferInstance FW (GroupoidScheme.isQuasicoherent_of_isCoherent FW hFWcoh) j
    refine IsZero.of_iso ?_ e'
    have := additive_representedAssociatedModule B S hS V.1.left
      (isAlgebraicSpace_yoneda B S hS V.1.left)
    exact Functor.map_isZero _
      ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ j _).2 (hd₀ d j hd hj))
  have hφ : IsEtale B S hS (representedSpaceMap B S hS π).hom :=
    isEtale_of_isPullback B S hS _ _ i D.hom sq.flip het
  let e₁ := (representedAssociatedModuleEtalePullbackIso B S hS π hφ).app (twistPow k d)
  let e₂ := (representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).mapIso
    (pullbackTwistPowIso k (T.map π) d)
  have hz' : IsZero (((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerived j).obj
      ((etaleModulePullback B S hS (representedSpaceMap B S hS π) hφ).obj
        ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
          (twistPow k d)))) :=
    hz.of_iso (((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerived j).mapIso
      (e₁ ≪≫ e₂))
  exact hz'.of_iso ((moduleHigherPushforwardEtaleBaseChangeIso B S hS
    (representedSpaceMap B S hS π) (representedSpaceMap B S hS ψ) D.hom i sq het j).app
      ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
        (twistPow k d))).symm

/-- **The direct image of the twists is coherent.**  If `X` is locally Noetherian, the scheme
underlying `Z` is locally Noetherian and `q = D.hom` is quasi-compact and quasi-separated, then
`q_* ((𝒪_Z ⊗ ℒ^{⊗ d})^a)` is a coherent `𝒪_X`-module for every `d`.

Coherence is tested on the affine étale charts `V` of `X`
(`AlgebraicGeometry.Space.isCoherent_of_forall_affine_chart`); over such a chart the restriction
is the direct image along the base change `h_{ψ_V}` of the restriction `(π^*(𝒪_Z ⊗ ℒ^{⊗ d}))^a`
(Stacks 071Z in degree zero), and `ψ_V` is H-projective, so this is Stacks 02O4
(`AlgebraicGeometry.Space.hasCoherentHigherDirectImages_representedSpaceMap`). -/
theorem isCoherent_modulePushforward_twistPow
    (D : ProjectiveSpaceImmersion B S hS n hP ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
    (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (hk : (D.imm ≫ D.coord).hom = yoneda.map k)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z)]
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (hqc : IsQuasiCompact B S hS D.hom.hom) (hqs : IsQuasiSeparated B S hS D.hom.hom) (d : ℕ) :
    IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS D.hom).obj
      ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
        (twistPow k d))) := by
  let T := BigFppfOver.toScheme B S hS
  have hq := D.relativelyRepresentable_hom
  have hpowZ : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj Z).presheaf
      (T.obj Z).ringCatSheaf.2 (tensorPowModule (T.obj Z) (schemeTwist k) (d : ℤ)) :=
    isInvertibleModule_tensorPowModule (T.obj Z) (schemeTwist k) (d : ℤ)
  have hMcoh : (twistPow k d).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible (T.obj Z)
      (unitModule (T.obj Z)) (tensorPowModule (T.obj Z) (schemeTwist k) (d : ℤ))
  refine isCoherent_of_forall_affine_chart B S hS X hXN _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.hom hqc hqs _
      (isQuasicoherentOnSite_representedAssociatedModule B S hS Z _ _
        (GroupoidScheme.isQuasicoherent_of_isCoherent _ hMcoh))) fun V hV ↦ ?_
  have : IsAffine (T.obj V.1.left) := hV
  have : IsLocallyNoetherian (T.obj V.1.left) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)
      X.2).1 hXN V.obj.left V.obj.hom V.property
  obtain ⟨π, hπ, hproj, -⟩ := exists_chart_isRelativelyAmple D k hk V
  let ψ := hq.snd V.1.hom
  have hψp : _root_.AlgebraicGeometry.IsProper (T.map ψ) := isProper_of_isProjectiveMorphism _ hproj
  let W := hq.pullback V.1.hom
  have : IsLocallyNoetherian (T.obj W) := LocallyOfFiniteType.isLocallyNoetherian (T.map ψ)
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS ψ)
  have := modulePushforward_additive B S hS D.hom
  have := preservesFiniteLimits_modulePushforward B S hS D.hom
  have sq : IsPullback (representedSpaceMap B S hS π) (representedSpaceMap B S hS ψ) D.hom
      (chartToSpace B S hS X V) := by
    refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ ?_) ?_
    · show yoneda.map π ≫ D.hom.hom = yoneda.map ψ ≫ V.1.hom
      rw [hπ]
      exact hq.w V.1.hom
    · show IsPullback (yoneda.map π) (yoneda.map ψ) D.hom.hom V.1.hom
      rw [hπ]
      exact hq.isPullback V.1.hom
  have hφ : IsEtale B S hS (representedSpaceMap B S hS π).hom :=
    isEtale_of_isPullback B S hS _ _ _ D.hom sq.flip (isEtale_chartToSpace B S hS X V)
  let L' := (Scheme.Modules.pullback (T.map π)).obj (schemeTwist k)
  let FW := Stacks.RelativeVeryAmple.tensorModules (T.obj W) (unitModule (T.obj W))
    (tensorPowModule (T.obj W) L' (d : ℤ))
  have hpow : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj W).presheaf
      (T.obj W).ringCatSheaf.2 (tensorPowModule (T.obj W) L' (d : ℤ)) :=
    isInvertibleModule_tensorPowModule (T.obj W) L' (d : ℤ)
  have hFWcoh : FW.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible (T.obj W)
      (unitModule (T.obj W)) (tensorPowModule (T.obj W) L' (d : ℤ))
  have hc := hasCoherentHigherDirectImages_representedSpaceMap B S hS ψ hproj FW hFWcoh 0
  let e₁ := (representedAssociatedModuleEtalePullbackIso B S hS π hφ).app (twistPow k d)
  let e₂ := (representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).mapIso
    (pullbackTwistPowIso k (T.map π) d)
  have hc' : IsCoherent B S hS (yoneda.obj V.1.left) (isAlgebraicSpace_yoneda B S hS V.1.left)
      (((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerived 0).obj
        ((etaleModulePullback B S hS (representedSpaceMap B S hS π) hφ).obj
          ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
            (twistPow k d)))) :=
    isCoherent_of_iso B S hS _
      (((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerived 0).mapIso
        (e₁ ≪≫ e₂)).symm hc
  exact isCoherent_of_iso B S hS _
    (((moduleHigherPushforwardEtaleBaseChangeIso B S hS
      (representedSpaceMap B S hS π) (representedSpaceMap B S hS ψ) D.hom
        (chartToSpace B S hS X V) sq (isEtale_chartToSpace B S hS X V) 0).app
      ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
        (twistPow k d))) ≪≫
      (etaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapIso
          ((modulePushforward B S hS D.hom).rightDerivedZeroIsoSelf.app _)) hc'

end AlgebraicGeometry.Space.ProjectiveSpaceImmersion

end
