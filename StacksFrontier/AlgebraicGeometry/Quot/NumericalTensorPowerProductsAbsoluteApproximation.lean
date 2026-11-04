module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentSituationSubringStageModel
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocalNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackSourceIso
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescend
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectObjectsDescendFamily

/-!
# Absolute Noetherian approximation of the numerical invariants over an affine base

Over the base `Spec ℤ`, let `f : X ⟶ Y` be a separated morphism of finite presentation whose
target is an affine scheme `Y = Spec Λ` of the site, with perfect objects `E_1, …, E_r` of
`D(𝒪_X)`. Write `Λ = colim Λ_i` over its finitely generated subrings. The numerical invariants
of an object of `Coh_{X/Y}` with respect to the `E_l` are, locally on the test scheme, pulled
back from a locally Noetherian scheme.

## Main definitions

* `AlgebraicGeometry.Space.subringStageBaseChange`: the base changes
  `X_j ×_{Spec Λ_j} Spec Λ_i` of a morphism `X_j ⟶ Spec Λ_j`, as Situation 09RH.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_subringStageBaseChange`: that system
  satisfies the convention of Stacks 07SD.
* `AlgebraicGeometry.Space.perfectObjectsDescend_subringStageBaseChange`: perfect objects
  descend along it (Stacks 09RJ).
* `AlgebraicGeometry.Space.NumericalSituation.isLocallyNoetherianPullbackAt_of_isAffine`: over an
  affine base the numerical invariants of Stacks 0DNE are everywhere locally pulled back from a
  locally Noetherian scheme.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))
  (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

section StageBaseChange

variable (j : Finset (affineRing hZ T)) {Xj : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  (hXj : IsAlgebraicSpace B _ hZ Xj) (fj : Xj ⟶ (stageSystem hZ T).obj (op j))
  (hfj : IsFinitePresentation B _ hZ fj)

/-- The base changes `X_j ×_{Spec Λ_j} Spec Λ_i`, `i ≥ j`, of a morphism of finite
presentation `X_j ⟶ Spec Λ_j`, as a `DescentSituation`, with limit `X_j ×_{Spec Λ_j} T`. -/
abbrev subringStageBaseChange : DescentSituation B (⊤_ Scheme.{u}) hZ hZ
    (subringStageSituation hZ T j).Stages :=
  (subringStageSituation hZ T j).stagesBaseChangeAlong hXj
    (isQuasiCompactSpace_of_isFinitePresentation B _ hZ fj
      (stageSystem_isAlgebraicSpace hZ T (op j))
      (stageSystem_isQuasiCompactSpace hZ T (op j)) hfj)
    (isAbsolutelyQuasiSeparated_of_isFinitePresentation B _ hZ hZ hXj
      (stageSystem_isAbsolutelyQuasiSeparated hZ T (op j)) hfj) fj

/-- The base changes `X_j ×_{Spec Λ_j} Spec Λ_i` satisfy `SiteContainsBaseChangeLimits`: their
diagrams of base changes to affine objects are those of the stages `Spec Λ_i`. -/
theorem siteContainsBaseChangeLimits_subringStageBaseChange :
    SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ
      (subringStageBaseChange hZ T j hXj fj hfj).system :=
  ((stageSystem_siteContainsBaseChangeLimits hZ T).comp_subtypeGe j).baseChangeOverSystem
    _ fj

/-- Perfect objects descend along the base changes `X_j ×_{Spec Λ_j} Spec Λ_i`: every perfect
object on the limit is the derived pullback of a perfect object on some stage. -/
theorem perfectObjectsDescend_subringStageBaseChange :
    PerfectObjectsDescend (fun i : (subringStageBaseChange hZ T j hXj fj hfj).Stages =>
      (subringStageBaseChange hZ T j hXj fj hfj).projection i.1) :=
  (DescentSituation.perfect_isColim_and_perfectObjectsDescend_of_siteContainsBaseChangeLimits _
    (siteContainsBaseChangeLimits_subringStageBaseChange hZ T j hXj fj hfj)).2

end StageBaseChange

namespace NumericalSituation

open CoherentSituation

variable {hZ T}

/-- Over an affine base `Spec Λ` of the site over `Spec ℤ`, for a separated morphism `f` and
perfect objects `E_1, …, E_r`, the numerical invariants of an object of `Coh_{X/Y}` are everywhere
locally pulled back from a locally Noetherian scheme. -/
theorem isLocallyNoetherianPullbackAt_of_isAffine
    (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)
    (eY : D.Y.1 ≅ yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T))
    (hf : IsSeparated B _ hZ D.f.hom) {r : ℕ}
    (E : Fin r → @DerivedCategory (Modules.{u, u} B _ hZ D.X.1 D.X.2) _ _
      (HasDerivedCategory.standard _))
    (hE : ∀ l, letI := HasDerivedCategory.standard (Modules.{u, u} B _ hZ D.X.1 D.X.2)
      (smallEtaleRingedSite B _ hZ D.X.1 D.X.2).IsPerfect (E l))
    (P : (Fin r → ℤ) → ℤ) (A : CoherentObject D) (t : A.testScheme) :
    IsLocallyNoetherianPullbackAt
      (schemePointsFunction (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A) t := by
  classical
  obtain ⟨j, Xj, fj, k, hXj, hfjfp, hfjsep, hsq⟩ := exists_stageModelSE hZ T D eY hf
  let Sub := subringStageSituation hZ T j.unop
  let Xs := subringStageBaseChange hZ T j.unop hXj fj hfjfp
  let πj : yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T) ⟶ (stageSystem hZ T).obj j :=
    (DescentSituation.stagesCone Sub).π.app (op (DescentSituation.baseStage Sub))
  have hsq' : IsPullback (D.f.hom ≫ eY.hom) k πj fj :=
    IsPullback.of_iso hsq.flip (Iso.refl _) eY (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [πj]; rfl) (by simp)
  let e₁ : D.X ≅ Xs.limitSpace := ObjectProperty.isoMk _ hsq'.isoPullback
  obtain ⟨i, F, hF, hFiso⟩ := Xs.exists_stage_derivedPullback_iso_of_perfectObjectsDescend
    (perfectObjectsDescend_subringStageBaseChange hZ T j.unop hXj fj hfjfp) e₁ E hE
  let ti := (DescentSituation.stagesToBase Sub).app (op i.1)
  let Di : CoherentSituation B (⊤_ Scheme.{u}) hZ :=
    { X := Xs.stage i.1
      Y := Sub.stage i.1.1
      f := ObjectProperty.homMk (pullback.fst ti fj)
      finitePresentation := IsFinitePresentation.of_isPullback B _ hZ (Xs.algebraicSpace i.1) hXj
        (Sub.algebraicSpace i.1.1) (Sub.algebraicSpace j.unop)
        (IsPullback.of_hasPullback ti fj).flip hfjfp }
  have hfi : IsSeparated B _ hZ Di.f.hom :=
    isSeparated_baseChange_of_isPullback (IsPullback.of_hasPullback ti fj).flip hfjsep
  let πi := (DescentSituation.stagesCone Sub).π.app (op i.1)
  let gi : D.Y ⟶ Di.Y := ObjectProperty.homMk (eY.hom ≫ πi)
  have hP : IsPullback (Xs.limitCone.π.app (op i.1)) (pullback.fst πj fj) (pullback.fst ti fj)
      πi :=
    isPullback_baseChangeOverMap B _ hZ πj ti πi
      (DescentSituation.stagesCone_π_comp Sub (op i.1)) fj
  have h₁ : IsPullback e₁.hom.hom D.f.hom (pullback.fst πj fj) eY.hom :=
    IsPullback.of_horiz_isIso (CommSq.mk hsq'.isoPullback_hom_fst)
  have hbig : IsPullback (e₁.hom.hom ≫ Xs.limitCone.π.app (op i.1)) D.f.hom Di.f.hom gi.hom :=
    h₁.paste_horiz hP
  let e : D.X ≅ (Di.baseChange gi).X := ObjectProperty.isoMk _ hbig.isoPullback
  have he : e.hom ≫ (Di.baseChange gi).f = D.f :=
    ObjectProperty.hom_ext _ hbig.isoPullback_hom_snd
  have hek : e.hom ≫ Di.baseChangeSourceProjection gi = e₁.hom ≫ Xs.projection i.1 :=
    ObjectProperty.hom_ext _ hbig.isoPullback_hom_fst
  have hs : IsSeparated B _ hZ (Di.baseChange gi).f.hom := isSeparated_baseChange hfi gi
  let := HasDerivedCategory.standard (Modules.{u, u} B _ hZ D.X.1 D.X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B _ hZ (Xs.stage i.1).1 (Xs.stage i.1).2)
  let E' := sourceIsoObjects e (baseChangeObjects Di gi F)
  have hE' := isPerfect_sourceIsoObjects e (baseChangeObjects Di gi F)
    (isPerfect_baseChangeObjects Di gi F hF)
  let eE : ∀ l, E l ≅ E' l := fun l =>
    (hFiso l).some.symm ≪≫ (smallEtaleDerivedModulePullbackCongr B _ hZ hek.symm).app _ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B _ hZ e.hom _).app (F l)).symm
  let hst := modulePullbackStabilityOfFinitePresentation B (⊤_ Scheme.{u}) hZ
  let A₀ := Di.baseChangeObject' hst gi
    (isoObject (D := Di.baseChange gi) (f' := D.f) D.finitePresentation e he hst A)
  have hχ : ∀ n, (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A n =
      (ofDerivedTensorPowerProducts hfi F hF P).numericalEuler A₀ n := fun n =>
    (numericalEuler_congr hf hE hE' eE P A n).trans
      ((numericalEuler_sourceIso (D := Di.baseChange gi) (f' := D.f) D.finitePresentation e he hs hf
        (baseChangeObjects Di gi F)
        (isPerfect_baseChangeObjects Di gi F hF) P A n).trans
        (numericalEuler_baseChange Di gi hfi hs F hF P _ n))
  have hYi : IsLocallyNoetherian B _ hZ Di.Y.1 := by
    have := isNoetherian_subringStage hZ (affineRing hZ T) (op i.1.1)
    exact isLocallyNoetherian_yoneda B _ hZ _ (inferInstanceAs
      (_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigAffineFppf.toScheme B _ hZ).obj
        (finsetStage hZ (affineRing hZ T) (op i.1.1)))))
  exact (isLocallyNoetherianPullbackAt_of_isLocallyNoetherian
    (ofDerivedTensorPowerProducts hfi F hF P) hYi A₀ t).congr
    fun n y => (congrFun (hχ n) _).symm

end NumericalSituation

end AlgebraicGeometry.Space

end
