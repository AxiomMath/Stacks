module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Bundle
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamClassPow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibres of a projective bundle are projective spaces, with their twist

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of constant rank `n + 1`, and
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle (`Stacks.RelativeProj.projectiveBundle`). For every point
`y ∈ X` the fibre of `p` over `y` is `ℙⁿ_{κ(y)} = Proj κ(y)[T₀, …, Tₙ]`, by a cartesian square over
`Spec κ(y) ⟶ X` along which `𝒪_P(1)` pulls back to `𝒪(1)`.

## Main results

* `Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle`: the cartesian square
  `ℙⁿ_{κ(y)} ⟶ P` over `Spec κ(y) ⟶ X`, with `𝒪_P(1)` pulling back to `𝒪(1)` in `Pic(ℙⁿ_{κ(y)})`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveBundleFibre

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.SheafOfModules (pullbackPicardHom)

/-- The structure morphism `ℙⁿ_A ⟶ Spec A` of the coefficient-chart model is that of the model
of `Stacks.ProjectiveCohomology`. -/
theorem projToSpecCoeff_eq_projModelToSpec (A : Type u) [CommRing A] (n : ℕ) :
    projToSpecCoeff A n = Stacks.ProjectiveCohomology.projModelToSpec A n := by
  unfold projToSpecCoeff Stacks.ProjectiveCohomology.projModelToSpec
    Stacks.ProjectiveCohomology.polyDegreeZeroHom
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change GradedRing.projZeroRingHom' _ (algebraMap A (MvPolynomial (Fin (n + 1)) A) r) =
    (Stacks.ProjectiveChart.degreeZeroEquiv A n).symm r
  rw [← SetLike.GradeZero.coe_algebraMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) r,
    GradedRing.projZeroRingHom'_apply_coe]
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  rfl

/-- The class of the pullback of an invertible module is the pullback of its class. -/
theorem pullbackPicardHom_picardClassOf {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    pullbackPicardHom f (Stacks.WeilCohomology.picardClassOf Y L hL) =
      Stacks.WeilCohomology.picardClassOf X ((Scheme.Modules.pullback f).obj L)
        (Stacks.WeilCohomology.isInvertible_pullback_obj f L hL) :=
  Stacks.SheafOfModules.pullbackPicardHom_picardClass f L _

/-- The iso `f^* g^* E ≅ h^* E` for a factorisation `f ≫ g = h`. -/
private def pullbackPullbackIsoOfComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (hfg : f ≫ g = h) (E : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj E) ≅
      (Scheme.Modules.pullback h).obj E :=
  (Scheme.Modules.pullbackComp f g).app E ≪≫ (Scheme.Modules.pullbackCongr hfg).app E

/-- **A module which is free on a neighbourhood pulls back to a free module** along a morphism
landing in that neighbourhood. -/
theorem nonempty_iso_pullback_of_restrict_free {X T : Scheme.{u}} (E : X.Modules) (I : Type u)
    (U : X.Opens) (e : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (j : T ⟶ X) (hj : Set.range j ⊆ U) :
    Nonempty (SheafOfModules.free (R := T.ringCatSheaf) I ≅ (Scheme.Modules.pullback j).obj E) := by
  have hj' : Set.range j ⊆ Set.range U.ι := by rwa [U.range_ι]
  let j' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι j hj'
  have hfac : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackFreeIso j' I).symm ≪≫ (Scheme.Modules.pullback j').mapIso e.symm ≪≫
    (Scheme.Modules.pullback j').mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E) ≪≫
    pullbackPullbackIsoOfComp j' U.ι hfac E⟩

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **`Proj A[T₀, …, Tₙ]` is the projective bundle of `𝒪^{n+1}` on `Spec A`**, with `𝒪(1)` the
tautological twist. -/
theorem exists_iso_freeProjectiveBundle :
    ∃ θ : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) ≅
        (Stacks.SymGraded.freeProjectiveBundle (X := Spec (CommRingCat.of A)) n).scheme,
      θ.hom ≫ (Stacks.SymGraded.freeProjectiveBundle (X := Spec (CommRingCat.of A)) n).toBase =
          projToSpecCoeff A n ∧
        Nonempty ((Scheme.Modules.pullback θ.hom).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist
              (Stacks.SymGraded.freeModule (X := Spec (CommRingCat.of A))
                (Stacks.SymGraded.coordIndex.{u} n))
              (Stacks.SymGraded.isQuasicoherentPieces_free (X := Spec (CommRingCat.of A))
                (Stacks.SymGraded.coordIndex.{u} n))) ≅
          Stacks.ProjectiveBundleDeRham.projectiveTwistOne A n) := by
  have sq1 := Stacks.ProjectiveCohomology.isPullback_terminal_from_projModel A n
  have sq2 := Stacks.Chow.FreeTower.isPullback_projectiveBundleToIntegralModel
    (Spec (CommRingCat.of A)) n
  let θ := sq1.isoIsPullback _ _ sq2.flip
  have hfst :
      θ.hom ≫ (Stacks.SymGraded.freeProjectiveBundle (X := Spec (CommRingCat.of A)) n).toBase =
      Stacks.ProjectiveCohomology.projModelToSpec A n := sq1.isoIsPullback_hom_fst _ _ sq2.flip
  have hsnd :
      θ.hom ≫ Stacks.SymGraded.projectiveBundleToIntegralModel (X := Spec (CommRingCat.of A)) n =
      Stacks.ProjectiveCohomology.projModelMap n (Stacks.ProjectiveCohomology.fromULiftInt A) :=
    sq1.isoIsPullback_hom_snd _ _ sq2.flip
  obtain ⟨β, -⟩ := Stacks.Chow.FreeTower.exists_tautologicalTwist_iso_pullback
    (Spec (CommRingCat.of A)) n
  obtain ⟨γ⟩ := Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport A n 1
  exact ⟨θ, hfst.trans (projToSpecCoeff_eq_projModelToSpec A n).symm,
    ⟨(Scheme.Modules.pullback θ.hom).mapIso β ≪≫ pullbackPullbackIsoOfComp _ _ hsnd _ ≪≫ γ⟩⟩

section Fibre

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- **The projection of the projective bundle of a module finite locally free of rank `m + 1` is
smooth.** -/
@[ega "IV 17.3.9" "special case"]
theorem smooth_projectiveBundleToBase (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)] :
    Smooth (projectiveBundleToBase X E) := by
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase E]
  have := Stacks.ProjectiveBundle.smooth_toBase E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) m
  infer_instance

/-- **The projection of the projective bundle of a module finite locally free of rank `m + 1` is
proper.** -/
theorem isProper_projectiveBundleToBase_of_rank (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)] :
    IsProper (projectiveBundleToBase X E) :=
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (m + 1)
  Stacks.RelativeProj.isProper_projectiveBundleToBase X E

/-- **The fibre of a projective bundle over a point is projective space, with its twist**: for
`ℰ` finite locally free of rank `n + 1` and `y ∈ X` there is a cartesian square
`ℙⁿ_{κ(y)} ⟶ 𝐏(ℰ)` over `Spec κ(y) ⟶ X`, along which `𝒪_{𝐏(ℰ)}(1)` pulls back to `𝒪(1)` in
`Pic(ℙⁿ_{κ(y)})`. -/
theorem exists_isPullback_projectiveBundle (y : X) :
    ∃ φ : AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (X.residueField y) n) ⟶
        projectiveBundle X E,
      IsPullback φ (projToSpecCoeff (X.residueField y) n) (projectiveBundleToBase X E)
          (X.fromSpecResidueField y) ∧
        pullbackPicardHom φ (Stacks.WeilCohomology.picardClassOf _ (tautologicalDatumTwist E)
            (isInvertible_tautologicalDatumTwist E)) =
          Stacks.WeilCohomology.picardClassOf _
            (Stacks.ProjectiveBundleDeRham.projectiveTwistOne (X.residueField y) n)
            (Stacks.ProjectiveBundleDeRham.isInvertible_projectiveTwistOne _ n) := by
  obtain ⟨U, hyU, ⟨e⟩⟩ := Stacks.ProjectiveBundle.exists_restrict_free E (n + 1) y
  let j : Spec (CommRingCat.of (X.residueField y)) ⟶ X := X.fromSpecResidueField y
  have hj : Set.range j ⊆ U := by
    change Set.range (X.fromSpecResidueField y) ⊆ U
    rw [X.range_fromSpecResidueField]
    simpa using hyU
  obtain ⟨hF⟩ := nonempty_iso_pullback_of_restrict_free E _ U e j hj
  have : (SheafOfModules.free (R := (Spec (CommRingCat.of (X.residueField y))).ringCatSheaf)
      (ULift.{u} (Fin (n + 1)))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  obtain ⟨θ, hθ, ⟨τ⟩⟩ := exists_iso_freeProjectiveBundle (X.residueField y) n
  let F := SheafOfModules.free (R := (Spec (CommRingCat.of (X.residueField y))).ringCatSheaf)
    (ULift.{u} (Fin (n + 1)))
  let ψ := θ ≪≫ Stacks.RelativeProj.bundlePresentationIso F
  let bc := Stacks.RelativeProj.projectiveBundleBaseChange j E F hF
  have hψ : ψ.hom ≫ projectiveBundleToBase _ F = projToSpecCoeff (X.residueField y) n :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => θ.hom ≫ k)
      (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase F)).trans hθ)
  refine ⟨ψ.hom ≫ bc, ?_, ?_⟩
  · refine (Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange j E F hF).flip.of_iso
      ψ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp [j])
    · simp [bc]
    · simp [← hψ]
  · rw [Stacks.SheafOfModules.pullbackPicardHom_comp_apply, pullbackPicardHom_picardClassOf,
      Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ (isInvertible_tautologicalDatumTwist F)
        (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso j E F hF),
      pullbackPicardHom_picardClassOf]
    refine Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _ ?_
    have h : ψ.hom ≫ (Stacks.RelativeProj.bundlePresentationIso F).inv = θ.hom := by
      simp [ψ]
    exact pullbackPullbackIsoOfComp _ _ h _ ≪≫ τ

end Fibre

end Stacks.ProjectiveBundleFibre
