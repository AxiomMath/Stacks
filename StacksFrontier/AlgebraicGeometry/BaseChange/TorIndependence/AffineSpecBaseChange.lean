module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The derived base change map over a pushout square of rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a pushout square of commutative rings and consider
the cartesian square of their spectra.  For a K-flat complex `M` of `A`-modules the derived base
change map of Stacks 08HY at `M̃` is invertible as soon as the comparison of derived with
degreewise extension of scalars along `R → R'` is invertible at `M` viewed over `R`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullbackComparison_tilde`: the comparison of
  derived with degreewise pullback along `Spec R' ⟶ Spec R` at `Ñ` is the image of the comparison
  of derived with degreewise extension of scalars at `N`.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- The comparison of derived with degreewise pullback, read out of `DerivedCategory.Q`, is
invertible at a complex exactly when the comparison out of `DerivedCategory.Qh` is invertible at
its class. -/
theorem isIso_derivedPullbackComparison_of_isIso_complexComparison {X Y : RingedSpace.{u, u}}
    (g : X ⟶ Y) (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (h : IsIso ((AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison g).app K)) :
    IsIso ((derivedPullbackComparison g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
  dsimp only [AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
  have h₁ := isIso_right_of_isIso_comp h inferInstance
  have h₂ : IsIso (((derivedPullbackComparison g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫ DerivedCategory.Qh.map
        (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K)) ≫
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    rwa [Category.assoc]
  exact isIso_left_of_isIso_comp (isIso_left_of_isIso_comp h₂ inferInstance) inferInstance

/-- The comparison of derived with degreewise pullback along `Spec R' ⟶ Spec R` at the complex
of sheaves associated to a complex `N` of `R`-modules is invertible as soon as the comparison of
derived with degreewise extension of scalars is invertible at `N`. -/
theorem isIso_derivedPullbackComparison_tilde {R R' : CommRingCat.{u}} (b : R ⟶ R')
    (N : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      b.hom).comparison.app N)) :
    IsIso ((derivedPullbackComparison (Spec.map b).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) := by
  have hfac := AlgebraicGeometry.StandardModel.affinePullbackComparison_fac R R' b N
  have h₁ :
      IsIso ((AlgebraicGeometry.StandardModel.extendScalarsTildeComparison R R' b).app N) := by
    dsimp only [AlgebraicGeometry.StandardModel.extendScalarsTildeComparison]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have h₂ :
      IsIso ((AlgebraicGeometry.StandardModel.tildeDerivedPullbackComparison R R' b).app N) := by
    have : IsIso ((AlgebraicGeometry.StandardModel.tildeDerivedPullbackComparison R R' b).app N ≫
        (AlgebraicGeometry.StandardModel.tildePullbackComplexCompQIso R R' b).hom.app N) := by
      rw [← hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((AlgebraicGeometry.StandardModel.tildePullbackComplexCompQIso R R' b).hom.app N)
  have h₃ : IsIso ((AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison
      (Spec.map b).toLRSHom.toShHom).app
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) := by
    dsimp only [AlgebraicGeometry.StandardModel.tildeDerivedPullbackComparison] at h₂
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      ((AlgebraicGeometry.StandardModel.tildeDerivedPullbackFactor R R' b).hom.app N) _ _ h₂
  exact isIso_derivedPullbackComparison_of_isIso_complexComparison
    (Spec.map b).toLRSHom.toShHom _ h₃

/-- The cartesian square of spectra of a pushout square of rings. -/
theorem isPullback_specMap {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'}
    {d : R' ⟶ A'} (h : IsPushout a b c d) :
    IsPullback (Spec.map c) (Spec.map d) (Spec.map a) (Spec.map b) :=
  isPullback_SpecMap_of_isPushout a b c d h

/-- **The derived base change map over a pushout square of rings, at a K-flat complex.**  For a
K-flat complex `M` of `A`-modules, the derived base change map of the square of spectra at `M̃` is
invertible as soon as the comparison of derived with degreewise extension of scalars along
`R → R'` is invertible at `M` viewed over `R`. -/
theorem isIso_derivedBaseChangeMap_specMap {R A R' A' : CommRingCat.{u}} {a : R ⟶ A}
    {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'} (h : IsPushout a b c d)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : CochainComplex.KFlat.{u, u} M)
    (hcmp : IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      b.hom).comparison.app (((ModuleCat.restrictScalars a.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M))) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
      (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
      (comp_toShHom_of_comm (isPullback_specMap h).w)
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))) := by
  have e := (NatIso.mapHomologicalComplex (asIso (pushforwardTildeNatTrans R A a))
    (ComplexShape.up ℤ)).app M
  have h₀ := isIso_derivedPullbackComparison_tilde b _ hcmp
  have h₃ := (NatTrans.isIso_app_iff_of_iso
    (derivedPullbackComparison (Spec.map b).toLRSHom.toShHom)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso e)).1 h₀
  exact isIso_derivedBaseChangeMap_Qh_of_isIso_comparison (isPullback_specMap h) _
    (fun n => (inferInstance : ((tilde.functor A).obj (M.X n)).IsQuasicoherent))
    (Stacks.TildeStalk.kFlatComplex_tilde A M hM) h₃

/-- Under Tor independence of `A` and `R'` over `R`, the comparison of derived with degreewise
extension of scalars along `R → R'` is invertible at every K-flat complex of `A`-modules viewed
over `R`. -/
theorem isIso_comparison_restrictScalars_of_torIndependent {R A R' : CommRingCat.{u}}
    (a : R ⟶ A) (b : R ⟶ R')
    (hTor : letI := a.hom.toAlgebra; letI := b.hom.toAlgebra;
      RingTheory.TorIndependence.TorIndependent R A R')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : CochainComplex.KFlat.{u, u} M) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      b.hom).comparison.app (((ModuleCat.restrictScalars a.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) := by
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  exact @RingTheory.TorIndependence.isIso_extendScalarsCounit_app_restrict_of_torIndependent
    R A R' _ _ _ _ _ _ _ hTor _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} b.hom).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      b.hom).isLeftDerived M hM

/-- **Tor-independent base change over a pushout square of rings.**  If `A` and `R'` are Tor
independent over `R`, the derived base change map of the square of spectra is invertible at every
object of `D(𝒪_{Spec A})` with quasi-coherent cohomology. -/
theorem isIso_derivedBaseChangeMap_specMap_of_torIndependent {R A R' A' : CommRingCat.{u}}
    {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'} (h : IsPushout a b c d)
    (hTor : letI := a.hom.toAlgebra; letI := b.hom.toAlgebra;
      RingTheory.TorIndependence.TorIndependent R A R')
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec A).toRingedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj E).IsQuasicoherent) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
      (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
      (comp_toShHom_of_comm (isPullback_specMap h).w) E) := by
  obtain ⟨M, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory A E hE
  obtain ⟨Q, hQ, ⟨e'⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} M
  let C := ((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
  let v : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≅ E :=
    (DerivedCategory.quotientCompQhIso _).app C ≪≫
      ((tilde.functor A).mapDerivedCategoryFactors.app Q).symm ≪≫
      (tilde.functor A).mapDerivedCategory.mapIso e' ≪≫ e
  exact isIso_derivedBaseChangeMap_of_iso _ _ _ _ _ v
    (isIso_derivedBaseChangeMap_specMap h Q hQ
      (isIso_comparison_restrictScalars_of_torIndependent a b hTor Q hQ))

end Stacks.Cohomology.DerivedBaseChange
