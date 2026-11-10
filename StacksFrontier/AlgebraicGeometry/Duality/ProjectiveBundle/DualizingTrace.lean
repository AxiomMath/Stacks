module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Statement
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopTrace
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DerivedPushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.KoszulCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PieceZeroUnit
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.ModelTransport
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf

/-!
# The trace `R π_*(π^*𝓛(-n-1)[n]) ≅ 𝒪_S` on a projective bundle

Let `ℰ` be a finite locally free `𝒪_S`-module of rank `n + 1`, `n ≥ 0`, with determinant
`𝓛 = ⋀ⁿ⁺¹ ℰ`, and `π : 𝐏(ℰ) ⟶ S` its projective bundle. In the proof of [Stacks, Tag 0A9W] the
canonical isomorphism `Rⁿ π_*(π^*𝓛(-n-1)) ≅ 𝒪_S` of [Stacks, Tag 01XX], together with the
vanishing of the other higher direct images, gives `R π_*(π^*𝓛(-n-1)[n]) ≅ 𝒪_S`. This file
proves that, at any model of the derived categories. For `n = 0` the projection is an
isomorphism and the tautological map `π^*ℰ ⟶ 𝒪(1)` is one, so `π^*𝓛(-1) ≅ 𝒪`.

## Main definitions

* `Stacks.Duality.ProjectiveBundleDualizing.dualizingModule`: `𝒪(-n-1) ⊗ π^*𝓛`.
* `Stacks.Duality.ProjectiveBundleDualizing.rightDerivedTopDualizingModuleIso`:
  `Rⁿ π_*(𝒪(-n-1) ⊗ π^*𝓛) ≅ 𝒪_S`.

## Main results

* `Stacks.Duality.ProjectiveBundleDualizing.isZero_rightDerived_dualizingModule`: the other
  higher direct images vanish.
* `Stacks.Duality.ProjectiveBundleDualizing.nonempty_derivedPushforward_dualizingModule_iso`:
  `R π_*(𝒪(-n-1) ⊗ π^*𝓛)[0] ≅ 𝒪_S[-n]`, at any model.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjectiveBundleCohomology (bundle bundlePushforward negTwist)

universe w u

namespace Stacks.Duality.ProjectiveBundleDualizing

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) (n : ℕ)

/-- The determinant `𝓛 = ⋀ⁿ⁺¹ ℰ`. -/
abbrev det : S.Modules := Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)

/-- The projection `π : 𝐏(ℰ) ⟶ S`. -/
abbrev proj : bundle E hqc ⟶ S :=
  (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase

/-- **`π^*𝓛(-n-1)`**, written `𝒪(-n-1) ⊗ π^*𝓛`. -/
abbrev dualizingModule : (bundle E hqc).Modules :=
  (Stacks.ProjectionFormula.tensorRightInvertible (bundle E hqc)
    ((Scheme.Modules.pullback (proj E hqc)).obj (det E n))).obj (negTwist E hqc D (n + 1))

section ProjectionFormula

variable {n} (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
include hfree

/-- The projection formula for the determinant, in the indexing by injective resolutions. -/
def rightDerivedDualizingModuleIso (q : ℕ) :
    ((bundlePushforward E hqc).rightDerived q).obj (dualizingModule E hqc D n) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible S (det E n)).obj
        (((bundlePushforward E hqc).rightDerived q).obj (negTwist E hqc D (n + 1))) :=
  haveI := Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isInvertible_det E hfree
  (Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) q).app _ ≪≫
    (Stacks.ProjectionFormula.higherDirectImageTensorRightIso (proj E hqc) (det E n) q).app
      (negTwist E hqc D (n + 1)) ≪≫
    (Stacks.ProjectionFormula.tensorRightInvertible S (det E n)).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) q).app _).symm

end ProjectionFormula

omit [E.IsQuasicoherent] in
/-- The determinant of a finite locally free module of rank `n + 1` is invertible. -/
theorem isInvertible_det_of_rank {n : ℕ}
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) :
    Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (det E n) :=
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
  Scheme.Modules.isInvertible_exteriorPower_self E (n + 1)

/-- `π^*𝓛(-n-1)` is invertible. -/
theorem isInvertible_dualizingModule
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) :
    Stacks.SheafOfModules.IsInvertible (bundle E hqc).presheaf (bundle E hqc).ringCatSheaf.2
      (dualizingModule E hqc D n) := by
  have := isInvertible_det_of_rank E hfree
  rw [dualizingModule, Stacks.ProjectionFormula.tensorRightInvertible_obj]
  exact Stacks.SheafOfModules.tensorProduct_isInvertible (bundle E hqc).presheaf
    (bundle E hqc).ringCatSheaf.2 (negTwist E hqc D (n + 1))
    ((Scheme.Modules.pullback (proj E hqc)).obj (det E n))

/-- `π^*𝓛(-n-1)` is quasi-coherent. -/
theorem isQuasicoherent_dualizingModule
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) :
    (dualizingModule E hqc D n).IsQuasicoherent :=
  Stacks.Picard.isQuasicoherent_of_isInvertible _
    (isInvertible_dualizingModule E hqc D n hfree)

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

variable {n} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
include hn hfree

/-- **`R^q π_*(π^*𝓛(-n-1)) = 0` for `q ≠ n`.** -/
theorem isZero_rightDerived_dualizingModule (q : ℕ) (hq : q ≠ n) :
    IsZero (((bundlePushforward E hqc).rightDerived q).obj (dualizingModule E hqc D n)) := by
  have := Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isInvertible_det E hfree
  refine IsZero.of_iso ?_ (rightDerivedDualizingModuleIso E hqc D hfree q)
  refine (Stacks.ProjectionFormula.tensorRightInvertible S (det E n)).map_isZero ?_
  refine IsZero.of_iso ?_
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) q).app _)
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · exact Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_rightDerivedPlus_zero_of_neg
      E hqc D (by omega) hfree (by omega)
  · open Stacks.AlgebraicGeometry.ProjectiveBundleCohomology in
    exact isZero_rightDerivedPlus_pushforward_twist_of_ne
      E hqc n hfree D _ (q : ℤ) (by exact_mod_cast hq0.ne') (by exact_mod_cast hq)

/-- **`Rⁿ π_*(π^*𝓛(-n-1)) ≅ 𝒪_S`**: the projection formula and the trace
`Rⁿ π_* 𝒪(-n-1) ⊗ 𝓛 ≅ 𝒪_S` of [Stacks, Tag 01XX]. -/
def rightDerivedTopDualizingModuleIso :
    ((bundlePushforward E hqc).rightDerived n).obj (dualizingModule E hqc D n) ≅
      SheafOfModules.unit S.ringCatSheaf :=
  rightDerivedDualizingModuleIso E hqc D hfree n ≪≫
    Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.topTraceIso E hqc D hn hfree

end Standard

section AnyModel

variable {n} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  [HasDerivedCategory.{w} (bundle E hqc).Modules] [HasDerivedCategory.{w} S.Modules]
include hn hfree

/-- Away from degree `n`, the cohomology of `R π_*(π^*𝓛(-n-1)[0])` vanishes, at any model. -/
theorem isZero_homology_derivedPushforward_dualizingModule (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules q).obj
      ((derivedPushforward.{w} (proj E hqc)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dualizingModule E hqc D n)))) := by
  rcases lt_or_ge q 0 with hq' | hq'
  · exact isZero_homology_derivedPushforward_of_neg _ _ q hq'
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq').symm⟩
    obtain ⟨e⟩ := nonempty_homology_derivedPushforward_iso_rightDerived.{w}
      (proj E hqc) (dualizingModule E hqc D n) k
    exact IsZero.of_iso (isZero_rightDerived_dualizingModule E hqc D hn hfree k
      (by exact_mod_cast hq)) e

/-- **`R π_*(π^*𝓛(-n-1)[0]) ≅ 𝒪_S[-n]`**, at any model, for `n ≥ 1`. -/
theorem nonempty_derivedPushforward_dualizingModule_iso_of_pos :
    Nonempty ((derivedPushforward.{w} (proj E hqc)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dualizingModule E hqc D n)) ≅
      (DerivedCategory.singleFunctor S.Modules (n : ℤ)).obj
        (SheafOfModules.unit S.ringCatSheaf)) := by
  set K := (derivedPushforward.{w} (proj E hqc)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (dualizingModule E hqc D n))
  have : K.IsGE (n : ℤ) := (DerivedCategory.isGE_iff K _).2 fun i hi =>
    isZero_homology_derivedPushforward_dualizingModule E hqc D hn hfree i (by omega)
  have : K.IsLE (n : ℤ) := (DerivedCategory.isLE_iff K _).2 fun i hi =>
    isZero_homology_derivedPushforward_dualizingModule E hqc D hn hfree i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K (n : ℤ)
  obtain ⟨t⟩ := nonempty_homology_derivedPushforward_iso_rightDerived.{w}
    (proj E hqc) (dualizingModule E hqc D n) n
  let eY : Y ≅ SheafOfModules.unit S.ringCatSheaf :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules (n : ℤ)).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor S.Modules (n : ℤ)).mapIso e.symm ≪≫ t ≪≫
      rightDerivedTopDualizingModuleIso E hqc D hn hfree
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor S.Modules _).mapIso eY⟩

end AnyModel

/-! ### Rank one -/

section RankOne

variable (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (0 + 1))

omit [E.IsQuasicoherent] in
include hfree in
/-- **The projective bundle of a module of rank one is the base**: `π : 𝐏(ℰ) ⟶ S` is an
isomorphism. Being an isomorphism is local on the base, and over an open trivializing `ℰ` the
bundle is `𝐏(𝒪) ≅ ℙ⁰ ≅` the open itself. -/
theorem isIso_proj_of_rank_one : IsIso (proj E hqc) := by
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (0 + 1)).mp hfree
  change MorphismProperty.isomorphisms Scheme (proj E hqc)
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro x
  obtain ⟨U, hxU, Φ, hΦ⟩ := Stacks.ProjectiveBundle.exists_iso_morphismRestrict_free E hqc 0 x
  refine ⟨U, hxU, ?_⟩
  rw [(Iso.eq_inv_comp Φ).mpr hΦ]
  change IsIso (Φ.inv ≫ (Stacks.SymGraded.freeProjectiveBundle (X := U.toScheme) 0).toBase)
  rw [← Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst]
  have : IsIso (projectiveSpaceOver 0 U.toScheme ↘ U.toScheme) :=
    Stacks.Duality.ProjectiveSpace.isIso_projectiveSpaceOver_zero U.toScheme
  have : IsIso (pullback.fst (terminal.from U.toScheme)
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} 0))) :=
    inferInstanceAs (IsIso (projectiveSpaceOver 0 U.toScheme ↘ U.toScheme))
  infer_instance

include hfree in
/-- For `ℰ` of rank one the tautological map `π^*ℰ ⟶ 𝒪(1)` is an isomorphism: it is an
epimorphism and its kernel, of rank zero, vanishes. -/
theorem isIso_tautologicalMap_of_rank_one :
    IsIso (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalMap E hqc D) := by
  have hK :
      IsZero (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalKernel E hqc D) :=
    (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_kernelExteriorPower_succ
      E hqc D hfree).of_iso
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.kernelAlgebras E hqc
        D).exteriorPowerOneIso.symm
  have := Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.epi_tautologicalMap E hqc D
  have : Mono (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalMap E hqc D) :=
    Preadditive.mono_of_kernel_zero (hK.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- For `ℰ` of rank one, `π^*𝓛(-1) = 𝒪(-1) ⊗ π^*ℰ ≅ 𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪`. -/
def dualizingModuleIsoUnitOfRankOne :
    dualizingModule E hqc D 0 ≅ SheafOfModules.unit (bundle E hqc).ringCatSheaf :=
  haveI := isIso_tautologicalMap_of_rank_one E hqc D hfree
  eqToIso (Stacks.ProjectionFormula.tensorRightInvertible_obj _ _ _) ≪≫
    Stacks.Tag01VSPullbackTensor.tensorSheafMapIso (Iso.refl _)
      ((Scheme.Modules.pullback (proj E hqc)).mapIso
        (eqToIso (congrArg (Scheme.Modules.exteriorPower E) (by norm_num)) ≪≫
          Scheme.Modules.exteriorPowerOneIsoSelf E) ≪≫
        asIso (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalMap E hqc D)) ≪≫
    @asIso _ _ _ _ (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistMul D
      (-((0 + 1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ))
      (Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_twistMul D
        (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc) _ _) ≪≫
    eqToIso (congrArg D.algebra.piece (by norm_num)) ≪≫
    Stacks.AlgebraicGeometry.ProjRepresentsF1.twistPieceZeroIsoUnit D
      (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc)

variable [HasDerivedCategory.{w} (bundle E hqc).Modules] [HasDerivedCategory.{w} S.Modules]

include hfree in
/-- **`R π_*(π^*𝓛(-1)[0]) ≅ 𝒪_S[0]`** for `ℰ` of rank one, at any model: `π` is an isomorphism
and `π^*𝓛(-1) ≅ 𝒪`. -/
theorem nonempty_derivedPushforward_dualizingModule_iso_of_rank_one :
    Nonempty ((derivedPushforward.{w} (proj E hqc)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dualizingModule E hqc D 0)) ≅
      (DerivedCategory.singleFunctor S.Modules ((0 : ℕ) : ℤ)).obj
        (SheafOfModules.unit S.ringCatSheaf)) := by
  have := isIso_proj_of_rank_one E hqc hfree
  exact ⟨(derivedPushforward.{w} (proj E hqc)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (dualizingModuleIsoUnitOfRankOne E hqc D hfree)) ≪≫
    Stacks.Duality.ProjectiveSpaceDualizing.derivedPushforwardSingleIsoOfIsAffineHom
      (proj E hqc) _ 0 ≪≫
    (DerivedCategory.singleFunctor S.Modules 0).mapIso
      ((Scheme.Modules.pushforward (proj E hqc)).mapIso
          (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso (proj E hqc)).symm ≪≫
        Stacks.Cohomology.SchemeIso.pushforwardPullbackIso (asIso (proj E hqc)) _)⟩

end RankOne

/-! ### All ranks -/

section AllRanks

variable {n} (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  [HasDerivedCategory.{w} (bundle E hqc).Modules] [HasDerivedCategory.{w} S.Modules]

include hfree in
/-- **`R π_*(π^*𝓛(-n-1)[0]) ≅ 𝒪_S[-n]`**, at any model, for every `n ≥ 0`. -/
theorem nonempty_derivedPushforward_dualizingModule_iso :
    Nonempty ((derivedPushforward.{w} (proj E hqc)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (dualizingModule E hqc D n)) ≅
      (DerivedCategory.singleFunctor S.Modules (n : ℤ)).obj
        (SheafOfModules.unit S.ringCatSheaf)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact nonempty_derivedPushforward_dualizingModule_iso_of_rank_one E hqc D hfree
  · exact nonempty_derivedPushforward_dualizingModule_iso_of_pos E hqc D hn hfree

end AllRanks

end Stacks.Duality.ProjectiveBundleDualizing

end
