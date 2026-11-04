module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TelescopeProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TwistDetectionKoszul
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TwistedFourierMukai
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineHomologyEdge
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# Twists of the structure sheaf detect cohomological vanishing on `ℙⁿ_A`

Let `A` be a ring and `K ∈ D_QCoh(𝒪_{ℙⁿ_A})`. If `H^i RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d)) = 0` for all
`i ≥ m` and `d = 0, …, n`, then `H^i(K) = 0` for all `i ≥ m`; in particular `𝒪, 𝒪(-1), …, 𝒪(-n)`
generate `D_QCoh(𝒪_{ℙⁿ_A})`. This is the implication (5) ⟹ (1) of the characterization of
pseudo-coherent objects on `ℙⁿ_A` by the cohomology of their twists ([Stacks, Tag 0CSG]).

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isZero_homology_of_twists`: if
  `H^i RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d)) = 0` for `i ≥ m` and `0 ≤ d ≤ n`, then `H^i(K) = 0` for `i ≥ m`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isZero_of_twists`: an object `K` of
  `D_QCoh(𝒪_{ℙⁿ_A})` with `RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d))` acyclic for `0 ≤ d ≤ n` is zero.

## Implementation notes

The proof runs through the derived direct image `Rπ_*` to the affine base rather than through
`RΓ_A`, the two having the same vanishing on `D_QCoh` over `Spec A`
(`isZero_homology_pushM_of_derivedGlobalSectionsOver`). The exactness and shift-compatibility of
`K ⊗^𝐋 -` and of `Rf_*` are seated as local instances on two abbreviations, `tensorObj` and
`pushM`, so that the composite's structure is found by instance search.

## References

* [Stacks Project, Tag 0CSG](https://stacks.math.columbia.edu/tag/0CSG)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow (ofScheme)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

/-- `K ⊗^𝐋 -` on a scheme. -/
abbrev tensorObj {X : Scheme.{u}} (K : DerivedCategory X.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).obj K

/-- `Rf_*` on schemes. -/
abbrev pushM {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  derivedPushforward f.toLRSHom.toShHom

/-- The functor `K ⊗^𝐋 -` commutes with the shift. -/
local instance {X : Scheme.{u}} (K : DerivedCategory X.Modules) : (tensorObj K).CommShift ℤ :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    X.toRingedSpace.sheaf).commShift_right K

/-- The functor `K ⊗^𝐋 -` is triangulated. -/
local instance {X : Scheme.{u}} (K : DerivedCategory X.Modules) : (tensorObj K).IsTriangulated :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    X.toRingedSpace.sheaf).exact_right K

/-- The derived pushforward `Rh_*` along a morphism of ringed spaces commutes with the shift. -/
local instance commShift_dp {X' Y' : RingedSpace.{u, u}} (h : X' ⟶ Y') :
    (derivedPushforward h).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedPushforward h) (derivedPushforwardUnit h)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ)) ℤ

/-- The derived pushforward `Rh_*` along a morphism of ringed spaces is triangulated. -/
local instance isTriangulated_dp {X' Y' : RingedSpace.{u, u}} (h : X' ⟶ Y') :
    (derivedPushforward h).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X')
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated
    (RingedSpaceModuleAdjunction.modulePushforward h) (derivedPushforward h)
    (derivedPushforwardUnit h)

/-- The derived pushforward `Rf_*` along a morphism of schemes commutes with the shift. -/
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) : (pushM f).CommShift ℤ := commShift_dp _

/-- The derived pushforward `Rf_*` along a morphism of schemes is triangulated. -/
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) : (pushM f).IsTriangulated := isTriangulated_dp _

variable {A : Type u} [CommRing A]

/-- Over an affine base, vanishing of `H^i RΓ_A(X, N)` gives vanishing of `H^i(Rf_*N)`. -/
theorem isZero_homology_pushM_of_derivedGlobalSectionsOver {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f]
    (N : DerivedCategory X.Modules)
    (hN : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj N).IsQuasicoherent) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((derivedGlobalSectionsOver f).obj N))) :
    IsZero ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      ((pushM f).obj N)) := by
  have hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules j).obj
      ((pushM f).obj N)).IsQuasicoherent := fun j =>
    AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs f N hN j
  have e := (derivedGlobalSectionsQuasicoherentCompHomologyIso (CommRingCat.of A) i).app
    ⟨(pushM f).obj N, hM⟩
  have h' : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj ((pushM f).obj N))) :=
    h.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      ((derivedGlobalSectionsOverPushforwardIso f).app N)).symm
  have := hM i
  exact isZero_of_isZero_globalSectionsOver_of_isQuasicoherent (𝟙 _) _ (h'.of_iso e.symm)

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

variable (n : ℕ)

/-- The twist `𝒪(d)` on `ℙⁿ_A`, as an object of the derived category placed in degree zero. -/
abbrev twistSingle (d : ℤ) :
    DerivedCategory (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules :=
  (DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (CommRingCat.of A)) d)

/-- The cohomology sheaves of `𝒪(d)` placed in degree zero are quasi-coherent. -/
theorem isQuasicoherent_twistSingle (d : ℤ) (j : ℤ) :
    ((DerivedCategory.homologyFunctor _ j).obj (twistSingle (A := A) n d)).IsQuasicoherent :=
  isQuasicoherent_homology_singleFunctor_obj _ _ inferInstance j

/-- If `H^i RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d)) = 0` for `i ≥ m` and `0 ≤ d ≤ n`, then
`H^i(Rπ_*(K ⊗^𝐋 𝒪(d))) = 0` for `i ≥ m` and every `d ≥ 0`. -/
theorem isZero_homology_pushM_tensor_twist
    (K : DerivedCategory (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent) (m : ℤ)
    (h : ∀ d : ℕ, d ≤ n → ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedGlobalSectionsOver (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj (twistSingle n d))))) :
    ∀ d : ℕ, ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj (twistSingle n d)))) := by
  have : IsProper (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) :=
    isProper_projectiveSpaceOver n _
  exact isZero_homology_obj_twist_of_window
    (F := tensorObj K ⋙ pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))) m
    fun d _ i hi => isZero_homology_pushM_of_derivedGlobalSectionsOver _ _
      (TorFormula.isQuasicoherent_homology_derivedTensor _ K _ hK
        (isQuasicoherent_twistSingle n _)) i (h d ‹_› i hi)

/-- If `H^i(Rπ_*(K ⊗ 𝒪(d))) = 0` for `i ≥ m` and every `d ≥ 0`, then the same holds with `𝒪(d)`
replaced by `j_*𝒪` of a standard chart, the colimit of `𝒪 → 𝒪(1) → ⋯`. -/
theorem isZero_homology_pushM_tensor_coconePt
    (K : DerivedCategory (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent) (m : ℤ)
    (hB : ∀ d : ℕ, ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj (twistSingle n d)))))
    (j : Fin (n + 1)) :
    ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj
          (coconeP n (Spec (CommRingCat.of A)) j).pt)))) := by
  have : IsProper (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) :=
    isProper_projectiveSpaceOver n _
  let M' : ULift.{u} ℕ → (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules :=
    fun k => (seqP n (Spec (CommRingCat.of A)) j).obj k.down
  let eM : ∀ k : ULift.{u} ℕ, (tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k)) ≅
      (tensorObj K).obj (twistSingle n (k.down : ℤ)) := fun k =>
    (tensorObj K).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (seqPObjIso n (Spec (CommRingCat.of A)) j k.down))
  have hM' : ∀ k, ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k))))) :=
    fun k i hi => (hB k.down i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).mapIso (eM k)))
  have hqc : ∀ k (i : ℤ), ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules i).obj
      ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k)))).IsQuasicoherent :=
    fun k i => (SheafOfModules.isQuasicoherent
      (projectiveSpaceOver n (Spec (CommRingCat.of A))).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules
        i).mapIso (eM k).symm)
      (TorFormula.isQuasicoherent_homology_derivedTensor
        (projectiveSpaceOver n (Spec (CommRingCat.of A))) K _ hK
        (isQuasicoherent_twistSingle n _) i)
  have h1 : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ))
      (DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules 0) :=
    Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_singleFunctor 0 _
  have h2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) (tensorObj K) :=
    Stacks.Cohomology.ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_derivedTensor_obj
      (projectiveSpaceOver n (Spec (CommRingCat.of A))).toRingedSpace _ K
  have h3 : IsIso (sigmaComparison (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)))
      (fun k => (tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k)))) :=
    Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent
      (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)) _ hqc
  have h3' := PreservesCoproduct.of_iso_comparison
      (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)))
      (fun k => (tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k)))
  let e0 : ∐ (seqP n (Spec (CommRingCat.of A)) j).obj ≅ ∐ M' :=
    Sigma.whiskerEquiv (f := (seqP n (Spec (CommRingCat.of A)) j).obj) (g := M')
      Equiv.ulift.symm fun _ => Iso.refl _
  let e : (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
      ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj
      (∐ (seqP n (Spec (CommRingCat.of A)) j).obj))) ≅
      ∐ fun k => (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj (M' k))) :=
    (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).mapIso
      ((tensorObj K).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e0 ≪≫
        PreservesCoproduct.iso
          (DerivedCategory.singleFunctor
            (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules 0)
          M') ≪≫
      PreservesCoproduct.iso (tensorObj K) _) ≪≫
        PreservesCoproduct.iso (pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))) _
  have hX : ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj
        (∐ (seqP n (Spec (CommRingCat.of A)) j).obj))))) := fun i hi =>
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj _ _ i fun k => hM' k i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have hT := (shortExact_telescopeP n (Spec (CommRingCat.of A)) j).singleTriangle_distinguished
  have hd := (tensorObj K ⋙
    pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).map_distinguished _ hT
  intro i hi
  exact (DerivedCategory.HomologySequence.exact₃ _ hd i (i + 1) rfl).isZero_of_both_zeros
    ((hX i hi).eq_of_src _ _) ((hX (i + 1) (by omega)).eq_of_tgt _ _)

/-- The composite of a standard chart `U ⟶ ℙⁿ_A` with the structure morphism to `Spec A` is
affine. -/
instance isAffineHom_chartP_ι (j : Fin (n + 1)) :
    IsAffineHom ((chartP n (Spec (CommRingCat.of A)) j).ι ≫
      (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))) :=
  Stacks.ChartDictionary.isAffineHom_standardChart_over n _ j

/-- The inclusion of a standard chart `U ⟶ ℙⁿ_A` is affine. -/
instance isAffineHom_chartP_ι' (j : Fin (n + 1)) :
    IsAffineHom (chartP n (Spec (CommRingCat.of A)) j).ι :=
  have : IsProper (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)) :=
    isProper_projectiveSpaceOver n _
  IsAffineHom.of_comp (f := (chartP n (Spec (CommRingCat.of A)) j).ι)
    (g := projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))

/-- Vanishing for `j_*𝒪` of a chart is vanishing of the cohomology of the restriction of
`K` to the chart: `K ⊗ j_*𝒪 ≅ Rj_*(j^*K)` and `Rπ_* ∘ Rj_* = R(π ∘ j)_*` with `π ∘ j` affine. -/
theorem isZero_homology_derivedPullback_chart
    (K : DerivedCategory (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent) (j : Fin (n + 1))
    (i : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        ((tensorObj K).obj ((DerivedCategory.singleFunctor _ 0).obj
          (coconeP n (Spec (CommRingCat.of A)) j).pt))))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback (ofScheme (chartP n (Spec (CommRingCat.of A)) j).ι)).obj K)) := by
  have hcoh : ∀ i', ((DerivedCategory.homologyFunctor _ i').obj
      ((derivedPullback (ofScheme (chartP n (Spec (CommRingCat.of A)) j).ι)).obj
        K)).IsQuasicoherent :=
    fun i' => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ K hK i'
  refine
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff
      ((chartP n (Spec (CommRingCat.of A)) j).ι ≫
        (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))) _ hcoh i).1 ?_
  let U := chartP n (Spec (CommRingCat.of A)) j
  have : (SheafOfModules.unit U.toScheme.ringCatSheaf).IsQuasicoherent := inferInstance
  let e1 : (DerivedCategory.singleFunctor
      (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules 0).obj
      (coconeP n (Spec (CommRingCat.of A)) j).pt ≅
      (derivedPushforward (ofScheme U.ι)).obj (DerivedChow.structureSheafSingle U.toScheme) :=
    (DerivedCategory.singleFunctor _ 0).mapIso (coconePPtIso n (Spec (CommRingCat.of A)) j) ≪≫
      (derivedPushforwardSingleIsoOfIsAffineHom U.ι
        (SheafOfModules.unit U.toScheme.ringCatSheaf)).symm
  let e2 : (tensorObj K).obj ((derivedPushforward (ofScheme U.ι)).obj
      (DerivedChow.structureSheafSingle U.toScheme)) ≅
      (derivedPushforward (ofScheme U.ι)).obj ((derivedPullback (ofScheme U.ι)).obj K) :=
    derivedProjectionFormulaUnitRightIso U.ι K hK
  let e3 := (derivedPushforwardCompIso (ofScheme U.ι)
      (ofScheme (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A)))).app
    ((derivedPullback (ofScheme U.ι)).obj K)
  exact h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((pushM (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).mapIso
      ((tensorObj K).mapIso e1 ≪≫ e2) ≪≫ e3)).symm

/-- A cohomology sheaf of `K` whose restriction to every standard chart vanishes is zero. -/
theorem isZero_homology_of_derivedPullback_chart
    (K : DerivedCategory (projectiveSpaceOver n (Spec (CommRingCat.of A))).Modules) (i : ℤ)
    (h : ∀ j : Fin (n + 1), IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback (ofScheme (chartP n (Spec (CommRingCat.of A)) j).ι)).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  have hcov : TopologicalSpace.IsOpenCover (chartP n (Spec (CommRingCat.of A))) :=
    TopologicalSpace.IsOpenCover.mk (projectiveSpaceOver.iSup_standardChart n _)
  have hiso : IsIso (0 : (DerivedCategory.homologyFunctor _ i).obj K ⟶
      (DerivedCategory.homologyFunctor _ i).obj K) := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ _ hcov fun j => ?_
    let ι := (chartP n (Spec (CommRingCat.of A)) j).ι
    have hz : IsZero ((Scheme.Modules.restrictFunctor ι).obj
        ((DerivedCategory.homologyFunctor _ i).obj K)) :=
      (h j).of_iso (((Scheme.Modules.restrictFunctorIsoPullback ι).app _) ≪≫
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (Scheme.Modules.pullback ι) i).app K).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso
          ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
            (ofScheme ι)).app K).symm)
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz, hz⟩
  exact ((isIsoZero_iff_source_target_isZero _ _).1 hiso).1

/-- **Detection of cohomological vanishing by the twists `𝒪, 𝒪(1), …, 𝒪(n)`.** Let `A` be a ring
and let `K` be an object of `D_QCoh(𝒪_{ℙⁿ_A})`. If `H^i RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d)) = 0` for every
`i ≥ m` and every `0 ≤ d ≤ n`, then the cohomology sheaves `H^i(K)` vanish for every `i ≥ m`.

The Koszul complex propagates the vanishing to every twist `𝒪(d)`, `d ≥ 0`
(`AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isZero_homology_obj_twist_of_window`); over the
affine base it is vanishing of `H^i(Rπ_*(K ⊗^𝐋 𝒪(d)))`. On a standard chart `j : U ⟶ ℙⁿ_A` the
sheaf `j_*𝒪_U` is the colimit of `𝒪 → 𝒪(1) → ⋯`, presented by the telescope short exact
sequence `0 → ⨁ 𝒪(d) → ⨁ 𝒪(d) → j_*𝒪_U → 0`; derived tensor product, `Rπ_*` ([Stacks, Tag 08DZ])
and cohomology commute with the direct sums, so `H^i(Rπ_*(K ⊗^𝐋 j_*𝒪_U)) = 0` for `i ≥ m`. By the
projection formula ([Stacks, Tag 08EU]) this is `H^i(R(π ∘ j)_*(K|_U))`, and `π ∘ j` is affine,
so `H^i(K)|_U = 0`. The charts cover `ℙⁿ_A`. -/
theorem isZero_homology_of_twists
    (K : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent) (m : ℤ)
    (h : ∀ d : ℕ, d ≤ n → ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedGlobalSectionsOver (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _).obj K).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) d)))))) :
    ∀ i, m ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := fun i hi =>
  isZero_homology_of_derivedPullback_chart n K i fun j =>
    isZero_homology_derivedPullback_chart n K hK j i
      (isZero_homology_pushM_tensor_coconePt n K hK m
        (isZero_homology_pushM_tensor_twist n K hK m h) j i hi)

/-- **The twists `𝒪, 𝒪(-1), …, 𝒪(-n)` generate `D_QCoh(𝒪_{ℙⁿ_A})`**, in the form: an object `K`
of `D_QCoh(𝒪_{ℙⁿ_A})` with `RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d))` acyclic for `0 ≤ d ≤ n` is zero. -/
theorem isZero_of_twists
    (K : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (h : ∀ d : ℕ, d ≤ n → ∀ i, IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedGlobalSectionsOver (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _).obj K).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) d)))))) :
    IsZero K := by
  have hz : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := fun i =>
    isZero_homology_of_twists n K hK i (fun d hd i' _ => h d hd i') i le_rfl
  have hiso : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    rw [(hz i).eq_of_src ((DerivedCategory.homologyFunctor _ i).map (0 : K ⟶ K)) (𝟙 _)]
    infer_instance
  exact ((isIsoZero_iff_source_target_isZero _ _).1 hiso).1

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence

end
