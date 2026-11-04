module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DirectImageInDerivedCategory
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundednessGenerator
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedBelowGeneratorPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsTensorPseudoCoherence
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The derived fibres of an object with perfect twisted global sections

Let `A` be a ring, `f : X ⟶ Spec A` flat, quasi-compact and quasi-separated, `G` a perfect
generator of `D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_X)` such that `RΓ(X, K ⊗^L G^∨)` is a perfect object
of `D(A)`. For a point `s` of `Spec A` with fibre `i : X_s ⟶ X`, the proof of Stacks 0GET shows
that `Li^*K` is bounded below, through the identification
`RHom(Li^*G, Li^*K) = RΓ(X, G^∨ ⊗^L K) ⊗^L_A κ(s)`. This module carries that step out.

The identification is reached here without a general base-change theorem (Stacks 08IB): with
`g : Spec κ(s) ⟶ Spec A`, the object `Ri_*Li^*K` is `K ⊗^L Lf^*(g_*𝒪)` by the projection formula
along the affine morphism `i` (Stacks 08EU) and flat base change of the structure sheaf
(Stacks 02KH in degree zero); the cohomology of `RΓ(X, K ⊗^L Lf^*(g_*𝒪) ⊗^L G^∨)` is that of
`RΓ(Spec A, Rf_*(K ⊗^L G^∨) ⊗^L g_*𝒪)`, by the projection formula along `f`, and
`Rf_*(K ⊗^L G^∨)` is the perfect object `RΓ(X, K ⊗^L G^∨)^~` (Stacks 08D5, 06Z0, 08EB), of
finite Tor dimension (Stacks 08CQ), so that cohomology is bounded below. Stacks 0GEQ on `X` then
bounds `Ri_*Li^*K` below, and the derived direct image along the affine `i` detects the
cohomology of `Li^*K`.

## Main results

* `AlgebraicGeometry.derivedPushforwardUnitIso`: `Ri_*𝒪_Y ≅ Lf^*(g_*𝒪_{S'})` for a cartesian
  square with `f` flat and `g`, `i` affine.
* `AlgebraicGeometry.derivedPushforwardPullbackIsoTensor`: `Ri_*Li^*K ≅ K ⊗^L Lf^*(g_*𝒪_{S'})`
  for `K ∈ D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.exists_isZero_homology_derivedGlobalSectionsOver_tensor_pullback`: for
  `RΓ(X, W)` perfect, `H^n(X, W ⊗^L Lf^*F) = 0` for `n ≪ 0` and `F` quasi-coherent on `Spec A`.
* `AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_fibre_of_isPerfect`: the derived
  fibres of `K` are locally bounded below.

## Implementation notes

Two derived tensor products of `D(𝒪_X)` occur: the one of the projection formula,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, and
`Stacks.SheafOfModules.derivedTensor`, in which the perfect-generator criteria and the hypothesis
of Stacks 0GET are stated. Both descend the total tensor complex of K-flat complexes, and
`AlgebraicGeometry.derivedTensorSpellingIso` identifies them. Everything is read at the standard
model of the derived categories.

## References

* [Stacks Project, Tag 0GET](https://stacks.math.columbia.edu/tag/0GET)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0GEQ](https://stacks.math.columbia.edu/tag/0GEQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard
/-- Derived global sections over an affine base are left t-exact. -/
theorem isZero_homology_derivedGlobalSectionsOver_id_of_lt {R : CommRingCat.{u}}
    (L : DerivedCategory (Spec R).Modules) (a : ℤ)
    (h : ∀ n < a, IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj L)) :
    ∀ n < a, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L)) := by
  have : L.IsGE a := (DerivedCategory.isGE_iff L a).2 h
  have : ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj L).IsGE a :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (globalSectionsOver (𝟙 (Spec R))) L a
  exact fun n hn => DerivedCategory.isZero_of_isGE _ a n hn

attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
  Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- The two spellings of the pullback of sheaves of modules along a morphism of schemes. -/
def modulePullbackIsoSchemePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback f.toLRSHom.toShHom ≅ Scheme.Modules.pullback f :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)


section UnitBaseChange

variable {X Y S S' : Scheme.{u}} {i : Y ⟶ X} {h : Y ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The structure sheaf of the target of a pullback square, pushed forward from the top-left
corner, as the flat pullback of the pushforward of the structure sheaf: `i_*𝒪_Y ≅ f^*g_*𝒪_{S'}`
for a cartesian square with `f` flat and `g` quasi-compact and quasi-separated. -/
def pushforwardUnitIsoPullbackPushforwardUnit (H : IsPullback i h f g) [Flat f]
    [QuasiCompact g] [QuasiSeparated g] :
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf)) :=
  haveI := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    H.flip (SheafOfModules.unit S'.ringCatSheaf)
  (Scheme.Modules.pushforward i).mapIso
      (((modulePullbackIsoSchemePullback h).app _).symm ≪≫
        modulePullbackObjUnitIso h.toLRSHom.toShHom).symm ≪≫
    (asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.flip.w).app
      (SheafOfModules.unit S'.ringCatSheaf))).symm

/-- **Derived flat base change of the structure sheaf along an affine morphism**: for a cartesian
square with `f` flat and `g` affine, `Ri_*𝒪_Y ≅ Lf^*(g_*𝒪_{S'})` in `D(𝒪_X)`. -/
def derivedPushforwardUnitIso (H : IsPullback i h f g) [Flat f] [IsAffineHom g]
    [IsAffineHom i] :
    (derivedPushforward i.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
          (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
          ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf))) :=
  letI : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteLimits_modulePullback_of_isFlat _
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom f)
  letI : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  (Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardSingleIso i
      (SheafOfModules.unit Y.ringCatSheaf)).symm ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).mapIso
      (pushforwardUnitIsoPullbackPushforwardUnit H ≪≫
        ((modulePullbackIsoSchemePullback f).app _).symm) ≪≫
    (((modulePullback f.toLRSHom.toShHom).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
    ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory
      f.toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom f)).app _).symm

end UnitBaseChange


/-- The two derived tensor products of `D(𝒪_X)`: the chosen one of Stacks 06YU on the ringed site
of opens, in which the projection formula is stated, and the one of
`Stacks.SheafOfModules.derivedTensor`, in which the perfect-generator criteria are stated. Both
descend the total tensor complex of K-flat complexes. -/
def derivedTensorSpellingIso (X : Scheme.{u}) :
    Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf ≅
      Stacks.SheafOfModules.derivedTensor X.sheaf :=
  (Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.sheaf
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf)).symm ≪≫
    Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.sheaf
      (Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf)


section PushPull

variable {X Y S S' : Scheme.{u}} {i : Y ⟶ X} {h : Y ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- **`Ri_*Li^*K ≅ K ⊗^L Lf^*(g_*𝒪_{S'})`** for a cartesian square with `f` flat and `g` affine
and `K` in `D_QCoh(𝒪_X)`: the projection formula of Stacks 08EU along `i` at the structure
sheaf, followed by the derived flat base change of the structure sheaf. -/
def derivedPushforwardPullbackIsoTensor (H : IsPullback i h f g) [Flat f] [IsAffineHom g]
    [IsAffineHom i] (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (derivedPushforward i.toLRSHom.toShHom).obj ((derivedPullback i.toLRSHom.toShHom).obj K) ≅
      ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj K).obj
        ((derivedPullback f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} S.ringCatSheaf) 0).obj
            ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit S'.ringCatSheaf)))) :=
  let U : DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
    (DerivedCategory.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  let L := (derivedPullback i.toLRSHom.toShHom).obj K
  haveI : IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      i.toLRSHom.toShHom U K) :=
    Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh i U K
      (fun n => Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj Y _
        inferInstance n) hK
  (derivedPushforward i.toLRSHom.toShHom).mapIso
      ((@MonoidalCategoryStruct.leftUnitor
        (DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Y.sheaf)) _
        (Stacks.SheafOfModules.derivedMonoidalStructure Y.sheaf).toMonoidalCategoryStruct L).symm ≪≫
        (((derivedTensorSpellingIso Y).app U).app L).symm) ≪≫
    (asIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      i.toLRSHom.toShHom U K)).symm ≪≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).mapIso
      (derivedPushforwardUnitIso H)).app K ≪≫
    ((derivedTensorSpellingIso X).app _).app K ≪≫
    (@BraidedCategory.braiding
      (DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)) _
      (Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf)
      (Stacks.SheafOfModules.derivedSymmetricStructure X.sheaf).toBraidedCategory _ K)

end PushPull


section Base

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- **The cohomology of `W ⊗^L Lf^*F` over an affine base is bounded below** when the derived
global sections of `W` are perfect: for `f : X ⟶ Spec A` quasi-compact and quasi-separated,
`W ∈ D_QCoh(𝒪_X)` with `RΓ(X, W)` perfect in `D(A)`, and `F` a quasi-coherent module on
`Spec A`, the groups `H^n(X, W ⊗^L Lf^*F)` vanish for `n ≪ 0`.

By the projection formula (Stacks 08EU) and the Leray identification `RΓ(X, -) = RΓ(Spec A, Rf_*-)`
these are the cohomology groups of `RΓ(Spec A, Rf_*W ⊗^L F)`; the object `Rf_*W` lies in
`D_QCoh(𝒪_{Spec A})` (Stacks 08D5), so it is `M̃` for `M = RΓ(Spec A, Rf_*W) = RΓ(X, W)` perfect,
hence perfect (Stacks 08EB) and of finite Tor dimension (Stacks 08CQ), which bounds
`Rf_*W ⊗^L F` below. -/
theorem exists_isZero_homology_derivedGlobalSectionsOver_tensor_pullback
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f]
    (W : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hW : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj W).IsQuasicoherent)
    (hP : StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj W))
    (F : (Spec (CommRingCat.of A)).Modules) (hF : F.IsQuasicoherent) :
    ∃ a : ℤ, ∀ n < a, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedGlobalSectionsOver f).obj
        (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj W).obj
          ((derivedPullback f.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Spec (CommRingCat.of A)).ringCatSheaf) 0).obj F))))) := by
  let Q := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Spec (CommRingCat.of A)).ringCatSheaf) 0).obj F
  let T := (derivedPushforward f.toLRSHom.toShHom).obj W
  have hT : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of A)).Modules n).obj T).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward f ⟨W, hW⟩
  obtain ⟨M0, ⟨e0⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) T hT
  have hu := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of A)
  have eM : M0 ≅ (derivedGlobalSectionsOver f).obj W :=
    asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.unit.app M0) ≪≫
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
        ((derivedTildeCompι (CommRingCat.of A)).app M0 ≪≫ e0) ≪≫
      ((derivedGlobalSectionsOverPushforwardIso f).app W).symm
  have hM0 : StacksDraft.Perfect.IsPerfect M0 := StacksDraft.Perfect.isPerfect_of_iso eM hP
  have hpt := (isPerfect_tilde_iff M0).2 hM0
  have htor :=
    (Stacks.Cohomology.TorAmplitude.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
      (X := (Spec (CommRingCat.of A)).toRingedSpace) _).1 hpt
  obtain ⟨a, b, hab⟩ :=
    (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
      (X := (Spec (CommRingCat.of A)).toRingedSpace) _).1 htor.2
  have hGE' := isZero_homology_derivedGlobalSectionsOver_id_of_lt
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Spec (CommRingCat.of A)).sheaf).obj T).obj Q) a (fun n hn =>
    (hab F n (by simp only [Set.mem_Icc]; omega)).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (Spec (CommRingCat.of A)).sheaf).mapIso e0).app Q).symm))
  have : IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      f.toLRSHom.toShHom W Q) :=
    Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f W Q hW
      (fun n => Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj _ F hF n)
  let e : (derivedGlobalSectionsOver f).obj
        (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj W).obj
          ((derivedPullback f.toLRSHom.toShHom).obj Q)) ≅
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (Spec (CommRingCat.of A)).sheaf).obj T).obj Q) :=
    (derivedGlobalSectionsOver f).mapIso
        (((derivedTensorSpellingIso X).app W).app _).symm ≪≫
      (derivedGlobalSectionsOverPushforwardIso f).app _ ≪≫
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
        (asIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
          f.toLRSHom.toShHom W Q)).symm
  exact ⟨a, fun n hn => (hGE' n hn).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)⟩


/-- If `H^n(X, W)` vanishes for `n < a` and `N ≅ W`, then the abelian-group cohomology of the
derived global sections of `N` vanishes in all sufficiently negative degrees. -/
theorem exists_isZero_homology_derivedModuleGlobalSections_of_iso
    (f : X ⟶ Spec (CommRingCat.of A))
    {N W : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)} (e : N ≅ W)
    (a : ℤ) (ha : ∀ n < a, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedGlobalSectionsOver f).obj W))) :
    ∃ b : ℤ, ∀ n ≤ b, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj N)) := by
  refine ⟨a - 1, fun n hn => ?_⟩
  refine ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
    n).app ((derivedGlobalSectionsOver f).obj W)).isZero_iff.2
      (Functor.map_isZero (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
        (ha n (by omega)))).of_iso ?_
  exact (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
    (((Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso
      f).app _).symm ≪≫
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.mapIso
        ((derivedGlobalSectionsOver f).mapIso e))

open Stacks.SheafOfModules in
/-- **The derived fibres of an object with perfect twisted global sections are bounded below.**
Let `f : X ⟶ Spec A` be flat, quasi-compact and quasi-separated, let `G` be a perfect generator
of `D_QCoh(𝒪_X)`, and let `K ∈ D_QCoh(𝒪_X)` with `RΓ(X, K ⊗^L G^∨)` perfect in `D(A)`. Then
for every point `s` of `Spec A` the derived pullback of `K` to the fibre `X_s` is locally
bounded below.

This is the fibre step of the proof of Stacks 0GET. With `i : X_s ⟶ X` and
`g : Spec κ(s) ⟶ Spec A`, `Ri_*Li^*K ≅ K ⊗^L Lf^*(g_*𝒪)` (Stacks 08EU along the affine `i`,
and flat base change of the structure sheaf), and the cohomology of
`RΓ(X, (K ⊗^L Lf^*(g_*𝒪)) ⊗^L G^∨)` is bounded below because `RΓ(X, K ⊗^L G^∨)` is perfect
(Stacks 08EU along `f`, 08D5, 08EB, 08CQ). By Stacks 0GEQ on `X` the object
`K ⊗^L Lf^*(g_*𝒪) ≅ Ri_*Li^*K` is bounded below, and `Ri_*` along the affine `i` detects the
cohomology of `Li^*K`. -/
theorem isLocallyBoundedBelow_derivedPullback_fibre_of_isPerfect
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hperf : StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj
      (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf G))))
    (s : Spec (CommRingCat.of A)) :
    RingedSpace.IsLocallyBoundedBelow
      (Limits.pullback f ((Spec (CommRingCat.of A)).fromSpecResidueField s)).toRingedSpace
      ((derivedPullback
        (Limits.pullback.fst f
          ((Spec (CommRingCat.of A)).fromSpecResidueField s)).toLRSHom.toShHom).obj
          K) := by
  have hqc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hqs : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let g := (Spec (CommRingCat.of A)).fromSpecResidueField s
  let i := Limits.pullback.fst f g
  have H : IsPullback i (Limits.pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : IsAffineHom i :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  let F := (Scheme.Modules.pushforward g).obj (SheafOfModules.unit
    (Spec ((Spec (CommRingCat.of A)).residueField s)).ringCatSheaf)
  have hF : F.IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward g _ inferInstance
  let P : DerivedCategory (StructureSheafModules X.sheaf) :=
    (derivedPullback f.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Spec (CommRingCat.of A)).ringCatSheaf) 0).obj F)
  let D := derivedDual X.sheaf G
  let M : DerivedCategory (StructureSheafModules X.sheaf) := ((derivedTensor X.sheaf).obj K).obj P
  let W : DerivedCategory (StructureSheafModules X.sheaf) := ((derivedTensor X.sheaf).obj K).obj D
  let L := (derivedPullback i.toLRSHom.toShHom).obj K
  have hL : ∀ n : ℤ, ((DerivedCategory.homologyFunctor _ n).obj L).IsQuasicoherent :=
    fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ K hK n
  have e1 : (derivedPushforward i.toLRSHom.toShHom).obj L ≅ M :=
    derivedPushforwardPullbackIsoTensor H K hK
  have hM : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) n).obj M).IsQuasicoherent := fun n =>
    ObjectProperty.prop_of_iso
      (P := fun N : SheafOfModules.{u} X.ringCatSheaf => N.IsQuasicoherent)
      ((Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso
        i L hL n).symm ≪≫ (DerivedCategory.homologyFunctor _ n).mapIso e1)
      (ProperCoherentFiniteType.isQuasicoherent_pushforward i _ (hL n))
  have hW : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) n).obj W).IsQuasicoherent :=
    isQuasicoherent_homology_derivedTensor_obj_obj X K D hK
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X D
        (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace D
          (isPerfect_derivedDual X.sheaf G hG)))
  obtain ⟨a, ha⟩ := exists_isZero_homology_derivedGlobalSectionsOver_tensor_pullback f W hW
    hperf F hF
  let := derivedMonoidalStructure X.sheaf
  let := derivedSymmetricStructure X.sheaf
  let eMW : ((derivedTensor X.sheaf).obj M).obj D ≅ ((derivedTensor X.sheaf).obj W).obj P :=
    MonoidalCategory.associator K P D ≪≫
      MonoidalCategory.whiskerLeftIso K (BraidedCategory.braiding P D) ≪≫
      (MonoidalCategory.associator K D P).symm
  obtain ⟨d, hd⟩ := plus_of_eventually_subsingleton_shiftedHom hqc hqs G M hG hgen hM
    ((eventually_subsingleton_shiftedHom_iff_ext hqc hqs G M hG hgen hM).2
      ((eventually_subsingleton_ext_iff_isZero_homology_atBot hqc hqs G M hG hgen hM).2
        (exists_isZero_homology_derivedModuleGlobalSections_of_iso f eMW a ha)))
  refine fun _ => ⟨⊤, trivial, d, fun n hn => Functor.map_isZero _ ?_⟩
  open Stacks.AlgebraicGeometry.AffinePushforwardTExactness in
  exact isZero_homology_of_isZero_homology_derivedPushforward i L hL
    (((DerivedCategory.homologyFunctor _ n).mapIso e1).isZero_iff.2 (M.isZero_of_isGE d n hn))

end Base

end AlgebraicGeometry

end
