module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnitIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceTransportOfUniv
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModuleComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.JointlySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# `ι` preserves and reflects quasi-coherence

Let `X` be an algebraic space over a scheme `S` and
`ι : Mod(X_étale, 𝒪_X) ⥤ Mod(X_{spaces,étale}, 𝒪)` the transport of
`AlgebraicGeometry.Space.toSpacesEtaleModules`: the universe lift followed by the module form of
Stacks 03G1. An `𝒪_X`-module `𝓕` is quasi-coherent exactly when `ι𝓕` is.

## Main results

* `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_of_isEquivalence`: a global
  presentation is carried along an equivalence of module categories matching the structure
  sheaves.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_liftModule`: the universe lift of a
  quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.Space.hasGlobalPresentation_toSpacesEtaleModules_over_iff`: `ι𝓕` is
  presented over the image of an étale chart `A` exactly when the lift of `𝓕` is presented
  over `A`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_toSpacesEtaleModules` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_toSpacesEtaleModules`: **`ι` preserves and
  reflects quasi-coherence.**

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.SheafOfModules.SiteTransport

universe a b a' b' n

/-- A global presentation is carried along an equivalence of categories of sheaves of modules
that matches the structure sheaves. -/
theorem hasGlobalPresentation_of_isEquivalence
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max a a' b b' n}}
    {C' : Type a'} [Category.{b'} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{max a a' b b' n}}
    (F : SheafOfModules.{max a a' b b' n} R ⥤ SheafOfModules.{max a a' b b' n} R')
    [F.IsEquivalence] (η : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit R')
    (M : SheafOfModules.{max a a' b b' n} R) (h : M.HasGlobalPresentation) :
    (F.obj M).HasGlobalPresentation :=
  hasGlobalPresentation_map_ofUniv.{a, b, a', b', max a a' b b' n,
      max a a' b b' n} M (F₀ := F) (F := F)
    (F.mapIso (SheafOfModules.uliftForPresentationSelfIso' _) ≪≫ η ≪≫
      (SheafOfModules.uliftForPresentationSelfIso' _).symm)
    (F.mapIso (SheafOfModules.uliftForPresentationSelfIso' _) ≪≫
      (SheafOfModules.uliftForPresentationSelfIso' _).symm) h

end Stacks.SheafOfModules.SiteTransport

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The universe lift of a quasi-coherent `𝒪_X`-module is quasi-coherent**, over the universe
lift of the structure sheaf of `X_étale`. -/
theorem isQuasicoherentOnSite_liftModule (M : Modules.{u, u} B S hS X.1 X.2)
    [hM : M.IsQuasicoherentOnSite] :
    (Stacks.SheafOfModules.CoherentLift.liftModule.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) M).IsQuasicoherentOnSite := by
  have h : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1)
      (structureRingPresheaf (smallEtaleRingedSite B S hS X.1 X.2).O.obj) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
  have hset : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1)
      (structureRingPresheaf (smallEtaleRingedSite B S hS X.1 X.2).O.obj ⋙ forget RingCat.{u}) :=
    isSheaf_structureRingPresheaf_forget B S hS X.1 X.2
  have h1 : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M) :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hM
  exact @Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftUp.{u + 1, u, u, 0} _ _ _
    (smallEtaleRingedSite B S hS X.1 X.2).O.obj h hset
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M) h1

/-- The universe lift of the structure sheaf of `X_étale`, read on the small étale site. -/
abbrev liftedEtaleRingSheaf : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (Stacks.SheafOfModules.CoherentLift.liftRingedSite.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2)).O)

/-- The universe lift of an `𝒪_X`-module, read on the small étale site. -/
abbrev liftedEtaleModule (F : Modules.{u, u} B S hS X.1 X.2) :
    SheafOfModules.{u + 1} (liftedEtaleRingSheaf B S hS X) :=
  Stacks.SheafOfModules.CoherentLift.liftModule.{u + 1, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2) F

/-- The comparison of structure sheaves of Stacks 03G1, restricted to an étale chart `A`. -/
noncomputable def comparisonRingIsoOver (A : SmallEtale B S hS X.1) :
    (liftedEtaleRingSheaf B S hS X).over A ≅
      ((Over.post (X := A) (comparisonFunctor B S hS X)).sheafPushforwardContinuous
        RingCat.{u + 1} ((SmallEtale.topology B S hS X.1).over A)
        ((SpacesEtale.topology B S hS X).over ((comparisonFunctor B S hS X).obj A))).obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over
        ((comparisonFunctor B S hS X).obj A)) :=
  ((Over.forget A).sheafPushforwardContinuous RingCat.{u + 1}
    ((SmallEtale.topology B S hS X.1).over A) (SmallEtale.topology B S hS X.1)).mapIso
    (comparisonRingIso B S hS X)

/-- **The module form of Stacks 03G1 localized at an étale chart `A`**: restriction to the scheme
charts over `A`, followed by restriction of scalars along the comparison of structure sheaves. -/
noncomputable def comparisonModuleEquivalenceOver (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over
          ((comparisonFunctor B S hS X).obj A)) ≌
      SheafOfModules.{u + 1} ((liftedEtaleRingSheaf B S hS X).over A) :=
  haveI := Stacks.Sites.overPost_isDenseSubsite (J := SmallEtale.topology B S hS X.1)
    (K := SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X) A
  (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence
      ((SmallEtale.topology B S hS X.1).over A)
      ((SpacesEtale.topology B S hS X).over ((comparisonFunctor B S hS X).obj A))
      (Over.post (X := A) (comparisonFunctor B S hS X))
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over
        ((comparisonFunctor B S hS X).obj A))).trans
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (comparisonRingIsoOver B S hS X A).symm)

/-- The localized module form of Stacks 03G1 carries the structure sheaf to the structure sheaf. -/
noncomputable def comparisonModuleEquivalenceOverUnitIso (A : SmallEtale B S hS X.1) :
    (comparisonModuleEquivalenceOver B S hS X A).functor.obj (SheafOfModules.unit _) ≅
      SheafOfModules.unit _ :=
  Stacks.Sheaves.RingedPoint.restrictScalarsUnitIsoOfIso (comparisonRingIsoOver B S hS X A)

/-- The localized module form of Stacks 03G1 carries `ι𝓕` restricted to the image of an étale
chart `A` to the universe lift of `𝓕` restricted to `A`. -/
noncomputable def comparisonModuleEquivalenceOverToSpacesEtaleModulesIso
    (F : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) :
    (comparisonModuleEquivalenceOver B S hS X A).functor.obj
        (((toSpacesEtaleModules B S hS X).obj F).over ((comparisonFunctor B S hS X).obj A)) ≅
      (liftedEtaleModule B S hS X F).over A :=
  Iso.refl _ ≪≫ (SheafOfModules.overFunctor _ A).mapIso
    (((toSpacesEtaleModulesRestrictionIso B S hS X).app F :
      (comparisonModuleEquivalence B S hS X).functor.obj ((toSpacesEtaleModules B S hS X).obj F) ≅
        liftedEtaleModule B S hS X F))

/-- `ι𝓕` has a global presentation over the image of an étale chart `A` exactly when the universe
lift of `𝓕` has one over `A`. -/
theorem hasGlobalPresentation_toSpacesEtaleModules_over_iff (F : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (((toSpacesEtaleModules B S hS X).obj F).over
      ((comparisonFunctor B S hS X).obj A)).HasGlobalPresentation ↔
      ((liftedEtaleModule B S hS X F).over A).HasGlobalPresentation := by
  let E := comparisonModuleEquivalenceOver B S hS X A
  let e₁ := comparisonModuleEquivalenceOverToSpacesEtaleModulesIso B S hS X F A
  let η : E.inverse.obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
    E.inverse.mapIso (comparisonModuleEquivalenceOverUnitIso B S hS X A).symm ≪≫
      (E.unitIso.app (SheafOfModules.unit _)).symm
  exact ⟨fun h ↦ SheafOfModules.HasGlobalPresentation.of_iso e₁
      (SiteTransport.hasGlobalPresentation_of_isEquivalence.{u + 1, u + 1, u + 1, u, u + 1}
        E.functor (comparisonModuleEquivalenceOverUnitIso B S hS X A) _ h),
    fun h ↦ SheafOfModules.HasGlobalPresentation.of_iso
      ((E.unitIso.app _) ≪≫ E.inverse.mapIso e₁).symm
      (SiteTransport.hasGlobalPresentation_of_isEquivalence.{u + 1, u, u + 1, u + 1, u + 1}
        E.inverse η _ h)⟩

/-- **`ι` preserves quasi-coherence**: the transport `ι𝓕` to the spaces-étale site of a
quasi-coherent `𝒪_X`-module `𝓕` is quasi-coherent. -/
theorem isQuasicoherentOnSite_toSpacesEtaleModules (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    ((toSpacesEtaleModules B S hS X).obj F).IsQuasicoherentOnSite := by
  have hL : (liftedEtaleModule B S hS X F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_liftModule B S hS X F
  have := Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem _ fun W ↦ ?_
  refine (SpacesEtale.topology B S hS X).transitive
    ((comparisonFunctor B S hS X).is_cover_of_isCoverDense (SpacesEtale.topology B S hS X) W) _
    fun Y g hg ↦ ?_
  obtain ⟨⟨A, lift, map, -⟩⟩ := hg
  refine Stacks.SheafOfModules.presentedSieve_mem_of_hom _ lift ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hL.locally_hasGlobalPresentation A
  refine (SpacesEtale.topology B S hS X).superset_covering ?_
    (((comparisonFunctor B S hS X).functorPushforward_mem_iff (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X)).mpr hcov)
  rintro Z _ ⟨Z', g', h', hg', rfl⟩
  obtain ⟨Y', a, b, ⟨i⟩, rfl⟩ := hg'
  rw [Functor.map_comp, ← Category.assoc]
  exact (Stacks.SheafOfModules.presentedSieve _ _).downward_closed
    ((hasGlobalPresentation_toSpacesEtaleModules_over_iff B S hS X F (V i)).mpr (hpres i)) _

/-- **`ι` reflects quasi-coherence**: an `𝒪_X`-module whose transport `ι𝓕` to the spaces-étale
site is quasi-coherent is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_toSpacesEtaleModules (F : Modules.{u, u} B S hS X.1 X.2)
    [hF : ((toSpacesEtaleModules B S hS X).obj F).IsQuasicoherentOnSite] :
    F.IsQuasicoherentOnSite := by
  have := Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  have := Functor.IsDenseSubsite.isLocallyFull (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  have hL : (liftedEtaleModule B S hS X F).IsQuasicoherentOnSite := by
    refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem _ fun A ↦ ?_
    obtain ⟨I, V, f, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
      ((comparisonFunctor B S hS X).obj A)
    let T : Sieve ((comparisonFunctor B S hS X).obj A) :=
      Stacks.SheafOfModules.presentedSieve ((toSpacesEtaleModules B S hS X).obj F) _
    have hT : T ∈ SpacesEtale.topology B S hS X _ := by
      refine (SpacesEtale.topology B S hS X).superset_covering ?_ hcov
      rintro Z _ ⟨Y', a, b, ⟨i⟩, rfl⟩
      exact T.downward_closed (hpres i) a
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (((comparisonFunctor B S hS X).functorPushforward_mem_iff (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X)).mp
        (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨T, hT⟩))
    intro B' g hg
    exact (hasGlobalPresentation_toSpacesEtaleModules_over_iff B S hS X F B').mp hg
  have h : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1)
      (structureRingPresheaf (smallEtaleRingedSite B S hS X.1 X.2).O.obj) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
  have hset := isSheaf_structureRingPresheaf_forget B S hS X.1 X.2
  exact SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation
    (@Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown.{u + 1, u, u, 0} _ _ _
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj h hset (liftedEtaleModule B S hS X F) hL)

end AlgebraicGeometry.Space
