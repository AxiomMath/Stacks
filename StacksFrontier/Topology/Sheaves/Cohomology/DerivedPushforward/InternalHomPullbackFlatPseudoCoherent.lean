module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.RestrictionIsPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow

/-!
# Flat pullback of a derived internal hom out of a pseudo-coherent object

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a flat morphism of ringed spaces, `K ∈ D(𝒪_Y)` pseudo-coherent and
`M ∈ D(𝒪_Y)` locally bounded below. If the canonical map `Lg^*R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` is
invertible at every strictly perfect complex `P`, along every morphism of ringed spaces `g`, then
the canonical map

`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)`

is an isomorphism.

## Main definitions

* `StrictlyPerfectInvertibility`: the canonical map `Lg^*R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` is
  invertible at every strictly perfect complex `P`.

## Main results

* `isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_strictlyPerfect`: given
  `StrictlyPerfectInvertibility`, the canonical map is an isomorphism for flat `h`, pseudo-coherent
  `K` and locally bounded below `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- In a commutative square whose two outer legs `Φ` inverts, `Φ` inverts one of the two
remaining legs exactly when it inverts the other. -/
theorem isIso_map_iff_of_comp_eq {C E : Type*} [Category C] [Category E] (Φ : C ⥤ E)
    {A B A' B' : C} {x : A ⟶ A'} {y : A' ⟶ B'} {z : A ⟶ B} {w : B ⟶ B'}
    (hx : IsIso (Φ.map x)) (hw : IsIso (Φ.map w)) (sq : x ≫ y = z ≫ w) :
    IsIso (Φ.map y) ↔ IsIso (Φ.map z) := by
  rw [← isIso_comp_left_iff (Φ.map x), ← isIso_comp_right_iff (Φ.map z) (Φ.map w), ← Φ.map_comp,
    ← Φ.map_comp, sq]

/-- For an isomorphism `K ≅ K'` and any functor `Φ`, the image under `Φ` of the canonical map
`derivedPullbackSheafHomMap h K M` is invertible exactly when that of
`derivedPullbackSheafHomMap h K' M` is. -/
theorem isIso_map_derivedPullbackSheafHomMap_iff_of_iso {E : Type*} [Category E]
    (Φ : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ⥤ E)
    {K K' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (e : K ≅ K')
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (Φ.map (derivedPullbackSheafHomMap h K M)) ↔
      IsIso (Φ.map (derivedPullbackSheafHomMap h K' M)) := by
  have sq := Transpose.homComparison_naturality_source (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X)
    (tensorHomBijection Y) (tensorHomBijection X) (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivDinatural_ringedSpace Y)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X) e.hom M
  have h₁ : IsIso (Φ.map ((derivedPullbackFunctor h).map
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).map e.hom.op).app M))) :=
    Iso.isIso_hom (Φ.mapIso ((derivedPullbackFunctor h).mapIso
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).mapIso e.op).app M)))
  have h₂ : IsIso (Φ.map (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
      ((derivedPullbackFunctor h).map e.hom).op).app ((derivedPullbackFunctor h).obj M))) :=
    Iso.isIso_hom (Φ.mapIso (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso
      ((derivedPullbackFunctor h).mapIso e).op).app ((derivedPullbackFunctor h).obj M)))
  exact isIso_map_iff_of_comp_eq Φ h₁ h₂ sq

section OpenSubspace

variable (Y) (U : TopologicalSpace.Opens Y)

/-- The inclusion of an open subspace is flat: its stalk maps are invertible. -/
theorem isFlat_openSubspaceInclusion :
    AlgebraicGeometry.IsFlat (openSubspaceInclusion Y U) := fun y => by
  have hi : IsIso ((openSubspaceInclusion Y U).hom.stalkMap y) :=
    AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso Y.toPresheafedSpace
      U.isOpenEmbedding y
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- **Derived restriction to an open subspace commutes with cohomology**:
`H^n(K|_U) ≅ H^n(K)|_U`. -/
def homologyDerivedPullbackOpenSubspaceIso (n : ℤ) :
    derivedPullbackFunctor (openSubspaceInclusion Y U) ⋙ DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen Y U)) n ≅
      DerivedCategory.homologyFunctor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) n ⋙
        RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U) :=
  haveI : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y U) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y U.isOpenEmbedding
  haveI : (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)).Additive :=
    RingedSpaceModuleAdjunction.modulePullback_additive _
  haveI : (RingedSpaceModuleAdjunction.modulePullback
      (openSubspaceInclusion Y U)).PreservesHomology :=
    Stacks.Cohomology.DerivedOpenImmersion.modulePullbackOpenImmersion_preservesHomology _
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  haveI : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
        (openSubspaceInclusion Y U)) _ ≪≫
    StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)) n

/-- **Derived restriction of the class of a complex is the class of its restriction.** -/
def derivedPullbackOpenSubspaceQIso
    (E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (derivedPullbackFunctor (openSubspaceInclusion Y U)).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex E U) :=
  haveI : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y U) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y U.isOpenEmbedding
  haveI : (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)).Additive :=
    RingedSpaceModuleAdjunction.modulePullback_additive _
  haveI : (RingedSpaceModuleAdjunction.modulePullback
      (openSubspaceInclusion Y U)).PreservesHomology :=
    Stacks.Cohomology.DerivedOpenImmersion.modulePullbackOpenImmersion_preservesHomology _
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  haveI : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y U)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
      (openSubspaceInclusion Y U)).app _ ≪≫
    (RingedSpaceModuleAdjunction.modulePullback
      (openSubspaceInclusion Y U)).mapDerivedCategoryFactors.app E ≪≫
    DerivedCategory.Q.mapIso ((@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
      (inferInstance : (RingedSpaceModuleAdjunction.modulePullback
        (openSubspaceInclusion Y U)).PreservesZeroMorphisms)
      (inferInstance : (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} Y
        U).PreservesZeroMorphisms)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback Y U).symm
        (ComplexShape.up ℤ)).app E)

/-- **A locally bounded below object is bounded below on a neighbourhood of every point.** -/
theorem exists_isGE_derivedPullback_openSubspace
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow Y M) (y : Y.carrier) :
    ∃ U : TopologicalSpace.Opens Y, y ∈ U ∧ ∃ N : ℤ,
      ((derivedPullbackFunctor (openSubspaceInclusion Y U)).obj M).IsGE N := by
  obtain ⟨U, hyU, N, hN⟩ := hM y
  refine ⟨U, hyU, N, ?_⟩
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (hN i hi).of_iso ((homologyDerivedPullbackOpenSubspaceIso Y U i).app M ≪≫
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback Y U).symm.app _)

end OpenSubspace

section Assembly

/-- The canonical map `derivedPullbackSheafHomMap g (DerivedCategory.Q.obj P) M` is invertible
for every morphism of ringed spaces `g`, every strictly perfect complex `P` and every object
`M`. -/
abbrev StrictlyPerfectInvertibility : Prop :=
  ∀ ⦃Z W : AlgebraicGeometry.RingedSpace.{u, u}⦄ (g : Z ⟶ W)
    (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W) ℤ),
    StrictlyPerfect.IsStrictlyPerfect P →
      ∀ M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W),
        IsIso (derivedPullbackSheafHomMap g (DerivedCategory.Q.obj P) M)

/-- Given `StrictlyPerfectInvertibility`, for a flat `h`, a pseudo-coherent `K` and `M` bounded
below, the canonical map `derivedPullbackSheafHomMap h K M` induces isomorphisms on every
cohomology object. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_isGE
    (hsp : StrictlyPerfectInvertibility.{u}) (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (derivedPullbackSheafHomMap h K M)) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso h _ eE M).1 ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n _ M fun x => ?_
  obtain ⟨U, hyU, P, hP, α, hα₁, hα₂⟩ := hE (a - n - 1) (h.hom.base x)
  refine ⟨U, hyU, ?_⟩
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso (restrictedMorphism h U) _
    (derivedPullbackOpenSubspaceQIso Y U E).symm _).1 ?_
  exact isIso_homologyMap_derivedPullbackSheafHomMap_of_approximation (restrictedMorphism h U)
    (isFlat_restrictedMorphism h hh U) α (a - n - 1) hα₁ hα₂ _ a
    (isGE_derivedPullback_obj_of_isFlat _ (isFlat_openSubspaceInclusion Y U) M a hM)
    (hsp _ P hP _) n (by lia)

/-- Given `StrictlyPerfectInvertibility`, for a flat morphism of ringed spaces `h : X ⟶ Y`, a
pseudo-coherent `K ∈ D(𝒪_Y)` and a locally bounded below `M ∈ D(𝒪_Y)`, the canonical map
`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism. -/
theorem isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_strictlyPerfect
    (hsp : StrictlyPerfectInvertibility.{u}) (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow Y M) :
    IsIso (derivedPullbackSheafHomMap h K M) := by
  refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n K M fun x => ?_
  obtain ⟨U, hyU, N, hN⟩ := exists_isGE_derivedPullback_openSubspace Y M hM (h.hom.base x)
  exact ⟨U, hyU, isIso_homologyMap_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_isGE
    (restrictedMorphism h U) hsp (isFlat_restrictedMorphism h hh U) _
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
      (openSubspaceInclusion Y U) K hK) _ N hN n⟩

end Assembly

end Stacks.Cohomology.DerivedInternalHomPullback

end
