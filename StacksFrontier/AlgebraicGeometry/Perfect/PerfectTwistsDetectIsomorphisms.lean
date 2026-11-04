module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTraceDiagram
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TwistedFourierMukai
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentDetectedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# Perfect twists detect isomorphisms out of a derived pullback along a closed immersion

Let `X` be a quasi-compact and quasi-separated scheme. An object `N` of `D_QCoh(𝒪_X)` whose
twists `N ⊗^𝐋 E` by all perfect objects `E` have vanishing derived global sections is zero: for a
perfect generator `G` of `D_QCoh(𝒪_X)` ([Stacks, Tag 09IS]) the groups `Hom(G[n], N)` are the
cohomology groups of `RΓ(X, N ⊗^𝐋 G^∨)` ([Stacks, Tag 08DQ]), and `G^∨` is perfect.

The consequence used for Grothendieck's existence theorem in its derived form
([Stacks, Tag 0DIF]): let `i : Y ⟶ X` be a closed immersion, `K ∈ D_QCoh(𝒪_X)`,
`M ∈ D_QCoh(𝒪_Y)` and `c : Li^*K ⟶ M`. If `RΓ(Y, c ⊗^𝐋 Li^*E)` is an isomorphism for every
perfect `E` on `X`, then `c` is an isomorphism. Indeed, with `C` the cone of `c`, the hypothesis
makes `RΓ(Y, C ⊗^𝐋 Li^*E)` vanish; by the projection formula ([Stacks, Tag 08EU]) and Leray
([Stacks, Tag 0D5W]) this is `RΓ(X, Ri_*C ⊗^𝐋 E)`, so `Ri_*C = 0` by the first statement, and
`Ri_*` detects vanishing on `D_QCoh(𝒪_Y)` because `i` is affine.

## Main results

* `AlgebraicGeometry.isZero_of_isZero_derivedModuleGlobalSections_derivedTensor`: perfect twists
  detect vanishing in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.isIso_of_isIso_derivedGlobalSectionsOver_map_derivedTensor`: perfect twists,
  pulled back along a closed immersion, detect isomorphisms out of a derived pullback.

## Implementation notes

The inputs ([Stacks, Tag 09IS], [Stacks, Tag 08DQ], [Stacks, Tag 08EU]) are proved at
`HasDerivedCategory.standard`, so this module works there: the standard model is a local
instance and the locally small instances of `StacksFrontier.Homology.DerivedCategory.LocallySmall`
are switched off locally, so that every derived category below resolves to the standard model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.SheafOfModules Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.AlgebraicGeometry.AffinePushforwardTExactness
  (isZero_homology_of_isZero_homology_derivedPushforward)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory ModuleCat.hasDerivedCategory

namespace AlgebraicGeometry

/-- An object of `D(R)` whose underlying complex of abelian groups is zero is zero. -/
theorem isZero_of_isZero_forget₂_mapDerivedCategory_obj {R : Type u} [CommRing R]
    {M : DerivedCategory (ModuleCat.{u} R)}
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) :
    IsZero M :=
  Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj M fun n => by
    have h₁ : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) :=
      (Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero h n).of_iso
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).app
          M).symm
    rw [AddCommGrpCat.isZero_iff_subsingleton] at h₁
    exact (ModuleCat.isZero_iff_subsingleton).2 h₁

variable {X : Scheme.{u}}

/-- Over a base ring, vanishing of the derived global sections is vanishing of the
abelian-group-valued derived global sections of the ringed site. -/
theorem isZero_derivedGlobalSectionsOver_obj_iff {A : Type u} [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (M : DerivedCategory X.Modules) :
    IsZero ((derivedGlobalSectionsOver f).obj M) ↔
      IsZero ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj M) := by
  let e := (Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso
    f).app M
  exact ⟨fun h => (Functor.map_isZero _ h).of_iso e.symm,
    fun h => isZero_of_isZero_forget₂_mapDerivedCategory_obj (h.of_iso e)⟩

/-- **Perfect twists detect vanishing in `D_QCoh(𝒪_X)`.** Let `X` be a quasi-compact and
quasi-separated scheme and let `N ∈ D_QCoh(𝒪_X)`. If `RΓ(X, N ⊗^𝐋 E) = 0` for every perfect
`E`, then `N = 0`.

For a perfect generator `G` of `D_QCoh(𝒪_X)` ([Stacks, Tag 09IS]) the group `Hom(G[n], N)` is
`Ext^{-n}(G, N) = H^{-n}(X, N ⊗^𝐋 G^∨)` ([Stacks, Tag 08DQ]), which vanishes since `G^∨` is
perfect. -/
theorem isZero_of_isZero_derivedModuleGlobalSections_derivedTensor [CompactSpace X]
    [QuasiSeparatedSpace X] (N : DerivedCategory (StructureSheafModules X.sheaf))
    (hN : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj N).IsQuasicoherent)
    (h : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        IsZero ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj N).obj E))) :
    IsZero N := by
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator (X := X) inferInstance inferInstance
  refine hgen N hN fun n g => ?_
  have hext : Subsingleton (DerivedCategory.Ext G N (-n)) :=
    (subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect G N hG (-n)).2
      (Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero
        (h _ (isPerfect_derivedDual X.sheaf G hG)) (-n))
  have hhom : Subsingleton (G⟦n⟧ ⟶ N) :=
    (((shiftEquiv' (DerivedCategory (StructureSheafModules X.sheaf)) n (-n)
      (by omega)).toAdjunction.homEquiv G N)).subsingleton_congr.2 hext
  exact Subsingleton.elim _ _

/-- A perfect object of `D(𝒪_X)`, in the sense of [Stacks, Tag 08CM], has quasi-coherent
cohomology sheaves. -/
theorem isQuasicoherent_homology_of_isPerfect
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) i).obj
      E).IsQuasicoherent :=
  isQuasicoherentDerived_of_isPseudoCoherent X E
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).1
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)) i

/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁[1]` of `D(𝒪_X)` whose first two vertices have
quasi-coherent cohomology, so does the third. -/
theorem isQuasicoherent_homology_obj₃_of_distinguished
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₁).IsQuasicoherent)
    (h₂ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₂).IsQuasicoherent)
    (i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₃).IsQuasicoherent :=
  DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) T.rotate
    (rot_of_distTriang T hT) h₂
    (DerivedCategoryB.derivedCategoryB_shift_mem _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) 1 h₁) i

/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁[1]` of `D(𝒪_Y)`, if `RΓ(Y, - ⊗^𝐋 P)` inverts
the first map then it kills the third vertex. -/
theorem isZero_derivedGlobalSectionsOver_derivedTensor_obj₃ {Y : Scheme.{u}} {B : Type u}
    [CommRing B] (g : Y ⟶ Spec (CommRingCat.of B))
    (T : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))))
    (hT : T ∈ distTriang _)
    (P : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (h : IsIso ((derivedGlobalSectionsOver g).map
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map T.mor₁).app
        P))) :
    IsZero ((derivedGlobalSectionsOver g).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj T.obj₃).obj
        P)) := by
  let : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      P).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).commShift_left P
  have : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      P).IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).exact_left P
  exact (Triangle.isZero₃_iff_isIso₁ _
    ((derivedGlobalSectionsOver g).map_distinguished _
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        P).map_distinguished _ hT))).2 h

/-- **Perfect twists, pulled back along a closed immersion, detect isomorphisms out of a derived
pullback.** Let `X` be a quasi-compact and quasi-separated scheme, `i : Y ⟶ X` a closed
immersion, `K ∈ D_QCoh(𝒪_X)`, `M ∈ D_QCoh(𝒪_Y)` and `c : Li^*K ⟶ M`. If for every perfect `E`
in `D(𝒪_X)` the map `RΓ(Y, c ⊗^𝐋 Li^*E)` is an isomorphism, then `c` is an isomorphism.

The cone `C` of `c` has `RΓ(Y, C ⊗^𝐋 Li^*E) = 0`, which is `RΓ(X, Ri_*C ⊗^𝐋 E)` by Leray
([Stacks, Tag 0D5W]) and the projection formula ([Stacks, Tag 08EU]); so `Ri_*C = 0` by
`isZero_of_isZero_derivedModuleGlobalSections_derivedTensor`, and `C = 0` because `i` is
affine. -/
theorem isIso_of_isIso_derivedGlobalSectionsOver_map_derivedTensor [CompactSpace X]
    [QuasiSeparatedSpace X] {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    {B : Type u} [CommRing B] (g : Y ⟶ Spec (CommRingCat.of B))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj K).IsQuasicoherent)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hM : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj M).IsQuasicoherent)
    (c : (derivedPullback i.toLRSHom.toShHom).obj K ⟶ M)
    (h : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        IsIso ((derivedGlobalSectionsOver g).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map c).app
            ((derivedPullback i.toLRSHom.toShHom).obj E)))) :
    IsIso c := by
  obtain ⟨C, a, b, hT⟩ := distinguished_cocone_triangle c
  have hLK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj
        ((derivedPullback i.toLRSHom.toShHom).obj K)).IsQuasicoherent :=
    fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel i K hK n
  have hC : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj C).IsQuasicoherent :=
    isQuasicoherent_homology_obj₃_of_distinguished _ hT hLK hM
  have hiC : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj C)).IsQuasicoherent :=
    fun n => Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i
      ⟨C, hC⟩ n
  have hzero : IsZero ((derivedPushforward i.toLRSHom.toShHom).obj C) := by
    refine isZero_of_isZero_derivedModuleGlobalSections_derivedTensor _ hiC fun E hE => ?_
    have hE' := Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace E hE
    have z₁ := isZero_derivedGlobalSectionsOver_derivedTensor_obj₃ g _ hT
      ((derivedPullback i.toLRSHom.toShHom).obj E) (h E hE')
    have z₂ := (isZero_derivedGlobalSectionsOver_obj_iff (i ≫ X.toSpecΓ) _).2
      ((isZero_derivedGlobalSectionsOver_obj_iff g _).1 z₁)
    have z₃ : IsZero ((derivedGlobalSectionsOver X.toSpecΓ).obj
        ((derivedPushforward i.toLRSHom.toShHom).obj
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj C).obj
            ((derivedPullback i.toLRSHom.toShHom).obj E)))) :=
      z₂.of_iso ((derivedGlobalSectionsOverCompIso i X.toSpecΓ).app _).symm
    have hpf := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent
      i C hC E (isQuasicoherent_homology_of_isPerfect E hE')
    have z₄ : IsZero ((derivedGlobalSectionsOver X.toSpecΓ).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
          ((derivedPushforward i.toLRSHom.toShHom).obj C)).obj E)) :=
      z₃.of_iso ((derivedGlobalSectionsOver X.toSpecΓ).mapIso
        (@asIso _ _ _ _ (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
          i.toLRSHom.toShHom C E) hpf))
    have z₅ : IsZero ((derivedGlobalSectionsOver X.toSpecΓ).obj
        (((derivedTensor X.sheaf).obj ((derivedPushforward i.toLRSHom.toShHom).obj C)).obj E)) :=
      z₄.of_iso ((derivedGlobalSectionsOver X.toSpecΓ).mapIso
        (RingedSite.derivedTensorObjIso (ringedSite X.sheaf) _ E))
    exact (isZero_derivedGlobalSectionsOver_obj_iff X.toSpecΓ _).1 z₅
  have hCzero : IsZero C :=
    Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj C fun n =>
      isZero_homology_of_isZero_homology_derivedPushforward i C hC
        (Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero hzero n)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hCzero

end AlgebraicGeometry

end
