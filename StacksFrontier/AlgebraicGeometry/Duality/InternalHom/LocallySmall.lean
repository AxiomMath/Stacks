module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.PerfectLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentHomQuasicoherent

/-!
# The derived internal Hom at the locally small model

For a scheme `X`, the derived internal Hom `R𝓗om_{𝒪_X}(P, -)` of [Stacks, Tag 08DH] is
constructed at `CategoryTheory.HasDerivedCategory.standard`
(`Stacks.SheafOfModules.derivedSheafHom`). This file reads it at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of `D(𝒪_X)`, where the compact generation
of `D_QCoh(𝒪_X)` is available, by conjugating with the comparison of the two models, which is the
identity on objects.

## Main definitions

* `Stacks.Duality.InternalHom.derivedSheafHom`: `R𝓗om_{𝒪_X}(P, -) : D(𝒪_X) ⥤ D(𝒪_X)` at the
  locally small model.

## Main results

* `Stacks.Duality.InternalHom.isZero_derivedRestrict_derivedSheafHom`: if `E|_U = 0` for an open
  immersion `j : U ⟶ X`, then `R𝓗om(P, E)|_U = 0`. This is the consequence of
  [Stacks, Tag 08DL] (the derived internal Hom commutes with restriction to opens) that the proof
  of [Stacks, Tag 0A9C] uses.
* `Stacks.Duality.InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent`:
  part (1) of [Stacks, Tag 0A6H] at the locally small model: for `P` pseudo-coherent and `E` in
  `D⁺_QCoh(𝒪_X)` the cohomology sheaves of `R𝓗om(P, E)` are quasi-coherent.

## Implementation notes

Perfectness, pseudo-coherence, quasi-coherence of cohomology and vanishing of stalks of
cohomology do not depend on the model
(`StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/LocallySmall.lean`), so the
statements are transported from the standard model object by object.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.PerfectApproximation

universe u

namespace Stacks.Duality.InternalHom

open Stacks.Duality.OpenImmersion (derivedRestrict)

variable {X : Scheme.{u}}

/-- The derived internal Hom of the standard model, as a bifunctor on its derived category. -/
abbrev standardSheafHom (X : Scheme.{u}) :
    (@DerivedCategory X.Modules _ _ (standardModel X))ᵒᵖ ⥤
      @DerivedCategory X.Modules _ _ (standardModel X) ⥤
        @DerivedCategory X.Modules _ _ (standardModel X) :=
  letI := standardModel X
  Stacks.SheafOfModules.derivedSheafHom X.sheaf

section StandardTensor

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived tensor product of the standard model, as a bifunctor on its derived category. -/
abbrev standardTensor (X : Scheme.{u}) :
    @DerivedCategory X.Modules _ _ (standardModel X) ⥤
      @DerivedCategory X.Modules _ _ (standardModel X) ⥤
        @DerivedCategory X.Modules _ _ (standardModel X) :=
  Stacks.SheafOfModules.derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite X.sheaf)

/-- [Stacks, Tag 08J8] at the standard model: `- ⊗ᴸ P ⊣ R𝓗om(P, -)`. -/
abbrev standardTensorSheafHomAdjunction (X : Scheme.{u})
    (P : @DerivedCategory X.Modules _ _ (standardModel X)) :
    (standardTensor X).flip.obj P ⊣ (standardSheafHom X).obj (op P) :=
  RingedSite.derivedTensorSheafHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf) P

end StandardTensor

/-- **`R𝓗om_{𝒪_X}(P, -)` at the locally small model**: the derived internal Hom out of `P` of
the standard model, conjugated by the comparison of the two models. -/
def derivedSheafHom (P : DerivedCategory X.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (StacksDraft.DerivedModel.schemeModulesComparison X).inverse ⋙
    (standardSheafHom X).obj
      (op ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P)) ⋙
    (StacksDraft.DerivedModel.schemeModulesComparison X).functor

/-- The objects of `R𝓗om(P, -)` at the two models are the same. -/
theorem derivedSheafHom_obj (P E : DerivedCategory X.Modules) :
    (derivedSheafHom P).obj E =
      ((standardSheafHom X).obj
        (op ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P))).obj
        ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj E) := rfl

/-- **[Stacks, Tag 0A6H] part (1) at the locally small model.** For `P` pseudo-coherent and `E`
in `D⁺_QCoh(𝒪_X)`, the cohomology sheaves of `R𝓗om(P, E)` are quasi-coherent. -/
theorem isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent
    (P E : DerivedCategory X.Modules) (hP : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) P)
    (hE : DerivedCategoryB.derivedCategoryBPlus (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj ((derivedSheafHom P).obj E)).IsQuasicoherent
    := by
  have h := AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P)
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj E)
    ((isPseudoCoherent_standard_iff P).2 hP)
    ⟨by
      obtain ⟨n, hn⟩ := hE.1
      exact ⟨n, fun k hk => (isZero_homology_standard_iff E k).2 (hn k hk)⟩,
     fun k => (isQuasicoherent_homology_standard_iff E k).2 (hE.2 k)⟩
  exact (isQuasicoherent_homology_standard_iff _ i).1 (h i)

/-- `- ⊗ᴸ P : D(𝒪_X) ⥤ D(𝒪_X)` at the locally small model, transported from the standard model:
the derived tensor product with `P` of [Stacks, Tag 08J8] conjugated by the comparison of the two
models. -/
def derivedTensorRight (P : DerivedCategory X.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (StacksDraft.DerivedModel.schemeModulesComparison X).inverse ⋙
    (standardTensor X).flip.obj
      ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P) ⋙
    (StacksDraft.DerivedModel.schemeModulesComparison X).functor

/-- **[Stacks, Tag 08J8] at the locally small model.** For an object `P` of `D(𝒪_X)`, tensoring
with `P` is left adjoint to `R𝓗om(P, -)`: `Hom(I ⊗ᴸ P, E) ≃ Hom(I, R𝓗om(P, E))`, naturally in
`I` and `E`. It is the adjunction of the standard model conjugated by the comparison of the two
models. -/
def derivedTensorSheafHomAdjunction (P : DerivedCategory X.Modules) :
    derivedTensorRight P ⊣ derivedSheafHom P :=
  ((StacksDraft.DerivedModel.schemeModulesComparison X).symm.toAdjunction.comp
    (standardTensorSheafHomAdjunction X
      ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P))).comp
      (StacksDraft.DerivedModel.schemeModulesComparison X).toAdjunction

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- At the standard model: the cohomology sheaves of `R𝓗om(P, E)` vanish at the points of an open
`W` at whose points those of `E` vanish. The restriction to `W` of `R𝓗om(P, E)` is
`R𝓗om(P|_W, E|_W)` by [Stacks, Tag 08DL], and `E|_W = 0`. -/
private theorem isZero_stalk_standardSheafHom (W : X.Opens)
    (P E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf))
    (hE : ∀ (k : ℤ) (v : W.toScheme), IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules k).obj E).val.presheaf) (W.ι v)))
    (i : ℤ) (v : W.toScheme) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor X.Modules i).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op P)).obj E)).val.presheaf)
          (W.ι v)) := by
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) W
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) W
  refine IsZero.of_iso ?_
    (Stacks.Duality.OpenImmersion.stalkHomologyDerivedRestrictIso W.ι _ i v).symm
  refine (Stacks.Duality.OpenImmersion.isZero_homology_iff_forall_isZero_stalk _ i).1 ?_ v
  refine (DerivedCategory.homologyFunctor _ i).map_isZero ?_
  refine IsZero.of_iso ?_ (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso W P E)
  have hEW : IsZero ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E) := by
    rw [DerivedCategory.isZero_iff_forall_isZero_homology]
    exact fun k => (Stacks.Duality.OpenImmersion.isZero_homology_iff_forall_isZero_stalk _ k).2
      fun v' => (hE k v').of_iso
        (Stacks.Duality.OpenImmersion.stalkHomologyDerivedRestrictIso W.ι E k v')
  exact (IsZero.iff_id_eq_zero _).2
    (((RingedSite.derivedTensorSheafHomAdjunction
      (Stacks.SheafOfModules.ringedSite W.toScheme.sheaf) _).homEquiv _ _).symm.injective
        (hEW.eq_of_tgt _ _))

end Standard

/-- **The derived internal Hom vanishes where its target does.** For an open immersion
`j : U ⟶ X` and objects `P`, `E` of `D(𝒪_X)` with `E|_U = 0`, also `R𝓗om(P, E)|_U = 0`. On
`W = j(U)` the derived internal Hom commutes with restriction by [Stacks, Tag 08DL], and the
derived internal Hom into zero vanishes. -/
theorem isZero_derivedRestrict_derivedSheafHom {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P E : DerivedCategory X.Modules) (hE : IsZero ((derivedRestrict j).obj E)) :
    IsZero ((derivedRestrict j).obj ((derivedSheafHom P).obj E)) := by
  refine Stacks.Duality.OpenImmersion.isZero_derivedRestrict_of_isZero_stalk j _ fun i u => ?_
  let W : X.Opens := j.opensRange
  let w : W.toScheme := ⟨j u, ⟨u, rfl⟩⟩
  refine (isZero_stalk_homology_standard_iff ((derivedSheafHom P).obj E) i (W.ι w)).1 ?_
  refine isZero_stalk_standardSheafHom W
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P)
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj E) (fun k v => ?_) i w
  obtain ⟨u', hu'⟩ := v.2
  have h := Stacks.Duality.OpenImmersion.isZero_stalk_of_isZero_derivedRestrict j E hE k u'
  rw [show j u' = W.ι v from hu'] at h
  exact (isZero_stalk_homology_standard_iff E k _).2 h

/-- **Restriction along an open immersion preserves perfectness, at the standard model.** This is
`Stacks.Duality.CompactPerfect.isPerfect_derivedRestrict` read across the comparison of the two
models, perfectness being independent of the model. -/
theorem isPerfect_restrictFunctor_standard {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace (standardModel Y)
      (@Functor.mapDerivedCategory X.Modules _ _ (standardModel X) Y.Modules _ _
        (standardModel Y) (Scheme.Modules.restrictFunctor g) _ _ _ |>.obj K) := by
  refine (isPerfect_standard_iff _).2 ?_
  have e := (@Stacks.Injectives.mapDerivedCategoryTargetModelIso Y.Modules _ _ _ X.Modules _ _
      (standardModel X) (Scheme.Modules.restrictFunctor g) _ _ _).app K ≪≫
    (Stacks.Injectives.mapDerivedCategoryModelIso X.Modules
      (Scheme.Modules.restrictFunctor g)).app K
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e.symm
    (Stacks.Duality.CompactPerfect.isPerfect_derivedRestrict g K hK)

section StandardPerfect

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Part (2) of [Stacks, Tag 0A6H] on the spectrum of a ring**, at the standard model: for `E`
perfect and `F` with quasi-coherent cohomology, `R𝓗om(E, F)` has quasi-coherent cohomology. Both
are sheafifications, `E ≅ K̃` with `K` perfect ([Stacks, Tag 08EB]) and `F ≅ L̃`
([Stacks, Tag 06Z0]), and `R𝓗om(K̃, L̃) ≅ R Hom_R(K, L)~` by part (3)(b). -/
theorem derivedCategoryB_derivedSheafHom_of_isPerfect_spec (R : CommRingCat.{u})
    (E F : DerivedCategory (Spec R).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).obj F) := by
  have hE' : RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) E := hE
  have hEq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E hE'.isPseudoCoherent
  obtain ⟨K, ⟨eK⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R E hEq
  obtain ⟨L, ⟨eL⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R F hF
  have hK : StacksDraft.Perfect.IsPerfect K :=
    (AlgebraicGeometry.isPerfect_tilde_iff K).1 (hE'.of_iso eK.symm)
  intro n
  have e := (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso eK.op).app
      ((tilde.functor R).mapDerivedCategory.obj L)).symm ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).mapIso eL
  have h₂ := (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      (AlgebraicGeometry.affinePerfectDerivedSheafHomIso R K L hK)).symm
    (AlgebraicGeometry.isQuasicoherent_homology_tildeDerived R
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (op K, L)) n)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) h₂

/-- Perfectness travels along restriction along an open immersion, at the standard model. -/
theorem isPerfect_restrictFunctor_mapDerivedCategory {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsOpenImmersion g] (K : DerivedCategory Z.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) :=
  isPerfect_restrictFunctor_standard g K ((isPerfect_standard_iff K).1 hK)

/-- If the cohomology of `B` is quasi-coherent and `B` is the restriction of `A` along an open
immersion, so is the restriction of the cohomology of `A`. -/
private theorem isQuasicoherent_restrictFunctor_homology_of_iso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsOpenImmersion g] (n : ℤ) {A : DerivedCategory Z.Modules} {B : DerivedCategory Y.Modules}
    (e : (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj A ≅ B)
    (h : ((DerivedCategory.homologyFunctor Y.Modules n).obj B).IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor g).obj
      ((DerivedCategory.homologyFunctor Z.Modules n).obj A)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso (Scheme.Modules.restrictFunctor g) n).app _)
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e).symm h)

/-- **Part (2) of [Stacks, Tag 0A6H] on an affine scheme**, at the standard model, transported
along `W.isoSpec.inv` from the case of the spectrum of a ring. -/
theorem derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine (W : Scheme.{u})
    [IsAffine W] (E F : DerivedCategory W.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom W.sheaf).obj (op E)).obj F) := by
  have h := derivedCategoryB_derivedSheafHom_of_isPerfect_spec Γ(W, ⊤) _ _
    (isPerfect_restrictFunctor_mapDerivedCategory W.isoSpec.inv E hE)
    (fun n => AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory
      W.isoSpec.inv hF n)
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun _ : PUnit.{u + 1} => W.isoSpec.inv)
    (by simpa using Scheme.Hom.opensRange_of_isIso W.isoSpec.inv) _ fun _ => ?_
  exact isQuasicoherent_restrictFunctor_homology_of_iso _ n
    (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso W.isoSpec.inv E F) (h n)

/-- **Part (2) of [Stacks, Tag 0A6H]**, at the standard model: on a scheme `Y`, for `E` perfect and
`F` with quasi-coherent cohomology, `R𝓗om(E, F)` has quasi-coherent cohomology. Both the
hypotheses and the conclusion are local, and on an affine open this is the affine case,
[Stacks, Tag 08DL] identifying the restriction of `R𝓗om(E, F)` with `R𝓗om(E|_U, F|_U)`. -/
theorem derivedCategoryB_derivedSheafHom_of_isPerfect (Y : Scheme.{u})
    (E F : DerivedCategory Y.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) E)
    (hF : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf) F) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj F) := by
  intro n
  refine Stacks.Descent.isQuasicoherent_of_restrictFunctor_zariski
    (fun U : Y.affineOpens => (U : Y.Opens).ι)
    (by simpa only [Scheme.Opens.opensRange_ι] using iSup_affineOpens_eq_top Y) _ fun U => ?_
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Y.ringCatSheaf) (U : Y.Opens)
  let _ : IsAffine (U : Y.Opens).toScheme := U.2
  have hres := derivedCategoryB_derivedSheafHom_of_isPerfect_of_isAffine
    (U : Y.Opens).toScheme
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj E)
    ((Scheme.Modules.restrictFunctor (U : Y.Opens).ι).mapDerivedCategory.obj F)
    (isPerfect_restrictFunctor_mapDerivedCategory (U : Y.Opens).ι E hE)
    (fun k => AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory
      (U : Y.Opens).ι hF k)
  exact isQuasicoherent_restrictFunctor_homology_of_iso _ n
    (Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso (U : Y.Opens) E F) (hres n)

end StandardPerfect

/-- **[Stacks, Tag 0A6H] part (2) at the locally small model.** For `P` perfect and `E` with
quasi-coherent cohomology, the cohomology sheaves of `R𝓗om(P, E)` are quasi-coherent. -/
theorem isQuasicoherent_homology_derivedSheafHom_of_isPerfect
    (P E : DerivedCategory X.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj ((derivedSheafHom P).obj E)).IsQuasicoherent
    := by
  have h := derivedCategoryB_derivedSheafHom_of_isPerfect X
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj P)
    ((StacksDraft.DerivedModel.schemeModulesComparison X).inverse.obj E)
    ((isPerfect_standard_iff P).2 hP)
    (fun k => (isQuasicoherent_homology_standard_iff E k).2 (hE k))
  exact (isQuasicoherent_homology_standard_iff _ i).1 (h i)

end Stacks.Duality.InternalHom

end
