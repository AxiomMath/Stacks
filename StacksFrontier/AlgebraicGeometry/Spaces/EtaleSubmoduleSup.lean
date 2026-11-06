module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleComap
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected

/-!
# Suprema of submodules on the small étale site of an algebraic space

Let `X` be an algebraic space and `M` an `𝒪_X`-module. The submodules of `M` form a complete
lattice (`SheafOfModules.Submodule`). Restriction of submodules along an étale morphism
`g : Y ⟶ X` is a left adjoint, with right adjoint `AlgebraicGeometry.Space.etaleSubmoduleComap`,
and restriction of a submodule of `M|_Z` along an étale `k : Y ⟶ Z` preserves binary suprema. The
supremum of two submodules is the image of their direct sum in `M`, so the supremum of two
submodules of finite type is of finite type.

## Main results

* `AlgebraicGeometry.Space.gc_etaleSubmoduleRestrict`: restriction along an étale morphism is a
  left adjoint.
* `AlgebraicGeometry.Space.etaleSubmoduleAlong_sup`: restriction of a submodule of `M|_Z` along
  `k : Y ⟶ Z` preserves binary suprema.
* `AlgebraicGeometry.Space.isFiniteType_sup`: the supremum of two submodules of finite type is
  of finite type.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule_of_mono`: the
  range of a monomorphism out of a quasi-coherent module of finite type is a quasi-coherent
  submodule of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]

/-- **The direct sum of two sheaves of modules of finite type is of finite type.** -/
theorem isFiniteType_biprod_of_isFiniteType (M N : SheafOfModules.{u} R)
    [HasBinaryBiproduct M N] (hM : M.IsFiniteType) (hN : N.IsFiniteType) :
    (M ⊞ N).IsFiniteType := by
  refine SheafOfModules.isFiniteType_of_presheaf_isFiniteType _
    (isFiniteType_presheaf_of_split (biprod.fst : M ⊞ N ⟶ M).val
      (biprod.snd : M ⊞ N ⟶ N).val (biprod.inl : M ⟶ M ⊞ N).val
      (biprod.inr : N ⟶ M ⊞ N).val (fun X x => ?_)
      (presheaf_isFiniteType_of_isFiniteType M hM)
      (presheaf_isFiniteType_of_isFiniteType N hN))
  have h := congrArg (fun φ : M ⊞ N ⟶ M ⊞ N => φ.val.app X x) (biprod.total (X := M) (Y := N))
  dsimp only at h
  rwa [SheafOfModules.add_val, PresheafOfModules.add_app] at h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Restrict

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **Restriction along an étale morphism is a left adjoint**, with right adjoint
`AlgebraicGeometry.Space.etaleSubmoduleComap`. -/
theorem gc_etaleSubmoduleRestrict :
    GaloisConnection (etaleSubmoduleRestrict B S hS g hg (M := M))
      (etaleSubmoduleComap B S hS g hg) :=
  fun N K => (le_etaleSubmoduleComap_iff B S hS g hg N K).symm

/-- Reading a submodule of an iterated étale pullback as one of the pullback along the
composite is an order isomorphism. -/
def etaleSubmoduleIterToCompOrderIso {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom) :
    ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj M)).Submodule ≃o
      ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule where
  toFun := etaleSubmoduleIterToComp B S hS k hk h hh hkh
  invFun := etaleSubmoduleCompToIter B S hS k hk h hh hkh
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **Restriction of a submodule of `M|_Z` along `k : Y ⟶ Z` preserves binary suprema.** -/
theorem etaleSubmoduleAlong_sup {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (N₁ N₂ : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule) :
    etaleSubmoduleAlong B S hS k hk h hh hkh (N₁ ⊔ N₂) =
      etaleSubmoduleAlong B S hS k hk h hh hkh N₁ ⊔
        etaleSubmoduleAlong B S hS k hk h hh hkh N₂ := by
  show etaleSubmoduleIterToCompOrderIso B S hS k hk h hh hkh
      (etaleSubmoduleRestrict B S hS k hk (N₁ ⊔ N₂)) = _
  rw [etaleSubmoduleRestrict_sup, OrderIso.map_sup]
  rfl

/-- Restriction of a submodule of `M|_Z` along `k : Y ⟶ Z` is monotone. -/
theorem etaleSubmoduleAlong_mono {Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    {N₁ N₂ : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule} (hle : N₁ ≤ N₂) :
    etaleSubmoduleAlong B S hS k hk h hh hkh N₁ ≤ etaleSubmoduleAlong B S hS k hk h hh hkh N₂ := by
  intro V s hs
  exact hle (op ((ringedSitePostcomp B S hS k hk).obj V.unop)) hs

/-- Transport along an equality of étale morphisms is monotone. -/
theorem etaleSubmoduleCongr_mono {a b : Y ⟶ X} (hab : a = b) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom)
    {N₁ N₂ : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule} (hle : N₁ ≤ N₂) :
    etaleSubmoduleCongr B S hS hab ha hb N₁ ≤ etaleSubmoduleCongr B S hS hab ha hb N₂ := by
  subst hab
  exact hle

end Restrict

section Sup

variable {X : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}

/-- The inclusion of a submodule into a larger one, as a morphism of sheaves of modules. -/
def submoduleHomOfLE {K K' : M.Submodule} (h : K ≤ K') :
    K.toSheafOfModules ⟶ K'.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (show K.toSubmodule ≤ K'.toSubmodule from h)⟩

/-- The inclusion `K ⟶ K'` followed by the inclusion of `K'` is the inclusion of `K`. -/
@[reassoc (attr := simp)]
theorem submoduleHomOfLE_ι {K K' : M.Submodule} (h : K ≤ K') :
    submoduleHomOfLE B S hS h ≫ K'.ι = K.ι := rfl

/-- **The range of a monomorphism out of a quasi-coherent module of finite type** is a
quasi-coherent submodule of finite type. -/
theorem isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule_of_mono
    {N : Modules.{u, u} B S hS X.1 X.2}
    (f : N ⟶ M) [Mono f] (hq : N.IsQuasicoherentOnSite) (hf : N.IsFiniteType) :
    (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule
      f).toSheafOfModules.IsQuasicoherentOnSite ∧
      (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule f).toSheafOfModules.IsFiniteType := by
  let e := Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso f
  have : Epi e.hom := ⟨fun a b hab => by simpa using congrArg (e.inv ≫ ·) hab⟩
  exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e hq,
    Stacks.SheafOfModules.isFiniteType_of_epi
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      e.hom hf⟩

open Stacks.SheafOfModules.ImageSubsheaf in
/-- **The supremum of two submodules is the image of their direct sum.** -/
theorem subobject_mk_sup_ι (K₁ K₂ : M.Submodule) :
    Subobject.mk (K₁ ⊔ K₂).ι = imageSubobject (biprod.desc K₁.ι K₂.ι) := by
  set f := biprod.desc K₁.ι K₂.ι with hf
  refine le_antisymm ?_ ?_
  · let P := monoRangeSubmodule (imageSubobject f).arrow
    have hP : Subobject.mk P.ι = imageSubobject f := subobject_mk_monoRangeSubmodule_ι _
    have h₁ : K₁ ≤ P := by
      refine submodule_le_of_subobject_mk_ι_le ?_
      rw [hP]
      exact Subobject.mk_le_of_comm (biprod.inl ≫ factorThruImageSubobject f)
        (by rw [Category.assoc, imageSubobject_arrow_comp, hf, biprod.inl_desc])
    have h₂ : K₂ ≤ P := by
      refine submodule_le_of_subobject_mk_ι_le ?_
      rw [hP]
      exact Subobject.mk_le_of_comm (biprod.inr ≫ factorThruImageSubobject f)
        (by rw [Category.assoc, imageSubobject_arrow_comp, hf, biprod.inr_desc])
    rw [← hP]
    exact Subobject.mk_le_mk_of_comm (submoduleHomOfLE B S hS (sup_le h₁ h₂))
      (submoduleHomOfLE_ι B S hS _)
  · refine imageSubobject_le_mk _ f
      (biprod.desc (submoduleHomOfLE B S hS (le_sup_left : K₁ ≤ K₁ ⊔ K₂))
        (submoduleHomOfLE B S hS (le_sup_right : K₂ ≤ K₁ ⊔ K₂))) ?_
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, hf, biprod.inl_desc, submoduleHomOfLE_ι]
    · rw [biprod.inr_desc_assoc, hf, biprod.inr_desc, submoduleHomOfLE_ι]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The supremum of two submodules of finite type is of finite type.** -/
theorem isFiniteType_sup (K₁ K₂ : M.Submodule) (h₁ : K₁.toSheafOfModules.IsFiniteType)
    (h₂ : K₂.toSheafOfModules.IsFiniteType) : (K₁ ⊔ K₂).toSheafOfModules.IsFiniteType := by
  have hsum := Stacks.SheafOfModules.isFiniteType_biprod_of_isFiniteType _ _ h₁ h₂
  have : Epi (factorThruImageSubobject (biprod.desc K₁.ι K₂.ι)) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  have hI := Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (factorThruImageSubobject (biprod.desc K₁.ι K₂.ι)) hsum
  rw [← subobject_mk_sup_ι] at hI
  exact Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (Subobject.underlyingIso _).hom hI

end Sup

end AlgebraicGeometry.Space

end
