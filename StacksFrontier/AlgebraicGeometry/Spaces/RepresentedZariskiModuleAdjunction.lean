module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDirectImage
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# `ε^* ⊣ ε_*` on modules of a representable algebraic space

Let `X = yoneda.obj U` be the algebraic space represented by an object `U` of the big fppf site
over `S`, with underlying scheme `X_0`, and let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. This
file identifies the direct image `ε_*` of sheaves of modules with restriction along the
equivalence of small étale sites followed by restriction to the Zariski opens of `X_0`, and
deduces from Descent, Proposition 03DX (2) for the scheme `X_0` that the adjunction `ε^* ⊣ ε_*`
is an equivalence on quasi-coherent modules.

## Main definitions

* `AlgebraicGeometry.Space.representedModuleEquivalence`: the equivalence of module categories
  given by restriction along the equivalence of small étale sites, as Mathlib's equivalence of
  pushforwards.
* `Space.representedZariskiModulePushforwardIsoRepresentedZariskiModuleAdjunction`: `ε_*` is
  that restriction followed by `AlgebraicGeometry.SmallEtale.restrictModule`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **The unit is invertible where the left adjoint is fully faithful.**  If `L` is bijective on
morphisms between objects of a class `P`, and both `X` and `R(L X)` belong to `P`, then the unit
`X ⟶ R(L X)` is an isomorphism. -/
theorem isIso_unit_app_of_bijective_representedZariskiModuleAdjunction (P : ObjectProperty C)
    (hP : ∀ ⦃Y X : C⦄, P Y → P X → Function.Bijective (fun g : Y ⟶ X => L.map g))
    {X : C} (hX : P X) (hRLX : P (R.obj (L.obj X))) : IsIso (adj.unit.app X) := by
  obtain ⟨g, hg⟩ := (hP hRLX hX).2 (adj.counit.app (L.obj X))
  have hg' : L.map g = adj.counit.app (L.obj X) := hg
  have ht := adj.left_triangle_components X
  refine ⟨g, (hP hX hX).1 ?_, ?_⟩
  · change L.map (adj.unit.app X ≫ g) = L.map (𝟙 X)
    rw [Functor.map_comp, hg', ht, Functor.map_id]
  · apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      ht, hg']
    simp

/-- **The counit is invertible at an object isomorphic to `L X` when the unit is invertible at
`X`**, by the triangle identity. -/
theorem isIso_counit_app_of_isIso_unit_app_representedZariskiModuleAdjunction {X : C}
    [IsIso (adj.unit.app X)] {Y : D} (e : L.obj X ≅ Y) : IsIso (adj.counit.app Y) := by
  have h₁ : IsIso (adj.counit.app (L.obj X)) := by
    have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by
      rw [adj.left_triangle_components X]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (L.map (adj.unit.app X)) _
  have hn := adj.counit.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← IsIso.eq_inv_comp] at hn
  rw [hn]
  infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.NatIso

variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}

/-- Bijectivity of a functor on the morphisms between two objects is invariant under natural
isomorphism of functors. -/
theorem bijective_map_of_iso_representedZariskiModuleAdjunction (e : F ≅ G) {X Y : C}
    (h : Function.Bijective (fun g : X ⟶ Y => G.map g)) :
    Function.Bijective (fun g : X ⟶ Y => F.map g) := by
  have key : ∀ g : X ⟶ Y, F.map g = e.hom.app X ≫ G.map g ≫ e.inv.app Y := fun g => by
    rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  refine ⟨fun g₁ g₂ hg => h.1 ?_, fun k => ?_⟩
  · have hg' : F.map g₁ = F.map g₂ := hg
    rw [key, key, cancel_epi] at hg'
    exact (cancel_mono (e.inv.app Y)).1 hg'
  · obtain ⟨g, hg⟩ := h.2 (e.inv.app X ≫ k ≫ e.hom.app Y)
    have hg' : G.map g = e.inv.app X ≫ k ≫ e.hom.app Y := hg
    exact ⟨g, (key g).trans (by rw [hg']; simp)⟩

end CategoryTheory.NatIso

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The equivalence of small étale sites of Stacks 04M0 as a morphism of ringed sites
`(X_étale, 𝒪_X) ⟶ (X_{0,étale}, 𝒪)`, presented by the inverse of the comparison. -/
def representedSmallEtaleRingedSiteHomRepresentedZariskiModuleAdjunction :
    RingedSite.HomGeneral (smallEtaleRingedSite B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property) where
  u := (representedSmallEtaleEquivalence B S hS U).inverse
  isMorphismOfSites := isMorphismOfSites_representedSmallEtaleEquivalence_inverse B S hS U
  fsharp := representedCommRingStructureMapRepresentedZariskiRingedToposHom B S hS U

/-- **The direct image of modules along the equivalence of small étale sites is restriction
along the inverse of the comparison**, `AlgebraicGeometry.Space.representedModuleRestriction`. -/
def representedSmallEtalePushforwardModulesIsoRepresentedZariskiModuleAdjunction :
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom
        B S hS U).pushforwardModules ≅
      representedModuleRestriction B S hS U :=
  (representedSmallEtaleRingedSiteHomRepresentedZariskiModuleAdjunction
    B S hS U).pushforwardToposIsoGeneral

/-- **`ε_*` is restriction along the equivalence of small étale sites followed by restriction to
the Zariski opens of `X_0`**, `AlgebraicGeometry.SmallEtale.restrictModule`. -/
def representedZariskiModulePushforwardIsoRepresentedZariskiModuleAdjunction :
    representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U ≅
      representedModuleRestriction B S hS U ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property :=
  RingedToposHom.pushforwardModulesCompIso
      (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom
        (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
        U.left.property) ≪≫
    Functor.isoWhiskerRight
      (representedSmallEtalePushforwardModulesIsoRepresentedZariskiModuleAdjunction B S hS U) _ ≪≫
    Functor.isoWhiskerLeft _ (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom
      (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
      U.left.property).pushforwardToposIsoGeneral

/-- **`ε^*` is the associated-module functor followed by transport along the equivalence of small
étale sites**, `AlgebraicGeometry.Space.representedAssociatedModule`. -/
def representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction :
    representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U ≅
      representedAssociatedModule B S hS U (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  RingedToposHom.pullbackModulesCompIso
      (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom
        (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
        U.left.property) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom
          (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
          U.left.property)) ≪≫
      _root_.AlgebraicGeometry.SmallEtale.assocIso (associatedBigEtaleSite B)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property) _ ≪≫
    Functor.isoWhiskerLeft _ (((RingedToposHom.pullbackAdjPushforwardModules
      (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).ofNatIsoRight
        (representedSmallEtalePushforwardModulesIsoRepresentedZariskiModuleAdjunction
          B S hS U)).leftAdjointUniq
      (representedModuleEquivalence.{u, u} B S hS U).toAdjunction)

/-- Restriction along the equivalence of small étale sites carries quasi-coherent modules to
quasi-coherent modules. -/
theorem isQuasicoherentOnSite_representedModuleRestriction_obj_representedZariskiModuleAdjunction
    (H : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (hH : H.IsQuasicoherentOnSite) :
    ((representedModuleRestriction B S hS U).obj H).IsQuasicoherentOnSite := by
  rw [← isQuasicoherentOnSite_representedSmallEtaleModule_iff]
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((representedModuleEquivalence.{u, u} B S hS U).counitIso.app H).symm hH

/-- **`ε_*` carries quasi-coherent modules to quasi-coherent modules.** -/
theorem isQuasicoherent_representedZariskiModulePushforward_obj_representedZariskiModuleAdjunction
    (H : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (hH : H.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      (R := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).ringCatSheaf)
      ((representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U).obj H) :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent _)
    ((representedZariskiModulePushforwardIsoRepresentedZariskiModuleAdjunction B S hS U).app H).symm
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property _
      (isQuasicoherentOnSite_representedModuleRestriction_obj_representedZariskiModuleAdjunction
        B S hS U H hH))

/-- `ε^*` carries quasi-coherent modules to quasi-coherent modules. -/
theorem
    isQuasicoherentOnSite_representedZariskiModulePullback_obj_representedZariskiModuleAdjunction
    (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules)
    (hF : F.IsQuasicoherent) :
    ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).obj
      F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
      B S hS U).app F).symm
    (isQuasicoherentOnSite_representedAssociatedModule B S hS U _ F hF)

/-- `ε^*` is bijective on morphisms between quasi-coherent modules. -/
theorem bijective_representedZariskiModulePullback_map_representedZariskiModuleAdjunction
    {F F' : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules}
    (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) :
    Function.Bijective (fun g : F ⟶ F' =>
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map g) := by
  let ff := fullyFaithfulRepresentedAssociatedModuleQcoh B S hS U
  refine NatIso.bijective_map_of_iso_representedZariskiModuleAdjunction
    (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
      B S hS U) ?_
  refine ⟨fun g₁ g₂ h => ?_, fun k => ?_⟩
  · have := ff.map_injective (X := ⟨F, hF⟩) (Y := ⟨F', hF'⟩)
      (f := ObjectProperty.homMk g₁) (g := ObjectProperty.homMk g₂) h
    exact congrArg (fun k : (⟨F, hF⟩ : (SheafOfModules.isQuasicoherent _).FullSubcategory) ⟶
      ⟨F', hF'⟩ => k.hom) this
  · exact ⟨(ff.preimage (X := ⟨F, hF⟩) (Y := ⟨F', hF'⟩) k).hom,
      ff.map_preimage (X := ⟨F, hF⟩) (Y := ⟨F', hF'⟩) k⟩

/-- The adjunction `ε^* ⊣ ε_*` on sheaves of modules. -/
abbrev representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction :
    representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U ⊣
      representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U :=
  RingedToposHom.pullbackAdjPushforwardModules
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **The unit `F ⟶ ε_* ε^* F` is an isomorphism for a quasi-coherent `𝒪_{X_0}`-module `F`.** -/
theorem isIso_representedZariskiModuleAdjunction_unit_app_representedZariskiModuleAdjunction
    (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules)
    (hF : F.IsQuasicoherent) :
    IsIso ((representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction
      B S hS U).unit.app F) :=
  Adjunction.isIso_unit_app_of_bijective_representedZariskiModuleAdjunction
    (representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction B S hS U)
    (SheafOfModules.isQuasicoherent
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).ringCatSheaf)
    (fun _ _ hY hX =>
      bijective_representedZariskiModulePullback_map_representedZariskiModuleAdjunction
        B S hS U hY hX) hF
    (isQuasicoherent_representedZariskiModulePushforward_obj_representedZariskiModuleAdjunction
      B S hS U _
      (isQuasicoherentOnSite_representedZariskiModulePullback_obj_representedZariskiModuleAdjunction
        B S hS U F hF))

/-- **Stacks 03DX (2) for `ε^*`**: every quasi-coherent `𝒪_X`-module is `ε^* F` for a
quasi-coherent `𝒪_{X_0}`-module `F`. -/
theorem exists_iso_representedZariskiModulePullback_obj_representedZariskiModuleAdjunction
    (H : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (hH : H.IsQuasicoherentOnSite) :
    ∃ (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules)
      (_ : F.IsQuasicoherent),
      Nonempty ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).obj F ≅
        H) := by
  obtain ⟨⟨F, hF⟩, ⟨e⟩⟩ :=
    _root_.AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule
      (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
      U.left.property _
      (isQuasicoherentOnSite_representedModuleRestriction_obj_representedZariskiModuleAdjunction
        B S hS U H hH)
  exact ⟨F, hF,
    ⟨(representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS U).app F ≪≫
      (representedModulePushforward B S hS U).mapIso e ≪≫
      (representedModuleEquivalence.{u, u} B S hS U).counitIso.app H⟩⟩

/-- **The counit `ε^* ε_* H ⟶ H` is an isomorphism for a quasi-coherent `𝒪_X`-module `H`.** -/
theorem isIso_representedZariskiModuleAdjunction_counit_app_representedZariskiModuleAdjunction
    (H : SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)))
    (hH : H.IsQuasicoherentOnSite) :
    IsIso ((representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction
      B S hS U).counit.app H) := by
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    exists_iso_representedZariskiModulePullback_obj_representedZariskiModuleAdjunction
      B S hS U H hH
  have :=
    isIso_representedZariskiModuleAdjunction_unit_app_representedZariskiModuleAdjunction
      B S hS U F hF
  exact Adjunction.isIso_counit_app_of_isIso_unit_app_representedZariskiModuleAdjunction
    (representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction B S hS U) e

end AlgebraicGeometry.Space
