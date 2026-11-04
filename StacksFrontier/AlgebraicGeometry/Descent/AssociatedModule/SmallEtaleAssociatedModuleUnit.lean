module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackIsoAdjunct
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit

/-!
# The unit characterisation of Stacks 070S on the small étale site

The identification `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf` of the
associated module `𝓕^a` with the presheaf of [Stacks, Tag 03DS] restricted to the small étale site
is characterised by its transpose across the associated-module adjunction of [Stacks, Tag 03DU]
(4): that transpose is `AlgebraicGeometry.SmallEtale.sectionsUnit`, the map which sends a section
of `𝓕` over an open `U` of `S` to its pullback to the open subscheme `U`.

## Main results

* `SmallEtale.forget_map_associatedModuleAdjunction_unit_comp_isoSectionsPresheaf`: the transpose
  of `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf` across the
  associated-module adjunction is `AlgebraicGeometry.SmallEtale.sectionsUnit`.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem unit_sections_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ : C}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₃ ⟶ O₄) (su : O₁ ⟶ O₄) (etam : O₄ ⟶ O₃)
    (hkey : su ≫ etam = a ≫ b) (hinv : etam ≫ c = 𝟙 O₄) :
    a ≫ b ≫ c = su := by
  rw [← Category.assoc, ← hkey, Category.assoc, hinv, Category.comp_id]

/-- **The identification of `𝓕^a` with the presheaf of Stacks 03DS is pinned by the unit of the
associated-module adjunction.**  Transposing the identification across the adjunction
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` of **Stacks 03DU (4)** — that is,
prefixing the unit and pushing forward — gives
`AlgebraicGeometry.SmallEtale.sectionsUnit`, the map which sends a section of `𝓕` over an open
`U` of `S` to its pullback to the open subscheme `U`. -/
public theorem forget_map_associatedModuleAdjunction_unit_comp_isoSectionsPresheaf
    (F : S.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.forget S.ringCatSheaf).map ((associatedModuleAdjunction B S hS).unit.app F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          (associatedModuleIsoSectionsPresheaf B S hS F).hom =
      sectionsUnit B S hS F := by
  have := isIso_sheafificationAdjunction_unit_app B S hS (sectionsPresheafOfModules B S hS F)
    (isSheaf_sectionsPresheafOfModules B S hS F)
  set Pf := PresheafOfModules.pushforward.{u} (structureMap B S hS).hom with hPf
  set Phi := SheafOfModules.forget (structureSheaf B S hS) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj) with hPhi
  set sc := sectionsComparison B S hS F with hsc
  set esp := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F) with hesp
  set nu := (SheafOfModules.pullbackIso.{u} (structureMap B S hS)).hom.app F ≫
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map sc with hnu
  have hcancel : (SheafOfModules.pullbackIso.{u} (structureMap B S hS)).inv.app F ≫ nu =
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map sc := by
    rw [hnu, ← Category.assoc,
      show (SheafOfModules.pullbackIso.{u} (structureMap B S hS)).inv.app F ≫
          (SheafOfModules.pullbackIso.{u} (structureMap B S hS)).hom.app F = 𝟙 _ from
        ((SheafOfModules.pullbackIso.{u} (structureMap B S hS)).app F).inv_hom_id,
      Category.id_comp]
  have key := SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app
    (structureMap B S hS) F
    ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
      (sectionsPresheafOfModules B S hS F)) nu
  have key2 := (congrArg (fun t =>
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).homEquiv
        F.val _
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B S hS).obj)).unit.app
            ((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj F.val) ≫
          Phi.map t)) hcancel).symm.trans key
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf B S hS).obj)).unit.naturality sc
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have key3 := (congrArg (fun t =>
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).homEquiv
        F.val _ t) hnat).trans key2
  have hL : (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (structureMap B S hS).hom).homEquiv F.val _ (sc ≫ esp) =
      sectionsUnit B S hS F ≫ Pf.map esp :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      ((congrArg (fun t => (PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (structureMap B S hS).hom).unit.app F.val ≫ t) (Pf.map_comp sc esp)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ Pf.map esp)
            (unit_comp_map_sectionsComparison B S hS F))))
  have hR : (SheafOfModules.forget S.ringCatSheaf).map
        ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).homEquiv F
          ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
            (sectionsPresheafOfModules B S hS F)) nu) =
      (SheafOfModules.forget S.ringCatSheaf).map
          ((associatedModuleAdjunction B S hS).unit.app F) ≫ Pf.map (Phi.map nu) :=
    (congrArg (SheafOfModules.forget S.ringCatSheaf).map
      (Adjunction.homEquiv_unit _ _ _ _)).trans
        ((SheafOfModules.forget S.ringCatSheaf).map_comp _ _)
  have hkey := hL.symm.trans (key3.trans hR)
  have hinv : Pf.map esp ≫ Pf.map (inv esp) = 𝟙 _ :=
    (Pf.map_comp esp (inv esp)).symm.trans
      ((congrArg Pf.map (IsIso.hom_inv_id esp)).trans (Pf.map_id _))
  show (SheafOfModules.forget S.ringCatSheaf).map
        ((associatedModuleAdjunction B S hS).unit.app F) ≫
      Pf.map (Phi.map nu ≫ inv esp) = sectionsUnit B S hS F
  refine Eq.trans (congrArg (fun t => (SheafOfModules.forget S.ringCatSheaf).map
      ((associatedModuleAdjunction B S hS).unit.app F) ≫ t)
    (Pf.map_comp (Phi.map nu) (inv esp))) ?_
  exact unit_sections_algebra _ _ _ _ _ hkey hinv

end AlgebraicGeometry.SmallEtale

end
