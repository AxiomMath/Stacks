module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnitOfTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction

/-!
# The structure sheaf and the free modules lie in `LQCoh^fbc(𝒪_𝒳)`

For a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}`:

* the restriction of the structure sheaf `𝒪_𝒳` to the small étale site of the scheme `U` below an
  object is the structure sheaf of `U_ét`;
* for every arrow `φ` of `𝒳` the comparison map `c_φ` of Stacks 06WC of `𝒪_𝒳` is an isomorphism
  already of presheaves: the pullback of the unit module along a functor of small étale sites
  sending the final object to a final object is the unit module
  (`PresheafOfModules.isIso_homEquiv_symm_unit`);

so `𝒪_𝒳` lies in `LQCoh^fbc(𝒪_𝒳)`. With the closure of `LQCoh^fbc(𝒪_𝒳)` under colimits
(Stacks 0771 (5)), in the étale and in the fppf modules, so do the free modules.

## Main results

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleUnitIso`
* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_unit`: the comparison maps of
  the structure sheaf are isomorphisms, for every arrow.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_unit`: the structure
  sheaf lies in `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChange`
  and
  `isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChangeFppf`:
  **Stacks 0771 (5)**, closure under colimits in the étale and in the fppf modules.
* `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_free` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeFppfModules_free`: the free
  modules lie in `LQCoh^fbc(𝒪_𝒳)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The map from the restriction of the structure sheaf of `𝒳` to the small étale site of the
scheme below `x` to the structure sheaf of that small étale site: the identification of
Stacks 06W9, read as a map of modules. -/
def restrictModuleToSmallEtaleUnitHom (x : 𝒳) :
    restrictModuleToSmallEtale B E h S hS p hp x τ hτ
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj) ⟶
      PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj :=
  let e := localStructurePresheafIso B E h S hS p hp x τ hτ
  PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (e.inv.app W).hom.toAddMonoidHom
      naturality := fun W W' f => by
        ext n
        exact ConcreteCategory.congr_hom (e.inv.naturality f) n }
    (fun W r n => by
      let n' : (restrictToSmallEtale B E h S hS p hp x
        (ringStructureSheafCore B S hS p hp τ hτ).obj).obj W := n
      change e.inv.app W (e.hom.app W r * n') = r * e.inv.app W n'
      rw [map_mul]
      congr 1
      exact ConcreteCategory.congr_hom (e.hom_inv_id_app W) r)

/-- The inverse of `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleUnitHom`. -/
def restrictModuleToSmallEtaleUnitInv (x : 𝒳) :
    PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj ⟶
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj) :=
  let e := localStructurePresheafIso B E h S hS p hp x τ hτ
  PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (e.hom.app W).hom.toAddMonoidHom
      naturality := fun W W' f => by
        ext n
        exact ConcreteCategory.congr_hom (e.hom.naturality f) n }
    (fun W r n => by
      let n' : (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj.obj W := n
      change e.hom.app W (r * n') = e.hom.app W r * e.hom.app W n'
      exact map_mul _ r n')

/-- On sections, `restrictModuleToSmallEtaleUnitHom` is the inverse of
`localStructurePresheafIso`. -/
theorem restrictModuleToSmallEtaleUnitHom_app (x : 𝒳) (W) (n) :
    (restrictModuleToSmallEtaleUnitHom B E h S hS p hp τ hτ x).app W n =
      (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app W n :=
  rfl

/-- On sections, `restrictModuleToSmallEtaleUnitInv` is the forward map of
`localStructurePresheafIso`. -/
theorem restrictModuleToSmallEtaleUnitInv_app (x : 𝒳) (W) (n) :
    (restrictModuleToSmallEtaleUnitInv B E h S hS p hp τ hτ x).app W n =
      (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app W n :=
  rfl

/-- **The restriction of the structure sheaf of `𝒳` to the small étale site of the scheme `U`
below an object is the structure sheaf of `U_ét`**, through the identification of Stacks 06W9 of
the restricted structure sheaf with the structure sheaf of the small étale site. -/
def restrictModuleToSmallEtaleUnitIso (x : 𝒳) :
    restrictModuleToSmallEtale B E h S hS p hp x τ hτ
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj) ≅
      PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj where
  hom := restrictModuleToSmallEtaleUnitHom B E h S hS p hp τ hτ x
  inv := restrictModuleToSmallEtaleUnitInv B E h S hS p hp τ hτ x
  hom_inv_id := PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun n => by
    let n' : (restrictToSmallEtale B E h S hS p hp x
      (ringStructureSheafCore B S hS p hp τ hτ).obj).obj W := n
    change (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app W
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app W n') = n'
    exact ConcreteCategory.congr_hom
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv_hom_id_app W) n')
  inv_hom_id := PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun n => by
    let n' : (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj.obj W := n
    change (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app W
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app W n') = n'
    exact ConcreteCategory.congr_hom
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).hom_inv_id_app W) n')

section Comparison

variable {x y : 𝒳} (φ : x ⟶ y)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- The map of unit modules underlying the map of structure sheaves `a_{small}^♯` of
Stacks 06WC: the map out of the unit module corresponding to the section `1` of the direct image
of the unit module. On sections it is `a_{small}^♯` itself. -/
def unitSmallEtaleStructureComparison :
    PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj y).left.1
        (contains_base B E h S hS p y)).obj ⟶
      (PresheafOfModules.pushforward.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj) :=
  (PresheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun X => (show (PresheafOfModules.unit (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj).obj
            (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj X.unop))
          from (1 : (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj.obj
              (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
                X.unop)))))
      (fun X Y f => PresheafOfModules.unit_map_one _ _))

/-- On sections, `unitSmallEtaleStructureComparison` is the map of structure sheaves
`smallEtaleStructureComparison`. -/
theorem unitSmallEtaleStructureComparison_app (X)
    (m : (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj.obj X) :
    (unitSmallEtaleStructureComparison B E h S hS p hp τ hτ φ).app X m =
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app X m := by
  show (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app X m * 1 = _
  exact mul_one _

/-- **The comparison map `c_φ` of Stacks 06WC of the structure sheaf of `𝒳` is an isomorphism,
for every arrow `φ` of `𝒳`**, already as a morphism of presheaves of modules: the base change of
small étale sites sends the final object to a final object, so the pullback of the unit module
is the unit module (`PresheafOfModules.isIso_homEquiv_symm_unit`), and the restrictions of the
structure sheaf of `𝒳` are the structure sheaves of the small étale sites. -/
theorem isIso_restrictModulePullbackComparison_unit :
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ
      (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj)) := by
  have hunit := PresheafOfModules.isIso_homEquiv_symm_unit
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
    (SmallEtale.finalIsTerminal E (p.obj y).left.1 (contains_base B E h S hS p y))
    (smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ))
    (unitSmallEtaleStructureComparison B E h S hS p hp τ hτ φ)
    (fun X => (unitSmallEtaleStructureComparison_app B E h S hS p hp τ hτ φ X 1).trans
      (map_one ((smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app X).hom))
  refine (PresheafOfModules.isIso_homEquiv_symm_iff_of_sections rfl
    (restrictModuleToSmallEtaleUnitIso B E h S hS p hp τ hτ y)
    (restrictModuleToSmallEtaleUnitIso B E h S hS p hp τ hτ x)
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ _)
    (unitSmallEtaleStructureComparison B E h S hS p hp τ hτ φ) ?_).2 hunit
  intro W n
  obtain ⟨φ', hfac, hbase⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W.unop
  have hmod : (restrictionPushforwardComparison B E h S hS p hp φ
      (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf).app W =
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf.map
          φ'.op :=
    restrictionPushforwardComparison_app B E h S hS p hp φ _ W.unop φ' hfac hbase
  have hring : (restrictionPushforwardComparison B E h S hS p hp φ
      (ringStructureSheafCore B S hS p hp τ hτ).obj).app W =
        (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op :=
    restrictionPushforwardComparison_app B E h S hS p hp φ _ W.unop φ' hfac hbase
  let e := localStructurePresheafIso B E h S hS p hp y τ hτ
  let n' : (restrictToSmallEtale B E h S hS p hp y
    (ringStructureSheafCore B S hS p hp τ hτ).obj).obj W := n
  show (unitSmallEtaleStructureComparison B E h S hS p hp τ hτ φ).app W (e.inv.app W n') =
    (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app _
      ((restrictionPushforwardComparison B E h S hS p hp φ
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf).app W n)
  rw [unitSmallEtaleStructureComparison_app]
  have happ : (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app W (e.inv.app W n') =
      (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app _
        ((restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app W (e.hom.app W (e.inv.app W n'))) :=
    rfl
  have hcancel : e.hom.app W (e.inv.app W n') = n' := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
    rfl
  have key : (restrictionPushforwardComparison B E h S hS p hp φ
      (ringStructureSheafCore B S hS p hp τ hτ).obj).app W n' =
      (restrictionPushforwardComparison B E h S hS p hp φ
        (PresheafOfModules.unit (ringStructureSheafCore B S hS p hp τ hτ).obj).presheaf).app W n :=
    (ConcreteCategory.congr_hom hring n').trans (ConcreteCategory.congr_hom hmod n).symm
  rw [happ, hcancel]
  exact congrArg ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app _) key

end Comparison

section Members

/-- **The structure sheaf of `𝒳` lies in `LQCoh^fbc(𝒪_𝒳)`**: it is an étale sheaf, its restrictions
to the small étale sites are their structure sheaves, which are quasi-coherent, and its
comparison maps `c_φ` are isomorphisms
(`AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_unit`). -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_unit :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))).val := by
  refine ⟨⟨(SheafOfModules.unit _).isSheaf, fun x => ?_⟩, ?_⟩
  · have hM := restrictModuleToSmallEtale_isSheaf B E h S hS p hp x _
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))).isSheaf
    refine ⟨hM, ?_⟩
    let e : (SheafOfModules.forget _).obj (⟨_, hM⟩ : SheafOfModules.{u} (SmallEtale.structureSheaf E
        (p.obj x).left.1 (contains_base B E h S hS p x))) ≅
        (SheafOfModules.forget _).obj (SheafOfModules.unit (SmallEtale.structureSheaf E
          (p.obj x).left.1 (contains_base B E h S hS p x))) :=
      restrictModuleToSmallEtaleUnitIso B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) x
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((SheafOfModules.fullyFaithfulForget _).preimageIso e).symm
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  · exact hasSheafFlatBaseChangeProperty_of_hasFlatBaseChangeProperty B E h S hS p hp _ _ _
      (fun φ _ => isIso_restrictModulePullbackComparison_unit B E h S hS p hp _ _ φ)

/-- **Stacks 0771 (5) / 0764 (4) for `Mod(𝒳_ét, 𝒪_𝒳)`: `LQCoh^fbc(𝒪_𝒳)` is closed under colimits**
computed in the étale sheaves of modules, for every shape along which abelian groups, modules and
modules on schemes have colimits. Local quasi-coherence is closed under them (Stacks 06WM (1)),
and the restrictions to the small étale sites and the sheafified pullbacks `f_{small}^*` preserve
them, so the comparison maps `c_φ` of a colimit are the colimits of the comparison maps. -/
theorem isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChange
    (K : Type u) [SmallCategory K]
    [HasColimitsOfShape K AddCommGrpCat.{u}]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [∀ U : Scheme.{u}, HasColimitsOfShape K (SheafOfModules.{u} U.ringCatSheaf)] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (C := SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
        F.val) K where
  colimitsOfShape_le := by
    rintro F ⟨c⟩
    have := hasSheafify_etaleAssociatedTopology B S hS p hp
    have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    have hQ := isClosedUnderColimitsOfShape_isLocallyQuasicoherent B E h S hS p hp K
    refine ⟨(isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).prop_of_isColimit c.isColimit
      fun k => (c.prop_diag_obj k).1, fun {x y} φ hφ => ?_⟩
    have hx := restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F.val F.isSheaf
    refine (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp _ _ φ F.val
      hx).1 ?_
    let α := sheafifiedRestrictModulePullbackComparisonNatTrans B E h S hS p hp φ
    have : (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).IsLeftAdjoint :=
      (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).isLeftAdjoint
    have hT : IsColimit ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).mapCocone c.cocone) :=
      isColimitOfPreserves _ c.isColimit
    have hR : IsColimit ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).mapCocone
        c.cocone) :=
      isColimitOfPreserves _ c.isColimit
    have hk : ∀ k, IsIso (α.app (c.diag.obj k)) := fun k => by
      have hk' := (c.prop_diag_obj k).2 φ hφ
      exact (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp _ _ φ
        (c.diag.obj k).val (restrictModuleToSmallEtale_isSheaf B E h S hS p hp x _
          (c.diag.obj k).isSheaf)).2 hk'
    have : ∀ k, IsIso ((Functor.whiskerLeft c.diag α).app k) := hk
    have : IsIso (Functor.whiskerLeft c.diag α) := NatIso.isIso_of_isIso_app _
    have he : (IsColimit.coconePointsIsoOfNatIso hT hR
        (asIso (Functor.whiskerLeft c.diag α))).hom = α.app c.cocone.pt :=
      hT.hom_ext fun k => by
        rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
        exact (α.naturality (c.cocone.ι.app k)).symm
    show IsIso (α.app c.cocone.pt)
    rw [← he]
    infer_instance

end Members

section Fppf

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0771 (5) for `Mod(𝒪_𝒳)`: `LQCoh^fbc(𝒪_𝒳)` is closed under colimits computed in the
fppf modules.** The colimit computed in the étale modules lies in `LQCoh^fbc(𝒪_𝒳)`, hence is an
fppf sheaf (Stacks 0771 (1)), hence is the colimit computed in the fppf modules. -/
theorem isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChangeFppf
    (K : Type u) [SmallCategory K]
    [HasColimitsOfShape K AddCommGrpCat.{u}]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [∀ U : Scheme.{u}, HasColimitsOfShape K (SheafOfModules.{u} U.ringCatSheaf)] :
    (locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p
        hp).IsClosedUnderColimitsOfShape
      K where
  colimitsOfShape_le := by
    rintro X ⟨c⟩
    have : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u} :=
      hasSheafify_etaleAssociatedTopology B S hS p hp
    have : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    let ε := fppfToEtaleComparison B S hS p hp
    let Pe : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.ringOfLe
        (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp)))
            :=
      fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
        F.val
    have : Pe.IsClosedUnderColimitsOfShape K :=
      isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChange B E h S hS p hp K
    have : Pe.IsWeakSerreClass :=
      isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS p hp
    let ff := Stacks.SheafOfModules.comparisonPushforwardFullyFaithful.{v, w, u, u}
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp)
    have : ε.Full := ff.full
    have : ε.Faithful := ff.faithful
    obtain ⟨cE, ⟨hcE⟩⟩ : ∃ cE : Cocone (c.diag ⋙ ε), Nonempty (IsColimit cE) :=
      ⟨_, ⟨colimit.isColimit _⟩⟩
    have hPE : Pe cE.pt := Pe.prop_of_isColimit hcE fun k => c.prop_diag_obj k
    have hsh := isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp
      cE.pt.val hPE
    let c' : fppfSiteModules B S hS p hp := ⟨cE.pt.val, hsh⟩
    have hpre : ∀ k, ε.map (ff.preimage (X := c.diag.obj k) (Y := c') (cE.ι.app k)) =
        cE.ι.app k := fun k => ff.map_preimage _
    let co : Cocone c.diag :=
      { pt := c'
        ι :=
          { app := fun k => ff.preimage (X := c.diag.obj k) (Y := c') (cE.ι.app k)
            naturality := fun k k' f => ε.map_injective (by
              show ε.map (c.diag.map f ≫ ff.preimage (X := c.diag.obj k') (Y := c')
                  (cE.ι.app k')) = ε.map (ff.preimage (X := c.diag.obj k) (Y := c')
                    (cE.ι.app k) ≫ 𝟙 c')
              rw [ε.map_comp, ε.map_comp, hpre, hpre, ε.map_id]
              exact (cE.w f).trans (Category.comp_id _).symm) } }
    have hco : IsColimit co := by
      refine isColimitOfReflects ε (IsColimit.ofIsoColimit hcE ?_)
      exact Cocone.ext (Iso.refl _) fun k => by
        show cE.ι.app k ≫ 𝟙 _ = ε.map (ff.preimage (X := c.diag.obj k) (Y := c')
          (cE.ι.app k))
        rw [Category.comp_id, hpre]
    exact Pe.prop_of_iso (ε.mapIso (IsColimit.coconePointUniqueUpToIso hco c.isColimit)) hPE

/-- **The structure sheaf lies in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`.** -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_unit :
    locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp
      (SheafOfModules.unit (fppfSiteRingSheaf B S hS p hp)) :=
  isLocallyQuasicoherentWithSheafFlatBaseChange_unit B E h S hS p hp

/-- **The free modules lie in `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`**: a free module is a coproduct of
copies of the structure sheaf. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_free (I : Type u) :
    locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules B E h S hS p hp
      (SheafOfModules.free (R := fppfSiteRingSheaf B S hS p hp) I) := by
  have := isClosedUnderColimitsOfShape_locallyQuasicoherentSheafFlatBaseChangeFppf B E h S hS p hp
    (Discrete I)
  exact ObjectProperty.prop_of_isColimit _ (colimit.isColimit _)
    fun _ => locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_unit B E h S hS p hp

end Fppf

section AlgebraicStacks

/-- **The free modules on the fppf site of an algebraic stack lie in `LQCoh^fbc(𝒪_𝒳)`**, with the
flat base change property of Stacks 0762 read with the pullback of sheaves. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_free
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (I : Type u) :
    letI := FlatFppf.hasSheafify_fppf_addCommGrpCat B S hS 𝒳
    letI := FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat B S hS 𝒳
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳
      (SheafOfModules.free (R := FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf) I) :=
  let := FlatFppf.hasSheafify_fppf_addCommGrpCat B S hS 𝒳
  let := FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat B S hS 𝒳
  locallyQuasicoherentSheafFlatBaseChangeFppfSiteModules_free B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids I

end AlgebraicStacks

end AlgebraicGeometry.Stack
