module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalExtendedCech
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction

/-!
# The extended alternating Čech complex along the iterated-slice equivalence

Let `(𝒞, 𝒪)` be a ringed site, `U` an object of `𝒞` and `W` an object of `𝒞/U`. The iterated
slice `(𝒞/U)/W` and the slice `𝒞/W.left` are equivalent sites
(`CategoryTheory.Over.iteratedSliceEquiv`), and the structure sheaves match on the nose. This file
transports the extended alternating Čech complex of a finite family of global sections of the
structure sheaf of `(𝒞/U)/W` along the induced equivalence of categories of sheaves of modules,
the pushforward along `CategoryTheory.Over.iteratedSliceBackward`, to the Čech complex of the
transported family on `𝒞/W.left`, compatibly with the augmentations.

The proofs are those of `CechGlobalSliceAway.lean` and `CechSliceRestriction.lean` for the
restriction to a slice, with the iterated-slice transport in place of that restriction: the
transport carries the structure sheaf to the structure sheaf on the nose, preserves colimits
(it is an equivalence), and carries multiplication by a global section to multiplication by the
transported section, so it carries the sequential colimit presenting `𝒪_f` to the one presenting
the localization at the transported section.

## Main definitions

* `AlgebraicGeometry.RingedSite.sliceTransport`: the pushforward of sheaves of modules from
  `(𝒞/U)/W` to `𝒞/W.left` along `CategoryTheory.Over.iteratedSliceBackward`.
* `AlgebraicGeometry.RingedSite.globalSectionTransport`: a global section of the structure sheaf
  of `(𝒞/U)/W`, read on `𝒞/W.left`.
* `AlgebraicGeometry.RingedSite.awayModuleTransportIso`: the transport of `𝒪_f` is `𝒪_{f'}`.
* `AlgebraicGeometry.RingedSite.extendedAlternatingCechTransportIso`: the transport of `Č(f)` is
  `Č(f')`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) (U : X.C) (W : Over U)

/-- **The iterated-slice transport of sheaves of modules**, from the iterated slice `(𝒞/U)/W` to
the slice `𝒞/W.left`: the pushforward along `CategoryTheory.Over.iteratedSliceBackward`, which
is the inverse of the equivalence
`Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`. -/
abbrev sliceTransport :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O) :=
  (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse

/-- The iterated-slice transport is an equivalence of categories. -/
instance isEquivalence_sliceTransport : (sliceTransport X U W).IsEquivalence :=
  (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).isEquivalence_inverse

/-- The iterated-slice transport is additive. -/
instance additive_sliceTransport : (sliceTransport X U W).Additive where
  map_add := rfl

/-- The transport carries the structure sheaf to the structure sheaf, on the nose. -/
theorem sliceTransport_obj_unit :
    (sliceTransport X U W).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)) =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O) :=
  rfl

/-- A global section of the structure sheaf of the iterated slice `(𝒞/U)/W`, read on the slice
`𝒞/W.left`: its value over `T` is its value over the image of `T` in the iterated slice. -/
def globalSectionTransport
    (h : Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections ((X.over W.left).O.obj ⋙ forget CommRingCat.{u}) :=
  (Presheaf.globalSectionsEquivSections _).symm
    { val := fun T => (Presheaf.globalSectionsEquivSections _ h).1
        (op (W.iteratedSliceBackward.obj T.unop))
      property := fun {_ _} f => (Presheaf.globalSectionsEquivSections _ h).2
        (W.iteratedSliceBackward.map f.unop).op }

/-- The value of the transported global section over `T` is the value of the original section
over the image of `T` in the iterated slice. -/
@[simp]
theorem globalSectionVal_globalSectionTransport
    (h : Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u}))
    (T : (Over W.left)ᵒᵖ) :
    globalSectionVal (globalSectionTransport X U W h) T =
      globalSectionVal h (op (W.iteratedSliceBackward.obj T.unop)) := by
  show (Presheaf.globalSectionsEquivSections _
    ((Presheaf.globalSectionsEquivSections _).symm _)).1 T = _
  rw [Equiv.apply_symm_apply]

section Smul

variable [HasWeakSheafify ((X.over U).over W).J CommRingCat.{u}]
  [HasWeakSheafify (X.over W.left).J CommRingCat.{u}]
  (h : Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify ((X.over U).over W).J CommRingCat.{u}]
  [HasWeakSheafify (X.over W.left).J CommRingCat.{u}] in
/-- **Multiplication by `f` transports to multiplication by the transported section.** -/
theorem sliceTransport_map_awaySmul_app_apply (T : (Over W.left)ᵒᵖ)
    (x : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O)).val.obj T) :
    (((sliceTransport X U W).map
        ((awaySmul ((X.over U).over W) h).asHom.app
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))).val.app T).hom x =
      globalSectionVal (globalSectionTransport X U W h) T • x := by
  rw [globalSectionVal_globalSectionTransport]
  exact awaySmul_app_apply ((X.over U).over W) h
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O))
    (op (W.iteratedSliceBackward.obj T.unop)) x

/-- Multiplication by the transported section, as the transport of multiplication by `f`. -/
def awaySmulTransport :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O) :=
  (sliceTransport X U W).map
    ((awaySmul ((X.over U).over W) h).asHom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))

omit [HasWeakSheafify ((X.over U).over W).J CommRingCat.{u}]
  [HasWeakSheafify (X.over W.left).J CommRingCat.{u}] in
/-- `awaySmulTransport` is multiplication by the transported section. -/
theorem awaySmulTransport_app_apply (T : (Over W.left)ᵒᵖ)
    (x : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W.left).O)).val.obj T) :
    ((awaySmulTransport X U W h).val.app T).hom x =
      globalSectionVal (globalSectionTransport X U W h) T • x :=
  sliceTransport_map_awaySmul_app_apply X U W h T x

/-- The transported sequential diagram is the sequential diagram of the transported section. -/
def awaySequenceTransportHom :
    awaySequence ((X.over U).over W)
        ((awaySmul ((X.over U).over W) h).asHom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O))) ⋙
        sliceTransport X U W ⟶
      awaySequence (X.over W.left) (awaySmulTransport X U W h) :=
  NatTrans.ofSequence (F := awaySequence ((X.over U).over W)
        ((awaySmul ((X.over U).over W) h).asHom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O))) ⋙
        sliceTransport X U W)
    (G := awaySequence (X.over W.left) (awaySmulTransport X U W h))
    (fun _ => 𝟙 _) (fun n => by
      have h₁ : (awaySequence ((X.over U).over W)
            ((awaySmul ((X.over U).over W) h).asHom.app
              (SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))).map
              (homOfLE (Nat.le_add_right n 1)) =
          (awaySmul ((X.over U).over W) h).asHom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)) :=
        awaySequence_map_succ ((X.over U).over W) _ n
      have h₂ : (awaySequence (X.over W.left) (awaySmulTransport X U W h)).map
            (homOfLE (Nat.le_add_right n 1)) = awaySmulTransport X U W h :=
        awaySequence_map_succ (X.over W.left) _ n
      dsimp only [Functor.comp_map]
      rw [h₁, h₂]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Each component of `awaySequenceTransportHom` is an isomorphism. -/
instance isIso_awaySequenceTransportHom_app (n : ℕ) :
    IsIso ((awaySequenceTransportHom X U W h).app n) := by
  have happ : (awaySequenceTransportHom X U W h).app n = 𝟙 _ := rfl
  rw [happ]
  exact IsIso.id _

/-- `awaySequenceTransportHom` is an isomorphism. -/
instance isIso_awaySequenceTransportHom : IsIso (awaySequenceTransportHom X U W h) :=
  NatIso.isIso_of_isIso_app _

/-- **The sequential diagram presenting `𝒪_f` transports to the one presenting `𝒪_{f'}`.** -/
def awaySequenceTransportIso :
    awaySequence ((X.over U).over W)
        ((awaySmul ((X.over U).over W) h).asHom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O))) ⋙
        sliceTransport X U W ≅
      awaySequence (X.over W.left) (awaySmulTransport X U W h) :=
  asIso (awaySequenceTransportHom X U W h)

/-- The colimit cocone presenting `𝒪_f`, transported. -/
def awayModuleTransportColimit :
    IsColimit ((sliceTransport X U W).mapCocone
      (awayModuleCocone ((X.over U).over W) h
        ((awaySmul ((X.over U).over W) h).asHom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))
        (fun V x => awaySmul_app_apply ((X.over U).over W) h _ V x))) :=
  isColimitOfPreserves _
    (isColimitAwayModuleCocone ((X.over U).over W) h
      ((awaySmul ((X.over U).over W) h).asHom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))
      (fun V x => awaySmul_app_apply ((X.over U).over W) h _ V x))

/-- The colimit cocone presenting `𝒪_{f'}`. -/
def awayTransportedColimit :
    IsColimit (awayModuleCocone (X.over W.left) (globalSectionTransport X U W h)
      (awaySmulTransport X U W h) (fun V x => awaySmulTransport_app_apply X U W h V x)) :=
  isColimitAwayModuleCocone (X.over W.left) (globalSectionTransport X U W h)
    (awaySmulTransport X U W h) (fun V x => awaySmulTransport_app_apply X U W h V x)

/-- **Inverting a global section commutes with the iterated-slice transport:**
the transport of `𝒪_f` is `𝒪_{f'}`, `f'` the transported section. -/
def awayModuleTransportIso :
    (sliceTransport X U W).obj (awayModule ((X.over U).over W) h) ≅
      awayModule (X.over W.left) (globalSectionTransport X U W h) :=
  IsColimit.coconePointsIsoOfNatIso (awayModuleTransportColimit X U W h)
    (awayTransportedColimit X U W h) (awaySequenceTransportIso X U W h)

/-- The identification is compatible with the canonical maps out of the structure sheaf. -/
theorem sliceTransport_map_unitToAwayModule_comp_awayModuleTransportIso :
    (sliceTransport X U W).map (unitToAwayModule ((X.over U).over W) h) ≫
        (awayModuleTransportIso X U W h).hom =
      unitToAwayModule (X.over W.left) (globalSectionTransport X U W h) := by
  have hleg := IsColimit.comp_coconePointsIsoOfNatIso_hom (awayModuleTransportColimit X U W h)
    (awayTransportedColimit X U W h) (awaySequenceTransportIso X U W h) 0
  have hsrc : ((sliceTransport X U W).mapCocone
        (awayModuleCocone ((X.over U).over W) h
          ((awaySmul ((X.over U).over W) h).asHom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O)))
          (fun V x => awaySmul_app_apply ((X.over U).over W) h _ V x))).ι.app 0 =
      (sliceTransport X U W).map (unitToAwayModule ((X.over U).over W) h) := by
    show (sliceTransport X U W).map (awayModuleCoconeι ((X.over U).over W) h 0) = _
    rw [awayModuleCoconeι_zero]
  have htgt : (awayModuleCocone (X.over W.left) (globalSectionTransport X U W h)
        (awaySmulTransport X U W h)
        (fun V x => awaySmulTransport_app_apply X U W h V x)).ι.app 0 =
      unitToAwayModule (X.over W.left) (globalSectionTransport X U W h) :=
    awayModuleCoconeι_zero (X.over W.left) (globalSectionTransport X U W h)
  rw [hsrc] at hleg
  rw [htgt] at hleg
  refine hleg.trans ?_
  have happ : (awaySequenceTransportIso X U W h).hom.app 0 = 𝟙 _ := rfl
  rw [happ]
  exact Category.id_comp _

end Smul

section Prod

variable [HasWeakSheafify ((X.over U).over W).J CommRingCat.{u}]
  [HasWeakSheafify (X.over W.left).J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify ((X.over U).over W).J CommRingCat.{u}]
  [HasWeakSheafify (X.over W.left).J CommRingCat.{u}] in
/-- The transport commutes with forming the subproduct `f_S` of a finite family. -/
theorem globalSectionTransport_prodGlobalSection (S : Finset (Fin r)) :
    globalSectionTransport X U W (prodGlobalSection f S) =
      prodGlobalSection (fun i => globalSectionTransport X U W (f i)) S := by
  refine (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext (funext fun V => ?_))
  show globalSectionVal (globalSectionTransport X U W (prodGlobalSection f S)) V =
    globalSectionVal (prodGlobalSection (fun i => globalSectionTransport X U W (f i)) S) V
  rw [globalSectionVal_globalSectionTransport, globalSectionVal_prodGlobalSection,
    globalSectionVal_prodGlobalSection]
  exact Finset.prod_congr rfl fun i _ =>
    (globalSectionVal_globalSectionTransport X U W (f i) V).symm

/-- `awayModuleTransportIso`, transported along an equality of the target section. -/
def awayModuleTransportIsoOfEq
    {h : Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u})}
    {h' : Presheaf.globalSections ((X.over W.left).O.obj ⋙ forget CommRingCat.{u})}
    (e : globalSectionTransport X U W h = h') :
    (sliceTransport X U W).obj (awayModule ((X.over U).over W) h) ≅
      awayModule (X.over W.left) h' :=
  e ▸ awayModuleTransportIso X U W h

/-- `awayModuleTransportIsoOfEq` is compatible with the canonical maps out of the structure
sheaf. -/
theorem sliceTransport_map_unitToAwayModule_comp_awayModuleTransportIsoOfEq
    {h : Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u})}
    {h' : Presheaf.globalSections ((X.over W.left).O.obj ⋙ forget CommRingCat.{u})}
    (e : globalSectionTransport X U W h = h') :
    (sliceTransport X U W).map (unitToAwayModule ((X.over U).over W) h) ≫
        (awayModuleTransportIsoOfEq X U W e).hom =
      unitToAwayModule (X.over W.left) h' := by
  subst e
  exact sliceTransport_map_unitToAwayModule_comp_awayModuleTransportIso X U W h

/-- **The terms of the extended alternating Čech complex transport correctly.** -/
def awayModuleProdTransportIso (S : Finset (Fin r)) :
    (sliceTransport X U W).obj (awayModule ((X.over U).over W) (prodGlobalSection f S)) ≅
      awayModule (X.over W.left)
        (prodGlobalSection (fun i => globalSectionTransport X U W (f i)) S) :=
  awayModuleTransportIsoOfEq X U W (globalSectionTransport_prodGlobalSection X U W f S)

/-- `awayModuleProdTransportIso` is compatible with the canonical maps out of the structure
sheaf. -/
theorem sliceTransport_map_unitToAwayModule_comp_awayModuleProdTransportIso
    (S : Finset (Fin r)) :
    (sliceTransport X U W).map (unitToAwayModule ((X.over U).over W) (prodGlobalSection f S)) ≫
        (awayModuleProdTransportIso X U W f S).hom =
      unitToAwayModule (X.over W.left)
        (prodGlobalSection (fun i => globalSectionTransport X U W (f i)) S) :=
  sliceTransport_map_unitToAwayModule_comp_awayModuleTransportIsoOfEq X U W
    (globalSectionTransport_prodGlobalSection X U W f S)

/-- **The identification of the Čech terms is natural in the subset.** -/
theorem sliceTransport_map_awayModuleTransition_comp_awayModuleProdTransportIso
    {S T : Finset (Fin r)} (hST : S ⊆ T) :
    (sliceTransport X U W).map (awayModuleTransition ((X.over U).over W) f hST) ≫
        (awayModuleProdTransportIso X U W f T).hom =
      (awayModuleProdTransportIso X U W f S).hom ≫
        awayModuleTransition (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i)) hST :=
  comp_hom_eq_hom_comp_of_hom_ext (awayModuleProdTransportIso X U W f S)
    (awayModuleProdTransportIso X U W f T)
    ((sliceTransport X U W).map (awayModuleTransition ((X.over U).over W) f hST))
    (awayModuleTransition (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i)) hST)
    (sliceTransport_map_unitToAwayModule_comp_awayModuleProdTransportIso X U W f S)
    (sliceTransport_map_unitToAwayModule_comp_awayModuleProdTransportIso X U W f T)
    (by rw [← Functor.map_comp, unitToAwayModule_comp_awayModuleTransition])
    (unitToAwayModule_comp_awayModuleTransition (X.over W.left)
      (fun i ↦ globalSectionTransport X U W (f i)) hST)
    fun h ↦ hom_ext_unitToAwayModule (X.over W.left)
      (prodGlobalSection (fun i ↦ globalSectionTransport X U W (f i)) S) _
      (bijective_smul_awayModule_prodGlobalSection_of_subset (X.over W.left)
        (fun i ↦ globalSectionTransport X U W (f i)) hST) h

/-- **The localization system of the Čech complex transports to the localization system of the
transported family.** -/
def awayLocalizationFunctorTransportIso :
    awayLocalizationFunctor ((X.over U).over W) f ⋙ sliceTransport X U W ≅
      awayLocalizationFunctor (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i)) :=
  NatIso.ofComponents (fun S ↦ awayModuleProdTransportIso X U W f S) fun {_S _T} g ↦
    sliceTransport_map_awayModuleTransition_comp_awayModuleProdTransportIso X U W f (leOfHom g)

/-- The transport preserves the finite products forming the terms of the Čech complex: it is an
equivalence. -/
instance preservesFiniteProducts_sliceTransport :
    PreservesFiniteProducts (sliceTransport X U W) :=
  inferInstance

/-- **`Č(f)` transports to `Č(f')`** along the iterated-slice transport. -/
def extendedAlternatingCechTransportIso :
    ((sliceTransport X U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech ((X.over U).over W) f) ≅
      extendedAlternatingCech (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i)) :=
  AlternatingCech.mapComplexIso (sliceTransport X U W)
      (awayLocalizationFunctor ((X.over U).over W) f) ≪≫
    AlternatingCech.complexMapIso (awayLocalizationFunctorTransportIso X U W f)

/-- The identification is compatible with the augmentations out of the structure sheaf. -/
theorem sliceTransport_map_extendedAlternatingCechAugmentation_comp :
    (sliceTransport X U W).map (extendedAlternatingCechAugmentation ((X.over U).over W) f) ≫
        (extendedAlternatingCechTransportIso X U W f).hom.f 0 =
      extendedAlternatingCechAugmentation (X.over W.left)
        (fun i ↦ globalSectionTransport X U W (f i)) :=
  AlternatingCech.mapTermIso_hom_comp_mapTerm_comp_lift
    (sliceTransport X U W) (awayLocalizationFunctor ((X.over U).over W) f)
    (awayLocalizationFunctorTransportIso X U W f)
    (fun S ↦ unitToAwayModule ((X.over U).over W) (prodGlobalSection f S))
    (fun S ↦ unitToAwayModule (X.over W.left)
      (prodGlobalSection (fun i ↦ globalSectionTransport X U W (f i)) S))
    (fun S ↦ sliceTransport_map_unitToAwayModule_comp_awayModuleProdTransportIso X U W f S) 0

/-- The transport of the structure sheaf placed in degree zero is the structure sheaf placed in
degree zero. -/
def structureSheafComplexTransportIso :
    ((sliceTransport X U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (structureSheafComplex ((X.over U).over W)) ≅ structureSheafComplex (X.over W.left) :=
  (HomologicalComplex.singleMapHomologicalComplex (sliceTransport X U W)
    (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf ((X.over U).over W).O))

/-- **The transport of `Č(f) ⟶ 𝒪` is `Č(f') ⟶ 𝒪`**, under `Č(f) ↦ Č(f')`. -/
theorem sliceTransport_map_cechAugmentation :
    ((sliceTransport X U W).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cechAugmentation ((X.over U).over W) f) ≫
        (structureSheafComplexTransportIso X U W).hom =
      (extendedAlternatingCechTransportIso X U W f).hom ≫
        cechAugmentation (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i)) :=
  have hkey : (sliceTransport X U W).map (unitIsoCechXZero ((X.over U).over W) f).hom ≫
        (extendedAlternatingCechTransportIso X U W f).hom.f 0 =
      (unitIsoCechXZero (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i))).hom :=
    (congrArg (fun m => (sliceTransport X U W).map m ≫
        (extendedAlternatingCechTransportIso X U W f).hom.f 0)
        (unitIsoCechXZero_hom ((X.over U).over W) f)).trans
      ((sliceTransport_map_extendedAlternatingCechAugmentation_comp X U W f).trans
        (unitIsoCechXZero_hom (X.over W.left) (fun i ↦ globalSectionTransport X U W (f i))).symm)
  (HomologicalComplex.map_mkHomToSingle _ _ _).trans
    (HomologicalComplex.comp_mkHomToSingle _ _ _ _ _
      ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp
        ((sliceTransport X U W).mapIso
          (unitIsoCechXZero ((X.over U).over W) f))).2 hkey))).symm

end Prod

section Ideal

variable (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) {s : ℕ}
  (g : Fin s → Presheaf.globalSections (((X.over U).over W).O.obj ⋙ forget CommRingCat.{u}))

/-- **A finite family generating `(ℐ|_U)|_W` on the iterated slice transports to a family
generating `ℐ|_{W.left}` on the slice.** The transported generators are sections of
`ℐ|_{W.left}` because the untransported ones are sections of `(ℐ|_U)|_W`, over the same objects
of `𝒞`; conversely a section of `ℐ|_{W.left}` over `T` is a section of `(ℐ|_U)|_W` over the
image of `T` in the iterated slice, hence locally a combination of the generators along a
covering sieve there, and that sieve pulled back along the cocontinuous functor
`CategoryTheory.Over.iteratedSliceBackward` is covering. -/
theorem idealOfGlobalSections_globalSectionTransport
    (hg : idealOfGlobalSections ((X.over U).over W) g = overIdeal (overIdeal I U) W) :
    idealOfGlobalSections (X.over W.left) (fun i => globalSectionTransport X U W (g i)) =
      overIdeal I W.left := by
  refine le_antisymm (idealOfGlobalSections_le _ _ fun i T => ?_) fun T x hx => ?_
  · have h := globalSectionVal_mem_idealOfGlobalSections ((X.over U).over W) g i
      (op (W.iteratedSliceBackward.obj T.unop))
    rw [hg] at h
    rw [globalSectionVal_globalSectionTransport]
    exact h
  · have hxZ : x ∈ (idealOfGlobalSections ((X.over U).over W) g).toSubmodule.obj
        (op (W.iteratedSliceBackward.obj T.unop)) := by
      rw [hg]
      exact hx
    obtain ⟨S, hS, hSx⟩ := (mem_idealOfGlobalSections_iff _ g _).1 hxZ
    refine (mem_idealOfGlobalSections_iff _ _ T).2
      ⟨S.functorPullback W.iteratedSliceBackward,
        W.iteratedSliceBackward.cover_lift (X.J.over W.left) ((X.J.over U).over W) hS,
        fun Y b hb => ?_⟩
    have hspan : Set.range (restrictGlobalSections (X.over W.left)
          (fun i => globalSectionTransport X U W (g i)) (op Y)) =
        Set.range (restrictGlobalSections ((X.over U).over W) g
          (op (W.iteratedSliceBackward.obj Y))) :=
      congrArg Set.range (funext fun i =>
        globalSectionVal_globalSectionTransport X U W (g i) (op Y))
    rw [hspan]
    exact hSx (W.iteratedSliceBackward.map b) hb

end Ideal

end AlgebraicGeometry.RingedSite

end
