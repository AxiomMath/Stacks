module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction

/-!
# The inverse image of sheaves of modules along isomorphic inverse-image functors

Let `Φ, Ψ : Sh(D) ⥤ Sh(C)` be finite-product-preserving functors between categories of sheaves
of sets and `e : Φ ≅ Ψ` a natural isomorphism. For a sheaf of rings `O` on `D`, the inverse images
`Φ⁻¹O` and `Ψ⁻¹O` of Stacks 03D2 carry transported ring structures, and `e` is an isomorphism of
sheaves of rings between them. For a sheaf of `O`-modules `G`, `e` is likewise an isomorphism of
the inverse images `Φ⁻¹G ≅ Ψ⁻¹G`, linear over the identification of the sheaves of rings. This
file records the two isomorphisms; their underlying maps on sections are the components of `e`.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafCongr`: the isomorphism `Φ⁻¹O ≅ Ψ⁻¹O`.
* `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorCongr`: the isomorphism of functors
  `G ↦ Φ⁻¹G` and `G ↦ Ψ⁻¹G`, the latter read over `Φ⁻¹O` by restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  {Φ Ψ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)} [hΦ : PreservesFiniteProducts Φ]
  [hΨ : PreservesFiniteProducts Ψ] (e : Φ ≅ Ψ) (O : Sheaf K RingCat.{ww'})

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- A natural transformation `Φ ⟶ Ψ` of inverse-image functors induces a map of the inverse
images of a sheaf of rings, which on sections is the given transformation. -/
def pullbackRingSheafCongrMap (θ : Φ ⟶ Ψ) : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Ψ O where
  hom :=
    { app := fun X =>
        letI := ringObjRing O (Φ ⋙ sectionsFunctor J X)
        letI := ringObjRing O (Ψ ⋙ sectionsFunctor J X)
        RingCat.ofHom (ringObjHom O (Functor.whiskerRight θ (sectionsFunctor J X)))
      naturality := fun X Y g => by
        refine RingCat.hom_ext (RingHom.ext fun x => ?_)
        change (θ.app (ringSheaf O)).hom.app Y ((Φ.obj (ringSheaf O)).obj.map g x) =
          (Ψ.obj (ringSheaf O)).obj.map g ((θ.app (ringSheaf O)).hom.app X x)
        exact NatTrans.naturality_apply (θ.app (ringSheaf O)).hom g x }

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] [J.HasSheafCompose (forget RingCat.{ww})] in
theorem pullbackRingSheafCongrMap_hom_app_apply (θ : Φ ⟶ Ψ) (X : Cᵒᵖ)
    (r : (pullbackRingSheaf J Φ O).obj.obj X) :
    ((pullbackRingSheafCongrMap J O θ).hom.app X).hom r = (θ.app (ringSheaf O)).hom.app X r :=
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- **The inverse images of a sheaf of rings along isomorphic inverse-image functors are
isomorphic**, by the components of the isomorphism. -/
def pullbackRingSheafCongr : pullbackRingSheaf J Φ O ≅ pullbackRingSheaf J Ψ O where
  hom := pullbackRingSheafCongrMap J O e.hom
  inv := pullbackRingSheafCongrMap J O e.inv
  hom_inv_id := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun X ↦ RingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    change (e.inv.app (ringSheaf O)).hom.app X ((e.hom.app (ringSheaf O)).hom.app X x) = x
    exact congrFun (congrArg (fun m ↦ m.hom.app X) (e.hom_inv_id_app (ringSheaf O))) x
  inv_hom_id := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun X ↦ RingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    change (e.hom.app (ringSheaf O)).hom.app X ((e.inv.app (ringSheaf O)).hom.app X x) = x
    exact congrFun (congrArg (fun m ↦ m.hom.app X) (e.inv_hom_id_app (ringSheaf O))) x

variable (G : SheafOfModules.{ww'} O)

/-- On the sections over one object, the inverse images of a sheaf of modules along isomorphic
inverse-image functors are identified by the component of the isomorphism, linearly over the
identification of the sheaves of rings. -/
def pullbackModuleCongrApp (X : Cᵒᵖ) :
    (pullbackModuleObj J Φ O G).val.obj X ⟶
      ((SheafOfModules.restrictScalars (pullbackRingSheafCongr J e O).hom).obj
        (pullbackModuleObj J Ψ O G)).val.obj X :=
  letI : Module ((pullbackRingSheaf J Φ O).obj.obj X) ((pullbackModuleAb J Φ O G).obj X) :=
    moduleObjModule O G (Φ ⋙ sectionsFunctor J X)
  ModuleCat.ofHom
    (X := ModuleCat.of ((pullbackRingSheaf J Φ O).obj.obj X) ((pullbackModuleAb J Φ O G).obj X))
    (Y := (ModuleCat.restrictScalars ((pullbackRingSheafCongr J e O).hom.hom.app X).hom).obj
      ((pullbackModuleObj J Ψ O G).val.obj X))
    { toFun := (Functor.whiskerRight e.hom (sectionsFunctor J X)).app (moduleSheaf O G)
      map_add' := fun x y => moduleAddObj_naturality O G
        (Functor.whiskerRight e.hom (sectionsFunctor J X)) x y
      map_smul' := fun r x => moduleSMulObj_naturality O G
        (Functor.whiskerRight e.hom (sectionsFunctor J X)) r x }

/-- The inverse direction of `pullbackModuleCongrApp`. -/
def pullbackModuleCongrAppInv (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars (pullbackRingSheafCongr J e O).hom).obj
        (pullbackModuleObj J Ψ O G)).val.obj X ⟶
      (pullbackModuleObj J Φ O G).val.obj X :=
  letI : Module ((pullbackRingSheaf J Φ O).obj.obj X) ((pullbackModuleAb J Φ O G).obj X) :=
    moduleObjModule O G (Φ ⋙ sectionsFunctor J X)
  ModuleCat.ofHom
    (Y := ModuleCat.of ((pullbackRingSheaf J Φ O).obj.obj X) ((pullbackModuleAb J Φ O G).obj X))
    (X := (ModuleCat.restrictScalars ((pullbackRingSheafCongr J e O).hom.hom.app X).hom).obj
      ((pullbackModuleObj J Ψ O G).val.obj X))
    { toFun := (Functor.whiskerRight e.inv (sectionsFunctor J X)).app (moduleSheaf O G)
      map_add' := fun x y => moduleAddObj_naturality O G
        (Functor.whiskerRight e.inv (sectionsFunctor J X)) x y
      map_smul' := fun r x => by
        have h := moduleSMulObj_naturality O G
          (Functor.whiskerRight e.inv (sectionsFunctor J X))
          ((Functor.whiskerRight e.hom (sectionsFunctor J X)).app (ringSheaf O) r) x
        have hr : (Functor.whiskerRight e.inv (sectionsFunctor J X)).app (ringSheaf O)
            ((Functor.whiskerRight e.hom (sectionsFunctor J X)).app (ringSheaf O) r) = r :=
          congrFun (congrArg (fun m ↦ m.hom.app X) (e.hom_inv_id_app (ringSheaf O))) r
        rw [hr] at h
        exact h }

/-- **The inverse images of a sheaf of modules along isomorphic inverse-image functors are
isomorphic**, linearly over `pullbackRingSheafCongr`. -/
def pullbackModuleObjCongr :
    pullbackModuleObj J Φ O G ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafCongr J e O).hom).obj
        (pullbackModuleObj J Ψ O G) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun X => { hom := pullbackModuleCongrApp J e O G X
                  inv := pullbackModuleCongrAppInv J e O G X
                  hom_inv_id := by
                    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
                    exact congrFun (congrArg (fun m ↦ m.hom.app X)
                      (e.hom_inv_id_app (moduleSheaf O G))) x
                  inv_hom_id := by
                    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
                    exact congrFun (congrArg (fun m ↦ m.hom.app X)
                      (e.inv_hom_id_app (moduleSheaf O G))) x })
      (fun {X Y} g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        change (e.hom.app (moduleSheaf O G)).hom.app Y
            ((Φ.obj (moduleSheaf O G)).obj.map g x) =
          (Ψ.obj (moduleSheaf O G)).obj.map g ((e.hom.app (moduleSheaf O G)).hom.app X x)
        exact NatTrans.naturality_apply (e.hom.app (moduleSheaf O G)).hom g x))

/-- **The inverse images of sheaves of modules along isomorphic inverse-image functors are
isomorphic functors**, the target read over `Φ⁻¹O` by restriction of scalars along
`pullbackRingSheafCongr`. -/
def pullbackModuleFunctorCongr :
    pullbackModuleFunctor J Φ O ≅
      pullbackModuleFunctor J Ψ O ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafCongr J e O).hom :=
  NatIso.ofComponents (pullbackModuleObjCongr J e O) fun {G G'} φ => by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (e.hom.app (moduleSheaf O G')).hom.app X
        (((Φ.map ((moduleSheafFunctor O).map φ)).hom.app X) x) =
      ((Ψ.map ((moduleSheafFunctor O).map φ)).hom.app X)
        ((e.hom.app (moduleSheaf O G)).hom.app X x)
    exact CategoryTheory.Functor.natTrans_app_map_apply
      (Functor.whiskerRight e.hom (sectionsFunctor J X))
      ((moduleSheafFunctor O).map φ) x

end Stacks.Sheaves.ToposPullback

end
