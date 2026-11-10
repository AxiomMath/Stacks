module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCompMonoidal
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism

/-!
# The pullback adjunction of modules along an invertible structure map

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose structure map
`f⁻¹O_D ⟶ O_C` is invertible. Then `f^*` on sheaves of modules is `f⁻¹` on underlying sheaves of
sets, and the adjunction `f^* ⊣ f_*` of Stacks 03D7 is the adjunction `f⁻¹ ⊣ f_*` of the
underlying topoi, read on underlying sheaves. Consequently `f^*` is fully faithful as soon as
`f⁻¹` is, and a sheaf of modules lies in the essential image of `f^*` exactly when its underlying
sheaf of sets lies in the essential image of `f⁻¹`.

## Main results

The first four names are in the namespace `AlgebraicGeometry.RingedToposHom`.

* `isIso_pullbackAdjPushforwardModules_unit_of_isIso_ringedToposMorphismAdjunction`: the unit
  of `f^* ⊣ f_*` is invertible when that of `f⁻¹ ⊣ f_*` is.
* `isIso_pullbackAdjPushforwardModules_counit_app_iff_ringedToposMorphismAdjunction`: the
  counit at `F` is invertible exactly when the counit of `f⁻¹ ⊣ f_*` is at the underlying sheaf.
* `pullbackModules_essImage_iff_ringedToposMorphismAdjunction`: the essential image of `f^*`.
* The transpose of a morphism `G ⟶ f_*F` of modules, on underlying sheaves, is the transpose of
  the underlying morphism of sheaves of sets:
`moduleSheafFunctor_map_pullbackAdjPushforward_homEquiv_symm_ringedToposMorphismAdjunction`.
* `CategoryTheory.Adjunction.isIso_counit_app_ofNatIsoRight_iff_ringedToposMorphismAdjunction`
  and `CategoryTheory.Adjunction.isIso_unit_ofNatIsoRight_iff_ringedToposMorphismAdjunction`:
  transporting a right adjoint does not change which components of the unit and counit are
  invertible.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (inverseImageModules
  inverseImageAdjDirectImageModules toposModulesHomEquiv)

universe u

namespace CategoryTheory.Adjunction

variable {C : Type*} {D : Type*} [Category C] [Category D] {F : C ⥤ D} {G H : D ⥤ C}

/-- Transporting the right adjoint along an isomorphism does not change which components of the
counit are invertible. -/
theorem isIso_counit_app_ofNatIsoRight_iff_ringedToposMorphismAdjunction (adj : F ⊣ G) (iso : G ≅ H)
    (Y : D) :
    IsIso ((adj.ofNatIsoRight iso).counit.app Y) ↔ IsIso (adj.counit.app Y) := by
  have h : (adj.ofNatIsoRight iso).counit.app Y = F.map (iso.inv.app Y) ≫ adj.counit.app Y := by
    rw [← Adjunction.homEquiv_symm_id, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
      Adjunction.homEquiv_counit, Category.id_comp]
  rw [h]
  exact ⟨fun _ => IsIso.of_isIso_comp_left (F.map (iso.inv.app Y)) _, fun _ => inferInstance⟩

/-- Transporting the right adjoint along an isomorphism does not change whether the unit is
invertible. -/
theorem isIso_unit_ofNatIsoRight_iff_ringedToposMorphismAdjunction (adj : F ⊣ G) (iso : G ≅ H) :
    IsIso (adj.ofNatIsoRight iso).unit ↔ IsIso adj.unit := by
  have h : ∀ X, (adj.ofNatIsoRight iso).unit.app X = adj.unit.app X ≫ iso.hom.app (F.obj X) :=
    fun X => by
      rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
        Adjunction.homEquiv_id]
  rw [NatTrans.isIso_iff_isIso_app, NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun X => ?_
  rw [h]
  exact ⟨fun _ => IsIso.of_isIso_comp_right _ (iso.hom.app (F.obj X)), fun _ => inferInstance⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{u, u, u}} {Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

/-- **The transpose of Stacks 03D7 on underlying sheaves.** For a morphism `β : G ⟶ f_*F` of
sheaves of modules, the underlying morphism of its transpose `f^*G ⟶ F`, precomposed with the
identification of the underlying sheaf of `f⁻¹G` with that of `f^*G`, is the transpose of the
underlying morphism of `β` along `f⁻¹ ⊣ f_*`. The adjunction is the one of the four-field
morphism of ringed topoi, before its direct image is transported to `pushforwardModules`. -/
theorem moduleSheafFunctor_map_toModulesHom_homEquiv_symm_ringedToposMorphismAdjunction
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (β : G ⟶ (Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F) :
    (pullbackUnitUnderlyingIso f).hom.app G ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toModulesHom).homEquiv G F).symm β) =
      (f.toToposHom.adj.homEquiv _ _).symm
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map β) := by
  have h1 : ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toModulesHom).homEquiv G F).symm β =
      ((fSharpAdjunction f).homEquiv _ F).symm
        (((inverseImageAdjDirectImageModules f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).homEquiv G _).symm β) :=
    congrArg (fun e => (e G F).symm β)
      (Adjunction.comp_homEquiv
        (inverseImageAdjDirectImageModules f.toModulesHom.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (fSharpAdjunction f))
  have h2 := (((fSharpAdjunction f).homEquiv _ F).apply_symm_apply
      (((inverseImageAdjDirectImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).homEquiv G _).symm β)).symm.trans
    ((fSharpAdjunction f).homEquiv_unit
      ((inverseImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).obj G) F
      (((fSharpAdjunction f).homEquiv _ F).symm
        (((inverseImageAdjDirectImageModules f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).homEquiv G _).symm β)))
  have h3 := (congrArg (Sheaf.moduleSheafFunctor
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).map
    h2).trans (CategoryTheory.Functor.map_comp _ _ _)
  refine (congrArg (fun t => (pullbackUnitUnderlyingIso f).hom.app G ≫
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map t)
      h1).trans ?_
  refine h3.symm.trans ?_
  have h0 : ((inverseImageAdjDirectImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).homEquiv G _).symm β =
      (toposModulesHomEquiv f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) G _).symm β := by
    unfold inverseImageAdjDirectImageModules
    rw [Adjunction.mkOfHomEquiv_homEquiv]
  refine (congrArg (Sheaf.moduleSheafFunctor
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).map
    h0).trans ?_
  exact Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_toposModulesHomEquiv_symm
    f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) β

/-- The counit of the four-field form of Stacks 03D7 at `F`, on underlying sheaves and after the
identification of underlying sheaves of `f⁻¹f_*F` and `f^*f_*F`, is the counit of `f⁻¹ ⊣ f_*` at
the underlying sheaf of `F`. -/
theorem moduleSheafFunctor_map_toModulesHom_counit_app_ringedToposMorphismAdjunction
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (pullbackUnitUnderlyingIso f).hom.app
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F) ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toModulesHom).counit.app F) =
      f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F) := by
  have h :=
    moduleSheafFunctor_map_toModulesHom_homEquiv_symm_ringedToposMorphismAdjunction f _ F (𝟙 _)
  rw [Adjunction.homEquiv_symm_id, CategoryTheory.Functor.map_id] at h
  exact h.trans (f.toToposHom.adj.homEquiv_symm_id _)

/-- The unit of the four-field form of Stacks 03D7 at `G`, on underlying sheaves, is the unit of
`f⁻¹ ⊣ f_*` at the underlying sheaf of `G` followed by the direct image of the identification of
underlying sheaves of `f⁻¹G` and `f^*G`. -/
theorem moduleSheafFunctor_map_toModulesHom_unit_app_ringedToposMorphismAdjunction
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).unit.app G) =
      f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) G) ≫
        f.toToposHom.pushforward.map ((pullbackUnitUnderlyingIso f).hom.app G) := by
  have h := moduleSheafFunctor_map_toModulesHom_homEquiv_symm_ringedToposMorphismAdjunction f G _
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      f.toModulesHom).unit.app G)
  rw [← Adjunction.homEquiv_id, Equiv.symm_apply_apply] at h
  have h' := (congrArg (f.toToposHom.adj.homEquiv _ _) h).trans (Equiv.apply_symm_apply _ _)
  have hid :=
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map_id
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom).obj G)
  rw [← Adjunction.homEquiv_id]
  refine h'.symm.trans ((f.toToposHom.adj.homEquiv_unit _ _ _).trans ?_)
  exact congrArg (fun t => f.toToposHom.adj.unit.app _ ≫ f.toToposHom.pushforward.map t)
    ((congrArg (fun t => (pullbackUnitUnderlyingIso f).hom.app G ≫ t) hid).trans
      (Category.comp_id _))

/-- **The counit of Stacks 03D7 along an invertible structure map.** The counit
`f^*f_*F ⟶ F` is invertible exactly when the counit `f⁻¹f_* ⟶ id` of the underlying topoi is
invertible at the underlying sheaf of `F`. -/
theorem isIso_pullbackAdjPushforwardModules_counit_app_iff_ringedToposMorphismAdjunction
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    IsIso ((pullbackAdjPushforwardModules f).counit.app F) ↔
      IsIso (f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F)) := by
  refine (Adjunction.isIso_counit_app_ofNatIsoRight_iff_ringedToposMorphismAdjunction
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    f.toModulesPushforwardIso F).trans ?_
  rw [← moduleSheafFunctor_map_toModulesHom_counit_app_ringedToposMorphismAdjunction f F]
  have hη := Iso.isIso_hom ((pullbackUnitUnderlyingIso f).app
    ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact @IsIso.comp_isIso _ _ _ _ _ _ _ hη
      (Iso.isIso_hom
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).mapIso
        (@asIso _ _ _ _ ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).counit.app F) h)))
  have : IsIso
      ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toModulesHom).counit.app F)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hη h
  exact isIso_of_reflects_iso _
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))

/-- **The unit of Stacks 03D7 along an invertible structure map.** The unit `G ⟶ f_*f^*G` is
invertible as soon as the unit `id ⟶ f_*f⁻¹` of the underlying topoi is. -/
theorem isIso_pullbackAdjPushforwardModules_unit_of_isIso_ringedToposMorphismAdjunction
    [IsIso f.toToposHom.adj.unit] :
    IsIso (pullbackAdjPushforwardModules f).unit := by
  refine (Adjunction.isIso_unit_ofNatIsoRight_iff_ringedToposMorphismAdjunction
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    f.toModulesPushforwardIso).2 ?_
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  have : IsIso ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toModulesHom).unit.app G)) := by
    rw [moduleSheafFunctor_map_toModulesHom_unit_app_ringedToposMorphismAdjunction]
    have := Iso.isIso_hom ((pullbackUnitUnderlyingIso f).app G)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (NatIso.isIso_app_of_isIso f.toToposHom.adj.unit _)
      (Functor.map_isIso f.toToposHom.pushforward ((pullbackUnitUnderlyingIso f).hom.app G))
  exact isIso_of_reflects_iso _
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **The essential image of the pullback of modules along an invertible structure map.** When
the inverse image of the underlying topoi is fully faithful, a sheaf of modules lies in the
essential image of `f^*` exactly when its underlying sheaf of sets lies in that of `f⁻¹`. -/
theorem pullbackModules_essImage_iff_ringedToposMorphismAdjunction [IsIso f.toToposHom.adj.unit]
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    f.toModulesHom.pullbackModules.essImage F ↔
      f.toToposHom.inverseImage.essImage
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F) := by
  have := f.toToposHom.adj.fullyFaithfulLOfIsIsoUnit.full
  have := f.toToposHom.adj.fullyFaithfulLOfIsIsoUnit.faithful
  have := (fullyFaithfulPullbackModules f).full
  have := (fullyFaithfulPullbackModules f).faithful
  rw [← (pullbackAdjPushforwardModules f).isIso_counit_app_iff_mem_essImage,
    ← f.toToposHom.adj.isIso_counit_app_iff_mem_essImage]
  exact isIso_pullbackAdjPushforwardModules_counit_app_iff_ringedToposMorphismAdjunction f F

/-- **The transpose of Stacks 03D7 on underlying sheaves.** For a morphism `β : G ⟶ f_*F` of
sheaves of modules, the underlying morphism of its transpose `f^*G ⟶ F`, precomposed with the
identification of the underlying sheaf of `f⁻¹G` with that of `f^*G`, is the transpose of the
underlying morphism of `β` along `f⁻¹ ⊣ f_*`. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforward_homEquiv_symm_ringedToposMorphismAdjunction
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (β : G ⟶ (pushforwardModules f).obj F) :
    (pullbackUnitUnderlyingIso f).hom.app G ≫
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          (((pullbackAdjPushforwardModules f).homEquiv G F).symm β) =
      (f.toToposHom.adj.homEquiv _ _).symm
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map β) := by
  have e1 : ((pullbackAdjPushforwardModules f).homEquiv G F).symm β =
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        f.toModulesHom).homEquiv G F).symm (β ≫ f.toModulesPushforwardIso.inv.app F) :=
    Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ β
  have e4 := (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp β
    (f.toModulesPushforwardIso.inv.app F)
  have e5 := moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id f F
  have e6 : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map β ≫
      𝟙 (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F)) =
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map β :=
    Category.comp_id _
  rw [e5] at e4
  have e3 := e4.trans e6
  rw [e1]
  refine (moduleSheafFunctor_map_toModulesHom_homEquiv_symm_ringedToposMorphismAdjunction f G F
    _).trans ?_
  exact congrArg (fun t => (f.toToposHom.adj.homEquiv
    (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)
    (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) F)).symm t) e3

end AlgebraicGeometry.RingedToposHom

end
