module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Internal Hom commutes with restriction along a functor that is an equivalence on slices

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `u : C ⥤ D` be a continuous and
cocontinuous functor such that each slice functor `Over.post u : C/W ⥤ D/u(W)` is an equivalence,
together with an invertible structure map `φ : O_C ⟶ u_* O_D`. Then restriction of modules along
`u` carries the internal Hom sheaf of Stacks 03EM to the internal Hom sheaf,

`φ_* Hom_{O_D}(A, B) ≅ Hom_{O_C}(φ_* A, φ_* B)`.

The sections of the left side over `W` are the morphisms `A|_{u(W)} ⟶ B|_{u(W)}` on `D/u(W)`,
those of the right side the morphisms `(φ_* A)|_W ⟶ (φ_* B)|_W` on `C/W`, and the equivalence of
slices `C/W ≌ D/u(W)` carries the one to the other. This is the argument of
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso`, which is the case of a global
equivalence of sites, carried out one slice at a time; no finite presentation of `A` is needed.

The motivating case is the inverse image of modules along a 1-morphism of categories fibred in
groupoids, whose slices are equivalences by Stacks 06W0: this is the observation of the proof of
Stacks 0GQP that the step `f^* SheafHom(F, G) = SheafHom(f^* F, f^* G)` does not use flatness
of `f`.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.slicePhi`: the structure map localized at `W`, and
  `Stacks.SheafOfModules.InternalHom.psiOfIsIso` the inverse structure map an invertible structure
  map determines along an equivalence of sites.
* `Stacks.SheafOfModules.InternalHom.sliceModulesEquiv'`: the induced equivalence of sheaves of
  modules on `D/u(W)` and on `C/W`.
* `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso`: **the transport**, the
  isomorphism `φ_* Hom_{O_D}(A, B) ≅ Hom_{O_C}(φ_* A, φ_* B)`.
* `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso`: the same isomorphism for the
  internal Hom read in the module universe of `A` and `B` on essentially small sites.

## Main results

* `Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso_hom_app`: on sections the transport
  restricts a local morphism along the slice functor `C/W ⥤ D/u(W)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

universe u v w m

namespace Stacks.SheafOfModules.InternalHom

variable {X Y : RingedSite.{u, v, w}} (F : Y.C ⥤ X.C)
  [F.IsContinuous Y.J X.J] [F.IsCocontinuous Y.J X.J]
  [hF : ∀ W : Y.C, (Over.post (X := W) F).IsEquivalence]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (F.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The equivalence of slices `C/W ≌ D/u(W)` induced by `u`. -/
abbrev sliceEquiv (W : Y.C) : Over W ≌ Over (F.obj W) :=
  (Over.post (X := W) F).asEquivalence

/-- The slice functor `C/W ⥤ D/u(W)` is continuous. -/
instance sliceEquiv_functor_isContinuous (W : Y.C) :
    (sliceEquiv F W).functor.IsContinuous (Y.J.over W) (X.J.over (F.obj W)) :=
  Functor.isContinuous_overPost Y.J X.J F W

/-- The inverse `D/u(W) ⥤ C/W` of the slice equivalence is continuous. -/
instance sliceEquiv_inverse_isContinuous (W : Y.C) :
    (sliceEquiv F W).inverse.IsContinuous (X.J.over (F.obj W)) (Y.J.over W) :=
  Functor.isContinuous_of_iso
    (Adjunction.rightAdjointUniq (Adjunction.ofIsLeftAdjoint (Over.post (X := W) F))
      (sliceEquiv F W).toAdjunction) _ _

/-- The structure map `O_C ⟶ u_* O_D`, localized at an object `W` of `C`: `φ` whiskered along
the slice projection. -/
def slicePhi (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⟶
      ((sliceEquiv F W).functor.sheafPushforwardContinuous RingCat.{w}
        (Y.J.over W) (X.J.over (F.obj W))).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (F.obj W)) :=
  ⟨Functor.whiskerLeft (Over.forget W).op φ.hom⟩

variable [IsIso φ]

/-- The localized structure map `slicePhi F φ W` is an isomorphism when `φ` is. -/
instance isIso_slicePhi (W : Y.C) : IsIso (slicePhi F φ W) := by
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf Y.J RingCat.{w}).map φ))
  have : IsIso ((sheafToPresheaf (Y.J.over W) RingCat.{w}).map (slicePhi F φ W)) := by
    change IsIso (Functor.whiskerLeft (Over.forget W).op φ.hom)
    infer_instance
  exact isIso_of_reflects_iso (slicePhi F φ W) (sheafToPresheaf (Y.J.over W) RingCat.{w})

section General

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

variable {C' : Type*} [Category C'] {D' : Type*} [Category D']
  {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
  (e : C' ≌ D') [e.functor.IsContinuous J' K'] [e.inverse.IsContinuous K' J']
  (R : Sheaf K' RingCat.{w}) (S : Sheaf J' RingCat.{w})
  (ph : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J' K').obj R) [IsIso ph]

/-- The underlying morphism of presheaves of an isomorphism of sheaves of rings is an isomorphism.
-/
instance isIso_hom_of_isIso' : IsIso ph.hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf J' RingCat.{w}).map ph))

/-- The inverse structure map determined by an invertible structure map along an equivalence of
sites: transport along the counit, then invert. -/
def psiOfIsIso : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} K' J').obj S :=
  ⟨Functor.whiskerRight (NatTrans.op e.counit) R.obj ≫
    Functor.whiskerLeft e.inverse.op (inv ph.hom)⟩

/-- The counit of `e`, whiskered into `R`, factors as `psiOfIsIso e R S ph` followed by `ph`
whiskered along `e.inverse`. -/
theorem psiOfIsIso_counit :
    Functor.whiskerRight (NatTrans.op e.counit) R.obj =
      (psiOfIsIso e R S ph).hom ≫ e.inverse.op.whiskerLeft ph.hom := by
  ext T x
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id ph.hom) (e.inverse.op.obj T))
    ((RingCat.Hom.hom (R.obj.map (e.counit.app T.unop).op)) x)).symm

/-- The composite of `ph`, `psiOfIsIso e R S ph` whiskered along `e.functor` and the unit of `e`
whiskered into `S` is the identity of `S`. -/
theorem psiOfIsIso_unit :
    ph.hom ≫ e.functor.op.whiskerLeft (psiOfIsIso e R S ph).hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) S.obj = 𝟙 S.obj := by
  ext T : 2
  obtain ⟨T⟩ := T
  have hn := ph.hom.naturality (e.unit.app T).op
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj, Functor.op_map] at hn
  have hi : (inv ph.hom).app (op (e.inverse.obj (e.functor.obj T))) ≫
      ph.hom.app (op (e.inverse.obj (e.functor.obj T))) = 𝟙 _ :=
    (asIso ph.hom).inv_hom_id_app _
  simp only [psiOfIsIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app, Category.assoc]
  rw [← cancel_mono (ph.hom.app (op T))]
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj]
  simp only [Category.assoc, Category.id_comp]
  rw [hn, ← Category.assoc ((inv ph.hom).app _) (ph.hom.app _), hi, Category.id_comp]
  change ph.hom.app (op T) ≫ R.obj.map (e.counit.app (e.functor.obj T)).op ≫
      R.obj.map (e.functor.map (e.unit.app T)).op = ph.hom.app (op T)
  rw [← Functor.map_comp, ← op_comp, e.functor_unit_comp T]
  simp only [Functor.id_obj, Functor.op_obj, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id (ph.hom.app (op T))

end General

/-- Sheaves of modules on `D/u(W)` and on `C/W` agree along the equivalence of slices. -/
def sliceModulesEquiv' (W : Y.C) :
    _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (F.obj W)) ≌
      _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (sliceEquiv F W)
    (slicePhi F φ W) (psiOfIsIso _ _ _ (slicePhi F φ W))
    (psiOfIsIso_counit _ _ _ (slicePhi F φ W)) (psiOfIsIso_unit _ _ _ (slicePhi F φ W))

variable (A B : _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A morphism `A|_{u(W)} ⟶ B|_{u(W)}` on `D/u(W)`, read as a morphism
`(φ_* A)|_W ⟶ (φ_* B)|_W` on `C/W`. -/
def sliceEquivSection (W : Y.C)
    (α : internalHomObj X.O.obj A.val B.val (F.obj W)) :
    internalHomObj Y.O.obj ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val
      ((_root_.SheafOfModules.pushforward.{m} φ).obj B).val W := by
  let e := sliceModulesEquiv'.{u, v, w, m} F φ W
  let α₁ : _root_.SheafOfModules.over A (F.obj W) ⟶ _root_.SheafOfModules.over B (F.obj W) :=
    (_root_.SheafOfModules.fullyFaithfulForget _).preimage α
  exact (_root_.SheafOfModules.forget _).map (e.functor.map α₁)

/-- The comparison on sections over `W` is a bijection. -/
def sliceEquivSectionEquiv (W : Y.C) :
    ((internalHomObj X.O.obj A.val B.val (F.obj W)) : Type _) ≃
      ((internalHomObj Y.O.obj ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B).val W) : Type _) := by
  let e := sliceModulesEquiv'.{u, v, w, m} F φ W
  let hA := _root_.SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (F.obj W))
  let hA' := _root_.SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)
  exact (hA.homEquiv (X := _root_.SheafOfModules.over A (F.obj W))
      (Y := _root_.SheafOfModules.over B (F.obj W))).symm.trans
    ((e.fullyFaithfulFunctor.homEquiv).trans (hA'.homEquiv))

/-- The comparison `φ_* Hom_{O_D}(A, B) ⟶ Hom_{O_C}(φ_* A, φ_* B)`, as a morphism of presheaves
of modules on `C`. -/
def sliceEquivInternalHomHom :
    RingedSite.valOf Y ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)) ⟶
      RingedSite.valOf Y (RingedSite.internalHomSheaf Y
        ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)) where
  app W := by
    letI : Module ((Oforget Y.O.obj).obj W)
        (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
          (RingedSite.internalHomSheaf X A B)).val.obj W) :=
      (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)).val.obj W).isModule
    letI : AddCommGroup
        (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
          (RingedSite.internalHomSheaf X A B)).val.obj W) :=
      (((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
        (RingedSite.internalHomSheaf X A B)).val.obj W).isAddCommGroup
    letI : Module ((Oforget Y.O.obj).obj W)
        ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
          ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W) :=
      ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W).isModule
    letI : AddCommGroup
        ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
          ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W) :=
      ((RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B)).val.obj W).isAddCommGroup
    exact ConcreteCategory.ofHom (C := ModuleCat ((Oforget Y.O.obj).obj W))
      { toFun := fun α => sliceEquivSection F φ A B W.unop α
        map_add' := by
          intro α β
          apply PresheafOfModules.hom_ext
          intro T
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl
        map_smul' := by
          intro r α
          apply PresheafOfModules.hom_ext
          intro T
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          have key : (fRestr X.O.obj (F.obj W.unop) ((φ.hom.app W).hom r)
              ((Over.post F).op.obj T))
              = (φ.hom.app (op T.unop.left)).hom (fRestr Y.O.obj W.unop r T) := by
            have h := ConcreteCategory.congr_hom (φ.hom.naturality T.unop.hom.op) r
            simp only [RingCat.hom_comp, RingHom.coe_comp] at h
            exact h.symm
          change (fRestr X.O.obj (F.obj W.unop)
              ((φ.hom.app W).hom r) ((Over.post F).op.obj T)) •
                (ModuleCat.Hom.hom (α.app ((Over.post F).op.obj T)) x) = _
          rw [key]
          rfl }
  naturality := by
    intro W Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hO : (Over.map (F.map f.unop)).obj ((Over.post F).obj T.unop)
        = (Over.post F).obj ((Over.map f.unop).obj T.unop) :=
      congrArg Over.mk (F.map_comp T.unop.hom f.unop).symm
    have key : α.app (op ((Over.map (F.map f.unop)).obj ((Over.post F).obj T.unop)))
        = α.app (op ((Over.post F).obj ((Over.map f.unop).obj T.unop))) := by
      have h : HEq (α.app (op ((Over.map (F.map f.unop)).obj ((Over.post F).obj T.unop))))
          (α.app (op ((Over.post F).obj ((Over.map f.unop).obj T.unop)))) := by
        rw [hO]
      exact eq_of_heq h
    change (ModuleCat.Hom.hom (α.app (op ((Over.map (F.map f.unop)).obj
        ((Over.post F).obj T.unop))))) x = _
    rw [key]
    rfl

/-- **Internal Hom commutes with restriction along a functor that is an equivalence on
slices.** -/
def sliceEquivInternalHomIso :
    (_root_.SheafOfModules.pushforward.{max u v m} φ).obj (RingedSite.internalHomSheaf X A B) ≅
      RingedSite.internalHomSheaf Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B) :=
  let app : ∀ W, ((RingedSite.valOf Y ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
      (RingedSite.internalHomSheaf X A B))).obj W) ≅
      ((RingedSite.valOf Y (RingedSite.internalHomSheaf Y
        ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B))).obj W) := fun W => by
    letI : IsIso ((sliceEquivInternalHomHom F φ A B).app W) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (sliceEquivSection F φ A B W.unop)
      exact (sliceEquivSectionEquiv F φ A B W.unop).bijective
    exact asIso ((sliceEquivInternalHomHom F φ A B).app W)
  (_root_.SheafOfModules.fullyFaithfulForget
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).preimageIso
    (PresheafOfModules.isoMk app (by
      intro W Z f
      exact (sliceEquivInternalHomHom F φ A B).naturality f))

/-- At an object `W` of `C`, the transport restricts a local morphism along the slice functor
`C/W ⥤ D/u(W)`. -/
theorem sliceEquivInternalHomIso_hom_app (W : Y.Cᵒᵖ)
    (α : ((_root_.SheafOfModules.pushforward.{max u v m} φ).obj
      (RingedSite.internalHomSheaf X A B)).val.obj W)
    (T : (Over W.unop)ᵒᵖ)
    (x : ((restrFun Y.O.obj W.unop).obj
      ((_root_.SheafOfModules.pushforward.{m} φ).obj A).val).obj T) :
    ((((sliceEquivInternalHomIso F φ A B).hom.val.app W).hom α).app T).hom x =
      (α.app ((Over.post F).op.obj T)).hom x :=
  rfl

omit [F.IsCocontinuous Y.J X.J] hF [IsIso φ] in
/-- Restriction of modules along `u` commutes with the universe lift of their sections: both act
objectwise, one reindexing along `u` and the other applying `ULift` to each module of sections. -/
def pushforwardModuleULiftIso.{t} (M : _root_.SheafOfModules.{m}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.SheafOfModules.moduleULift.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        ((_root_.SheafOfModules.pushforward.{m} φ).obj M) ≅
      (_root_.SheafOfModules.pushforward.{max m t} φ).obj
        ((Stacks.SheafOfModules.moduleULift.{t, m}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl))

variable [EssentiallySmall.{m} X.C] [EssentiallySmall.{m} Y.C]

/-- **Internal Hom commutes with restriction along a functor that is an equivalence on slices**,
for the internal Hom read in the module universe of its arguments on essentially small sites
(`AlgebraicGeometry.RingedSite.internalHomSheafSmall`). It is
`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomIso` brought down along the fully faithful
universe lift. -/
def sliceEquivInternalHomSmallIso :
    (_root_.SheafOfModules.pushforward.{m} φ).obj (RingedSite.internalHomSheafSmall X A B) ≅
      RingedSite.internalHomSheafSmall Y ((_root_.SheafOfModules.pushforward.{m} φ).obj A)
        ((_root_.SheafOfModules.pushforward.{m} φ).obj B) :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v, m}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).preimageIso
    (pushforwardModuleULiftIso.{u, v, w, m} F φ _ ≪≫
      (_root_.SheafOfModules.pushforward.{max u v m} φ).mapIso
        (RingedSite.internalHomSheafSmallIso X A B) ≪≫
      sliceEquivInternalHomIso F φ A B ≪≫
      (RingedSite.internalHomSheafSmallIso Y _ _).symm)

end Stacks.SheafOfModules.InternalHom

end
