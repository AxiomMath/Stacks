module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition

/-!
# Associativity of the composition comparison for proper-support direct image

For three separated morphisms locally of finite type in a big étale site, the two ways of
comparing the thrice-iterated proper-support direct image with the proper-support direct image
along the triple composite agree: comparing the first two and then the outer composite gives
the same isomorphism as comparing the last two and then the inner composite, once the
associativity of composition of scheme morphisms is taken into account.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso_assoc`: the coherence square for the
  comparison isomorphisms of `AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso`.

## Implementation notes

The source draws the square with the arrows inverse to the composition comparisons; the
equality here is written with the comparisons in the forward direction, which is equivalent
because all four arrows are isomorphisms. The two parenthesizations of the composite
`f ≫ g ≫ h` are identified by `eqToHom`, and the corresponding transport of the direct image
functors and of the proper-support subsheaves is recorded in the auxiliary lemmas below.

Since the comparison isomorphisms are characterised by their squares with the monomorphisms
into the ordinary direct images, the coherence statement is proved by cancelling one of those
monomorphisms and comparing the two composites in the ordinary direct image, where the
corresponding coherence is the associativity of the comparison isomorphism of the étale
direct image functors.

## References

* [Stacks Project, Tag 0F77](https://stacks.math.columbia.edu/tag/0F77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section Pullbacks

variable {C : Type*} [Category C] [HasPullbacks C]

@[reassoc] private lemma pullbackComp_hom_fst_fst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Over Z) :
    ((Over.pullbackComp f g).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g =
      pullback.fst U.hom (f ≫ g) := by
  simpa [Over.pullbackComp] using congrArg (fun q => q.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv U)

private lemma pullback_eqToHom_fst {X Y : C} {f g : X ⟶ Y} (e : f = g) (U : Over Y) :
    ((eqToHom (congrArg (fun k : X ⟶ Y => Over.pullback k) e)).app U).left ≫ pullback.fst U.hom g =
      pullback.fst U.hom f := by
  subst g
  simp

private lemma pullbackComp_assoc {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (U : Over T) :
    (Over.pullbackComp (f ≫ g) h).hom.app U ≫
        (Over.pullbackComp f g).hom.app ((Over.pullback h).obj U) =
      (eqToHom (congrArg (fun k : X ⟶ T => Over.pullback k) (Category.assoc f g h))).app U ≫
        (Over.pullbackComp f (g ≫ h)).hom.app U ≫
        (Over.pullback f).map ((Over.pullbackComp g h).hom.app U) := by
  have hsnd := (Over.w ((Over.pullbackComp (f ≫ g) h).hom.app U ≫
        (Over.pullbackComp f g).hom.app ((Over.pullback h).obj U))).trans
    (Over.w ((eqToHom (congrArg (fun k : X ⟶ T => Over.pullback k)
        (Category.assoc f g h))).app U ≫
        (Over.pullbackComp f (g ≫ h)).hom.app U ≫
        (Over.pullback f).map ((Over.pullbackComp g h).hom.app U))).symm
  ext1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Over.comp_left, Category.assoc]
        have hm : ((Over.pullback f).map ((Over.pullbackComp g h).hom.app U)).left ≫
            pullback.fst ((Over.pullback h ⋙ Over.pullback g).obj U).hom f ≫
              pullback.fst (pullback.snd U.hom h) g ≫ pullback.fst U.hom h =
            (pullback.fst ((Over.pullback (g ≫ h)).obj U).hom f ≫
              ((Over.pullbackComp g h).hom.app U).left) ≫
                pullback.fst (pullback.snd U.hom h) g ≫ pullback.fst U.hom h :=
          pullback.lift_fst_assoc _ _ _ _
        simp only [Functor.comp_obj, Over.pullback_obj_hom, Category.assoc] at hm ⊢
        rw [hm]
        have hfg := pullbackComp_hom_fst_fst_assoc f g ((Over.pullback h).obj U)
          (pullback.fst U.hom h)
        simp only [Over.pullback_obj_hom] at hfg
        rw [hfg, pullbackComp_hom_fst_fst g h U, pullbackComp_hom_fst_fst (f ≫ g) h U,
          pullbackComp_hom_fst_fst f (g ≫ h) U,
          pullback_eqToHom_fst (Category.assoc f g h)]
      · simp only [Over.pullback_obj_hom, Category.assoc,
          pullback.condition, pullback.condition_assoc]
        simpa only [Functor.comp_obj, Over.pullback_obj_hom, Category.assoc] using
          congrArg (fun q => q ≫ f ≫ g) hsnd
    · simp only [Over.pullback_obj_hom, Category.assoc, pullback.condition]
      simpa only [Functor.comp_obj, Over.pullback_obj_hom, Category.assoc] using
        congrArg (fun q => q ≫ f) hsnd
  · exact hsnd

end Pullbacks

private lemma smallEtaleBaseChange_eqToHom_app
    (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    {f g : X ⟶ Y} (e : f = g) (U : SmallEtale B Y.obj Y.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((eqToHom (congrArg (fun k : X ⟶ Y => smallEtaleBaseChange B k) e)).app U) =
      (eqToHom (congrArg (fun k : X ⟶ Y => Over.pullback k) e)).app U.obj := by
  subst g
  simp

private lemma pushforward_eqToHom_app
    (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    {f g : X ⟶ Y} (e : f = g)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
    (((eqToHom (congrArg (fun k : X ⟶ Y =>
      (smallEtaleBaseChange B k).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)) e)).app F).hom.app U) =
      F.obj.map ((eqToHom (congrArg
        (fun k : X ⟶ Y => smallEtaleBaseChange B k) e.symm)).app U.unop).op := by
  subst g
  simp
  rfl

private lemma properSupport_eqToHom_comp_inclusion
    (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    {f g : X ⟶ Y} (e : f = g)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    (eqToHom (show SmallEtale.properSupportFunctor.{u,v} B f =
        SmallEtale.properSupportFunctor B g by subst g; rfl)).app F ≫
        (SmallEtale.fShriekSubsheaf B g F).val.arrow =
      (SmallEtale.fShriekSubsheaf B f F).val.arrow ≫
        (eqToHom (congrArg (fun k : X ⟶ Y =>
          (smallEtaleBaseChange B k).sheafPushforwardContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)) e)).app F := by
  subst g
  simp only [eqToHom_refl, NatTrans.id_app, fShriekSubsheaf_arrow, fShriekSubsheaf_obj_left,
    Category.comp_id]
  exact Category.id_comp _

private theorem smallEtaleBaseChange_compIso_inv_app
    (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : SmallEtale B Z.obj Z.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) =
      (Over.pullbackComp f g).hom.app U.obj := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  apply (cancel_mono ((Over.pullbackComp f g).inv.app U.obj)).1
  calc
    _ = (SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) ≫
          (SmallEtale.inclusion B X.obj X.property).map
            ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app U) :=
        congrArg
          (fun q => (SmallEtale.inclusion B X.obj X.property).map
            ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) ≫ q)
          (smallEtaleBaseChange_compIso_app B X Y Z f g U).symm
    _ = (SmallEtale.inclusion B X.obj X.property).map
          (((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) ≫
            (smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app U) := by
        rw [← Functor.map_comp]
    _ = _ := by simp

private lemma smallEtaleBaseChange_compIso_inv_assoc
    (B : BigEtaleSite.{u}) {X Y Z T : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (U : SmallEtale B T.obj T.property) :
      (smallEtaleBaseChange_compIso B X Z T (f ≫ g) h).val.inv.app U ≫
        (smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app
          ((smallEtaleBaseChange B h).obj U) =
      (eqToHom (congrArg (fun k : X ⟶ T => smallEtaleBaseChange B k)
        (Category.assoc f g h))).app U ≫
        (smallEtaleBaseChange_compIso B X Y T f (g ≫ h)).val.inv.app U ≫
        (smallEtaleBaseChange B f).map
          ((smallEtaleBaseChange_compIso B Y Z T g h).val.inv.app U) := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  apply (SmallEtale.inclusion B X.obj X.property).map_injective
  simp only [Functor.map_comp]
  rw [smallEtaleBaseChange_compIso_inv_app, smallEtaleBaseChange_compIso_inv_app]
  have hlast :
      (SmallEtale.inclusion B X.obj X.property).map
          ((smallEtaleBaseChange B f).map
            ((smallEtaleBaseChange_compIso B Y Z T g h).val.inv.app U)) =
        (Over.pullback f).map ((Over.pullbackComp g h).hom.app U.obj) := by
    calc
      _ = (Over.pullback f).map
          ((SmallEtale.inclusion B Y.obj Y.property).map
          ((smallEtaleBaseChange_compIso B Y Z T g h).val.inv.app U)) := rfl
      _ = _ := by
        rw [smallEtaleBaseChange_compIso_inv_app]
        rfl
  rw [smallEtaleBaseChange_compIso_inv_app, hlast,
    smallEtaleBaseChange_eqToHom_app B (Category.assoc f g h) U]
  exact pullbackComp_assoc f g h U.obj

private abbrev etalePushforward (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

private abbrev etalePushforwardCompIso (B : BigEtaleSite.{u})
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z f g).val AddCommGrpCat.{v}
    (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)

-- Component calculations normalize several nested pushforwards and equality transports.
private lemma etalePushforwardCompIso_assoc
    (B : BigEtaleSite.{u}) {X Y Z T : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    (etalePushforward B h).map ((etalePushforwardCompIso B f g).app F).hom ≫
        ((etalePushforwardCompIso B (f ≫ g) h).app F).hom =
      ((etalePushforwardCompIso B g h).app ((etalePushforward B f).obj F)).hom ≫
        ((etalePushforwardCompIso B f (g ≫ h)).app F).hom ≫
        (eqToHom (congrArg (fun k : X ⟶ T => etalePushforward.{u,v} B k)
          (Category.assoc f g h).symm)).app F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etalePushforward, etalePushforwardCompIso, Iso.app_hom,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    pushforward_eqToHom_app B (Category.assoc f g h).symm,
    Functor.sheafPushforwardContinuous_obj_obj_map]
  have hs := congrArg (fun q => F.obj.map q.op)
    (smallEtaleBaseChange_compIso_inv_assoc B f g h U.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at hs
  exact hs

/-- A composite of morphisms of a big étale site which are locally of finite type as morphisms
of schemes is again locally of finite type. -/
public lemma locallyOfFiniteType_map_comp (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map g)] :
    LocallyOfFiniteType (B.inclusion.map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

/-- A composite of separated morphisms of a big étale site is separated. -/
public lemma isSeparated_map_comp (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g)] :
    IsSeparated (B.inclusion.map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

/-- Canonical proper-support direct-image comparisons are associative. -/
@[stacks 0F77 "composition_coherence"]
public theorem properSupportFunctor_compIso_assoc
    (B : BigEtaleSite.{u}) {X Y Z T : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map h)] :
    letI := locallyOfFiniteType_map_comp B f g
    letI := locallyOfFiniteType_map_comp B g h
    letI := locallyOfFiniteType_map_comp B (f ≫ g) h
    letI := locallyOfFiniteType_map_comp B f (g ≫ h)
    letI := isSeparated_map_comp B f g
    letI := isSeparated_map_comp B g h
    let fBang := SmallEtale.properSupportFunctor.{u, v} B f
    let gBang := SmallEtale.properSupportFunctor.{u, v} B g
    let hBang := SmallEtale.properSupportFunctor.{u, v} B h
    (Functor.isoWhiskerRight
        (SmallEtale.properSupportFunctor_compIso.{u, v} B f g).val hBang ≪≫
      (SmallEtale.properSupportFunctor_compIso.{u, v} B (f ≫ g) h).val) =
    (Functor.associator fBang gBang hBang ≪≫
      Functor.isoWhiskerLeft fBang
        (SmallEtale.properSupportFunctor_compIso.{u, v} B g h).val ≪≫
      (SmallEtale.properSupportFunctor_compIso.{u, v} B f (g ≫ h)).val ≪≫
      eqToIso (by
        have heq : f ≫ (g ≫ h) = (f ≫ g) ≫ h := (Category.assoc f g h).symm
        cases heq
        rfl)) := by
  classical
  let _ := locallyOfFiniteType_map_comp B f g
  let _ := locallyOfFiniteType_map_comp B g h
  let _ := locallyOfFiniteType_map_comp B (f ≫ g) h
  let _ := locallyOfFiniteType_map_comp B f (g ≫ h)
  let _ := isSeparated_map_comp B f g
  let _ := isSeparated_map_comp B g h
  apply Iso.ext
  apply NatTrans.ext
  funext F
  let iFinal :=
    (SmallEtale.fShriekSubsheaf B ((f ≫ g) ≫ h) F).val.arrow
  let hBang := SmallEtale.properSupportFunctor B h
  have hfgMap : hBang.map ((SmallEtale.properSupportFunctor_compIso B f g).val.hom.app F) =
      hBang.map ((SmallEtale.properSupportSheaf_compIso B f g F).val.hom) :=
    congrArg hBang.map (congrArg Iso.hom
      ((SmallEtale.properSupportFunctor_compIso B f g).property F))
  have hOuter := (SmallEtale.properSupportFunctor_compIso B (f ≫ g) h).property F
  have hRight := (SmallEtale.properSupportFunctor_compIso B f (g ≫ h)).property F
  have hOuterProp := (SmallEtale.properSupportSheaf_compIso B (f ≫ g) h F).property
  let fSub := SmallEtale.fShriekSubsheaf B f F
  let gSub := SmallEtale.fShriekSubsheaf B g fSub.val.obj.left
  let fgSub := SmallEtale.fShriekSubsheaf B (f ≫ g) F
  let fBang := SmallEtale.properSupportFunctor B f
  let gOnlySub := SmallEtale.fShriekSubsheaf B g (fBang.obj F)
  let hGOnlySub := SmallEtale.fShriekSubsheaf B h gOnlySub.val.obj.left
  let ghSub := SmallEtale.fShriekSubsheaf B (g ≫ h) (fBang.obj F)
  let hFgSub := SmallEtale.fShriekSubsheaf B h fgSub.val.obj.left
  let hGfSub := SmallEtale.fShriekSubsheaf B h gSub.val.obj.left
  let hStar :=
    (smallEtaleBaseChange B h).sheafPushforwardContinuous AddCommGrpCat
      (SmallEtale.topology B T.obj T.property) (SmallEtale.topology B Z.obj Z.property)
  let hFgArrow : hBang.obj fgSub.val.obj.left ⟶
      hStar.obj fgSub.val.obj.left := hFgSub.val.arrow
  let hGfArrow : hBang.obj gSub.val.obj.left ⟶
      hStar.obj gSub.val.obj.left := hGfSub.val.arrow
  let gStar :=
    (smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat
      (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
  let fStar :=
    (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  let fgStarF :=
    ((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous
      AddCommGrpCat (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B X.obj X.property)).obj F
  let Dfg := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z f g).val
    AddCommGrpCat (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
  let DghGrp := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B Y Z T g h).val
    AddCommGrpCat (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)
  let Douter := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Z T (f ≫ g) h).val
    AddCommGrpCat (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)
  let Dright := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y T f (g ≫ h)).val
    AddCommGrpCat (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)
  let ghStar := (smallEtaleBaseChange B (g ≫ h)).sheafPushforwardContinuous
    AddCommGrpCat (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B Y.obj Y.property)
  let iRight := (SmallEtale.fShriekSubsheaf B (f ≫ (g ≫ h)) F).val.arrow
  let eStar := (eqToHom (congrArg (fun k : X ⟶ T =>
    (smallEtaleBaseChange B k).sheafPushforwardContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B X.obj X.property)) (Category.assoc f g h).symm)).app F
  let eBang := (eqToHom (show SmallEtale.properSupportFunctor.{u,v} B (f ≫ (g ≫ h)) =
      SmallEtale.properSupportFunctor B ((f ≫ g) ≫ h) by
        have heq : f ≫ (g ≫ h) = (f ≫ g) ≫ h := (Category.assoc f g h).symm
        cases heq
        rfl)).app F
  have hCast : eBang ≫ iFinal = iRight ≫ eStar :=
    properSupport_eqToHom_comp_inclusion B (Category.assoc f g h).symm F
  have hDA : hStar.map (Dfg.app F).hom ≫ (Douter.app F).hom =
      (DghGrp.app (fStar.obj F)).hom ≫ (Dright.app F).hom ≫ eStar :=
    etalePushforwardCompIso_assoc B f g h F
  have hDNat : hStar.map (gStar.map fSub.val.arrow) ≫ (DghGrp.app (fStar.obj F)).hom =
      (DghGrp.app fSub.val.obj.left).hom ≫ ghStar.map fSub.val.arrow :=
    DghGrp.hom.naturality fSub.val.arrow
  have hfgProp := (SmallEtale.properSupportSheaf_compIso B f g F).property
  let egh := SmallEtale.properSupportSheaf_compIso B g h (fBang.obj F)
  let eghHom : hBang.obj gSub.val.obj.left ⟶ ghSub.val.obj.left := egh.val.hom
  have hghProp : eghHom ≫ ghSub.val.arrow =
      hGfArrow ≫ hStar.map gSub.val.arrow ≫
        (DghGrp.app fSub.val.obj.left).hom := egh.property
  have hRightProp : (SmallEtale.properSupportSheaf_compIso B f (g ≫ h) F).val.hom ≫ iRight =
      ghSub.val.arrow ≫ ghStar.map fSub.val.arrow ≫ (Dright.app F).hom :=
    (SmallEtale.properSupportSheaf_compIso B f (g ≫ h) F).property
  have hNatLeft :
      hBang.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫ hFgArrow =
        hGfArrow ≫ hStar.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom := by
    simpa [hBang, hStar, hFgArrow, hGfArrow, hFgSub, hGfSub, fSub, gSub, fgSub,
      SmallEtale.properSupportFunctor] using
      (SmallEtale.fShriekMap B h
        gSub.val.obj.left fgSub.val.obj.left
        (SmallEtale.properSupportSheaf_compIso B f g F).val.hom).property
  have hOuterArrowEq := congrArg
    (fun q => hBang.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫ q)
    hOuterProp
  have hNatLeftEq := congrArg
    (fun q => q ≫ hStar.map fgSub.val.arrow ≫
      (Douter.app F).hom)
    hNatLeft
  have hfgPush := congrArg hStar.map hfgProp
  have hfgMapPush :
      hStar.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫
          hStar.map fgSub.val.arrow =
        hStar.map (gSub.val.arrow ≫ gStar.map fSub.val.arrow ≫ (Dfg.app F).hom) :=
    (hStar.map_comp _ _).symm.trans hfgPush
  have hOuterFinal := congrArg
    (fun q => (hBang.map ((SmallEtale.properSupportSheaf_compIso B f g F).val.hom) ≫ q) ≫ iFinal)
    (congrArg Iso.hom hOuter)
  apply (cancel_mono iFinal).1
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft,
    Functor.associator_hom_app, Functor.mapIso_hom, Iso.app_hom,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  refine Eq.trans (congrArg (fun q => (q ≫
    ((SmallEtale.properSupportFunctor_compIso B (f ≫ g) h).val.app F).hom) ≫ iFinal) hfgMap) ?_
  calc
    _ = (hBang.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫
          (SmallEtale.properSupportSheaf_compIso B (f ≫ g) h F).val.hom) ≫ iFinal := hOuterFinal
    _ = hBang.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫
        (hFgArrow ≫ hStar.map fgSub.val.arrow ≫
          (Douter.app F).hom) :=
      (Category.assoc _ _ _).trans hOuterArrowEq
    _ = hGfArrow ≫
        hStar.map (SmallEtale.properSupportSheaf_compIso B f g F).val.hom ≫
        hStar.map fgSub.val.arrow ≫
        (Douter.app F).hom := by
      simpa only [Category.assoc] using hNatLeftEq
    _ = hGfArrow ≫ hStar.map
          (gSub.val.arrow ≫ gStar.map fSub.val.arrow ≫ (Dfg.app F).hom) ≫
        (Douter.app F).hom := by
      simpa only [Category.assoc] using congrArg
        (fun q : hStar.obj gSub.val.obj.left ⟶ hStar.obj fgStarF =>
          hGfArrow ≫ q ≫
          (Douter.app F).hom)
        hfgMapPush
    _ = hGfArrow ≫ hStar.map gSub.val.arrow ≫
        hStar.map (gStar.map fSub.val.arrow) ≫
        (DghGrp.app (fStar.obj F)).hom ≫ (Dright.app F).hom ≫ eStar := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun q : hStar.obj (gStar.obj (fStar.obj F)) ⟶
            (etalePushforward B ((f ≫ g) ≫ h)).obj F =>
          hGfArrow ≫ hStar.map gSub.val.arrow ≫
            hStar.map (gStar.map fSub.val.arrow) ≫ q) hDA
    _ = hGfArrow ≫ hStar.map gSub.val.arrow ≫
        (DghGrp.app fSub.val.obj.left).hom ≫ ghStar.map fSub.val.arrow ≫
        (Dright.app F).hom ≫ eStar := by
      simpa only [Category.assoc] using congrArg
        (fun q : hStar.obj (gStar.obj fSub.val.obj.left) ⟶ ghStar.obj (fStar.obj F) =>
          hGfArrow ≫ hStar.map gSub.val.arrow ≫ q ≫ (Dright.app F).hom ≫ eStar)
        hDNat
    _ = eghHom ≫ ghSub.val.arrow ≫ ghStar.map fSub.val.arrow ≫
        (Dright.app F).hom ≫ eStar :=
      (congrArg
        (fun q => q ≫ ghStar.map fSub.val.arrow ≫ (Dright.app F).hom ≫ eStar)
        hghProp.symm).trans (Category.assoc _ _ _)
    _ = eghHom ≫ (SmallEtale.properSupportSheaf_compIso B f (g ≫ h) F).val.hom ≫
        iRight ≫ eStar :=
      (congrArg (fun q => eghHom ≫ q ≫ eStar) hRightProp.symm).trans
        (congrArg (fun q => eghHom ≫ q) (Category.assoc _ _ _))
    _ = eghHom ≫ (SmallEtale.properSupportSheaf_compIso B f (g ≫ h) F).val.hom ≫
        eBang ≫ iFinal :=
      congrArg
        (fun q => eghHom ≫ (SmallEtale.properSupportSheaf_compIso B f (g ≫ h) F).val.hom ≫ q)
        hCast.symm
    _ = _ := by
      have hRightHom := congrArg Iso.hom hRight
      simp only [Category.id_comp, eghHom, ← hRightHom]
      rfl

end AlgebraicGeometry.SmallEtale
