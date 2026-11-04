module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMapComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The stalks of a finite direct image of a sheaf of modules

Let `f : X ⟶ Y` be a finite morphism of a big étale site and `G` a sheaf of `Λ`-modules on
`X_étale`. For a geometric point `y` of `Y` the stalk of `f_* G` at `y` is the product of the
stalks of `G` at the lifts of `y` to `X` (Tag 03QP), as `Λ`-modules: the comparison map is the
`Λ`-linear map whose component at a lift `x` sends the germ of a section over an étale
neighbourhood `U` of `y` to the germ of the same section of `G` over `U ×_Y X`, pointed by `x`.
It is compatible with the maps of stalks along morphisms of geometric points (Tag 04FN): a
morphism `a : y ⟶ y'` carries the component at a lift `x'` of `y'` to the component at the lift
`a ≫ x'` of `y`.

## Main definitions

* `AlgebraicGeometry.liftedEtaleNeighborhoodMap`: the base change of a morphism of étale
  neighbourhoods, as a morphism of the lifted neighbourhoods.
* `AlgebraicGeometry.finitePushforwardModuleStalkComponent`: the component at a lift.

## Main results

* `AlgebraicGeometry.finitePushforwardModuleStalkComponent_germ`: the component on germs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

/-- The base change along `f` of a morphism `U ⟶ V` of étale neighbourhoods of `y` is a morphism
of the lifted neighbourhoods at any lift `x` of `y`. -/
public def liftedEtaleNeighborhoodMap
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    {U V : (geometricPointFiber B Y.1 Y.property y).Elements} (g : U ⟶ V) :
    liftedEtaleNeighborhood B f y x U ⟶ liftedEtaleNeighborhood B f y x V := by
  letI := hasPullbacks_bigEtaleSite B
  letI := preservesPullbacks_bigEtaleSiteInclusion B
  refine ⟨(smallEtaleBaseChange B f).map g.1, Subtype.ext ?_⟩
  change (liftedEtaleNeighborhood B f y x U).2.1 ≫
      (SmallEtale.toScheme B X.1 X.property).map ((smallEtaleBaseChange B f).map g.1) =
    (liftedEtaleNeighborhood B f y x V).2.1
  apply ((IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f).map B.inclusion).hom_ext
  · have hg : U.2.1 ≫ (SmallEtale.toScheme B Y.1 Y.property).map g.1 = V.2.1 :=
      congrArg Subtype.val g.2
    have hU := liftedEtaleNeighborhood_point_fst B f y x U
    have hV := liftedEtaleNeighborhood_point_fst B f y x V
    have key : ((Over.pullback f).map g.1.hom).left ≫ pullback.fst V.1.obj.hom f =
        pullback.fst U.1.obj.hom f ≫ g.1.hom.left :=
      pullback.lift_fst _ _ _
    have e1 : B.inclusion.map ((Over.pullback f).map g.1.hom).left ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) =
        B.inclusion.map (pullback.fst U.1.obj.hom f) ≫ B.inclusion.map g.1.hom.left := by
      rw [← Functor.map_comp, key, Functor.map_comp]
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e1).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ B.inclusion.map g.1.hom.left) hU).trans (hg.trans hV.symm)
  · have key : ((Over.pullback f).map g.1.hom).left ≫ pullback.snd V.1.obj.hom f =
        pullback.snd U.1.obj.hom f :=
      pullback.lift_snd _ _ _
    have e1 : B.inclusion.map ((Over.pullback f).map g.1.hom).left ≫
        B.inclusion.map (pullback.snd V.1.obj.hom f) =
        B.inclusion.map (pullback.snd U.1.obj.hom f) := by
      rw [← Functor.map_comp, key]
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e1).trans ?_)
    exact (liftedEtaleNeighborhood B f y x U).2.2.trans (liftedEtaleNeighborhood B f y x V).2.2.symm

variable (Λ : Type) [CommRing Λ]
  (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))

/-- The direct image `f_* G` of a sheaf of `Λ`-modules. -/
public abbrev moduleDirectImage :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ) :=
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G

/-- The cocone of germs at a lift `x`, over the étale neighbourhoods of `y`. -/
public def finitePushforwardModuleStalkCocone
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    Cocone ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (moduleDirectImage B f Λ G).obj) where
  pt := etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x) G.obj
  ι :=
    { app := fun U => colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
          (op (liftedEtaleNeighborhood B f y x U.unop))
      naturality := fun _ _ g =>
        (colimit.w ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
          (liftedEtaleNeighborhoodMap B f y x g.unop).op).trans (Category.comp_id _).symm }

/-- **The component at a lift `x` of the stalk of `f_* G` at `y`**: the germ at `y` of a section
over an étale neighbourhood `U` goes to the germ at `x` of the same section of `G` over
`U ×_Y X`, pointed by `x`. -/
public def finitePushforwardModuleStalkComponent
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    etaleStalk (A := ModuleCat.{u + 1} Λ) B Y.1 Y.property y (moduleDirectImage B f Λ G).obj ⟶
      etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x) G.obj :=
  colimit.desc _ (finitePushforwardModuleStalkCocone B f y Λ G x)

/-- The component on germs. -/
@[reassoc]
public theorem finitePushforwardModuleStalkComponent_germ
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (U : (geometricPointFiber B Y.1 Y.property y).Elements) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
        (moduleDirectImage B f Λ G).obj) (op U) ≫
        finitePushforwardModuleStalkComponent B f y Λ G x =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
        (op (liftedEtaleNeighborhood B f y x U)) :=
  colimit.ι_desc _ _

/-! ### Comparison with the stalks of the underlying sheaf of sets -/

/-- The underlying sheaf of sets of `G`. -/
public abbrev underlyingTypeSheaf :
    Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)) :=
  (sheafCompose (SmallEtale.topology B X.1 X.property) (forget (ModuleCat.{u + 1} Λ))).obj G

/-- The underlying set of the stalk of a presheaf of modules is the stalk of the underlying
presheaf of sets. -/
public def etaleStalkForgetIso {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    (forget (ModuleCat.{u + 1} Λ)).obj (etaleStalk (A := ModuleCat.{u + 1} Λ) B S hS s P) ≅
      etaleStalk B S hS s (P ⋙ forget (ModuleCat.{u + 1} Λ)) :=
  haveI := preservesFilteredColimitsOfSize_forget_moduleCatMax.{u, 0} Λ
  (((geometricPointSitePoint B S hS s).presheafFiberCompIso
    (forget (ModuleCat.{u + 1} Λ))).app P).symm

/-- The comparison of stalks on germs. -/
public theorem etaleStalkForgetIso_germ {S : Scheme.{u}} (hS : B.Contains S)
    (s : GeometricPoint S) (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (U : (geometricPointFiber B S hS s).Elements) (t : P.obj (op U.1)) :
    (etaleStalkForgetIso B Λ hS s P).hom
        ((colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) (op U)).hom t) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (P ⋙ forget (ModuleCat.{u + 1} Λ))) (op U) t := by
  have := preservesFilteredColimitsOfSize_forget_moduleCatMax.{u, 0} Λ
  have h := (geometricPointSitePoint B S hS s).toPresheafFiber_presheafFiberCompIso_hom_app
    (forget (ModuleCat.{u + 1} Λ)) U.1 U.2 P
  have h' := congrArg (fun φ => ((geometricPointSitePoint B S hS s).presheafFiberCompIso
    (forget (ModuleCat.{u + 1} Λ))).inv.app P (φ t)) h
  simp only [types_comp_apply, Iso.hom_inv_id_app_apply] at h'
  exact h'.symm

/-- The components of the stalk of `f_* G`, read on underlying sets, are the components of the
stalk of the direct image of the underlying sheaf of sets. -/
public theorem finitePushforwardStalkToProduct_etaleStalkForgetIso
    (z : etaleStalk (A := ModuleCat.{u + 1} Λ) B Y.1 Y.property y (moduleDirectImage B f Λ G).obj)
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}) :
    finitePushforwardStalkToProduct B f y (underlyingTypeSheaf B Λ G)
        ((etaleStalkForgetIso B Λ Y.property y (moduleDirectImage B f Λ G).obj).hom z) x =
      (etaleStalkForgetIso B Λ X.property (geometricPointLift (B.inclusion.map f) y x) G.obj).hom
        ((finitePushforwardModuleStalkComponent B f y Λ G x).hom z) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCatMax.{u, 0} Λ
  obtain ⟨U, u', t, rfl⟩ :=
    (geometricPointSitePoint B Y.1 Y.property y).toPresheafFiber_jointly_surjective
      (P := (moduleDirectImage B f Λ G).obj) z
  have h1 := etaleStalkForgetIso_germ B Λ Y.property y (moduleDirectImage B f Λ G).obj ⟨U, u'⟩ t
  have h2 := ConcreteCategory.congr_hom
    (finitePushforwardModuleStalkComponent_germ B f y Λ G x ⟨U, u'⟩) t
  have h3 := etaleStalkForgetIso_germ B Λ X.property (geometricPointLift (B.inclusion.map f) y x)
    G.obj (liftedEtaleNeighborhood B f y x ⟨U, u'⟩) t
  refine (congrArg (fun w => finitePushforwardStalkToProduct B f y (underlyingTypeSheaf B Λ G) w x)
    h1).trans ?_
  refine (finitePushforwardStalkToProduct_germ B f y (underlyingTypeSheaf B Λ G) ⟨U, u'⟩ t
    x).trans ?_
  refine h3.symm.trans ?_
  exact congrArg (etaleStalkForgetIso B Λ X.property (geometricPointLift (B.inclusion.map f) y x)
    G.obj).hom h2.symm

/-- **Stacks Project, Tag 03QP, part (1), for sheaves of modules.** For a finite morphism the
components at the lifts identify the stalk of `f_* G` at `y` with the product of the stalks of
`G` at the lifts of `y`. -/
public theorem finitePushforwardModuleStalkComponent_bijective [IsFinite (B.inclusion.map f)] :
    Function.Bijective fun z : etaleStalk (A := ModuleCat.{u + 1} Λ) B Y.1 Y.property y
        (moduleDirectImage B f Λ G).obj =>
      fun x => (finitePushforwardModuleStalkComponent B f y Λ G x).hom z := by
  let eY := etaleStalkForgetIso B Λ Y.property y (moduleDirectImage B f Λ G).obj
  let eX := fun x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom} =>
    etaleStalkForgetIso B Λ X.property (geometricPointLift (B.inclusion.map f) y x) G.obj
  have hfun : (fun z => fun x => (finitePushforwardModuleStalkComponent B f y Λ G x).hom z) =
      (fun w x => (eX x).inv (w x)) ∘ finitePushforwardStalkToProduct B f y
        (underlyingTypeSheaf B Λ G) ∘ eY.hom := by
    funext z x
    show _ = (eX x).inv (finitePushforwardStalkToProduct B f y (underlyingTypeSheaf B Λ G)
      (eY.hom z) x)
    rw [finitePushforwardStalkToProduct_etaleStalkForgetIso]
    exact ((eX x).toEquiv.symm_apply_apply _).symm
  rw [hfun]
  exact (Equiv.piCongrRight fun x => (eX x).toEquiv.symm).bijective.comp
    ((finitePushforwardStalkToProduct_bijective B f y (underlyingTypeSheaf B Λ G)).comp
      eY.toEquiv.bijective)

/-! ### Compatibility with morphisms of geometric points -/

section PointMap

variable {y y' : GeometricPoint Y.1} (a : GeometricPoint.Hom y y')

/-- A morphism `a : y ⟶ y'` and lifts `x` of `y` and `x'` of `y'` with `a ≫ x' = x` give a
morphism of geometric points of `X` from the lift `x` to the lift `x'`. -/
public def GeometricLifts.homOfComm
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (x' : {g : y'.source ⟶ X.1 // g ≫ B.inclusion.map f = y'.hom}) (h : a.hom ≫ x'.1 = x.1) :
    GeometricPoint.Hom (geometricPointLift (B.inclusion.map f) y x)
      (geometricPointLift (B.inclusion.map f) y' x') where
  hom := a.hom
  comm := h

/-- Lifting a neighbourhood restricted along `a` is restricting the lifted neighbourhood. -/
public theorem liftedEtaleNeighborhood_neighborhoodFunctor
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (x' : {g : y'.source ⟶ X.1 // g ≫ B.inclusion.map f = y'.hom}) (h : a.hom ≫ x'.1 = x.1)
    (U : (geometricPointFiber B Y.1 Y.property y').Elements) :
    liftedEtaleNeighborhood B f y x ((neighborhoodFunctor B Y.1 Y.property a).obj U) =
      (neighborhoodFunctor B X.1 X.property (GeometricLifts.homOfComm B f a x x' h)).obj
        (liftedEtaleNeighborhood B f y' x' U) := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  apply ((IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion).hom_ext
  · refine (liftedEtaleNeighborhood_point_fst B f y x
      ((neighborhoodFunctor B Y.1 Y.property a).obj U)).trans ?_
    show a.hom ≫ U.2.1 = (a.hom ≫ (liftedEtaleNeighborhood B f y' x' U).2.1) ≫ _
    exact (congrArg (a.hom ≫ ·) (liftedEtaleNeighborhood_point_fst B f y' x' U).symm).trans
      (Category.assoc _ _ _).symm
  · refine (liftedEtaleNeighborhood B f y x
      ((neighborhoodFunctor B Y.1 Y.property a).obj U)).2.2.trans ?_
    show x.1 = (a.hom ≫ (liftedEtaleNeighborhood B f y' x' U).2.1) ≫ _
    exact h.symm.trans ((congrArg (a.hom ≫ ·) (liftedEtaleNeighborhood B f y' x' U).2.2.symm).trans
      (Category.assoc _ _ _).symm)

/-- **The components of the stalk of `f_* G` are compatible with morphisms of geometric
points**: along `a : y ⟶ y'`, the component at a lift `x'` of `y'` goes to the component at a
lift `x` of `y` with `a ≫ x' = x`. -/
public theorem geometricPointStalkMap_comp_finitePushforwardModuleStalkComponent
    (x : {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom})
    (x' : {g : y'.source ⟶ X.1 // g ≫ B.inclusion.map f = y'.hom}) (h : a.hom ≫ x'.1 = x.1) :
    (geometricPointStalkMap B Y.1 Y.property a (ModuleCat.{u + 1} Λ)).app
        (moduleDirectImage B f Λ G).obj ≫
      finitePushforwardModuleStalkComponent B f y Λ G x =
    finitePushforwardModuleStalkComponent B f y' Λ G x' ≫
      (geometricPointStalkMap B X.1 X.property (GeometricLifts.homOfComm B f a x x' h)
        (ModuleCat.{u + 1} Λ)).app G.obj := by
  refine colimit.hom_ext fun U => ?_
  have hA := colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
    (moduleDirectImage B f Λ G).obj) (neighborhoodFunctor B Y.1 Y.property a).op U
  have hB := colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
    (neighborhoodFunctor B X.1 X.property (GeometricLifts.homOfComm B f a x x' h)).op
    (op (liftedEtaleNeighborhood B f y' x' U.unop))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ finitePushforwardModuleStalkComponent B f y Λ G x) hA).trans ?_
  refine (finitePushforwardModuleStalkComponent_germ B f y Λ G x
    ((neighborhoodFunctor B Y.1 Y.property a).obj U.unop)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ (geometricPointStalkMap B X.1 X.property
    (GeometricLifts.homOfComm B f a x x' h) (ModuleCat.{u + 1} Λ)).app G.obj)
    (finitePushforwardModuleStalkComponent_germ B f y' Λ G x' U.unop)).symm
  refine Eq.trans ?_ hB.symm
  have h' := congrArg op (liftedEtaleNeighborhood_neighborhoodFunctor B f a x x' h U.unop)
  refine (colimit.w _ (eqToHom h')).symm.trans ?_
  simp only [eqToHom_map]
  exact Category.id_comp _

end PointMap

end AlgebraicGeometry

end
