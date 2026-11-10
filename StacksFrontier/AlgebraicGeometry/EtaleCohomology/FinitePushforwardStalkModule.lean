module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# Stalks of a finite direct image of a sheaf of modules, and changing the geometric point

Let `f : X ⟶ Y` be a finite morphism of a big étale site, `ȳ` a geometric point of `Y` and `G` a
sheaf of `R`-modules on the small étale site of `X`. For every lift `x̄` of `ȳ` through `f` there
is an `R`-linear map from the stalk of `f_* G` at `ȳ` to the stalk of `G` at `x̄`, sending the germ
of a section over an étale neighbourhood `U` of `ȳ` (a section of `G` over `U ×_Y X`) to its germ
at `U ×_Y X` pointed by the lift. Together these maps are bijective: this is
[Tag 03QP](https://stacks.math.columbia.edu/tag/03QP), part (1), for sheaves of modules, obtained
from the statement for sheaves of sets (`AlgebraicGeometry.finitePushforwardStalkEquiv`) since the
forgetful functor commutes with the filtered colimits defining the stalks.

The decomposition is compatible with morphisms of geometric points: a morphism `θ : ȳ₁ ⟶ ȳ₂`
carries a lift `x̄₂` of `ȳ₂` to the lift `θ ≫ x̄₂` of `ȳ₁`, and the action of `θ` on the stalk of
`f_* G` (Tag 04FN) followed by the component at `θ ≫ x̄₂` is the component at `x̄₂` followed by the
action of `θ`, read as a morphism of geometric points of `X`. For an endomorphism `θ` of `ȳ`, such
as the geometric Frobenius at a closed point, this says that `θ` permutes the summands of
`(f_* G)_ȳ` along its action `x̄ ↦ θ ≫ x̄` on the lifts.

## Main definitions

* `AlgebraicGeometry.finitePushforwardStalkLiftHom`: the component at a lift, a morphism of
  `R`-modules.
* `AlgebraicGeometry.GeometricLifts.comap`, `AlgebraicGeometry.GeometricLifts.liftHom`: the lift
  `θ ≫ x̄` and the morphism of geometric points of `X` it comes with.

## Main results

* `AlgebraicGeometry.ι_finitePushforwardStalkLiftHom`: the component on germs.
* `AlgebraicGeometry.bijective_finitePushforwardStalkLiftHom`: Tag 03QP (1) for modules.
* `AlgebraicGeometry.geometricPointStalkMap_comp_finitePushforwardStalkLiftHom`: compatibility
  with morphisms of geometric points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Neighborhoods

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

/-- A point of an étale neighbourhood and a lift agree after composing to the base `Y`. -/
private theorem elements_comp_eq_lift_comp
    (U : (geometricPointFiber B Y.1 Y.property y).Elements) (x : GeometricLifts B f y) :
    U.2.1 ≫ B.inclusion.map
      (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) = x.1 ≫ B.inclusion.map f :=
  U.2.2.trans x.2.symm

/-- The pointed base change `AlgebraicGeometry.liftedEtaleNeighborhood` is functorial in the
étale neighbourhood: a morphism of neighbourhoods of `ȳ` base changes to a morphism of the pointed
neighbourhoods of the lift. -/
public theorem liftedEtaleNeighborhood_map
    {U V : (geometricPointFiber B Y.1 Y.property y).Elements} (g : U ⟶ V)
    (x : GeometricLifts B f y) :
    (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) y x)).map ((smallEtaleBaseChange B f).map g.1)
      (liftedEtaleNeighborhood B f y x U).2 = (liftedEtaleNeighborhood B f y x V).2 := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  apply Subtype.ext
  let hpb := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f).map B.inclusion
  let hpbU := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion
  have wU := elements_comp_eq_lift_comp B f y U x
  have wV := elements_comp_eq_lift_comp B f y V x
  change hpbU.lift U.2.1 x.1 wU ≫ B.inclusion.map
      ((Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map g.1)).left =
    hpb.lift V.2.1 x.1 wV
  apply hpb.hom_ext
  · rw [IsPullback.lift_fst]
    calc _ = hpbU.lift U.2.1 x.1 wU ≫ B.inclusion.map
          (((Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map g.1)).left ≫
            pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) := by
          rw [Functor.map_comp]
          exact Category.assoc _ _ _
      _ = (hpbU.lift U.2.1 x.1 wU ≫ B.inclusion.map
            (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f)) ≫
          B.inclusion.map ((SmallEtale.inclusion B Y.1 Y.property).map g.1).left := by
          rw [overBaseChangeMap_fst B f ((SmallEtale.inclusion B Y.1 Y.property).map g.1),
            Functor.map_comp, Category.assoc]
      _ = V.2.1 := by
          rw [IsPullback.lift_fst]
          simpa [geometricPointFiber] using congrArg (fun z => z.1) g.2
  · rw [IsPullback.lift_snd]
    calc _ = hpbU.lift U.2.1 x.1 wU ≫ B.inclusion.map
          (((Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map g.1)).left ≫
            pullback.snd (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) := by
          rw [Functor.map_comp]
          exact Category.assoc _ _ _
      _ = x.1 := by
          rw [overBaseChangeMap_snd B f ((SmallEtale.inclusion B Y.1 Y.property).map g.1),
            IsPullback.lift_snd]

end Neighborhoods

section Module

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)
  (R : Type) [Ring R]

/-- The forgetful functor of `R`-modules commutes with the colimit defining an étale stalk: the
category of étale neighbourhoods is cofiltered and essentially small. -/
public theorem preservesColimitsOfShape_forget_moduleCat_geometricPointFiber (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget (ModuleCat.{u + 1} R)) := by
  have : PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget AddCommGrpCat.{u + 1}) := by
    have : PreservesFilteredColimitsOfSize.{u, u, u + 1, u + 1, u + 2, u + 2}
        (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u, u + 1, u + 1, u + 2, u + 2}
        (forget AddCommGrpCat.{u + 1})
    exact Functor.Final.preservesColimitsOfShape_of_final
      (FinallySmall.fromFilteredFinalModel.{u} ((geometricPointFiber B S hS s).Elementsᵒᵖ)) _
  exact comp_preservesColimitsOfShape (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

attribute [local instance] preservesColimitsOfShape_forget_moduleCat_geometricPointFiber

/-- The cocone of germs at the lift `x̄`: a section of `f_* G` over a neighbourhood `U` of `ȳ`
is a section of `G` over `U ×_Y X`, and goes to its germ at `U ×_Y X` pointed by `x̄`. -/
public def finitePushforwardStalkLiftCocone
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (x : GeometricLifts B f y) :
    Cocone ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj G).obj) where
  pt := etaleStalk B X.1 X.property (geometricPointLift (B.inclusion.map f) y x) G.obj
  ι :=
    { app := fun U => colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
          (op (liftedEtaleNeighborhood B f y x U.unop))
      naturality := by
        intro U V g
        let h := Functor.Elements.homMk (x := liftedEtaleNeighborhood B f y x V.unop)
          (y := liftedEtaleNeighborhood B f y x U.unop) ((smallEtaleBaseChange B f).map g.unop.hom)
          (liftedEtaleNeighborhood_map B f y g.unop x)
        change G.obj.map (((smallEtaleBaseChange B f).map g.unop.1).op) ≫
            colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property
              (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
              (op (liftedEtaleNeighborhood B f y x V.unop)) =
          colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property
            (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
            (op (liftedEtaleNeighborhood B f y x U.unop)) ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w ((Functor.Elements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj) h.op }

/-- **The component at a lift of the stalk of a direct image**, for sheaves of `R`-modules:
the `R`-linear map `(f_* G)_ȳ ⟶ G_x̄` induced by the germs at the pointed base changes. -/
public def finitePushforwardStalkLiftHom
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (x : GeometricLifts B f y) :
    etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj ⟶
      etaleStalk B X.1 X.property (geometricPointLift (B.inclusion.map f) y x) G.obj :=
  colimit.desc _ (finitePushforwardStalkLiftCocone B f y R G x)

/-- The component at a lift on germs. -/
@[reassoc]
public theorem ι_finitePushforwardStalkLiftHom
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (x : GeometricLifts B f y) (U : (geometricPointFiber B Y.1 Y.property y).Elementsᵒᵖ) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj) U ≫
        finitePushforwardStalkLiftHom B f y R G x =
      colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj)
        (op (liftedEtaleNeighborhood B f y x U.unop)) :=
  colimit.ι_desc (finitePushforwardStalkLiftCocone B f y R G x) U

/-- The underlying sheaf of sets of a sheaf of `R`-modules. -/
public def moduleSheafUnderlyingTypeSheaf (S : Scheme.{u}) (hS : B.Contains S)
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} R)) :
    Sheaf (SmallEtale.topology B S hS) (Type (u + 1)) where
  obj := G.obj ⋙ forget (ModuleCat.{u + 1} R)
  property :=
    haveI : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
      ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0} (R := R)
    (Presheaf.isSheaf_iff_isSheaf_forget (J := SmallEtale.topology B S hS)
    (P' := G.obj) (forget (ModuleCat.{u + 1} R))).1 G.property

/-- The underlying set of an étale stalk of a sheaf of modules is the étale stalk of its
underlying sheaf of sets. -/
public def etaleStalkForgetModuleIso (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} R)) :
    (forget (ModuleCat.{u + 1} R)).obj (etaleStalk B S hS s G.obj) ≅
      etaleStalk B S hS s (moduleSheafUnderlyingTypeSheaf B R S hS G).obj :=
  preservesColimitIso (forget (ModuleCat.{u + 1} R))
      ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ G.obj) ≪≫
    (colimit.isColimit (((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ G.obj) ⋙
      forget (ModuleCat.{u + 1} R))).coconePointUniqueUpToIso
      (colimit.isColimit ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (moduleSheafUnderlyingTypeSheaf B R S hS G).obj))

/-- The comparison of `AlgebraicGeometry.etaleStalkForgetModuleIso` on germs. -/
public theorem forget_map_ι_etaleStalkForgetModuleIso_hom (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} R))
    (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    (forget (ModuleCat.{u + 1} R)).map
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ G.obj) U) ≫
      (etaleStalkForgetModuleIso B R S hS s G).hom =
    colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (moduleSheafUnderlyingTypeSheaf B R S hS G).obj) U := by
  change _ ≫ (preservesColimitIso _ _).hom ≫ (IsColimit.coconePointUniqueUpToIso _ _).hom = _
  rw [ι_preservesColimitIso_hom_assoc]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ U

/-- The underlying function of the component at a lift is the component for the underlying
sheaf of sets. -/
public theorem finitePushforwardStalkLiftHom_forget
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (x : GeometricLifts B f y)
    (z : (forget (ModuleCat.{u + 1} R)).obj (etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj)) :
    (etaleStalkForgetModuleIso B R X.1 X.property _ G).hom
        ((finitePushforwardStalkLiftHom B f y R G x).hom z) =
      finitePushforwardStalkComponent B f y (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G) x
        ((etaleStalkForgetModuleIso B R Y.1 Y.property y
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj G)).hom z) := by
  let D := (Functor.Elements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
    (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G).obj
  let E := (Functor.Elements.π (geometricPointFiber B X.1 X.property
    (geometricPointLift (B.inclusion.map f) y x))).op ⋙ G.obj
  obtain ⟨U, t, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{u + 1} R)) (colimit.isColimit D)) z
  have h1 : (finitePushforwardStalkLiftHom B f y R G x).hom ((colimit.ι D U).hom t) =
      (colimit.ι E (op (liftedEtaleNeighborhood B f y x U.unop))).hom t :=
    congrArg (fun φ => φ.hom t) (ι_finitePushforwardStalkLiftHom B f y R G x U)
  have h2 := ConcreteCategory.congr_hom (forget_map_ι_etaleStalkForgetModuleIso_hom B R X.1
    X.property (geometricPointLift (B.inclusion.map f) y x) G
    (op (liftedEtaleNeighborhood B f y x U.unop))) t
  have h3 := ConcreteCategory.congr_hom (forget_map_ι_etaleStalkForgetModuleIso_hom B R Y.1
    Y.property y (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G) U) t
  change (etaleStalkForgetModuleIso B R X.1 X.property _ G).hom
      ((finitePushforwardStalkLiftHom B f y R G x).hom ((colimit.ι D U).hom t)) =
    finitePushforwardStalkComponent B f y (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G) x
      ((etaleStalkForgetModuleIso B R Y.1 Y.property y _).hom ((colimit.ι D U).hom t))
  rw [h1]
  refine h2.trans ?_
  refine Eq.trans ?_ (congrArg (finitePushforwardStalkComponent B f y
    (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G) x) h3).symm
  exact (finitePushforwardStalkComponent_germ B f y
    (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G) x U.unop t).symm

/-- **Tag 03QP (1) for sheaves of modules.** For a finite `f`, the components at the lifts of
`ȳ` together give a bijection from the stalk of `f_* G` at `ȳ` onto the product of the stalks of
`G` at the lifts. -/
public theorem bijective_finitePushforwardStalkLiftHom [IsFinite (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)) :
    Function.Bijective (fun (z : etaleStalk (A := ModuleCat.{u + 1} R) B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj) (x : GeometricLifts B f y) =>
      (finitePushforwardStalkLiftHom B f y R G x).hom z) := by
  let eY := etaleStalkForgetModuleIso B R Y.1 Y.property y
    (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G)
  let eX := fun x : GeometricLifts B f y =>
    etaleStalkForgetModuleIso B R X.1 X.property (geometricPointLift (B.inclusion.map f) y x) G
  let e := finitePushforwardStalkEquiv B f y (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G)
  have hc : (fun z x => (eX x).hom ((finitePushforwardStalkLiftHom B f y R G x).hom z)) =
      (fun z => e (eY.hom z)) := by
    funext z x
    exact (finitePushforwardStalkLiftHom_forget B f y R G x z).trans
      (finitePushforwardStalkEquiv_apply B f y (moduleSheafUnderlyingTypeSheaf B R X.1 X.property G)
        (eY.hom z) x).symm
  have hb : Function.Bijective
      (fun z x => (eX x).hom ((finitePushforwardStalkLiftHom B f y R G x).hom z)) := by
    rw [hc]
    exact e.bijective.comp eY.toEquiv.bijective
  exact hb.of_comp_left (Equiv.piCongrRight (fun x => (eX x).toEquiv)).injective

end Module

/-! ### Changing the geometric point -/

section PointChange

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {y₁ y₂ : GeometricPoint Y.1}
  (θ : GeometricPoint.Hom y₁ y₂)

/-- A morphism of geometric points `θ : ȳ₁ ⟶ ȳ₂` carries a lift `x̄` of `ȳ₂` to the lift
`θ ≫ x̄` of `ȳ₁`. -/
public def GeometricLifts.comap (x : GeometricLifts B f y₂) : GeometricLifts B f y₁ :=
  ⟨θ.hom ≫ x.1, by rw [Category.assoc, x.2, θ.comm]⟩

/-- The morphism of geometric points of `X` from the lift `θ ≫ x̄` to the lift `x̄`. -/
public def GeometricLifts.liftHom (x : GeometricLifts B f y₂) :
    GeometricPoint.Hom (geometricPointLift (B.inclusion.map f) y₁ (GeometricLifts.comap B f θ x))
      (geometricPointLift (B.inclusion.map f) y₂ x) where
  hom := θ.hom
  comm := rfl

/-- The pointed base change of the restriction along `θ` of a neighbourhood of `ȳ₂` is the
restriction along `θ` of its pointed base change. -/
public theorem liftedEtaleNeighborhood_neighborhoodFunctor_comap (x : GeometricLifts B f y₂)
    (U : (geometricPointFiber B Y.1 Y.property y₂).Elements) :
    liftedEtaleNeighborhood B f y₁ (GeometricLifts.comap B f θ x)
        ((neighborhoodFunctor B Y.1 Y.property θ).obj U) =
      (neighborhoodFunctor B X.1 X.property (GeometricLifts.liftHom B f θ x)).obj
        (liftedEtaleNeighborhood B f y₂ x U) := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  refine congrArg (Functor.elementsMk _ _) (Subtype.ext ?_)
  let hpb := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion
  have w₂ := elements_comp_eq_lift_comp B f y₂ U x
  have w₁ : (θ.hom ≫ U.2.1) ≫ B.inclusion.map
      (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) =
        (θ.hom ≫ x.1) ≫ B.inclusion.map f := by
    rw [Category.assoc, w₂, Category.assoc]
  change hpb.lift (θ.hom ≫ U.2.1) (θ.hom ≫ x.1) w₁ = θ.hom ≫ hpb.lift U.2.1 x.1 w₂
  apply hpb.hom_ext
  · rw [IsPullback.lift_fst, Category.assoc, IsPullback.lift_fst]
  · rw [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd]

variable (R : Type) [Ring R]

/-- **The stalk decomposition of a direct image is compatible with morphisms of geometric
points**: for `θ : ȳ₁ ⟶ ȳ₂` and a lift `x̄` of `ȳ₂`, the action of `θ` on `(f_* G)` followed by
the component at `θ ≫ x̄` is the component at `x̄` followed by the action of `θ` on `G`, along the
morphism of geometric points `θ ≫ x̄ ⟶ x̄`. -/
public theorem geometricPointStalkMap_comp_finitePushforwardStalkLiftHom
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (x : GeometricLifts B f y₂) :
    (geometricPointStalkMap B Y.1 Y.property θ (ModuleCat.{u + 1} R)).app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj ≫
        finitePushforwardStalkLiftHom B f y₁ R G (GeometricLifts.comap B f θ x) =
      finitePushforwardStalkLiftHom B f y₂ R G x ≫
        (geometricPointStalkMap B X.1 X.property (GeometricLifts.liftHom B f θ x)
          (ModuleCat.{u + 1} R)).app G.obj := by
  have hY : (geometricPointStalkMap B Y.1 Y.property θ (ModuleCat.{u + 1} R)).app
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G).obj =
      colimit.pre ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property y₁)).op ⋙
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G).obj)
        (neighborhoodFunctor B Y.1 Y.property θ).op := rfl
  have hX : (geometricPointStalkMap B X.1 X.property (GeometricLifts.liftHom B f θ x)
      (ModuleCat.{u + 1} R)).app G.obj =
      colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y₁ (GeometricLifts.comap B f θ x)))).op ⋙ G.obj)
        (neighborhoodFunctor B X.1 X.property (GeometricLifts.liftHom B f θ x)).op := rfl
  rw [hY, hX]
  apply colimit.hom_ext
  intro U
  refine (colimit.ι_pre_assoc ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property y₁)).op ⋙
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj G).obj)
      (neighborhoodFunctor B Y.1 Y.property θ).op U _).trans ?_
  refine (ι_finitePushforwardStalkLiftHom B f y₁ R G (GeometricLifts.comap B f θ x) _).trans ?_
  refine Eq.trans ?_ ((ι_finitePushforwardStalkLiftHom_assoc B f y₂ R G x U _).trans
    (colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property
        (geometricPointLift (B.inclusion.map f) y₁ (GeometricLifts.comap B f θ x)))).op ⋙ G.obj)
      (neighborhoodFunctor B X.1 X.property (GeometricLifts.liftHom B f θ x)).op
      (op (liftedEtaleNeighborhood B f y₂ x U.unop)))).symm
  exact eq_of_heq (congr_arg_heq (colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1
    X.property (geometricPointLift (B.inclusion.map f) y₁ (GeometricLifts.comap B f θ x)))).op ⋙
      G.obj)) (congrArg op (liftedEtaleNeighborhood_neighborhoodFunctor_comap B f θ x U.unop)))

/-- `AlgebraicGeometry.geometricPointStalkMap_comp_finitePushforwardStalkLiftHom` for any lift `μ`
of `ȳ₁` equal to `θ ≫ x̄` and any morphism of geometric points `μ ⟶ x̄` with underlying morphism
that of `θ`; for an endomorphism `θ` of `ȳ` and a lift `x̄` fixed by it, this reads the action of
`θ` on the summand of `x̄` as an endomorphism of the geometric point `x̄`. -/
public theorem geometricPointStalkMap_comp_finitePushforwardStalkLiftHom_of_eq
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (μ : GeometricLifts B f y₁) (x : GeometricLifts B f y₂) (hμ : μ.1 = θ.hom ≫ x.1)
    (θX : GeometricPoint.Hom (geometricPointLift (B.inclusion.map f) y₁ μ)
      (geometricPointLift (B.inclusion.map f) y₂ x)) (hθ : θX.hom = θ.hom) :
    (geometricPointStalkMap B Y.1 Y.property θ (ModuleCat.{u + 1} R)).app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj G).obj ≫
        finitePushforwardStalkLiftHom B f y₁ R G μ =
      finitePushforwardStalkLiftHom B f y₂ R G x ≫
        (geometricPointStalkMap B X.1 X.property θX (ModuleCat.{u + 1} R)).app G.obj := by
  obtain rfl : μ = GeometricLifts.comap B f θ x := Subtype.ext hμ
  obtain ⟨h, c⟩ := θX
  subst hθ
  exact geometricPointStalkMap_comp_finitePushforwardStalkLiftHom B f θ R G x

end PointChange

end AlgebraicGeometry

end
