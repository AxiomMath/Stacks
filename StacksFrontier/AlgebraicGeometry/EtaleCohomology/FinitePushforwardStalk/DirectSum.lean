module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Bijectivity
import all Mathlib.CategoryTheory.Limits.HasLimits
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

/-!
# The stalk of a finite direct image of an abelian sheaf as a direct sum

The abelian version of Tag 03QP, part (1): for a finite morphism, the stalk of the direct image
of an abelian sheaf at a geometric point is the direct sum of the stalks over its lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

section Abelian

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (y : GeometricPoint Y.1)

/-- Lifts of a geometric point through a morphism, retaining its chosen field. -/
public abbrev GeometricLifts :=
  {g : y.source ⟶ X.1 // g ≫ B.inclusion.map f = y.hom}

/-- A finite morphism has finitely many geometric lifts of a point. -/
public theorem finite_geometricLifts [IsFinite (B.inclusion.map f)] :
    Finite (GeometricLifts B f y) :=
  finite_geometricPointLifts (B.inclusion.map f) y

/-- The map on a geometric stalk induced by a morphism of abelian sheaves. -/
public noncomputable def etaleStalkMap (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}}
    (α : F ⟶ G) :
    AlgebraicGeometry.etaleStalk B S hS s F.obj ⟶
      AlgebraicGeometry.etaleStalk B S hS s G.obj :=
  colim.map (Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B S hS s)).op) α.hom)

private def liftedNeighborhood
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (x : GeometricLifts B f y) :
    (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x)).Elements := by
  let := AlgebraicGeometry.hasPullbacks_bigEtaleSite B
  let := AlgebraicGeometry.preservesPullbacks_bigEtaleSiteInclusion B
  let hxy : x.1 ≫ B.inclusion.map f = U.2.1 ≫ B.inclusion.map U.1.obj.hom := by
    calc
      x.1 ≫ B.inclusion.map f = y.hom := x.2
      _ = U.2.1 ≫ B.inclusion.map U.1.obj.hom := U.2.2.symm
  let hpb := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion
  let p := hpb.lift U.2.1 x.1 hxy.symm
  refine ⟨(smallEtaleBaseChange B f).obj U.1, ?_⟩
  refine ⟨p, ?_⟩
  change p ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1
  simp [p]

private theorem liftedNeighborhood_map
    {U V : (geometricPointFiber B Y.1 Y.property y).Elements}
    (g : U ⟶ V) (x : GeometricLifts B f y) :
    (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x)).map ((smallEtaleBaseChange B f).map g.1)
      (liftedNeighborhood B f y U x).2 = (liftedNeighborhood B f y V x).2 := by
  apply Subtype.ext
  let hpb := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f).map B.inclusion
  let hpbU := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion
  have wU : U.2.1 ≫ B.inclusion.map
      (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) = x.1 ≫ B.inclusion.map f := by
    calc
      U.2.1 ≫ B.inclusion.map
          (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) = y.hom := U.2.2
      _ = x.1 ≫ B.inclusion.map f := x.2.symm
  let pU := hpbU.lift U.2.1 x.1 wU
  apply hpb.hom_ext
  · have hliftfst := hpbU.lift_fst U.2.1 x.1 wU
    have hmap := overBaseChangeMap_fst B f
      ((SmallEtale.inclusion B Y.1 Y.property).map g.1)
    have hg := congrArg (fun z => z.1) g.2
    show pU ≫ B.inclusion.map
          ((Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map g.1)).left ≫
        B.inclusion.map (pullback.fst (Over.hom
          ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) =
      (liftedNeighborhood B f y V x).2.1 ≫ B.inclusion.map
        (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f)
    calc
      _ = pU ≫ B.inclusion.map
          (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f ≫
            ((SmallEtale.inclusion B Y.1 Y.property).map g.1).left) := by
          rw [← B.inclusion.map_comp, hmap]
      _ = (pU ≫ B.inclusion.map
          (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f)) ≫
            B.inclusion.map ((SmallEtale.inclusion B Y.1 Y.property).map g.1).left := by
          rw [B.inclusion.map_comp]
          cat_disch
      _ = U.2.1 ≫ B.inclusion.map ((SmallEtale.inclusion B Y.1 Y.property).map g.1).left := by
          rw [hliftfst]
      _ = V.2.1 := by simpa [geometricPointFiber] using hg
      _ = (liftedNeighborhood B f y V x).2.1 ≫ B.inclusion.map
          (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) := by
          symm
          show hpb.lift V.2.1 x.1 _ ≫ B.inclusion.map
            (pullback.fst (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) = _
          simp
  · have hliftsnd := hpbU.lift_snd U.2.1 x.1 wU
    have hmap := overBaseChangeMap_snd B f
      ((SmallEtale.inclusion B Y.1 Y.property).map g.1)
    show pU ≫ B.inclusion.map
          ((Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map g.1)).left ≫
        B.inclusion.map (pullback.snd (Over.hom
          ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) =
      (liftedNeighborhood B f y V x).2.1 ≫ B.inclusion.map
        (pullback.snd (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f)
    calc
      _ = pU ≫ B.inclusion.map
          (pullback.snd (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f) := by
            rw [← B.inclusion.map_comp, hmap]
      _ = x.1 := by rw [hliftsnd]
      _ = (liftedNeighborhood B f y V x).2.1 ≫
            B.inclusion.map (pullback.snd
              (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj V.1)) f) := by
            symm
            exact (liftedNeighborhood B f y V x).2.2

private def pointedPullbackNeighborhoodMap
    (x : GeometricLifts B f y)
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x)).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (hU : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1)
    (hX : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1) :
    V ⟶ liftedNeighborhood B f y U x := by
  let hpb := (IsPullback.of_hasPullback
    (Over.hom ((SmallEtale.inclusion B Y.1 Y.property).obj U.1)) f).map B.inclusion
  refine CategoryOfElements.homMk V (liftedNeighborhood B f y U x) t ?_
  apply Subtype.ext
  apply hpb.hom_ext
  · change V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      (liftedNeighborhood B f y U x).2.1 ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f)
    calc
      _ = U.2.1 := hU
      _ = (liftedNeighborhood B f y U x).2.1 ≫
          B.inclusion.map (pullback.fst U.1.obj.hom f) := by
        symm
        simp [liftedNeighborhood]
  · change V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f) =
      (liftedNeighborhood B f y U x).2.1 ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f)
    calc
      _ = x.1 := hX
      _ = (liftedNeighborhood B f y U x).2.1 ≫
          B.inclusion.map (pullback.snd U.1.obj.hom f) := by
        symm
        exact (liftedNeighborhood B f y U x).2.2

private noncomputable def stalkPushforwardComponentCocone
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y) :
    Cocone ((CategoryOfElements.π
      (geometricPointFiber B Y.1 Y.property y)).op ⋙
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj) := by
  let u := smallEtaleBaseChange B f
  let q := geometricPointFiber B Y.1 Y.property y
  let r := geometricPointFiber B X.1 X.property
    (geometricPointLift
      (B.inclusion.map f) y x)
  let D := (CategoryOfElements.π q).op ⋙
    (((u.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.1 Y.property)
      (SmallEtale.topology B X.1 X.property)).obj F).obj)
  let E := (CategoryOfElements.π r).op ⋙ F.obj
  let c : Cocone D := {
    pt := colimit E
    ι := {
      app := fun U => by
        exact colimit.ι E (Opposite.op (liftedNeighborhood B f y U.unop x))
      naturality := by
        intro U V g
        let h := CategoryOfElements.homMk
          (liftedNeighborhood B f y V.unop x)
          (liftedNeighborhood B f y U.unop x)
          (u.map g.unop.1)
          (liftedNeighborhood_map B f y g.unop x)
        change F.obj.map ((u.map g.unop.1).op) ≫
          colimit.ι E (Opposite.op (liftedNeighborhood B f y V.unop x)) =
            colimit.ι E (Opposite.op (liftedNeighborhood B f y U.unop x))
        exact colimit.w E h.op
    }
  }
  exact c

private noncomputable def stalkPushforwardComponentHom
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y) :
    AlgebraicGeometry.etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj ⟶
      AlgebraicGeometry.etaleStalk B X.1 X.property
        (geometricPointLift
          (B.inclusion.map f) y x) F.obj :=
  colimit.desc _ (stalkPushforwardComponentCocone B f y F x)

/-- The component map sends the germ at `U` to the germ at its pulled-back neighborhood. -/
private theorem stalkPushforwardComponentHom_ι
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y)
    (U : (geometricPointFiber B Y.1 Y.property y).Elementsᵒᵖ) :
    colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj) U ≫
        stalkPushforwardComponentHom B f y F x =
      colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y x))).op ⋙ F.obj)
        (op (liftedNeighborhood B f y U.unop x)) :=
  colimit.ι_desc (stalkPushforwardComponentCocone B f y F x) U

private theorem stalkPushforwardComponentHom_germ
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y)
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x)).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (hU : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1)
    (hX : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1) :
    colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj)
        (op U) ≫ stalkPushforwardComponentHom B f y F x =
      F.obj.map t.op ≫ colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y x))).op ⋙ F.obj)
        (op V) := by
  let k := pointedPullbackNeighborhoodMap B f y x U V t hU hX
  let E := (CategoryOfElements.π
    (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x))).op ⋙ F.obj
  rw [stalkPushforwardComponentHom_ι B f y F x (op U)]
  exact (colimit.w E k.op).symm

private def underlyingGroupSheaf (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    Sheaf (SmallEtale.topology B S hS) (Type (u + 1)) where
  obj := F.obj ⋙ forget AddCommGrpCat
  property := (Presheaf.isSheaf_iff_isSheaf_forget
    (J := SmallEtale.topology B S hS) (P' := F.obj)
    (forget AddCommGrpCat.{u + 1})).1 F.property


private theorem etaleStalk_preservesColimits
    (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget AddCommGrpCat.{u + 1}) := by
  let : IsCofiltered (geometricPointFiber B S hS s).Elements :=
    isCofiltered_geometricPointFiber_elements B S hS s
  let : PreservesFilteredColimitsOfSize.{u, u, u + 1, u + 1, u + 2, u + 2}
      (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u, u + 1, u + 1, u + 2, u + 2}
      (forget AddCommGrpCat.{u + 1})
  exact Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u}
      ((geometricPointFiber B S hS s).Elementsᵒᵖ)) _

attribute [local instance] etaleStalk_preservesColimits

private noncomputable def etaleStalkForgetIso
    (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    (forget AddCommGrpCat.{u + 1}).obj (AlgebraicGeometry.etaleStalk B S hS s F.obj) ≅
      AlgebraicGeometry.etaleStalk B S hS s (underlyingGroupSheaf B S hS F).obj :=
  preservesColimitIso (forget AddCommGrpCat.{u + 1})
    ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F.obj)

private theorem etaleStalkForgetIso_ι
    (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    (forget AddCommGrpCat.{u + 1}).map (colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ F.obj) U) ≫
      (etaleStalkForgetIso B S hS s F).hom =
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
      (underlyingGroupSheaf B S hS F).obj) U :=
  ι_preservesColimitIso_hom _ _ _


private theorem counitStalk_germ
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (x : GeometricPoint X.1)
    (y : GeometricPoint Y.1) (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property x).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (ht : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
      B.inclusion.map (pullback.fst U.1.obj.hom f) =
        eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) h) ≫ U.2.1)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U.1))) :
    (etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).counit.app F)
      (((smallEtalePullbackStalkIso B f x).inv.app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F))
        (h.symm ▸ (colimit.ι
          ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
            (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj) (op U) s))) =
      colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B X.1 X.property x)).op ⋙ F.obj)
        (op V) (F.obj.map t.op s) :=
  pushforwardEtaleStalkComponent_germ B f x y h F U V t ht s

private theorem stalkPushforwardComponentHom_forget
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y) :
    (forget AddCommGrpCat.{u + 1}).map (stalkPushforwardComponentHom B f y F x) ≫
      (etaleStalkForgetIso B X.1 X.property
        (geometricPointLift
          (B.inclusion.map f) y x) F).hom =
    (etaleStalkForgetIso B Y.1 Y.property y
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).obj F)).hom ≫
      (↾finitePushforwardStalkComponent B f y
        (underlyingGroupSheaf B X.1 X.property F) x) := by
  let P := ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj F
  let D := (CategoryOfElements.π
    (geometricPointFiber B Y.1 Y.property y)).op ⋙ P.obj
  let z := geometricPointLift
    (B.inclusion.map f) y x
  let E := (CategoryOfElements.π
    (geometricPointFiber B X.1 X.property z)).op ⋙ F.obj
  let eX := etaleStalkForgetIso B X.1 X.property z F
  let eY := etaleStalkForgetIso B Y.1 Y.property y P
  let C := finitePushforwardStalkComponent B f y
    (underlyingGroupSheaf B X.1 X.property F) x
  apply (isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) (colimit.isColimit D)).hom_ext
  intro U
  show (forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫
      (forget AddCommGrpCat.{u + 1}).map (stalkPushforwardComponentHom B f y F x) ≫
        eX.hom = (forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫ eY.hom ≫ (↾C)
  have hmc : (forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫
      (forget AddCommGrpCat.{u + 1}).map (stalkPushforwardComponentHom B f y F x) =
      (forget AddCommGrpCat.{u + 1}).map
        (colimit.ι D U ≫ stalkPushforwardComponentHom B f y F x) :=
    ((forget AddCommGrpCat.{u + 1}).map_comp _ _).symm
  rw [← Category.assoc, hmc, stalkPushforwardComponentHom_ι B f y F x U]
  show (forget AddCommGrpCat.{u + 1}).map
      (colimit.ι E (op (liftedNeighborhood B f y U.unop x))) ≫
      (etaleStalkForgetIso B X.1 X.property z F).hom =
    (forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫
      (etaleStalkForgetIso B Y.1 Y.property y P).hom ≫ (↾C)
  have hassoc : (forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫
      (etaleStalkForgetIso B Y.1 Y.property y P).hom ≫ (↾C) =
      ((forget AddCommGrpCat.{u + 1}).map (colimit.ι D U) ≫
        (etaleStalkForgetIso B Y.1 Y.property y P).hom) ≫ (↾C) :=
    (Category.assoc _ _ _).symm
  rw [etaleStalkForgetIso_ι, hassoc, etaleStalkForgetIso_ι]
  ext s
  symm
  let hxy : z.map (B.inclusion.map f) = y :=
    congrArg (fun h : y.source ⟶ Y.1 => ({ y with hom := h } : GeometricPoint Y.1)) x.property
  have ht : (liftedNeighborhood B f y U.unop x).2.1 ≫
      (SmallEtale.toScheme B X.1 X.property).map (𝟙 _) ≫
      B.inclusion.map (pullback.fst U.unop.1.obj.hom f) =
      eqToHom (congrArg (fun q : GeometricPoint Y.1 => q.source) hxy) ≫
        U.unop.2.1 := by
    simp [liftedNeighborhood]
  have h := counitStalk_germ B f z y hxy
    (underlyingGroupSheaf B X.1 X.property F) U.unop
    (liftedNeighborhood B f y U.unop x) (𝟙 _) ht s
  have hs := ConcreteCategory.congr_hom
    (F.obj.map_id (op (liftedNeighborhood B f y U.unop x).1)) s
  change (underlyingGroupSheaf B X.1 X.property F).obj.map (𝟙 _).op s = s at hs
  exact h.trans (congrArg (fun v => colimit.ι
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property z)).op ⋙
      (underlyingGroupSheaf B X.1 X.property F).obj)
    (op (liftedNeighborhood B f y U.unop x)) v) hs)

private theorem isIso_pi_lift_of_bijective
    {ι : Type u} {A : AddCommGrpCat.{u + 1}} (G : ι → AddCommGrpCat.{u + 1})
    (a : ∀ i, A ⟶ G i) (h : Function.Bijective (fun z i => a i z)) :
    IsIso (Pi.lift a) := by
  let U := forget AddCommGrpCat.{u + 1}
  let e := PreservesProduct.iso U G ≪≫ Types.productIso.{u, u + 1} (fun i => U.obj (G i))
  have he : U.map (Pi.lift a) ≫ e.hom = (↾fun z i => a i z) := by
    ext z i
    show ((U.map (Pi.lift a) ≫ (PreservesProduct.iso U G).hom) ≫
      Pi.π (fun i => U.obj (G i)) i) z = _
    rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
      ← U.map_comp, Pi.lift_π]
    rfl
  have : IsIso (U.map (Pi.lift a) ≫ e.hom) := by
    rw [he]
    exact (CategoryTheory.isIso_iff_bijective _).2 h
  have : IsIso (U.map (Pi.lift a)) := IsIso.of_isIso_comp_right _ e.hom
  exact isIso_of_reflects_iso (Pi.lift a) U

private theorem stalkPushforwardComponents_bijective
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun a x => stalkPushforwardComponentHom B f y F x a) := by
  let P := ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj F
  let eY := etaleStalkForgetIso B Y.1 Y.property y P
  let eX := fun x : GeometricLifts B f y => etaleStalkForgetIso B X.1 X.property
    (geometricPointLift
      (B.inclusion.map f) y x) F
  let e := finitePushforwardStalkEquiv
    B f y (underlyingGroupSheaf B X.1 X.property F)
  have hc : (fun a x => (eX x).hom (stalkPushforwardComponentHom B f y F x a)) =
      (fun a => e (eY.hom a)) := by
    funext a x
    exact (ConcreteCategory.congr_hom
        (stalkPushforwardComponentHom_forget B f y F x) a).trans
      (finitePushforwardStalkEquiv_apply B f y
        (underlyingGroupSheaf B X.1 X.property F) (eY.hom a) x).symm
  have hb : Function.Bijective
      (fun a x => (eX x).hom (stalkPushforwardComponentHom B f y F x a)) := by
    rw [hc]
    exact e.bijective.comp eY.toEquiv.bijective
  exact hb.of_comp_left (Equiv.piCongrRight (fun x => (eX x).toEquiv)).injective

private noncomputable def stalkPushforwardHomIntoSum
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) :
    AlgebraicGeometry.etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj ⟶
      ∐ fun x : GeometricLifts B f y =>
        AlgebraicGeometry.etaleStalk B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y x) F.obj := by
  classical
  let := finite_geometricLifts B f y
  let G := fun x : GeometricLifts B f y =>
    AlgebraicGeometry.etaleStalk B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x) F.obj
  let : HasBiproduct G := inferInstance
  exact Limits.Pi.lift (fun x => stalkPushforwardComponentHom B f y F x) ≫
    (biproduct.isoProduct G).inv ≫ (biproduct.isoCoproduct G).hom

private theorem stalkPushforwardHomIntoSum_π
    [IsFinite (B.inclusion.map f)]
    [DecidableEq (GeometricLifts B f y)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y) :
    stalkPushforwardHomIntoSum B f y F ≫ Limits.Sigma.π _ x =
      stalkPushforwardComponentHom B f y F x := by
  classical
  let := finite_geometricLifts B f y
  let G := fun x : GeometricLifts B f y =>
    AlgebraicGeometry.etaleStalk B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x) F.obj
  let : HasBiproduct G := inferInstance
  have hb : (biproduct.isoCoproduct G).hom ≫ Limits.Sigma.π G x =
      biproduct.π G x := by
    apply biproduct.hom_ext'
    intro j
    simp [biproduct.isoCoproduct_hom, biproduct.ι_desc_assoc,
      Sigma.ι_π, biproduct.ι_π]
  show Limits.Pi.lift (fun x => stalkPushforwardComponentHom B f y F x) ≫
    (biproduct.isoProduct G).inv ≫
      ((biproduct.isoCoproduct G).hom ≫ Limits.Sigma.π G x) = _
  rw [hb, biproduct.isoProduct_inv, biproduct.lift_π, Limits.Pi.lift_π]

private theorem stalkPushforwardComponentHom_natural
    [IsFinite (B.inclusion.map f)]
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}}
    (α : F ⟶ G) (x : GeometricLifts B f y) :
    etaleStalkMap B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).map α) ≫
      stalkPushforwardComponentHom B f y G x =
    stalkPushforwardComponentHom B f y F x ≫
      etaleStalkMap B X.1 X.property
        (geometricPointLift
          (B.inclusion.map f) y x) α := by
  change colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B Y.1 Y.property y)).op
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).map α).hom) ≫
      stalkPushforwardComponentHom B f y G x =
    stalkPushforwardComponentHom B f y F x ≫ colim.map (Functor.whiskerLeft (CategoryOfElements.π
        (geometricPointFiber B X.1 X.property
          (geometricPointLift (B.inclusion.map f) y x))).op α.hom)
  refine colimit.hom_ext fun U => ?_
  erw [colimit.ι_map_assoc, stalkPushforwardComponentHom_ι B f y G x U,
    ← Category.assoc, stalkPushforwardComponentHom_ι B f y F x U, colimit.ι_map]
  rfl

private theorem sigmaMap_comp_π
    {ι : Type u} [DecidableEq ι]
    {F G : ι → AddCommGrpCat.{u + 1}}
    [HasCoproduct F] [HasCoproduct G]
    (α : ∀ i, F i ⟶ G i) (i : ι) :
    Limits.Sigma.map α ≫ Limits.Sigma.π G i =
      Limits.Sigma.π F i ≫ α i := by
  apply Limits.Sigma.hom_ext
  intro j
  rw [Limits.Sigma.ι_map_assoc]
  by_cases h : j = i
  · subst h
    simp
  · rw [Limits.Sigma.ι_π_of_ne G h, Limits.Sigma.ι_π_of_ne_assoc F h]
    simp

/-- The stalk of a finite direct image is canonically the direct sum of its
stalks at the geometric lifts. -/
@[no_expose, stacks 03QP "part (1): the stalk of a finite pushforward, for abelian sheaves"]
public noncomputable def stalkPushforwardIsoDirectSum
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) :
    AlgebraicGeometry.etaleStalk B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).obj F).obj ≅
      ∐ fun x : GeometricLifts B f y =>
        AlgebraicGeometry.etaleStalk B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y x) F.obj :=
  by
    classical
    let e := stalkPushforwardHomIntoSum B f y F
    let := finite_geometricLifts B f y
    let G := fun x : GeometricLifts B f y =>
      AlgebraicGeometry.etaleStalk B X.1 X.property
        (geometricPointLift
          (B.inclusion.map f) y x) F.obj
    let : IsIso (Limits.Pi.lift (fun x => stalkPushforwardComponentHom B f y F x)) :=
      isIso_pi_lift_of_bijective G _ (stalkPushforwardComponents_bijective B f y F)
    let : IsIso e := by
      dsimp [e, stalkPushforwardHomIntoSum]
      infer_instance
    exact asIso e

/-- The `x`-th projection of the direct-sum isomorphism is the component map. -/
private theorem stalkPushforwardIsoDirectSum_hom_π
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y) :
    (stalkPushforwardIsoDirectSum B f y F).hom ≫ (by classical exact Limits.Sigma.π _ x) =
      stalkPushforwardComponentHom B f y F x :=
  by classical exact stalkPushforwardHomIntoSum_π B f y F x

/-- On each component, the finite direct-image stalk decomposition takes a
section over a neighborhood of `y` to its germ at a lift `x`, after pulling
the neighborhood back to `X`. The auxiliary neighborhood `V` is any étale
neighborhood of `x` mapping to that pullback and carrying the specified point. -/
@[stacks 03QP "part (1): the stalk of a finite pushforward, for abelian sheaves"]
public theorem stalkPushforwardIsoDirectSum_germ
    [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (x : GeometricLifts B f y)
    (U : (geometricPointFiber B Y.1 Y.property y).Elements)
    (V : (geometricPointFiber B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x)).Elements)
    (t : V.1 ⟶ (smallEtaleBaseChange B f).obj U.1)
    (hU : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1)
    (hX : V.2.1 ≫ (SmallEtale.toScheme B X.1 X.property).map t ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1) :
    colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property y)).op ⋙
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology B Y.1 Y.property)
            (SmallEtale.topology B X.1 X.property)).obj F).obj)
        (op U) ≫
      (stalkPushforwardIsoDirectSum B f y F).hom ≫
      (by classical exact Limits.Sigma.π _ x) =
    F.obj.map t.op ≫
      colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y x))).op ⋙ F.obj)
    (op V) := by
  classical
  erw [stalkPushforwardIsoDirectSum_hom_π]
  exact stalkPushforwardComponentHom_germ B f y F x U V t hU hX

/-- The finite direct-sum decomposition is natural in the abelian sheaf. -/
@[stacks 03QP "part (1): the stalk of a finite pushforward, for abelian sheaves"]
public theorem stalkPushforwardIsoDirectSum_natural
    [IsFinite (B.inclusion.map f)]
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}}
    (α : F ⟶ G) :
    etaleStalkMap B Y.1 Y.property y
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).map α) ≫
        (stalkPushforwardIsoDirectSum B f y G).hom =
      (stalkPushforwardIsoDirectSum B f y F).hom ≫
    Limits.Sigma.map (fun x : GeometricLifts B f y =>
          etaleStalkMap B X.1 X.property
            (geometricPointLift
              (B.inclusion.map f) y x) α) := by
  classical
  let := finite_geometricLifts B f y
  let H := fun x : GeometricLifts B f y =>
    AlgebraicGeometry.etaleStalk B X.1 X.property
      (geometricPointLift
        (B.inclusion.map f) y x) G.obj
  let : HasBiproduct H := inferInstance
  apply (cancel_mono (biproduct.isoCoproduct H).inv).1
  apply biproduct.hom_ext
  intro x
  have hproj : (biproduct.isoCoproduct H).inv ≫ biproduct.π H x =
      Limits.Sigma.π H x := by
    apply Limits.Sigma.hom_ext
    intro j
    simp [biproduct.isoCoproduct_inv,
      Sigma.ι_π, biproduct.ι_π]
  simp only [Category.assoc, hproj]
  have hFπ :
      (stalkPushforwardIsoDirectSum B f y F).hom ≫
          Limits.Sigma.map (fun j : GeometricLifts B f y =>
            etaleStalkMap B X.1 X.property
              (geometricPointLift
                (B.inclusion.map f) y j) α) ≫ Limits.Sigma.π H x =
        stalkPushforwardComponentHom B f y F x ≫
          etaleStalkMap B X.1 X.property
            (geometricPointLift
              (B.inclusion.map f) y x) α := by
    let K := fun j : GeometricLifts B f y =>
      AlgebraicGeometry.etaleStalk B X.1 X.property
        (geometricPointLift
          (B.inclusion.map f) y j) F.obj
    have hcomp := sigmaMap_comp_π
      (fun j : GeometricLifts B f y =>
        etaleStalkMap B X.1 X.property
          (geometricPointLift
            (B.inclusion.map f) y j) α) x
    have hFproj := stalkPushforwardIsoDirectSum_hom_π B f y F x
    calc
      _ = (stalkPushforwardIsoDirectSum B f y F).hom ≫
          (Limits.Sigma.π K x ≫
            etaleStalkMap B X.1 X.property
              (geometricPointLift
                (B.inclusion.map f) y x) α) := by
            rw [hcomp]
      _ = _ := by rw [← Category.assoc, hFproj]
  rw [stalkPushforwardIsoDirectSum_hom_π B f y G x]
  exact (stalkPushforwardComponentHom_natural B f y α x).trans hFπ.symm


end Abelian

end AlgebraicGeometry

end
