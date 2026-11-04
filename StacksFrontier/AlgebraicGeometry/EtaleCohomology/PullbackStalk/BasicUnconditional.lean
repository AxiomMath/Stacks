module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# BasicUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u v w r

namespace CategoryTheory.GrothendieckTopology.Point

open Opposite

section

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category.{v} A] [HasColimitsOfSize.{w, w} A]

end

section

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

end

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (q : Point.{w} K) (u : C ⥤ D) [RepresentablyFlat u]
  [u.IsContinuous J K] (hu : CoverPreserving J K u)
  [InitiallySmall.{w} (u ⋙ q.fiber).Elements]
  {A : Type*} [Category.{v} A] [HasProducts.{w} A]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

/-- Pull a section over `V` back to an étale neighborhood `U` mapping to the base change
of `V`. -/
public def pullbackSectionAlongUniv (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.1 S.property) (Type (max (u + 1) v)))
    (V : SmallEtale B S.1 S.property) (U : SmallEtale B T.1 T.property)
    (a : U ⟶ (smallEtaleBaseChange B f).obj V) :
    F.obj.obj (Opposite.op V) →
      (((smallEtaleBaseChange B f).sheafPullback (Type (max (u + 1) v))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).obj F).obj.obj (Opposite.op U) :=
  fun t =>
    let η := (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).unit.app F).hom.app (Opposite.op V)
    let ρ := (((smallEtaleBaseChange B f).sheafPullback (Type (max (u + 1) v))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).obj F).obj.map a.op
    ρ (η t)

/-- **Stacks 03Q1.** Pullback of an étale sheaf commutes naturally with taking stalks at a
geometric point. -/
@[sga "4½ Arcata 2.3.3" "(f^*F)_x̄ = F_f(x̄)"]
public def smallEtalePullbackStalkIsoUniv (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1) :
    (smallEtaleBaseChange B f).sheafPullback (Type (max (u + 1) v))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property) ⋙
      etaleStalkFunctor.{u, max (u + 1) v} B T.1 T.property x ≅
    etaleStalkFunctor.{u, max (u + 1) v} B S.1 S.property (x.map (B.inclusion.map f)) := by
  let J := SmallEtale.topology B S.1 S.property
  let K := SmallEtale.topology B T.1 T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.1 T.property x
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.1 S.property)
      ((SmallEtale.finalIsTerminal B S.1 S.property).isTerminalObj u)
  letI : HasFiniteLimits (SmallEtale B S.1 S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)) ≅
      u ⋙ geometricPointFiber B T.1 T.property x :=
    geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B S.1 S.property)
    (P := geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)))
    (Q := u ⋙ geometricPointFiber B T.1 T.property x) eFiber
  haveI : InitiallySmall.{u}
      (u ⋙ geometricPointFiber B T.1 T.property x).Elements := by
    have hModel : Functor.Initial (fromInitialModel.{u} p.fiber.Elements) := inferInstance
    have hEquiv : eElements.functor.IsEquivalence := eElements.isEquivalence_functor
    exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor hModel hEquiv⟩
  haveI : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    change InitiallySmall.{u} (u ⋙ geometricPointFiber B T.1 T.property x).Elements
    infer_instance
  letI : HasColimitsOfShape p.fiber.Elementsᵒᵖ (Type (max (u + 1) v)) :=
    hasColimitsOfShape_geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))
  letI : HasColimitsOfShape
      (u ⋙ geometricPointFiber B T.1 T.property x).Elementsᵒᵖ (Type (max (u + 1) v)) :=
    hasColimitsOfShape_of_finallySmall _ (Type (max (u + 1) v))
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIsoGeneral.{_, _, _, max (u + 1) v} J eFiber
  let eComap := q.sheafFiberComapIso u hcover (Type (max (u + 1) v))
  change (u.sheafPullback (Type (max (u + 1) v)) J K ⋙ q.sheafFiber) ≅ p.sheafFiber
  exact eComap.symm ≪≫ eStalk.symm

/-- **Stacks 03Q1.** The comparison sends the germ of a section pulled back to a pointed
étale neighborhood to the germ of the original section. -/
public theorem smallEtalePullbackStalkIso_germ_univ (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B S.1 S.property) (Type (max (u + 1) v)))
    (U : (geometricPointFiber B T.1 T.property x).Elements)
    (V : (geometricPointFiber B S.1 S.property
      (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B T.1 T.property).map a ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1)
    (t : F.obj.obj (Opposite.op V.1)) :
    ((smallEtalePullbackStalkIsoUniv B f x).hom.app F)
      ((colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B T.1 T.property x)).op ⋙
          (((smallEtaleBaseChange B f).sheafPullback (Type (max (u + 1) v))
            (SmallEtale.topology B S.1 S.property)
            (SmallEtale.topology B T.1 T.property)).obj F).obj)
        (Opposite.op U)) (pullbackSectionAlongUniv B f F V.1 U.1 a t)) =
      (colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B S.1 S.property
          (x.map (B.inclusion.map f)))).op ⋙ F.obj)
        (Opposite.op V)) t := by
  let J := SmallEtale.topology B S.1 S.property
  let K := SmallEtale.topology B T.1 T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.1 T.property x
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.1 S.property)
      ((SmallEtale.finalIsTerminal B S.1 S.property).isTerminalObj u)
  have : HasFiniteLimits (SmallEtale B S.1 S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  have : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : p.fiber ≅ u ⋙ q.fiber := geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso eFiber
  have : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    have hModel : Functor.Initial (fromInitialModel.{u} p.fiber.Elements) := inferInstance
    have hEquiv : eElements.functor.IsEquivalence := eElements.isEquivalence_functor
    exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor hModel hEquiv⟩
  have : HasColimitsOfShape p.fiber.Elementsᵒᵖ (Type (max (u + 1) v)) :=
    hasColimitsOfShape_geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))
  have : HasColimitsOfShape (u ⋙ q.fiber).Elementsᵒᵖ (Type (max (u + 1) v)) :=
    hasColimitsOfShape_of_finallySmall _ (Type (max (u + 1) v))
  let eComap := q.sheafFiberComapIso u hcover (Type (max (u + 1) v))
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIsoGeneral.{_, _, _, max (u + 1) v} J eFiber
  show ((eComap.symm ≪≫ eStalk.symm).hom.app F)
      (colimit.ι ((CategoryOfElements.π q.fiber).op ⋙
        ((u.sheafPullback (Type (max (u + 1) v)) J K).obj F).obj)
        (Opposite.op U) (pullbackSectionAlongUniv B f F V.1 U.1 a t)) =
    colimit.ι ((CategoryOfElements.π p.fiber).op ⋙ F.obj) (Opposite.op V) t
  have hpoint : q.fiber.map a U.2 = eFiber.hom.app V.1 V.2 := by
    apply (geometricPointFiberBaseChangeEquiv B f x V.1).symm.injective
    show (geometricPointFiberBaseChangeEquiv B f x V.1).symm (q.fiber.map a U.2) =
      (geometricPointFiberBaseChangeEquiv B f x V.1).symm
        (geometricPointFiberBaseChangeEquiv B f x V.1 V.2)
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    show (U.2.1 ≫ (SmallEtale.toScheme B T.1 T.property).map a) ≫
      eqToHom (smallEtaleBaseChange_toScheme_obj_eq B f V.1) ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1
    simpa using ha
  let G := (u.sheafPullback (Type (max (u + 1) v)) J K).obj F
  let η := ((u.sheafAdjunctionContinuous (Type (max (u + 1) v)) J K).unit.app F).hom.app
    (Opposite.op V.1)
  have hstalk := CategoryOfElements.ι_sheafColimIsoOfNatIso_hom_general J eFiber F V
  have hcomap := Point.toSheafFiber_sheafFiberComapIso_hom q u hcover F V.1
    (eFiber.hom.app V.1 V.2)
  have hw := q.toPresheafFiber_w a U.2 G.obj
  rw [hpoint] at hw
  have h : η ≫ G.obj.map a.op ≫ q.toPresheafFiber U.1 U.2 G.obj =
      p.toPresheafFiber V.1 V.2 F.obj ≫ eStalk.hom.app F ≫ eComap.hom.app F :=
    (congrArg (fun k => η ≫ k) hw).trans
      (hcomap.symm.trans
        (((congrArg (fun k => k ≫ eComap.hom.app F) hstalk).symm).trans
          (Category.assoc _ _ _)))
  let E := eStalk ≪≫ eComap
  have h' : η ≫ G.obj.map a.op ≫ q.toPresheafFiber U.1 U.2 G.obj =
      p.toPresheafFiber V.1 V.2 F.obj ≫ E.hom.app F := h
  have hh : (η ≫ G.obj.map a.op ≫ q.toPresheafFiber U.1 U.2 G.obj) ≫
      E.inv.app F = p.toPresheafFiber V.1 V.2 F.obj :=
    (congrArg (fun k => k ≫ E.inv.app F) h').trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => p.toPresheafFiber V.1 V.2 F.obj ≫ k) (E.hom_inv_id_app F)).trans
          (Category.comp_id _)))
  exact congrArg (fun k => k t) hh

end AlgebraicGeometry

end
