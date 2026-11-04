module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.GluingAction
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Morphisms of descent data from the gluing action

For descent data relative to a single morphism, a morphism of descent data is nothing more than a
morphism of the underlying schemes over `X` that commutes with the gluing action. This file
provides that recognition principle in the model of literal fibre products, together with the two
facts about a pullback functor that make the criterion checkable: its object isomorphism turns the
action of a pulled-back datum into the source map, and it intertwines the action with the base
change of a morphism.

## Main definitions

* `AlgebraicGeometry.DescentData.actOnMap` is the base change of a morphism of the underlying
  objects to the fibre products on which the action is defined.
* `AlgebraicGeometry.DescentData.homOfActOn` and
  `AlgebraicGeometry.DescentData.isoOfActOn` build a morphism, respectively an isomorphism, of
  descent data out of one that commutes with the action.

## Main results

* `AlgebraicGeometry.DescentData.PullbackFunctor.actOn_objIso_fst` describes the action of a
  pulled-back descent datum by the source map of the pullback functor.
* `AlgebraicGeometry.DescentData.PullbackFunctor.map_objIso_fst` is the action of the pullback
  functor on morphisms, read in the fibre-product model.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

variable {S X : Scheme.{u}} {a : X ⟶ S}

section ActOnMap

variable {D E : DescentData (fun _ : Unit ↦ a)} (e : D.obj () ⟶ E.obj ())

/-- A morphism of the underlying objects, base changed to the fibre products `V ×_S X` on which
the gluing action lives. -/
def actOnMap : pullback ((D.obj ()).hom ≫ a) a ⟶ pullback ((E.obj ()).hom ≫ a) a :=
  pullback.lift (pullback.fst _ _ ≫ e.left) (pullback.snd _ _)
    (by rw [Category.assoc, Over.w_assoc]; exact pullback.condition)

/-- The first projection of `actOnMap e` is the first projection followed by `e.left`. -/
@[reassoc]
lemma actOnMap_fst :
    actOnMap e ≫ pullback.fst ((E.obj ()).hom ≫ a) a =
      pullback.fst ((D.obj ()).hom ≫ a) a ≫ e.left :=
  pullback.lift_fst _ _ _

/-- `actOnMap e` commutes with the second projections to `X`. -/
@[reassoc]
lemma actOnMap_snd :
    actOnMap e ≫ pullback.snd ((E.obj ()).hom ≫ a) a =
      pullback.snd ((D.obj ()).hom ≫ a) a :=
  pullback.lift_snd _ _ _

/-- Under the isomorphisms `sourceProdIso` with the products over `S`, `actOnMap e` corresponds
to the product of `e`, viewed over `S`, with the identity of `X`. -/
lemma sourceProdIso_hom_actOnMap :
    D.sourceProdIso.hom ≫ actOnMap e =
      (prod.map ((Over.map a).map e) (𝟙 (Over.mk a))).left ≫ E.sourceProdIso.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, actOnMap_fst, Category.assoc, E.sourceProdIso_hom_fst,
      D.sourceProdIso_hom_fst_assoc]
    exact (congrArg Over.Hom.left (prod.map_fst ((Over.map a).map e) (𝟙 (Over.mk a)))).symm
  · rw [Category.assoc, actOnMap_snd, Category.assoc, E.sourceProdIso_hom_snd,
      D.sourceProdIso_hom_snd]
    have hm : prod.map ((Over.map a).map e) (𝟙 (Over.mk a)) ≫ prod.snd =
        (prod.snd : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ _) := by simp
    exact (congrArg Over.Hom.left hm).symm

/-- Commuting with the gluing action is exactly what makes a morphism of the underlying objects a
morphism of descent data. -/
def homOfActOn (h : D.actOn ≫ e.left = actOnMap e ≫ E.actOn) : D ⟶ E where
  hom _ := e
  comm i j := by
    cases i
    cases j
    have hprod : (prod.map ((Over.map a).map e) (𝟙 (Over.mk a))).left ≫
        (E.gluingAction).left = (D.gluingAction).left ≫ e.left := by
      rw [← E.sourceProdIso_hom_actOn, ← Category.assoc, ← sourceProdIso_hom_actOnMap,
        Category.assoc, ← h, ← D.sourceProdIso_hom_actOn, Category.assoc]
    apply prod.hom_ext
    · simp only [Category.assoc, DescentData.gluing_hom_fst, prod.map_fst,
        prod.map_fst_assoc, Category.comp_id]
      congr 1
      apply Over.OverMorphism.ext
      exact e.w
    · apply Over.OverMorphism.ext
      simpa only [Over.comp_left, Category.assoc, prod.map_snd, Over.id_left,
        Over.map_map_left, Category.comp_id] using hprod

/-- An isomorphism of the underlying objects commuting with the gluing action is an isomorphism of
descent data. -/
def isoOfActOn (e : D.obj () ≅ E.obj ())
    (h : D.actOn ≫ e.hom.left = actOnMap e.hom ≫ E.actOn) : D ≅ E := by
  refine ⟨homOfActOn e.hom h, { hom := fun _ ↦ e.inv, comm := ?_ }, ?_, ?_⟩
  · rintro ⟨⟩ ⟨⟩
    have hcomm := (homOfActOn e.hom h).comm () ()
    change prod.map ((Over.map a).map e.hom) (𝟙 _) ≫ _ =
      _ ≫ prod.map (𝟙 _) ((Over.map a).map e.hom) at hcomm
    have h' := congrArg
      (fun k ↦ prod.map ((Over.map a).map e.inv) (𝟙 _) ≫ k ≫
        prod.map (𝟙 _) ((Over.map a).map e.inv)) hcomm
    simpa [Category.assoc] using h'.symm
  · refine DescentData.hom_ext ?_
    intro i
    cases i
    exact e.hom_inv_id
  · refine DescentData.hom_ext ?_
    intro i
    cases i
    exact e.inv_hom_id

end ActOnMap

namespace PullbackFunctor

variable {S' X' : Scheme.{u}} {a' : X' ⟶ S'} {h : S' ⟶ S} {f : X' ⟶ X}
  {comm : f ≫ a = a' ≫ h} (P : PullbackFunctor a a' h f comm)
  (D : DescentData (fun _ : Unit ↦ a))

/-- The object isomorphism followed by the second projection to `X'` is the structure morphism of
the pulled-back object. -/
@[reassoc]
lemma objIso_hom_left_snd :
    (P.objIso D).hom.left ≫ pullback.snd (D.obj ()).hom f =
      ((P.functor.obj D).obj ()).hom := by
  rw [← Over.pullback_obj_hom]
  exact Over.w (P.objIso D).hom

/-- The gluing action of a pulled-back descent datum, read through the object isomorphism: it is
the source map of the pullback functor followed by the original action. -/
@[reassoc]
lemma actOn_objIso_fst :
    (P.functor.obj D).actOn ≫ (P.objIso D).hom.left ≫ pullback.fst _ _ =
      P.sourceMap D ≫ D.actOn := by
  simp only [DescentData.actOn, Category.assoc]
  rw [← P.targetMap_snd D, ← Category.assoc, P.gluing D, Category.assoc]

/-- The pullback functor acts on morphisms by base change, read in the fibre-product model. -/
lemma map_objIso_fst {D E : DescentData (fun _ : Unit ↦ a)} (g : D ⟶ E) :
    ((P.functor.map g).hom ()).left ≫ (P.objIso E).hom.left ≫ pullback.fst _ _ =
      (P.objIso D).hom.left ≫ pullback.fst _ _ ≫ (g.hom ()).left := by
  have hmap := congrArg (fun k ↦ k.left ≫ pullback.fst (E.obj ()).hom f) (P.map g)
  simpa [Over.pullback_map_left, Category.assoc, pullback.lift_fst] using hmap.symm

end PullbackFunctor

end AlgebraicGeometry.DescentData
