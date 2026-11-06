module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Sheafifying a map into a small-étale direct image

Let `g : T ⟶ S` be a morphism in a big étale site. Base change along `g` realises the direct
image of an abelian presheaf on the small étale site of `T` as precomposition with
`AlgebraicGeometry.smallEtaleBaseChange`. A map `α : G ⟶ g_* G'` of abelian presheaves on the
small étale site of `S` therefore induces a map from the sheafification of `G` into the direct
image of the sheafification of `G'`, and that induced map is the unique one compatible with the
two sheafification maps.

Passing to inverse images turns the induced map into a morphism of sheaves on the small étale
site of `T`, and its effect on geometric stalks can be read off from the adjunction unit: the
germ at a lift `p'` of a geometric point of `T` of a section of `G` over an étale neighborhood
`U` of the image point is the germ of its image under `α` over the base-changed neighborhood.

## Main definitions

* `AlgebraicGeometry.sheafifiedPushforwardMap`: the induced map from the sheafification of `G`
  into the direct image of the sheafification of `G'`.
* `AlgebraicGeometry.sheafifiedPushforwardAdjoint`: the same map transported through the
  inverse image / direct image adjunction.

## Main results

* `AlgebraicGeometry.sheafifiedPushforwardMap_comm` and
  `AlgebraicGeometry.sheafifiedPushforwardMap_unique`: the defining commutative square, and
  the fact that it determines the induced map.
* `AlgebraicGeometry.sheafifiedPushforwardMap_stalk`: the value of the adjoint map on the
  germ of a section at a lift of a geometric point.

## Implementation notes

The induced map is the sheafification lift of `α` followed by the sheafification map upstairs;
it exists because the direct image of a sheaf along a continuous functor is a sheaf. The stalk
formula is obtained from the triangle identity for the adjunction, which identifies the
composite of the unit with the direct image of the adjoint map with the induced map itself,
and then from the compatibility of a colimit injection with the induced map of colimits.

## References

* [Stacks Project, Tag 0F78](https://stacks.math.columbia.edu/tag/0F78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (g : T ⟶ S)

/-- **Stacks 0F78.** The map from the sheafification of `G` to the small-étale direct image of
the sheafification of `G'` induced by a map `α : G ⟶ g_* G'` of abelian presheaves. -/
@[stacks 0F78 "canonical map"]
public def sheafifiedPushforwardMap
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G' : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : G ⟶ (smallEtaleBaseChange B g).op ⋙ G') :
    (SmallEtale.topology B S.obj S.property).sheafify G ⟶
      (smallEtaleBaseChange B g).op ⋙
        (SmallEtale.topology B T.obj T.property).sheafify G' :=
  (SmallEtale.topology B S.obj S.property).sheafifyLift
    (α ≫ Functor.whiskerLeft (smallEtaleBaseChange B g).op
      ((SmallEtale.topology B T.obj T.property).toSheafify G'))
    ((smallEtaleBaseChange B g).op_comp_isSheaf_of_isSheaf
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)
      ((SmallEtale.topology B T.obj T.property).sheafify G')
      ((SmallEtale.topology B T.obj T.property).sheafify_isSheaf G'))

/-- **Stacks 0F78.** The induced map commutes with the two sheafification maps. -/
@[stacks 0F78 "commutative square"]
public theorem sheafifiedPushforwardMap_comm
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G' : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : G ⟶ (smallEtaleBaseChange B g).op ⋙ G') :
    (SmallEtale.topology B S.obj S.property).toSheafify G ≫
        sheafifiedPushforwardMap B g G G' α =
      α ≫ Functor.whiskerLeft (smallEtaleBaseChange B g).op
        ((SmallEtale.topology B T.obj T.property).toSheafify G') :=
  (SmallEtale.topology B S.obj S.property).toSheafify_sheafifyLift _ _

/-- **Stacks 0F78.** The commutative square of the previous result determines the induced map
uniquely. -/
@[stacks 0F78 "uniqueness"]
public theorem sheafifiedPushforwardMap_unique
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G' : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : G ⟶ (smallEtaleBaseChange B g).op ⋙ G')
    (β : (SmallEtale.topology B S.obj S.property).sheafify G ⟶
      (smallEtaleBaseChange B g).op ⋙
        (SmallEtale.topology B T.obj T.property).sheafify G')
    (hβ : (SmallEtale.topology B S.obj S.property).toSheafify G ≫ β =
      α ≫ Functor.whiskerLeft (smallEtaleBaseChange B g).op
        ((SmallEtale.topology B T.obj T.property).toSheafify G')) :
    β = sheafifiedPushforwardMap B g G G' α :=
  (SmallEtale.topology B S.obj S.property).sheafifyLift_unique _ _ _ hβ

/-- **Stacks 0F78.** The induced map transported through the adjunction between the small-étale
inverse image and direct image along `g`. -/
@[stacks 0F78 "adjoint map"]
public def sheafifiedPushforwardAdjoint
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G' : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : G ⟶ (smallEtaleBaseChange B g).op ⋙ G') :
    ((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).obj
        ⟨(SmallEtale.topology B S.obj S.property).sheafify G,
          (SmallEtale.topology B S.obj S.property).sheafify_isSheaf G⟩ ⟶
      ⟨(SmallEtale.topology B T.obj T.property).sheafify G',
        (SmallEtale.topology B T.obj T.property).sheafify_isSheaf G'⟩ :=
  ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).homEquiv
    ⟨(SmallEtale.topology B S.obj S.property).sheafify G,
      (SmallEtale.topology B S.obj S.property).sheafify_isSheaf G⟩
    ⟨(SmallEtale.topology B T.obj T.property).sheafify G',
      (SmallEtale.topology B T.obj T.property).sheafify_isSheaf G'⟩ |>.symm
      (ObjectProperty.homMk (sheafifiedPushforwardMap B g G G' α))

/-- **Stacks 0F78.** The germ, at a lift `p'` of a geometric point of `T`, of a section of `G`
over an étale neighborhood `U` of the image point is carried by the adjoint map to the germ
over the base-changed neighborhood of the image of the section under `α`. -/
@[stacks 0F78 "geometric stalk formula"]
public theorem sheafifiedPushforwardMap_stalk
    (G : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G' : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (α : G ⟶ (smallEtaleBaseChange B g).op ⋙ G')
    (s' : GeometricPoint T.obj)
    [HasColimit ((CategoryOfElements.π
      (geometricPointFiber B T.obj T.property s')).op ⋙
        (((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj
            ⟨(SmallEtale.topology B S.obj S.property).sheafify G,
              (SmallEtale.topology B S.obj S.property).sheafify_isSheaf G⟩).obj)]
    [HasColimit ((CategoryOfElements.π
      (geometricPointFiber B T.obj T.property s')).op ⋙
        (SmallEtale.topology B T.obj T.property).sheafify G')] :
    let F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} :=
      ⟨(SmallEtale.topology B S.obj S.property).sheafify G,
        (SmallEtale.topology B S.obj S.property).sheafify_isSheaf G⟩
    let D := (CategoryOfElements.π
      (geometricPointFiber B T.obj T.property s')).op ⋙
        (((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj
    let D' := (CategoryOfElements.π
      (geometricPointFiber B T.obj T.property s')).op ⋙
        (SmallEtale.topology B T.obj T.property).sheafify G'
    ∀ (U : SmallEtale B S.obj S.property)
        (p' : (geometricPointFiber B T.obj T.property s').obj
          ((smallEtaleBaseChange B g).obj U)),
        (((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫
            (((smallEtaleBaseChange B g).sheafAdjunctionContinuous
              AddCommGrpCat.{u + 1}
              (SmallEtale.topology B S.obj S.property)
              (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op U) ≫
            colimit.ι D (op (Functor.elementsMk _ ((smallEtaleBaseChange B g).obj U) p')) ≫
            colim.map (Functor.whiskerLeft
              ((CategoryOfElements.π
                (geometricPointFiber B T.obj T.property s')).op)
              (sheafifiedPushforwardAdjoint B g G G' α).hom)) =
          α.app (op U) ≫
            ((SmallEtale.topology B T.obj T.property).toSheafify G').app
              (op ((smallEtaleBaseChange B g).obj U)) ≫
              colimit.ι D' (op (Functor.elementsMk _ ((smallEtaleBaseChange B g).obj U) p')) := by
  intro F D D' U p'
  let adj := (smallEtaleBaseChange B g).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)
  let Gsheaf : Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1} :=
    ⟨(SmallEtale.topology B T.obj T.property).sheafify G',
      (SmallEtale.topology B T.obj T.property).sheafify_isSheaf G'⟩
  let push := (smallEtaleBaseChange B g).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)
  let β : F ⟶ push.obj Gsheaf :=
    ObjectProperty.homMk (sheafifiedPushforwardMap B g G G' α)
  have htriangle : adj.unit.app F ≫ push.map (sheafifiedPushforwardAdjoint B g G G' α) = β := by
    calc
      _ = adj.homEquiv F Gsheaf (sheafifiedPushforwardAdjoint B g G G' α) :=
        (adj.homEquiv_unit F Gsheaf (sheafifiedPushforwardAdjoint B g G G' α)).symm
      _ = β := by
        simp [sheafifiedPushforwardAdjoint, F, Gsheaf, adj, push, β]
  let j : (geometricPointFiber B T.obj T.property s').Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B g).obj U) p'
  let unitAt : F.obj.obj (op U) ⟶ D.obj (op j) := (adj.unit.app F).hom.app (op U)
  have hcomponent' : unitAt ≫
      (sheafifiedPushforwardAdjoint B g G G' α).hom.app
        (op ((smallEtaleBaseChange B g).obj U)) =
      (sheafifiedPushforwardMap B g G G' α).app (op U) :=
    congrArg (fun f => f.hom.app (op U)) htriangle
  have hbase :
      ((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫
          unitAt ≫
          (sheafifiedPushforwardAdjoint B g G G' α).hom.app
            (op ((smallEtaleBaseChange B g).obj U)) =
        α.app (op U) ≫
          ((SmallEtale.topology B T.obj T.property).toSheafify G').app
            (op ((smallEtaleBaseChange B g).obj U)) := by
    calc
      _ = ((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫
            (sheafifiedPushforwardMap B g G G' α).app (op U) := by
        simpa only [Category.assoc, adj, unitAt] using
          congrArg (fun f =>
            ((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫ f)
            hcomponent'
      _ = _ := by
        simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.comp_obj, Functor.op_obj] using
          congrArg (fun f => f.app (op U)) (sheafifiedPushforwardMap_comm B g G G' α)
  show ((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫
      unitAt ≫
      colimit.ι D (op j) ≫
      colim.map (Functor.whiskerLeft
        ((CategoryOfElements.π (geometricPointFiber B T.obj T.property s')).op)
        (sheafifiedPushforwardAdjoint B g G G' α).hom) =
    α.app (op U) ≫
      ((SmallEtale.topology B T.obj T.property).toSheafify G').app
        (op ((smallEtaleBaseChange B g).obj U)) ≫ colimit.ι D' (op j)
  let θ := Functor.whiskerLeft
    ((CategoryOfElements.π (geometricPointFiber B T.obj T.property s')).op)
    (sheafifiedPushforwardAdjoint B g G G' α).hom
  calc
    _ = (((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫ unitAt) ≫
          (colimit.ι D (op j) ≫ colim.map θ) := by rw [Category.assoc]
    _ = (((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫ unitAt) ≫
          (θ.app (op j) ≫ colimit.ι D' (op j)) := by rw [colimit.ι_map]
    _ = (((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫ unitAt) ≫
          ((sheafifiedPushforwardAdjoint B g G G' α).hom.app
            (op ((smallEtaleBaseChange B g).obj U)) ≫ colimit.ι D' (op j)) := by rfl
    _ = ((((SmallEtale.topology B S.obj S.property).toSheafify G).app (op U) ≫ unitAt) ≫
          (sheafifiedPushforwardAdjoint B g G G' α).hom.app
            (op ((smallEtaleBaseChange B g).obj U))) ≫ colimit.ι D' (op j) :=
      (Category.assoc _ _ _).symm
    _ = (α.app (op U) ≫
          ((SmallEtale.topology B T.obj T.property).toSheafify G').app
            (op ((smallEtaleBaseChange B g).obj U))) ≫ colimit.ι D' (op j) :=
      congrArg (fun f => f ≫ colimit.ι D' (op j)) ((Category.assoc _ _ _).trans hbase)
    _ = _ := Category.assoc _ _ _

end AlgebraicGeometry

end
