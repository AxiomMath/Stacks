module

public import StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction

/-!
# Groupoid schemes cartesian over a pair groupoid, and descent data

Let `f : X ⟶ S` be a morphism of schemes. Groupoid schemes cartesian over the pair groupoid of
`f` (equivalently, by Tag 0APE, equivariant schemes for it) are equivalent to descent data
`AlgebraicGeometry.DescentDatum` relative to `f`; this is Tag 0APF with the base scheme of the
groupoid equal to the target of `f`. The first notion records the gluing data as an isomorphism
of two fibre products over the arrow scheme `X ×_S X` and states its cocycle law on generalized
points, the second as an isomorphism of two binary products formed in `Over S` and states its
cocycle law as a diagram on the triple product.

## Main definitions

* `AlgebraicGeometry.pairTargetPullbackIso` and `AlgebraicGeometry.pairSourcePullbackIso`
  identify the two fibre products of a scheme over `X` with the arrow scheme of the pair
  groupoid with the two binary products `V ×_S X` and `X ×_S V` formed in `Over S`.
* `AlgebraicGeometry.EquivariantScheme.pairAct` is the action of an equivariant scheme for the
  pair groupoid, read on generalized points: a point of `V` and a point of `X` give a new
  point of `V`.
* `AlgebraicGeometry.descentDatumToEquivariant` and
  `AlgebraicGeometry.descentDatumToEquivariantFunctor` build the equivariant scheme of a
  descent datum, and `AlgebraicGeometry.EquivariantScheme.pairDescentDatum` the descent datum
  of an equivariant scheme.
* `AlgebraicGeometry.EquivariantScheme.pairHomMk` and
  `AlgebraicGeometry.EquivariantScheme.pairIsoMk` build a morphism, respectively an
  isomorphism, of equivariant schemes out of one of the underlying objects which is
  compatible with the actions.
* `AlgebraicGeometry.EquivariantScheme.objIso` reads an isomorphism of equivariant schemes on
  the underlying schemes over the object scheme of the groupoid.
* `AlgebraicGeometry.descentDatumCartesianOver` is the groupoid scheme cartesian over the pair
  groupoid which a descent datum determines, and
  `AlgebraicGeometry.descentDatumCartesianOverObjectsIso` identifies its object scheme, over
  `X`, with the scheme `V` the descent datum is carried by.

## Main results

* `AlgebraicGeometry.descentDatumEquivalenceEquivariant`: descent data relative to
  `f : X ⟶ S` are the same thing as equivariant schemes for the pair groupoid of `f`.
* `AlgebraicGeometry.cartesianOverEquivDescentDatum`: groupoid schemes cartesian over the
  pair groupoid `(X, X ×_S X, s, t, c)` are the same thing as descent data relative to `X/S`.
* `AlgebraicGeometry.EquivariantScheme.pairAct_self` and
  `AlgebraicGeometry.EquivariantScheme.pairAct_act` are the two laws of the action of an
  equivariant scheme for the pair groupoid, and
  `AlgebraicGeometry.EquivariantScheme.action_eq_pairAct` says that no information is lost in
  passing to that description.

## Implementation notes

**The cocycle laws.**  A generalized arrow of the pair groupoid is a pair of generalized points
of `X`, and composition of arrows is `(x, y) ∘ (y, z) = (x, z)`. So the cocycle law of an
equivariant scheme, `AlgebraicGeometry.EquivariantScheme.pairAct_act`, is the law
`(v · x) · y = v · y`, which `AlgebraicGeometry.cocycle_iff_gluingAction_act_act` shows is
equivalent to the cocycle diagram of a descent datum.

**Spellings.**  `Stacks.Groupoids.GroupoidScheme` reaches its object and arrow schemes through
projections, so the fields of an equivariant scheme are stated in terms of
`(pairGroupoid f).objects` and `(pairGroupoid f).arrows` while this file's own statements use
`CategoryTheory.Over.mk f` and `AlgebraicGeometry.pairArrows f`.  The two spellings are
definitionally equal but not syntactically so, and `pairGroupoid` is not reducible, so `rw`
cannot cross between them.  `AlgebraicGeometry.EquivariantScheme.pairObjMap` and
`AlgebraicGeometry.EquivariantScheme.pairDescentIso` are reducible restatements of
`obj.hom` and `descentIso` which put the seam in one place; past it, every statement here is
in the second spelling, and the crossings are made by `exact` and `Eq.trans`, which check up
to definitional equality.

**The base scheme.**  Tag 0APF is stated for a morphism `f : X ⟶ Y` of schemes *over a base
`S`*, with the pair groupoid `(X, X ×_Y X, s, t, c)` regarded as a groupoid scheme over `S`.
This file treats the case `Y = S`, where the groupoid scheme is `U = X`, `R = X ×_S X`. The
case `Y = S` is not an instance of the general statement up to definitional equality, since
`CategoryTheory.Over.map (𝟙 S)` is not the identity functor.

**The inverse of the equivalence.**  The equivalence of Tag 0APE is produced from a `Nonempty`
by `Classical.choice`, and the equations
`AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme_obj_eq`,
`AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme_descentIso_hom` and
`AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme_map_hom` concern its *forward*
functor only. `AlgebraicGeometry.descentDatumCartesianOverObjectsIso` identifies the object
scheme of the cartesian groupoid attached to a descent datum through the counit, as an
isomorphism over `X`.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 0APD](https://stacks.math.columbia.edu/tag/0APD)
* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}} {f : X ⟶ S}


/-- `A ×_{X,t} (X ×_S X) ≅ A ×_S X`. -/
def pairTargetPullbackIso {A : Over S} (g : A ⟶ Over.mk f) :
    pullback g (pairTarget f) ≅ A ⨯ Over.mk f where
  hom := prod.lift (pullback.fst g (pairTarget f))
    (pullback.snd g (pairTarget f) ≫ pairSource f)
  inv := pullback.lift prod.fst (pairArrowMk f (prod.fst ≫ g) prod.snd)
    (by rw [pairArrowMk_target])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, comp_pairArrowMk,
        prod.lift_snd, ← Category.assoc, prod.lift_fst, pullback.condition]
      exact pairArrowMk_eq f _
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, pullback.lift_snd,
        pairArrowMk_source, Category.id_comp]

/-- `(X ×_S X) ×_{s,X} A ≅ X ×_S A`. -/
def pairSourcePullbackIso {A : Over S} (g : A ⟶ Over.mk f) :
    pullback (pairSource f) g ≅ Over.mk f ⨯ A where
  hom := prod.lift (pullback.fst (pairSource f) g ≫ pairTarget f)
    (pullback.snd (pairSource f) g)
  inv := pullback.lift (pairArrowMk f prod.fst (prod.snd ≫ g)) prod.snd
    (by rw [pairArrowMk_source])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, comp_pairArrowMk,
        prod.lift_fst, ← Category.assoc, prod.lift_snd, ← pullback.condition]
      exact pairArrowMk_eq f _
    · rw [Category.assoc, pullback.lift_snd, prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, ← Category.assoc, pullback.lift_fst,
        pairArrowMk_target, Category.id_comp]
    · rw [Category.assoc, prod.lift_snd, pullback.lift_snd, Category.id_comp]

/-- `pairTargetPullbackIso g` pairs the point of `A` with the source of the arrow. -/
lemma pairTargetPullbackIso_hom_eq {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).hom = prod.lift (pullback.fst g (pairTarget f))
      (pullback.snd g (pairTarget f) ≫ pairSource f) := rfl

/-- The inverse of `pairTargetPullbackIso g` sends a pair `(v, x)` to `v` and the arrow from `x`
to the image of `v`. -/
lemma pairTargetPullbackIso_inv_eq {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).inv = pullback.lift prod.fst
      (pairArrowMk f (prod.fst ≫ g) prod.snd)
      (pairArrowMk_target f (prod.fst ≫ g) prod.snd).symm := rfl

/-- `pairSourcePullbackIso g` pairs the target of the arrow with the point of `A`. -/
lemma pairSourcePullbackIso_hom_eq {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).hom = prod.lift
      (pullback.fst (pairSource f) g ≫ pairTarget f) (pullback.snd (pairSource f) g) := rfl

/-- The inverse of `pairSourcePullbackIso g` sends a pair `(x, v)` to the arrow from the image of
`v` to `x` and to `v`. -/
lemma pairSourcePullbackIso_inv_eq {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).inv = pullback.lift
      (pairArrowMk f prod.fst (prod.snd ≫ g)) prod.snd
      (pairArrowMk_source f prod.fst (prod.snd ≫ g)) := rfl

/-- The comparison sends a pair to its point of `A`. -/
@[simp]
lemma pairTargetPullbackIso_hom_comp_fst {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).hom ≫ prod.fst = pullback.fst g (pairTarget f) := by
  rw [pairTargetPullbackIso_hom_eq, prod.lift_fst]

/-- The comparison sends a pair to the source of its arrow. -/
@[simp]
lemma pairTargetPullbackIso_hom_comp_snd {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).hom ≫ prod.snd =
      pullback.snd g (pairTarget f) ≫ pairSource f := by
  rw [pairTargetPullbackIso_hom_eq, prod.lift_snd]

/-- The comparison applied to a generalized point of the fibre product. -/
@[simp]
lemma pullbackLift_comp_pairTargetPullbackIso_hom {A T : Over S} (g : A ⟶ Over.mk f)
    (v : T ⟶ A) (a : T ⟶ pairArrows f) (w : v ≫ g = a ≫ pairTarget f) :
    pullback.lift v a w ≫ (pairTargetPullbackIso g).hom = prod.lift v (a ≫ pairSource f) := by
  rw [pairTargetPullbackIso_hom_eq, prod.comp_lift, pullback.lift_fst, ← Category.assoc,
    pullback.lift_snd]

/-- The inverse comparison applied to a generalized point of the product. -/
@[simp]
lemma prodLift_comp_pairTargetPullbackIso_inv {A T : Over S} (g : A ⟶ Over.mk f)
    (v : T ⟶ A) (x : T ⟶ Over.mk f) :
    prod.lift v x ≫ (pairTargetPullbackIso g).inv =
      pullback.lift v (pairArrowMk f (v ≫ g) x)
        (pairArrowMk_target f (v ≫ g) x).symm := by
  rw [pairTargetPullbackIso_inv_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, comp_pairArrowMk, prod.lift_snd,
      ← Category.assoc, prod.lift_fst, pullback.lift_snd]

/-- The comparison sends a pair to its point of `A`. -/
@[simp]
lemma pairSourcePullbackIso_hom_comp_snd {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).hom ≫ prod.snd = pullback.snd (pairSource f) g := by
  rw [pairSourcePullbackIso_hom_eq, prod.lift_snd]

/-- The comparison sends a pair to the target of its arrow. -/
@[simp]
lemma pairSourcePullbackIso_hom_comp_fst {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).hom ≫ prod.fst =
      pullback.fst (pairSource f) g ≫ pairTarget f := by
  rw [pairSourcePullbackIso_hom_eq, prod.lift_fst]

/-- The inverse comparison recovers the point of `A`. -/
@[simp]
lemma pairSourcePullbackIso_inv_comp_snd {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).inv ≫ pullback.snd (pairSource f) g = prod.snd := by
  rw [pairSourcePullbackIso_inv_eq, pullback.lift_snd]

/-- The inverse comparison builds the arrow out of the point of `X` and the point of `A`. -/
@[simp]
lemma pairSourcePullbackIso_inv_comp_fst {A : Over S} (g : A ⟶ Over.mk f) :
    (pairSourcePullbackIso g).inv ≫ pullback.fst (pairSource f) g =
      pairArrowMk f prod.fst (prod.snd ≫ g) := by
  rw [pairSourcePullbackIso_inv_eq, pullback.lift_fst]

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The gluing isomorphism of a descent datum, as an isomorphism of schemes over `S`. -/
abbrev DescentDatum.transitionIso (D : DescentDatum f) :
    (Over.map f).obj D.over ⨯ Over.mk f ≅ Over.mk f ⨯ (Over.map f).obj D.over :=
  D.gluingIso () ()

/-- The forward map of `DescentDatum.transitionIso` is the underlying morphism of the forward
transition map. -/
@[simp] lemma DescentDatum.transitionIso_hom (D : DescentDatum f) :
    D.transitionIso.hom = D.transition.hom.left := rfl

/-- The inverse of `DescentDatum.transitionIso` is the underlying morphism of the inverse
transition map. -/
@[simp] lemma DescentDatum.transitionIso_inv (D : DescentDatum f) :
    D.transitionIso.inv = D.transition.inv.left := rfl

/-- The descent isomorphism of the equivariant scheme attached to a descent datum. -/
def descentDatumDescentIso (D : DescentDatum f) :
    pullback (structureMap f D.over) (pairTarget f) ≅
      pullback (pairSource f) (structureMap f D.over) :=
  pairTargetPullbackIso (structureMap f D.over) ≪≫ D.transitionIso ≪≫
    (pairSourcePullbackIso (structureMap f D.over)).symm

/-- The descent isomorphism of a descent datum, evaluated at a generalized point: it computes
the action of the source of the arrow. -/
lemma descentDatumDescentIso_lift (D : DescentDatum f) {T : Over S}
    (v : T ⟶ (Over.map f).obj D.over) (a : T ⟶ pairArrows f)
    (w : v ≫ structureMap f D.over = a ≫ pairTarget f) :
    pullback.lift v a w ≫ (descentDatumDescentIso D).hom ≫
      pullback.snd (pairSource f) (structureMap f D.over) = D.act v (a ≫ pairSource f) := by
  simp only [descentDatumDescentIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    DescentDatum.transitionIso_hom]
  rw [← Category.assoc (pullback.lift v a w), pullbackLift_comp_pairTargetPullbackIso_hom,
    pairSourcePullbackIso_inv_comp_snd]
  rfl

/-- The descent isomorphism of a descent datum lies over the arrow scheme. -/
lemma descentDatumDescentIso_over (D : DescentDatum f) :
    (descentDatumDescentIso D).hom ≫ pullback.fst (pairSource f) (structureMap f D.over) =
      pullback.snd (structureMap f D.over) (pairTarget f) := by
  simp only [descentDatumDescentIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    DescentDatum.transitionIso_hom, pairSourcePullbackIso_inv_comp_fst]
  rw [comp_pairArrowMk, comp_pairArrowMk,
    D.transition_hom_left_comp_fst, D.transition_hom_left_comp_snd_structureMap,
    ← Category.assoc, pairTargetPullbackIso_hom_comp_fst,
    pairTargetPullbackIso_hom_comp_snd, pullback.condition]
  exact pairArrowMk_eq f _

end AlgebraicGeometry

namespace AlgebraicGeometry
namespace EquivariantScheme
variable {S X : Scheme.{u}} {f : X ⟶ S} (W : EquivariantScheme (pairGroupoid f))

/-- The structure map, with the object scheme spelled `Over.mk f`. -/
abbrev pairObjMap : W.obj.left ⟶ Over.mk f := W.obj.hom

/-- `AlgebraicGeometry.EquivariantScheme.action_arrow_eq`, with the arrow scheme spelled in pair
coordinates. -/
lemma pairAction_arrow_eq {T : Over S} (v : T ⟶ W.obj.left) (a a' : T ⟶ pairArrows f)
    (w : v ≫ W.pairObjMap = a ≫ pairTarget f)
    (w' : v ≫ W.pairObjMap = a' ≫ pairTarget f) (h : a = a') :
    W.action v a w = W.action v a' w' := W.action_arrow_eq v a a' w w' h

/-- `AlgebraicGeometry.EquivariantScheme.comp_action`, with the arrow scheme spelled in pair
coordinates. -/
lemma pairComp_action {T U : Over S} (k : U ⟶ T) (v : T ⟶ W.obj.left) (a : T ⟶ pairArrows f)
    (w : v ≫ W.pairObjMap = a ≫ pairTarget f)
    (w' : (k ≫ v) ≫ W.pairObjMap = (k ≫ a) ≫ pairTarget f) :
    k ≫ W.action v a w =
      W.action (k ≫ v) ((k ≫ a : U ⟶ pairArrows f)) w' := W.comp_action k v a w w'

/-- `AlgebraicGeometry.EquivariantScheme.action_comp_hom`, with the arrow scheme spelled in pair
coordinates. -/
lemma pairAction_comp_pairObjMap {T : Over S} (v : T ⟶ W.obj.left) (a : T ⟶ pairArrows f)
    (w : v ≫ W.pairObjMap = a ≫ pairTarget f) :
    W.action v a w ≫ W.pairObjMap = a ≫ pairSource f := W.action_comp_hom v a w

/-- The action, in pair-groupoid coordinates. -/
def pairAct {T : Over S} (v : T ⟶ W.obj.left) (x : T ⟶ Over.mk f) : T ⟶ W.obj.left :=
  W.action v (pairArrowMk f (v ≫ W.pairObjMap) x)
    (pairArrowMk_target f (v ≫ W.pairObjMap) x).symm

/-- Every action of a generalized arrow is the action of its source. -/
lemma action_eq_pairAct {T : Over S} (v : T ⟶ W.obj.left) (a : T ⟶ pairArrows f)
    (w : v ≫ W.pairObjMap = a ≫ pairTarget f) :
    W.action v a w = W.pairAct v (a ≫ pairSource f) := by
  refine W.pairAction_arrow_eq v a _ w _ ?_
  rw [w]
  exact (pairArrowMk_eq f a).symm

/-- The point produced by the action lies over the acting point of `X`. -/
@[simp]
lemma pairAct_comp_pairObjMap {T : Over S} (v : T ⟶ W.obj.left) (x : T ⟶ Over.mk f) :
    W.pairAct v x ≫ W.pairObjMap = x :=
  (W.pairAction_comp_pairObjMap v _ _).trans (pairArrowMk_source f (v ≫ W.pairObjMap) x)

/-- The action commutes with change of test object. -/
@[simp]
lemma comp_pairAct {T U : Over S} (k : U ⟶ T) (v : T ⟶ W.obj.left)
    (x : T ⟶ Over.mk f) : k ≫ W.pairAct v x = W.pairAct (k ≫ v) (k ≫ x) := by
  have hw' : (k ≫ v) ≫ W.pairObjMap =
      (k ≫ pairArrowMk f (v ≫ W.pairObjMap) x) ≫ pairTarget f := by
    rw [comp_pairArrowMk, pairArrowMk_target, Category.assoc]
  refine (W.pairComp_action k v _ _ hw').trans ?_
  refine W.pairAction_arrow_eq _ _ _ _ _ ?_
  rw [comp_pairArrowMk, Category.assoc]

/-- A point of the object scheme is fixed by the point of `X` it lies over.  This is the
normalization along the identity section. -/
lemma pairAct_self {T : Over S} (v : T ⟶ W.obj.left) :
    W.pairAct v (v ≫ W.pairObjMap) = v := by
  refine Eq.trans ?_ (W.identity T v)
  refine W.pairAction_arrow_eq _ _ _ _ _ ?_
  exact (comp_pairIdentity_eq f (v ≫ W.pairObjMap)).symm.trans
    (Category.assoc v W.pairObjMap (pairIdentity f))

/-- Acting twice is acting once.  This is the cocycle condition of an equivariant scheme, read in
pair coordinates. -/
lemma pairAct_act {T : Over S} (v : T ⟶ W.obj.left) (x y : T ⟶ Over.mk f) :
    W.pairAct (W.pairAct v x) y = W.pairAct v y := by
  have wva : v ≫ W.pairObjMap = pairArrowMk f (v ≫ W.pairObjMap) x ≫ pairTarget f :=
    (pairArrowMk_target f (v ≫ W.pairObjMap) x).symm
  have wab : pairArrowMk f (v ≫ W.pairObjMap) x ≫ pairSource f =
      pairArrowMk f x y ≫ pairTarget f := by
    rw [pairArrowMk_source, pairArrowMk_target]
  have h := W.cocycle T v (pairArrowMk f (v ≫ W.pairObjMap) x) (pairArrowMk f x y) wva wab
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine W.pairAction_arrow_eq _ _ _ _ _ ?_
    congr 1
    exact W.pairAct_comp_pairObjMap v x
  · refine W.pairAction_arrow_eq _ _ _ _ _ ?_
    exact pairGroupoid_compose_pairArrowMk f (v ≫ W.pairObjMap) x y wab

end EquivariantScheme
end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The equivariant scheme for the pair groupoid of `f` attached to a descent datum. -/
def descentDatumToEquivariant (D : DescentDatum f) : EquivariantScheme (pairGroupoid f) where
  obj := Over.mk (structureMap f D.over)
  descentIso := descentDatumDescentIso D
  descentIso_over := descentDatumDescentIso_over D
  identity := by
    intro T v
    refine (descentDatumDescentIso_lift D v _ _).trans ?_
    have hx : (v ≫ structureMap f D.over ≫ pairIdentity f) ≫ pairSource f =
        v ≫ structureMap f D.over := by
      rw [Category.assoc, Category.assoc, pairIdentity_source, Category.comp_id]
    exact (congrArg (D.act v) hx).trans (D.act_self v)
  cocycle := by
    intro T v a b wva wab
    refine (descentDatumDescentIso_lift D _ b _).trans ?_
    refine Eq.trans ?_ (descentDatumDescentIso_lift D v _ _).symm
    refine Eq.trans (congrArg (fun z ↦ D.act z (b ≫ pairSource f))
      (descentDatumDescentIso_lift D v a wva)) ?_
    refine Eq.trans (D.act_act v (a ≫ pairSource f) (b ≫ pairSource f)) ?_
    exact (congrArg (D.act v) (groupoidCompose_source (pairGroupoid f) a b wab)).symm

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The object scheme of the equivariant scheme attached to a descent datum is the base change of
the underlying scheme. -/
@[simp]
lemma descentDatumToEquivariant_obj (D : DescentDatum f) :
    (descentDatumToEquivariant D).obj = Over.mk (structureMap f D.over) := rfl

/-- The action of the equivariant scheme attached to a descent datum is the action of the descent
datum. -/
lemma descentDatumToEquivariant_pairAct (D : DescentDatum f) {T : Over S}
    (v : T ⟶ (Over.map f).obj D.over) (x : T ⟶ Over.mk f) :
    (descentDatumToEquivariant D).pairAct v x = D.act v x := by
  refine (descentDatumDescentIso_lift D v
    (pairArrowMk f (v ≫ structureMap f D.over) x) _).trans ?_
  exact congrArg (D.act v) (pairArrowMk_source f (v ≫ structureMap f D.over) x)

/-- A morphism of schemes over `X` commutes with the structure maps to `X`. -/
lemma structureMap_comp_of_hom {D E : DescentDatum f} (h : D.over ⟶ E.over) :
    (Over.map f).map h ≫ structureMap f E.over = structureMap f D.over :=
  Over.OverMorphism.ext (Over.w h)

/-- The equivariant morphism attached to a morphism of descent data. -/
def descentDatumToEquivariantMap {D E : DescentDatum f} (φ : D ⟶ E) :
    descentDatumToEquivariant D ⟶ descentDatumToEquivariant E where
  hom := Over.homMk ((Over.map f).map (φ.hom ())) (structureMap_comp_of_hom (φ.hom ()))
  comm := by
    intro T v a w
    have hA : (descentDatumToEquivariant D).action v a w = D.act v (a ≫ pairSource f) :=
      ((descentDatumToEquivariant D).action_eq_pairAct v a w).trans
        (descentDatumToEquivariant_pairAct D v _)
    have hassoc : (v ≫ (Over.map f).map (φ.hom ())) ≫ structureMap f E.over =
        v ≫ ((Over.map f).map (φ.hom ()) ≫ structureMap f E.over) := Category.assoc _ _ _
    have hw : (v ≫ (Over.map f).map (φ.hom ())) ≫ structureMap f E.over =
        a ≫ pairTarget f :=
      hassoc.trans ((congrArg (fun z : (Over.map f).obj D.over ⟶ Over.mk f ↦ v ≫ z)
        (structureMap_comp_of_hom (φ.hom ()))).trans w)
    have hB := ((descentDatumToEquivariant E).action_eq_pairAct
        (v ≫ (Over.map f).map (φ.hom ())) a hw).trans
      (descentDatumToEquivariant_pairAct E (v ≫ (Over.map f).map (φ.hom ()))
        (a ≫ pairSource f))
    refine Eq.trans (congrArg (fun z ↦ z ≫ (Over.map f).map (φ.hom ())) hA) ?_
    refine Eq.trans ?_ hB.symm
    exact (DescentDatum.hom_comm_iff D E (φ.hom ())).mp (φ.comm () ()) v (a ≫ pairSource f)

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The functor from descent data relative to `f` to equivariant schemes for the pair
groupoid of `f`. -/
def descentDatumToEquivariantFunctor (f : X ⟶ S) :
    DescentDatum f ⥤ EquivariantScheme (pairGroupoid f) where
  obj D := descentDatumToEquivariant D
  map φ := descentDatumToEquivariantMap φ
  map_id D := by
    refine EquivariantScheme.hom_ext _ _ ?_
    apply Over.OverMorphism.ext
    have h : (Over.map f).map ((𝟙 D : D ⟶ D).hom ()) = 𝟙 ((Over.map f).obj D.over) := by
      rw [DescentData.id_hom, CategoryTheory.Functor.map_id]
    exact h
  map_comp φ ψ := by
    refine EquivariantScheme.hom_ext _ _ ?_
    apply Over.OverMorphism.ext
    have h : (Over.map f).map ((φ ≫ ψ).hom ()) =
        (Over.map f).map (φ.hom ()) ≫ (Over.map f).map (ψ.hom ()) := by
      rw [DescentData.comp_hom, CategoryTheory.Functor.map_comp]
    exact h

/-- The comparison functor is faithful: a morphism of descent data is determined by its
underlying morphism of `X`-schemes, and so is its image. -/
instance : (descentDatumToEquivariantFunctor f).Faithful where
  map_injective {D E} {φ ψ} h := by
    refine DescentData.hom_ext (fun _ ↦ Over.OverMorphism.ext ?_)
    exact congrArg (fun k : EquivariantScheme.Hom _ _ ↦ k.hom.left.left) h

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The comparison functor is full: a morphism over the object scheme which is equivariant
comes from a morphism of descent data. -/
instance : (descentDatumToEquivariantFunctor f).Full where
  map_surjective {D E} ψ := by
    have hw0 : ψ.hom.left ≫ structureMap f E.over = structureMap f D.over := Over.w ψ.hom
    have hw1 : ψ.hom.left.left ≫ E.over.hom = D.over.hom := congrArg Over.Hom.left hw0
    refine ⟨{ hom := fun _ ↦ Over.homMk ψ.hom.left.left hw1, comm := ?_ }, ?_⟩
    · intro i j
      have hmap : (Over.map f).map (Over.homMk ψ.hom.left.left hw1 : D.over ⟶ E.over) =
          ψ.hom.left := by
        apply Over.OverMorphism.ext
        rfl
      refine (DescentDatum.hom_comm_iff D E (Over.homMk ψ.hom.left.left hw1)).mpr ?_
      intro T v x
      have hw : v ≫ (descentDatumToEquivariant D).obj.hom =
          pairArrowMk f (v ≫ structureMap f D.over) x ≫ (pairGroupoid f).target :=
        (pairArrowMk_target f (v ≫ structureMap f D.over) x).symm
      have hc := ψ.comm T v (pairArrowMk f (v ≫ structureMap f D.over) x) hw
      have hA : (descentDatumToEquivariant D).action v
          (pairArrowMk f (v ≫ structureMap f D.over) x) hw = D.act v x :=
        ((descentDatumToEquivariant D).action_eq_pairAct v _ hw).trans
          ((descentDatumToEquivariant_pairAct D v _).trans
            (congrArg (D.act v) (pairArrowMk_source f (v ≫ structureMap f D.over) x)))
      have hwE : (v ≫ ψ.hom.left) ≫ (descentDatumToEquivariant E).obj.hom =
          pairArrowMk f (v ≫ structureMap f D.over) x ≫ (pairGroupoid f).target :=
        (Category.assoc v ψ.hom.left (structureMap f E.over)).trans
          ((congrArg (fun z : (Over.map f).obj D.over ⟶ Over.mk f ↦ v ≫ z) hw0).trans hw)
      have hB : (descentDatumToEquivariant E).action (v ≫ ψ.hom.left)
          (pairArrowMk f (v ≫ structureMap f D.over) x) hwE =
            E.act (v ≫ ψ.hom.left) x :=
        ((descentDatumToEquivariant E).action_eq_pairAct (v ≫ ψ.hom.left) _ hwE).trans
          ((descentDatumToEquivariant_pairAct E (v ≫ ψ.hom.left) _).trans
            (congrArg (E.act (v ≫ ψ.hom.left))
              (pairArrowMk_source f (v ≫ structureMap f D.over) x)))
      rw [hmap]
      exact ((congrArg (fun z ↦ z ≫ ψ.hom.left) hA).symm.trans hc).trans hB
    · refine EquivariantScheme.hom_ext _ _ ?_
      apply Over.OverMorphism.ext
      rfl

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The inverse comparison builds the arrow out of the point of `A` and the point of `X`. -/
@[simp]
lemma pairTargetPullbackIso_inv_comp_snd {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).inv ≫ pullback.snd g (pairTarget f) =
      pairArrowMk f (prod.fst ≫ g) prod.snd := by
  rw [pairTargetPullbackIso_inv_eq, pullback.lift_snd]

/-- The inverse comparison recovers the point of `A`. -/
@[simp]
lemma pairTargetPullbackIso_inv_comp_fst {A : Over S} (g : A ⟶ Over.mk f) :
    (pairTargetPullbackIso g).inv ≫ pullback.fst g (pairTarget f) = prod.fst := by
  rw [pairTargetPullbackIso_inv_eq, pullback.lift_fst]

namespace EquivariantScheme
variable (W : EquivariantScheme (pairGroupoid f))

/-- The descent isomorphism, with its source and target spelled in pair coordinates. -/
abbrev pairDescentIso : pullback W.pairObjMap (pairTarget f) ≅
    pullback (pairSource f) W.pairObjMap := W.descentIso

/-- The descent isomorphism lies over the arrow scheme. -/
lemma pairDescentIso_over :
    W.pairDescentIso.hom ≫ pullback.fst (pairSource f) W.pairObjMap =
      pullback.snd W.pairObjMap (pairTarget f) := W.descentIso_over

/-- The gluing isomorphism of an equivariant scheme for the pair groupoid of `f`. -/
def pairGluingIso : W.obj.left ⨯ Over.mk f ≅ Over.mk f ⨯ W.obj.left where
  hom := (pairTargetPullbackIso W.pairObjMap).inv ≫ W.pairDescentIso.hom ≫
    (pairSourcePullbackIso W.pairObjMap).hom
  inv := (pairSourcePullbackIso W.pairObjMap).inv ≫ W.pairDescentIso.inv ≫
    (pairTargetPullbackIso W.pairObjMap).hom
  hom_inv_id := by
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  inv_hom_id := by
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The gluing isomorphism of an equivariant scheme, by its definition. -/
@[simp]
lemma pairGluingIso_hom :
    W.pairGluingIso.hom = (pairTargetPullbackIso W.pairObjMap).inv ≫ W.pairDescentIso.hom ≫
      (pairSourcePullbackIso W.pairObjMap).hom := rfl

/-- The gluing isomorphism of an equivariant scheme computes its action. -/
lemma prodLift_comp_pairGluingIso_hom_comp_snd {T : Over S} (v : T ⟶ W.obj.left)
    (x : T ⟶ Over.mk f) :
    prod.lift v x ≫ W.pairGluingIso.hom ≫ prod.snd = W.pairAct v x := by
  rw [pairGluingIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (prod.lift v x), prodLift_comp_pairTargetPullbackIso_inv,
    pairSourcePullbackIso_hom_comp_snd]
  rfl

/-- The gluing isomorphism preserves the point of `X` under the point of the object scheme. -/
lemma pairGluingIso_hom_comp_fst :
    W.pairGluingIso.hom ≫ prod.fst = prod.fst ≫ W.pairObjMap := by
  rw [pairGluingIso_hom]
  simp only [Category.assoc]
  rw [pairSourcePullbackIso_hom_comp_fst, ← Category.assoc W.pairDescentIso.hom,
    W.pairDescentIso_over, ← Category.assoc, pairTargetPullbackIso_inv_comp_snd,
    pairArrowMk_target]

/-- The gluing isomorphism carries the point of `X` to the point under the new point of the
object scheme. -/
lemma pairGluingIso_hom_comp_snd_pairObjMap :
    W.pairGluingIso.hom ≫ prod.snd ≫ W.pairObjMap = prod.snd := by
  have h := W.prodLift_comp_pairGluingIso_hom_comp_snd (prod.fst : W.obj.left ⨯ Over.mk f ⟶ _)
    prod.snd
  rw [prod.lift_fst_snd, Category.id_comp] at h
  rw [← Category.assoc, h, W.pairAct_comp_pairObjMap]

end EquivariantScheme
end AlgebraicGeometry

namespace AlgebraicGeometry
namespace EquivariantScheme
variable {S X : Scheme.{u}} {f : X ⟶ S} (W : EquivariantScheme (pairGroupoid f))

/-- The scheme over `X` underlying an equivariant scheme for the pair groupoid of `f`. -/
abbrev pairOver : Over X := Over.mk W.pairObjMap.left

/-- The comparison between the base change of `pairOver` and the object scheme of `W`. -/
def pairOverIso : (Over.map f).obj W.pairOver ≅ W.obj.left :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w W.pairObjMap).symm)

/-- The comparison is the identity on underlying schemes. -/
@[simp] lemma pairOverIso_hom_left : W.pairOverIso.hom.left = 𝟙 W.obj.left.left := rfl

/-- The comparison is a morphism over `X`. -/
lemma pairOverIso_hom_comp_pairObjMap :
    W.pairOverIso.hom ≫ W.pairObjMap = structureMap f W.pairOver :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The inverse comparison is a morphism over `X`. -/
lemma pairOverIso_inv_comp_structureMap :
    W.pairOverIso.inv ≫ structureMap f W.pairOver = W.pairObjMap := by
  rw [← W.pairOverIso_hom_comp_pairObjMap, Iso.inv_hom_id_assoc]

/-- The gluing isomorphism of the descent datum attached to an equivariant scheme. -/
def pairGluingDatumIso : (Over.map f).obj W.pairOver ⨯ Over.mk f ≅
    Over.mk f ⨯ (Over.map f).obj W.pairOver :=
  prod.mapIso W.pairOverIso (Iso.refl (Over.mk f)) ≪≫ W.pairGluingIso ≪≫
    prod.mapIso (Iso.refl (Over.mk f)) W.pairOverIso.symm

/-- The gluing isomorphism of the attached descent datum, by its definition. -/
@[simp]
lemma pairGluingDatumIso_hom : W.pairGluingDatumIso.hom =
    prod.map W.pairOverIso.hom (𝟙 (Over.mk f)) ≫ W.pairGluingIso.hom ≫
      prod.map (𝟙 (Over.mk f)) W.pairOverIso.inv := rfl

/-- The action of the attached descent datum is the action of the equivariant scheme, transported
along the comparison. -/
lemma gluingAction_pairGluingDatumIso {T : Over S}
    (v : T ⟶ (Over.map f).obj W.pairOver) (x : T ⟶ Over.mk f) :
    gluingAction W.pairOver W.pairGluingDatumIso.hom v x =
      W.pairAct (v ≫ W.pairOverIso.hom) x ≫ W.pairOverIso.inv := by
  rw [gluingAction, pairGluingDatumIso_hom]
  simp only [Category.assoc]
  rw [prod.map_snd, ← Category.assoc (prod.lift v x), prod.lift_map, Category.comp_id,
    ← Category.assoc W.pairGluingIso.hom, ← Category.assoc,
    prodLift_comp_pairGluingIso_hom_comp_snd]

/-- The attached descent datum's gluing isomorphism lies over the first factor of `X ×_S X`. -/
lemma pairGluingDatumIso_hom_comp_fst :
    W.pairGluingDatumIso.hom ≫ prod.fst = prod.fst ≫ structureMap f W.pairOver := by
  rw [pairGluingDatumIso_hom]
  simp only [Category.assoc]
  rw [prod.map_fst, Category.comp_id, pairGluingIso_hom_comp_fst, ← Category.assoc,
    prod.map_fst, Category.assoc, pairOverIso_hom_comp_pairObjMap]

/-- The gluing isomorphism of the attached descent datum lies over the second factor of
`X ×_S X`. -/
lemma pairGluingDatumIso_hom_comp_snd_structureMap :
    W.pairGluingDatumIso.hom ≫ prod.snd ≫ structureMap f W.pairOver = prod.snd := by
  rw [pairGluingDatumIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (prod.map (𝟙 (Over.mk f)) W.pairOverIso.inv), prod.map_snd,
    Category.assoc, pairOverIso_inv_comp_structureMap,
    pairGluingIso_hom_comp_snd_pairObjMap, prod.map_snd, Category.comp_id]

end EquivariantScheme
end AlgebraicGeometry

namespace AlgebraicGeometry
namespace EquivariantScheme
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- An equivariant morphism out of a map of the underlying objects which is compatible with
the two actions. -/
def pairHomMk {V W : EquivariantScheme (pairGroupoid f)} (g : V.obj ⟶ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (x : T ⟶ Over.mk f),
      V.pairAct v x ≫ g.left = W.pairAct (v ≫ g.left) x) : V ⟶ W where
  hom := g
  comm := by
    intro T v a w
    have hwW : (v ≫ g.left) ≫ W.pairObjMap = a ≫ pairTarget f :=
      (Category.assoc v g.left W.pairObjMap).trans
        ((congrArg (fun z : V.obj.left ⟶ Over.mk f ↦ v ≫ z) (Over.w g)).trans w)
    refine Eq.trans (congrArg (fun z ↦ z ≫ g.left) (V.action_eq_pairAct v a w)) ?_
    refine Eq.trans ?_ (W.action_eq_pairAct (v ≫ g.left) a hwW).symm
    exact h v (a ≫ pairSource f)

/-- An isomorphism of equivariant schemes out of an isomorphism of the underlying objects
which is compatible with the two actions. -/
def pairIsoMk {V W : EquivariantScheme (pairGroupoid f)} (i : V.obj ≅ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (x : T ⟶ Over.mk f),
      V.pairAct v x ≫ i.hom.left = W.pairAct (v ≫ i.hom.left) x) : V ≅ W where
  hom := pairHomMk i.hom h
  inv := pairHomMk i.inv (by
    intro T u x
    have hhi : i.hom.left ≫ i.inv.left = 𝟙 V.obj.left := by
      rw [← Over.comp_left, i.hom_inv_id, Over.id_left]
    have hih : i.inv.left ≫ i.hom.left = 𝟙 W.obj.left := by
      rw [← Over.comp_left, i.inv_hom_id, Over.id_left]
    have key := h (u ≫ i.inv.left) x
    rw [Category.assoc, hih, Category.comp_id] at key
    rw [← key, Category.assoc, hhi, Category.comp_id])
  hom_inv_id := EquivariantScheme.hom_ext _ _ i.hom_inv_id
  inv_hom_id := EquivariantScheme.hom_ext _ _ i.inv_hom_id

variable (W : EquivariantScheme (pairGroupoid f))

/-- The gluing isomorphism of the descent datum attached to an equivariant scheme, as an
isomorphism over `X ×_S X`. -/
def pairGluingSliceIso :
    Over.mk (prod.map (structureMap f W.pairOver) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f W.pairOver)) :=
  Over.isoMk W.pairGluingDatumIso (by
    have h : W.pairGluingDatumIso.hom ≫
        prod.map (𝟙 (Over.mk f)) (structureMap f W.pairOver) =
          prod.map (structureMap f W.pairOver) (𝟙 (Over.mk f)) := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, prod.map_fst, Category.comp_id,
          W.pairGluingDatumIso_hom_comp_fst, prod.map_fst]
      · rw [Category.assoc, prod.map_snd, W.pairGluingDatumIso_hom_comp_snd_structureMap,
          prod.map_snd, Category.comp_id]
    exact h)

/-- The descent datum attached to an equivariant scheme for the pair groupoid of `f`. -/
def pairDescentDatum : DescentDatum f :=
  DescentDatum.mk' W.pairOver W.pairGluingSliceIso
    ((cocycle_iff_gluingAction_act_act W.pairOver W.pairGluingDatumIso.hom
        W.pairGluingDatumIso_hom_comp_fst
        W.pairGluingDatumIso_hom_comp_snd_structureMap).mpr (by
      intro T v x y
      rw [W.gluingAction_pairGluingDatumIso, W.gluingAction_pairGluingDatumIso,
        W.gluingAction_pairGluingDatumIso, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, W.pairAct_act]))

end EquivariantScheme
end AlgebraicGeometry

namespace AlgebraicGeometry
variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The comparison functor is essentially surjective: every equivariant scheme for the pair
groupoid is isomorphic to the one attached to a descent datum. -/
instance : (descentDatumToEquivariantFunctor f).EssSurj where
  mem_essImage W := by
    refine ⟨W.pairDescentDatum, ⟨EquivariantScheme.pairIsoMk
      (Over.isoMk W.pairOverIso W.pairOverIso_hom_comp_pairObjMap) ?_⟩⟩
    intro T v x
    have h1 : (descentDatumToEquivariant W.pairDescentDatum).pairAct v x =
        W.pairAct (v ≫ W.pairOverIso.hom) x ≫ W.pairOverIso.inv :=
      (descentDatumToEquivariant_pairAct W.pairDescentDatum v x).trans
        (W.gluingAction_pairGluingDatumIso v x)
    refine (congrArg (fun z ↦ z ≫ W.pairOverIso.hom) h1).trans ?_
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

/-- The comparison functor is an equivalence. -/
instance : (descentDatumToEquivariantFunctor f).IsEquivalence where

/-- Descent data relative to `f` are the same thing as equivariant schemes for the pair
groupoid of `f`. -/
def descentDatumEquivalenceEquivariant (f : X ⟶ S) :
    DescentDatum f ≌ EquivariantScheme (pairGroupoid f) :=
  (descentDatumToEquivariantFunctor f).asEquivalence

/-- Groupoid schemes cartesian over the pair groupoid `(X, X ×_S X, s, t, c)`, as a groupoid
scheme over `S`, are the same thing as descent data relative to `X/S`. -/
@[stacks 0APF "the equivalence for the base scheme equal to the target of `f`"]
def cartesianOverEquivDescentDatum (f : X ⟶ S) :
    CartesianOver (pairGroupoid f) ≌ DescentDatum f :=
  (cartesianOverEquivalenceEquivariantScheme (pairGroupoid f)).trans
    (descentDatumEquivalenceEquivariant f).symm

/-- An isomorphism of equivariant schemes, read on the underlying schemes over the object
scheme of the groupoid. -/
def EquivariantScheme.objIso {G : GroupoidScheme S} {V W : EquivariantScheme G} (e : V ≅ W) :
    V.obj ≅ W.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg (fun k : EquivariantScheme.Hom V V ↦ k.hom) e.hom_inv_id
  inv_hom_id := congrArg (fun k : EquivariantScheme.Hom W W ↦ k.hom) e.inv_hom_id

/-- The groupoid scheme cartesian over the pair groupoid of `f` which a descent datum
determines, by the equivalence `AlgebraicGeometry.cartesianOverEquivDescentDatum`. -/
def descentDatumCartesianOver (D : DescentDatum f) : CartesianOver (pairGroupoid f) :=
  (cartesianOverEquivDescentDatum f).inverse.obj D

/-- The object scheme of `AlgebraicGeometry.descentDatumCartesianOver D` is isomorphic to the
scheme `V` carrying `D`, both regarded as schemes over `X` through their structure morphisms to
the objects of the pair groupoid. -/
def descentDatumCartesianOverObjectsIso (D : DescentDatum f) :
    (Over.mk (descentDatumCartesianOver D).hom.mapObjects : Over ((pairGroupoid f).objects)) ≅
      Over.mk (structureMap f D.over) :=
  (eqToIso (cartesianOverEquivalenceEquivariantScheme_obj_eq (pairGroupoid f)
    (descentDatumCartesianOver D)).symm).trans
    (EquivariantScheme.objIso
      ((cartesianOverEquivalenceEquivariantScheme (pairGroupoid f)).counitIso.app
        (descentDatumToEquivariant D)))

end AlgebraicGeometry

end

end
