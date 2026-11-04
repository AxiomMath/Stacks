module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
public import StacksFrontier.AlgebraicGeometry.Simplicial.DescentViaSimplicialSchemes
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian schemes over `(X/S)_•` and descent data relative to `X/S`

Let `f : X ⟶ S` be a morphism of schemes. A cartesian simplicial scheme `Y ⟶ (X/S)_•` gives a
descent datum `(V, φ)` relative to `f`, with `V = Y_0` over `X`. This file shows that this
construction is an equivalence of categories.

## Main definitions

* `Stacks.Simplicial.Descent.descentDatumOfAction`: a descent datum on a simplicial object from
  a transition isomorphism whose action on generalized points is unital and transitive.
* `AlgebraicGeometry.SimplicialScheme.pointAct`: the action of a descent datum relative to `f`
  on generalized points of schemes.
* `AlgebraicGeometry.SimplicialScheme.toDescentDatumFunctor`: the passage from a descent datum
  on `(X/S)_•` to the descent datum `(V, φ)` relative to `f`, as a functor.
* `AlgebraicGeometry.SimplicialScheme.cartesianDescentDatumFunctor`: the construction of
  Lemma 024B, as a functor, and `cartesianSchemesEquivalenceDescentData` the resulting
  equivalence.
* `AlgebraicGeometry.SimplicialScheme.ofDescentDatumDatum`: the descent datum on `(X/S)_•`
  attached to a descent datum relative to `f`, with `V` placed over `(X/S)_0` by its unique
  vertex and the transition isomorphism given by the action along edges.

## Main results

* `AlgebraicGeometry.SimplicialScheme.cartesianDescentDatumFunctor_isEquivalence`: **the
  construction of Lemma 024B is an equivalence of categories.**
* `AlgebraicGeometry.SimplicialScheme.toDescentDatumFunctor_fullyFaithful` and
  `AlgebraicGeometry.SimplicialScheme.ofDescentDatumIso` are the two halves: the passage from
  descent data on `(X/S)_•` to descent data relative to `f` is fully faithful and essentially
  surjective. Composing with the equivalence of Tag 07TC gives the lemma.

## Implementation notes

Both categories of descent data are described by an action on generalized points: a point `v`
of `V` and a point `x` of `X` over the same point of `S` give a new point of `V` over `x`
(`AlgebraicGeometry.DescentDatum.act` for the gluing isomorphism `φ`, and `transport` along an
edge of `(X/S)_•` for a descent datum on the simplicial scheme). The comparison is the
statement that the two actions agree, and the unit and cocycle conditions on both sides become
the statements that the action is unital and transitive.

## References

* [Stacks Project, Tag 024C](https://stacks.math.columbia.edu/tag/024C)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Simplicial.Descent
open scoped Simplicial

universe v u

namespace Stacks.Simplicial.Descent

/-! ### A descent datum from a unital, transitive action -/

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (X : SimplicialObject C)

/-- A descent datum on a simplicial object `X`, from a transition isomorphism over `X₁` whose
action on generalized points is unital and transitive. -/
def descentDatumOfAction (V : Over (X.obj (op ⦋0⦌)))
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅ (Over.pullback (X.δ (0 : Fin 2))).obj V)
    (hunit : ∀ (T : C) (t : T ⟶ X.obj (op ⦋0⦌)) (v : T ⟶ V.left)
      (h : v ≫ V.hom = (t ≫ X.σ (0 : Fin 1)) ≫ X.δ (1 : Fin 2)),
      action φ.hom (t ≫ X.σ (0 : Fin 1)) v h = v)
    (htrans : ∀ (T : C) (t : T ⟶ X.obj (op ⦋2⦌)) (v : T ⟶ V.left)
      (h₁ : v ≫ V.hom = (t ≫ X.δ (1 : Fin 3)) ≫ X.δ (1 : Fin 2))
      (h₂ : v ≫ V.hom = (t ≫ X.δ (2 : Fin 3)) ≫ X.δ (1 : Fin 2))
      (h₃ : action φ.hom (t ≫ X.δ (2 : Fin 3)) v h₂ ≫ V.hom =
        (t ≫ X.δ (0 : Fin 3)) ≫ X.δ (1 : Fin 2)),
      action φ.hom (t ≫ X.δ (1 : Fin 3)) v h₁ =
        action φ.hom (t ≫ X.δ (0 : Fin 3)) (action φ.hom (t ≫ X.δ (2 : Fin 3)) v h₂) h₃) :
    DescentDatum X where
  V := V
  iso := φ
  unit := (unit_iff_action _ _ _ _ _ _ _).mpr fun T t v _ => hunit T t v _
  cocycle := (cocycle_iff_action _ _ _ _ _ _ _ _ _ _).mpr fun T t v _ => htrans T t v _ _ _

/-- The object over `X₀` of the descent datum assembled from an action is the given one. -/
@[simp] lemma descentDatumOfAction_V (V : Over (X.obj (op ⦋0⦌)))
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅ (Over.pullback (X.δ (0 : Fin 2))).obj V)
    (hunit) (htrans) : (descentDatumOfAction X V φ hunit htrans).V = V := rfl

/-- The transition isomorphism of the descent datum assembled from an action is the given
one. -/
@[simp] lemma descentDatumOfAction_iso (V : Over (X.obj (op ⦋0⦌)))
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅ (Over.pullback (X.δ (0 : Fin 2))).obj V)
    (hunit) (htrans) : (descentDatumOfAction X V φ hunit htrans).iso = φ := rfl

end Stacks.Simplicial.Descent

namespace AlgebraicGeometry

namespace SimplicialScheme

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-! ### The action of a descent datum relative to `f` on generalized points of schemes -/

section PointAct

variable (W : AlgebraicGeometry.DescentDatum f) {T : Scheme.{u}} (s : T ⟶ S)
  (v : T ⟶ W.over.left) (x y : T ⟶ X)

/-- The action of a descent datum relative to `f : X ⟶ S` on a point `v` of `V` and a point `x`
of `X` lying over the same point `s` of `S`. -/
def pointAct (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s) : T ⟶ W.over.left :=
  (W.act (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx)).left

/-- The defining description of the action. -/
lemma pointAct_def (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s) :
    pointAct W s v x hv hx =
      (W.act (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx)).left := rfl

/-- The action of a descent datum, read on the underlying scheme morphisms. -/
lemma act_left {R : Over S} (vv : R ⟶ (Over.map f).obj W.over) (xx : R ⟶ Over.mk f) :
    (W.act vv xx).left = pointAct W R.hom vv.left xx.left (Over.w vv) (Over.w xx) := rfl

/-- The point produced by the action lies over the acting point of `X`. -/
lemma pointAct_base (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s) :
    pointAct W s v x hv hx ≫ W.over.hom = x := by
  have h2 : ((W.act (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx)) ≫
        structureMap f W.over).left =
      (Over.homMk x hx : Over.mk s ⟶ Over.mk f).left :=
    congrArg CommaMorphism.left
      (W.act_comp_structureMap (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx))
  simp only [pointAct_def]
  simpa only [Over.comp_left, Over.homMk_left] using h2

/-- The point produced by the action lies over `s`. -/
lemma pointAct_comp_base (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s) :
    pointAct W s v x hv hx ≫ W.over.hom ≫ f = s := by
  rw [← Category.assoc, pointAct_base]
  exact hx

/-- Acting twice is acting once. -/
lemma pointAct_act (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s) (hy : y ≫ f = s) :
    pointAct W s (pointAct W s v x hv hx) y (pointAct_comp_base W s v x hv hx) hy =
      pointAct W s v y hv hy := by
  have key : (Over.homMk (pointAct W s v x hv hx) (pointAct_comp_base W s v x hv hx) :
        Over.mk s ⟶ (Over.map f).obj W.over) =
      W.act (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx) :=
    Over.OverMorphism.ext (pointAct_def W s v x hv hx)
  have h := congrArg CommaMorphism.left
    (W.act_act (T := Over.mk s) (Over.homMk v hv) (Over.homMk x hx) (Over.homMk y hy))
  rw [← key] at h
  exact h

/-- A point is fixed by the point of `X` it lies over. -/
lemma pointAct_self (hv : v ≫ W.over.hom ≫ f = s) (hv' : (v ≫ W.over.hom) ≫ f = s) :
    pointAct W s v (v ≫ W.over.hom) hv hv' = v := by
  have key : (Over.homMk (v ≫ W.over.hom) hv' : Over.mk s ⟶ Over.mk f) =
      (Over.homMk v hv : Over.mk s ⟶ (Over.map f).obj W.over) ≫ structureMap f W.over :=
    Over.OverMorphism.ext rfl
  have h := congrArg CommaMorphism.left (W.act_self (T := Over.mk s) (Over.homMk v hv))
  rw [← key] at h
  exact h

/-- The action depends only on the three morphisms, not on the compatibility proofs. -/
lemma pointAct_congr (s' : T ⟶ S) (v' : T ⟶ W.over.left) (x' : T ⟶ X)
    (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s)
    (hv' : v' ≫ W.over.hom ≫ f = s') (hx' : x' ≫ f = s')
    (hs : s = s') (hvv : v = v') (hxx : x = x') :
    pointAct W s v x hv hx = pointAct W s' v' x' hv' hx' := by
  subst hs; subst hvv; subst hxx; rfl

/-- The action commutes with change of test scheme. -/
lemma pointAct_precomp (hv : v ≫ W.over.hom ≫ f = s) (hx : x ≫ f = s)
    {T' : Scheme.{u}} (a : T' ⟶ T)
    (hav : (a ≫ v) ≫ W.over.hom ≫ f = a ≫ s) (hax : (a ≫ x) ≫ f = a ≫ s) :
    a ≫ pointAct W s v x hv hx = pointAct W (a ≫ s) (a ≫ v) (a ≫ x) hav hax := by
  have hk : (Over.homMk a rfl : Over.mk (a ≫ s) ⟶ Over.mk s) ≫
        (Over.homMk v hv : Over.mk s ⟶ (Over.map f).obj W.over) =
      (Over.homMk (a ≫ v) hav : Over.mk (a ≫ s) ⟶ (Over.map f).obj W.over) :=
    Over.OverMorphism.ext rfl
  have hk' : (Over.homMk a rfl : Over.mk (a ≫ s) ⟶ Over.mk s) ≫
        (Over.homMk x hx : Over.mk s ⟶ Over.mk f) =
      (Over.homMk (a ≫ x) hax : Over.mk (a ≫ s) ⟶ Over.mk f) :=
    Over.OverMorphism.ext rfl
  have h := congrArg CommaMorphism.left
    (W.comp_act (T := Over.mk s) (U := Over.mk (a ≫ s))
      (Over.homMk a rfl) (Over.homMk v hv) (Over.homMk x hx))
  rw [hk, hk'] at h
  simpa only [pointAct_def, Over.comp_left, Over.homMk_left] using h

end PointAct

/-! ### The construction of Lemma 024B as a functor -/

section Functor

variable {D E : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)}

/-- The gluing isomorphism of the descent datum `(V, φ)` is `φ`. -/
lemma toDescentDatum_transition_hom_left
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    (toDescentDatum D).transition.hom.left = transitionHom D := rfl

/-- The action of the descent datum `(V, φ)` is the transport of `D` along an edge. -/
lemma toDescentDatum_act_left
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) {R : Over S}
    (a : R ⟶ (Over.map f).obj (descentObj D)) (b : R ⟶ Over.mk f) :
    ((toDescentDatum D).act a b : R ⟶ (Over.map f).obj (descentObj D)).left =
      transport D (a.left ≫ (descentObj D).hom) b.left (lift_cond D a b) a.left rfl := by
  have h0 : ((toDescentDatum D).act a b : R ⟶ (Over.map f).obj (descentObj D)) =
      prod.lift a b ≫ actMap D := by
    simp only [AlgebraicGeometry.DescentDatum.act, gluingAction, toDescentDatum_over,
      toDescentDatum_transition_hom_left]
    rw [transitionHom_snd]
  rw [h0, actMap_lift_left]

/-- The action of the descent datum `(V, φ)` is the transport along any edge from the base point
of the acting point. -/
private lemma toDescentDatum_act_left_eq_transport
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) {R : Over S}
    (a : R ⟶ (Over.map f).obj (descentObj D)) (b : R ⟶ Over.mk f) (x : R.left ⟶ X)
    (hx : a.left ≫ D.V.hom ≫ proj f 0 0 = x) (hxy : x ≫ f = b.left ≫ f) :
    ((toDescentDatum D).act a b : R ⟶ (Over.map f).obj (descentObj D)).left =
      transport D x b.left hxy a.left hx := by
  subst hx
  exact toDescentDatum_act_left D a b

/-- Transport along an edge is compatible with a morphism of descent data on `(X/S)_•`. -/
lemma transport_compatibility (a : D ⟶ E) {R : Scheme.{u}} (x y : R ⟶ X) (hxy : x ≫ f = y ≫ f)
    (v : R ⟶ D.V.left) (hv : v ≫ D.V.hom ≫ proj f 0 0 = x)
    (hv' : (v ≫ a.hom.left) ≫ E.V.hom ≫ proj f 0 0 = x) :
    transport E x y hxy (v ≫ a.hom.left) hv' = transport D x y hxy v hv ≫ a.hom.left :=
  (action_compatibility ((simplicialScheme f).δ (1 : Fin 2)) ((simplicialScheme f).δ (0 : Fin 2))
    D.iso.hom E.iso.hom a.hom).mp a.comm R (edgeSimplex f x y hxy) v _

/-- A morphism of descent data on `(X/S)_•` is a morphism of schemes over `X`. -/
lemma hom_left_comp_proj (a : D ⟶ E) :
    a.hom.left ≫ E.V.hom ≫ proj f 0 0 = D.V.hom ≫ proj f 0 0 := by
  rw [← Category.assoc, Over.w a.hom]

/-- The morphism of `X`-schemes underlying a morphism of descent data on `(X/S)_•`. -/
def toDescentDatumHom (a : D ⟶ E) : descentObj D ⟶ descentObj E :=
  Over.homMk a.hom.left (hom_left_comp_proj a)

/-- The underlying map of schemes is the degree-zero component. -/
@[simp] lemma toDescentDatumHom_left (a : D ⟶ E) : (toDescentDatumHom a).left = a.hom.left := rfl

/-- A morphism of descent data on `(X/S)_•` is equivariant for the two actions. -/
lemma act_compatibility (a : D ⟶ E) {R : Over S}
    (vv : R ⟶ (Over.map f).obj (toDescentDatum D).over) (xx : R ⟶ Over.mk f) :
    (toDescentDatum D).act vv xx ≫ (Over.map f).map (toDescentDatumHom a) =
      (toDescentDatum E).act (vv ≫ (Over.map f).map (toDescentDatumHom a)) xx := by
  have hbase : (vv.left ≫ D.V.hom ≫ proj f 0 0) ≫ f = xx.left ≫ f := lift_cond D vv xx
  have hxEq : (vv.left ≫ a.hom.left) ≫ E.V.hom ≫ proj f 0 0 =
      vv.left ≫ D.V.hom ≫ proj f 0 0 :=
    (Category.assoc _ _ _).trans (congrArg (vv.left ≫ ·) (hom_left_comp_proj a))
  have hL : ((toDescentDatum D).act vv xx ≫ (Over.map f).map (toDescentDatumHom a)).left =
      transport D (vv.left ≫ D.V.hom ≫ proj f 0 0) xx.left hbase vv.left rfl ≫ a.hom.left :=
    congrArg (· ≫ a.hom.left) (toDescentDatum_act_left_eq_transport D vv xx _ rfl hbase)
  have hR : ((toDescentDatum E).act (vv ≫ (Over.map f).map (toDescentDatumHom a)) xx).left =
      transport E (vv.left ≫ D.V.hom ≫ proj f 0 0) xx.left hbase (vv.left ≫ a.hom.left) hxEq :=
    toDescentDatum_act_left_eq_transport E _ xx _ hxEq hbase
  exact Over.OverMorphism.ext
    (hL.trans ((transport_compatibility a _ xx.left hbase vv.left rfl hxEq).symm.trans hR.symm))

/-- The construction of Lemma 024B on a morphism of descent data on `(X/S)_•`. -/
def toDescentDatumMap (a : D ⟶ E) : toDescentDatum D ⟶ toDescentDatum E where
  hom _ := toDescentDatumHom a
  comm _ _ :=
    (AlgebraicGeometry.DescentDatum.hom_comm_iff (toDescentDatum D) (toDescentDatum E)
      (toDescentDatumHom a)).mpr fun vv xx => act_compatibility a vv xx

/-- The component of the morphism of descent data relative to `f`. -/
@[simp] lemma toDescentDatumMap_hom (a : D ⟶ E) (i : Unit) :
    (toDescentDatumMap a).hom i = toDescentDatumHom a := rfl

/-- **The construction of Lemma 024B**, from descent data on `(X/S)_•` to descent data
relative to `f : X ⟶ S`, as a functor. -/
def toDescentDatumFunctor (f : X ⟶ S) :
    Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f) ⥤
      AlgebraicGeometry.DescentDatum f where
  obj := toDescentDatum
  map := toDescentDatumMap
  map_id _ := AlgebraicGeometry.DescentData.hom_ext fun _ => Over.OverMorphism.ext rfl
  map_comp _ _ := AlgebraicGeometry.DescentData.hom_ext fun _ => Over.OverMorphism.ext rfl

/-! ### Full faithfulness -/

/-- The morphism of descent data on `(X/S)_•` underlying a morphism of the associated descent
data relative to `f`. -/
def ofDescentDatumHom (g : toDescentDatum D ⟶ toDescentDatum E) : D.V ⟶ E.V :=
  Over.homMk (g.hom ()).left
    (zero_hom_ext f ((Category.assoc (g.hom ()).left E.V.hom (proj f 0 0)).trans
      (Over.w (g.hom ()))))

/-- The underlying map of schemes is the one of the given morphism. -/
@[simp] lemma ofDescentDatumHom_left (g : toDescentDatum D ⟶ toDescentDatum E) :
    (ofDescentDatumHom g).left = (g.hom ()).left := rfl

/-- Transport is compatible with a morphism of the associated descent data relative to `f`. -/
lemma transport_compatibility_of_hom (g : toDescentDatum D ⟶ toDescentDatum E)
    {R : Scheme.{u}} (x y : R ⟶ X) (hxy : x ≫ f = y ≫ f) (v : R ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x)
    (hv' : (v ≫ (g.hom ()).left) ≫ E.V.hom ≫ proj f 0 0 = x) :
    transport E x y hxy (v ≫ (g.hom ()).left) hv' =
      transport D x y hxy v hv ≫ (g.hom ()).left := by
  have H := (AlgebraicGeometry.DescentDatum.hom_comm_iff (toDescentDatum D) (toDescentDatum E)
    (g.hom ())).mp (g.comm () ()) (T := Over.mk (x ≫ f))
  have hvv : v ≫ ((Over.map f).obj (descentObj D)).hom = (Over.mk (x ≫ f) : Over S).hom :=
    (Category.assoc v (descentObj D).hom f).symm.trans (congrArg (· ≫ f) hv)
  let vv : (Over.mk (x ≫ f) : Over S) ⟶ (Over.map f).obj (descentObj D) := Over.homMk v hvv
  let xx : (Over.mk (x ≫ f) : Over S) ⟶ Over.mk f := Over.homMk y hxy.symm
  have hD : ((toDescentDatum D).act vv xx :
        (Over.mk (x ≫ f) : Over S) ⟶ (Over.map f).obj (descentObj D)).left =
      transport D x y hxy v hv :=
    toDescentDatum_act_left_eq_transport D vv xx x hv hxy
  have hE : ((toDescentDatum E).act (vv ≫ (Over.map f).map (g.hom ())) xx :
        (Over.mk (x ≫ f) : Over S) ⟶ (Over.map f).obj (descentObj E)).left =
      transport E x y hxy (v ≫ (g.hom ()).left) hv' :=
    toDescentDatum_act_left_eq_transport E (vv ≫ (Over.map f).map (g.hom ())) xx x hv' hxy
  have key : ((toDescentDatum D).act vv xx :
        (Over.mk (x ≫ f) : Over S) ⟶ (Over.map f).obj (descentObj D)).left ≫
        (g.hom ()).left =
      ((toDescentDatum E).act (vv ≫ (Over.map f).map (g.hom ())) xx :
        (Over.mk (x ≫ f) : Over S) ⟶ (Over.map f).obj (descentObj E)).left :=
    congrArg CommaMorphism.left (H vv xx)
  exact (((congrArg (· ≫ (g.hom ()).left) hD).symm.trans key).trans hE).symm

/-- The lifted morphism is compatible with the transition isomorphisms. -/
lemma ofDescentDatumHom_comm (g : toDescentDatum D ⟶ toDescentDatum E) :
    (Over.pullback ((simplicialScheme f).δ (1 : Fin 2))).map (ofDescentDatumHom g) ≫ E.iso.hom =
      D.iso.hom ≫
        (Over.pullback ((simplicialScheme f).δ (0 : Fin 2))).map (ofDescentDatumHom g) := by
  refine (action_compatibility ((simplicialScheme f).δ (1 : Fin 2))
    ((simplicialScheme f).δ (0 : Fin 2)) D.iso.hom E.iso.hom (ofDescentDatumHom g)).mpr ?_
  intro R t v hvt
  have hxy : (t ≫ proj f 1 0) ≫ f = (t ≫ proj f 1 1) ≫ f := by
    simp only [Category.assoc, proj_comp]
  have ht : t = edgeSimplex f (t ≫ proj f 1 0) (t ≫ proj f 1 1) hxy :=
    one_hom_ext f (edgeSimplex_proj_zero f _ _ hxy).symm (edgeSimplex_proj_one f _ _ hxy).symm
  have hv : v ≫ D.V.hom ≫ proj f 0 0 = t ≫ proj f 1 0 := by
    rw [← Category.assoc, hvt, Category.assoc, delta_one_proj]
  have hv' : (v ≫ (g.hom ()).left) ≫ E.V.hom ≫ proj f 0 0 = t ≫ proj f 1 0 :=
    (Category.assoc v (g.hom ()).left (E.V.hom ≫ proj f 0 0)).trans
      ((congrArg (v ≫ ·) (Over.w (g.hom ()))).trans hv)
  have hw2 : (v ≫ (ofDescentDatumHom g).left) ≫ E.V.hom =
      t ≫ (simplicialScheme f).δ (1 : Fin 2) :=
    (Category.assoc v (ofDescentDatumHom g).left E.V.hom).trans
      ((congrArg (v ≫ ·) (Over.w (ofDescentDatumHom g))).trans hvt)
  have hDa : action D.iso.hom t v hvt =
      transport D (t ≫ proj f 1 0) (t ≫ proj f 1 1) hxy v hv :=
    action_congr D.iso.hom hvt _ ht rfl
  have hEa : action E.iso.hom t (v ≫ (ofDescentDatumHom g).left) hw2 =
      transport E (t ≫ proj f 1 0) (t ≫ proj f 1 1) hxy (v ≫ (g.hom ()).left) hv' :=
    action_congr E.iso.hom hw2 _ ht rfl
  exact hEa.trans ((transport_compatibility_of_hom g _ _ hxy v hv hv').trans
    (congrArg (· ≫ (g.hom ()).left) hDa).symm)

/-- **The construction of Lemma 024B is fully faithful.** -/
def toDescentDatumFunctor_fullyFaithful (f : X ⟶ S) :
    (toDescentDatumFunctor f).FullyFaithful where
  preimage {_ _} g := ⟨ofDescentDatumHom g, ofDescentDatumHom_comm g⟩
  map_preimage {_ _} _ :=
    AlgebraicGeometry.DescentData.hom_ext fun _ => Over.OverMorphism.ext rfl
  preimage_map {_ _} _ := Stacks.Simplicial.Descent.DescentDatum.Hom.ext _ _
    (Over.OverMorphism.ext rfl)

end Functor

/-! ### Essential surjectivity -/

section EssSurj

/-! The degeneracy of `(X/S)_0` and the faces of `(X/S)_2`, read on vertices and on the base.
These are index computations in the simplex category. -/

/-- The degeneracy `σ 0 : ⦋1⦌ ⟶ ⦋0⦌` sends the vertex `1` to `0`. -/
lemma sigma_zero_ohom_one : (SimplexCategory.σ (0 : Fin 1)).toOrderHom 1 = 0 := by decide

/-- The face `δ 2 : ⦋1⦌ ⟶ ⦋2⦌` sends the vertex `1` to `1`. -/
lemma delta_two_ohom_one : (SimplexCategory.δ (2 : Fin 3)).toOrderHom 1 = 1 := by decide

/-- The face `δ 1 : ⦋1⦌ ⟶ ⦋2⦌` sends the vertex `1` to `2`. -/
lemma delta_one_ohom_one : (SimplexCategory.δ (1 : Fin 3)).toOrderHom 1 = 2 := by decide

/-- The face `δ 0 : ⦋1⦌ ⟶ ⦋2⦌` sends the vertex `1` to `2`. -/
lemma delta_zero_ohom_one : (SimplexCategory.δ (0 : Fin 3)).toOrderHom 1 = 2 := by decide

/-- The degeneracy `σ 0 : ⦋1⦌ ⟶ ⦋0⦌` sends the vertex `0` to `0`. -/
lemma sigma_zero_ohom_zero : (SimplexCategory.σ (0 : Fin 1)).toOrderHom 0 = 0 := by decide

/-- The face `δ 2 : ⦋1⦌ ⟶ ⦋2⦌` sends the vertex `0` to `0`. -/
lemma delta_two_ohom_zero : (SimplexCategory.δ (2 : Fin 3)).toOrderHom 0 = 0 := by decide

/-- The degeneracy `σ 0 : (X/S)_0 ⟶ (X/S)_1` followed by the projection `1` is the projection
`0` of `(X/S)_0`. -/
lemma sigma_zero_proj : (simplicialScheme f).σ (0 : Fin 1) ≫ proj f 1 1 = proj f 0 0 := by
  simp [SimplicialObject.σ, sigma_zero_ohom_one]

/-- The degeneracy `σ 0 : (X/S)_0 ⟶ (X/S)_1` followed by the projection `0` is the projection
`0` of `(X/S)_0`. -/
lemma sigma_zero_proj_zero : (simplicialScheme f).σ (0 : Fin 1) ≫ proj f 1 0 = proj f 0 0 := by
  simp [SimplicialObject.σ, sigma_zero_ohom_zero]

/-- The face `δ 2 : (X/S)_2 ⟶ (X/S)_1` followed by the projection `0` is the projection `0` of
`(X/S)_2`. -/
lemma delta_two_proj_zero : (simplicialScheme f).δ (2 : Fin 3) ≫ proj f 1 0 = proj f 2 0 := by
  simp [SimplicialObject.δ, delta_two_ohom_zero]

/-- The face `δ 2 : (X/S)_2 ⟶ (X/S)_1` followed by the projection `1` is the projection `1` of
`(X/S)_2`. -/
lemma delta_two_proj : (simplicialScheme f).δ (2 : Fin 3) ≫ proj f 1 1 = proj f 2 1 := by
  simp [SimplicialObject.δ, delta_two_ohom_one]

/-- The face `δ 1 : (X/S)_2 ⟶ (X/S)_1` followed by the projection `1` is the projection `2` of
`(X/S)_2`. -/
lemma delta_one_proj_two : (simplicialScheme f).δ (1 : Fin 3) ≫ proj f 1 1 = proj f 2 2 := by
  simp [SimplicialObject.δ, delta_one_ohom_one]

/-- The face `δ 0 : (X/S)_2 ⟶ (X/S)_1` followed by the projection `1` is the projection `2` of
`(X/S)_2`. -/
lemma delta_zero_proj_two : (simplicialScheme f).δ (0 : Fin 3) ≫ proj f 1 1 = proj f 2 2 := by
  simp [SimplicialObject.δ, delta_zero_ohom_one]

/-- Every face map `(X/S)_2 ⟶ (X/S)_1` commutes with the structure morphisms to `S`. -/
lemma delta_baseMap (i : Fin 3) : (simplicialScheme f).δ i ≫ baseMap f 1 = baseMap f 2 := by
  rw [← proj_comp f 1 0, ← Category.assoc]
  simp [SimplicialObject.δ]

/-- The degeneracy `σ 0 : (X/S)_0 ⟶ (X/S)_1` commutes with the structure morphisms to `S`. -/
lemma sigma_baseMap : (simplicialScheme f).σ (0 : Fin 1) ≫ baseMap f 1 = baseMap f 0 := by
  rw [← proj_comp f 1 0, ← Category.assoc]
  simp [SimplicialObject.σ]

variable (W : AlgebraicGeometry.DescentDatum f)

/-- The scheme `V` of a descent datum relative to `f`, viewed over `(X/S)_0` through the unique
vertex of `(X/S)_0`. -/
abbrev vertexObj : Over ((simplicialScheme f).obj (op ⦋0⦌)) :=
  Over.mk (vertexSimplex f W.over.hom)

/-- The unique vertex of `(X/S)_0` recovers the structure morphism of `V`. -/
lemma vertexObj_proj : (vertexObj W).hom ≫ proj f 0 0 = W.over.hom :=
  vertexSimplex_proj f W.over.hom 0

/-- A point of the base change of `V` along the `i`-th face lies over the `k`-th vertex. -/
lemma faceCond (i k : Fin 2) (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k) :
    pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i) ≫ W.over.hom =
      pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 k := by
  have h := congrArg (· ≫ proj f 0 0)
    (pullback.condition (f := (vertexObj W).hom) (g := (simplicialScheme f).δ i))
  simpa only [Category.assoc, vertexObj_proj, hi] using h

/-- A point of the base change of `V` along the `i`-th face lies over the same point of `S` as
the edge it sits over. -/
lemma faceHv (i k : Fin 2) (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k) :
    pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i) ≫ W.over.hom ≫ f =
      pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1 := by
  rw [← Category.assoc, faceCond W i k hi, Category.assoc, proj_comp]

/-- A vertex of the edge under a point of the base change lies over the same point of `S`. -/
lemma faceHx (i l : Fin 2) :
    (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 l) ≫ f =
      pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1 := by
  rw [Category.assoc, proj_comp]

/-- Translation of a point of the base change of `V` along the `i`-th face to a point of the
base change along the `j`-th face: the point of `V` is carried along the edge to the `l`-th
vertex, which is the vertex the `j`-th face names. -/
def faceTranslate (i k : Fin 2) (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k)
    (j l : Fin 2) (hj : (simplicialScheme f).δ j ≫ proj f 0 0 = proj f 1 l) :
    pullback (vertexObj W).hom ((simplicialScheme f).δ i) ⟶
      pullback (vertexObj W).hom ((simplicialScheme f).δ j) :=
  pullback.lift
    (pointAct W (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1)
      (pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i))
      (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 l)
      (faceHv W i k hi) (faceHx W i l))
    (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i))
    (zero_hom_ext f (by
      rw [Category.assoc, Category.assoc, vertexObj_proj, hj, pointAct_base]))

/-- Translation does not move the edge. -/
@[reassoc] lemma faceTranslate_snd (i k : Fin 2)
    (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k) (j l : Fin 2)
    (hj : (simplicialScheme f).δ j ≫ proj f 0 0 = proj f 1 l) :
    faceTranslate W i k hi j l hj ≫
        pullback.snd (vertexObj W).hom ((simplicialScheme f).δ j) =
      pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) :=
  pullback.lift_snd _ _ _

/-- Translation moves the point of `V` by the action. -/
lemma faceTranslate_fst (i k : Fin 2)
    (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k) (j l : Fin 2)
    (hj : (simplicialScheme f).δ j ≫ proj f 0 0 = proj f 1 l) :
    faceTranslate W i k hi j l hj ≫
        pullback.fst (vertexObj W).hom ((simplicialScheme f).δ j) =
      pointAct W (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1)
        (pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i))
        (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 l)
        (faceHv W i k hi) (faceHx W i l) :=
  pullback.lift_fst _ _ _

/-- Translating to the `j`-th face and back is the identity. -/
lemma faceTranslate_comp (i k : Fin 2)
    (hi : (simplicialScheme f).δ i ≫ proj f 0 0 = proj f 1 k) (j l : Fin 2)
    (hj : (simplicialScheme f).δ j ≫ proj f 0 0 = proj f 1 l) :
    faceTranslate W i k hi j l hj ≫ faceTranslate W j l hj i k hi = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, faceTranslate_fst, Category.id_comp,
      pointAct_precomp W _ _ _ (faceHv W j l hj) (faceHx W j k)
        (faceTranslate W i k hi j l hj)
        (by rw [faceTranslate_fst, pointAct_comp_base, faceTranslate_snd_assoc])
        (by rw [faceTranslate_snd_assoc, faceTranslate_snd_assoc, Category.assoc, proj_comp])]
    refine Eq.trans (pointAct_congr W _ _ _
      (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1)
      (pointAct W (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ baseMap f 1)
        (pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i))
        (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 l)
        (faceHv W i k hi) (faceHx W i l))
      (pullback.snd (vertexObj W).hom ((simplicialScheme f).δ i) ≫ proj f 1 k) _ _
      (pointAct_comp_base W _ _ _ (faceHv W i k hi) (faceHx W i l)) (faceHx W i k)
      (by rw [faceTranslate_snd_assoc]) (faceTranslate_fst W i k hi j l hj)
      (by rw [faceTranslate_snd_assoc])) ?_
    refine Eq.trans (pointAct_act W _ _ _ _ (faceHv W i k hi) (faceHx W i l) (faceHx W i k)) ?_
    refine Eq.trans (pointAct_congr W _ _ _ _ _
      (pullback.fst (vertexObj W).hom ((simplicialScheme f).δ i) ≫ W.over.hom)
      (faceHv W i k hi) (faceHx W i k) (faceHv W i k hi)
      (by rw [faceCond W i k hi, Category.assoc, proj_comp])
      rfl rfl (faceCond W i k hi).symm) ?_
    exact pointAct_self W _ _ (faceHv W i k hi) _
  · rw [Category.assoc, faceTranslate_snd, faceTranslate_snd, Category.id_comp]

/-- **The transition isomorphism of the descent datum on `(X/S)_•` attached to `(V, φ)`.** -/
def transitionOverIso :
    (Over.pullback ((simplicialScheme f).δ (1 : Fin 2))).obj (vertexObj W) ≅
      (Over.pullback ((simplicialScheme f).δ (0 : Fin 2))).obj (vertexObj W) :=
  Over.isoMk
    { hom := faceTranslate W 1 0 (delta_one_proj f) 0 1 (delta_zero_proj f)
      inv := faceTranslate W 0 1 (delta_zero_proj f) 1 0 (delta_one_proj f)
      hom_inv_id := faceTranslate_comp W 1 0 (delta_one_proj f) 0 1 (delta_zero_proj f)
      inv_hom_id := faceTranslate_comp W 0 1 (delta_zero_proj f) 1 0 (delta_one_proj f) }
    (faceTranslate_snd W 1 0 (delta_one_proj f) 0 1 (delta_zero_proj f))

/-- The action of the transition isomorphism on a point of `V` over the zeroth vertex of an
edge is the action of `(V, φ)` on that point and the first vertex. -/
lemma action_transitionOverIso {R : Scheme.{u}}
    (t : R ⟶ (simplicialScheme f).obj (op ⦋1⦌)) (v : R ⟶ W.over.left)
    (h : v ≫ (vertexObj W).hom = t ≫ (simplicialScheme f).δ (1 : Fin 2))
    (sb : R ⟶ S) (hs : t ≫ baseMap f 1 = sb) (xx : R ⟶ X) (hxx : t ≫ proj f 1 1 = xx)
    (hv : v ≫ W.over.hom ≫ f = sb) (hx : xx ≫ f = sb) :
    action (transitionOverIso W).hom t v h = pointAct W sb v xx hv hx := by
  change pullback.lift v t h ≫
      faceTranslate W 1 0 (delta_one_proj f) 0 1 (delta_zero_proj f) ≫
        pullback.fst (vertexObj W).hom ((simplicialScheme f).δ (0 : Fin 2)) =
      pointAct W sb v xx hv hx
  rw [faceTranslate_fst, pointAct_precomp W _ _ _
    (faceHv W 1 0 (delta_one_proj f)) (faceHx W 1 1) (pullback.lift v t h)
    (by rw [pullback.lift_fst, pullback.lift_snd_assoc]; exact hv.trans hs.symm)
    (by rw [pullback.lift_snd_assoc, pullback.lift_snd_assoc, Category.assoc, proj_comp])]
  exact pointAct_congr W _ _ _ sb v xx _ _ hv hx
    (by rw [pullback.lift_snd_assoc]; exact hs) (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_snd_assoc]; exact hxx)

/-- **The action is normalized**: a point is fixed by the degenerate edge at the vertex it
lies over. -/
lemma transitionOverIso_action_self {R : Scheme.{u}}
    (t : R ⟶ (simplicialScheme f).obj (op ⦋0⦌)) (v : R ⟶ W.over.left)
    (h : v ≫ (vertexObj W).hom =
      (t ≫ (simplicialScheme f).σ (0 : Fin 1)) ≫ (simplicialScheme f).δ (1 : Fin 2)) :
    action (transitionOverIso W).hom (t ≫ (simplicialScheme f).σ (0 : Fin 1)) v h = v := by
  have hσδ : (simplicialScheme f).σ (0 : Fin 1) ≫ (simplicialScheme f).δ (1 : Fin 2) = 𝟙 _ :=
    (simplicialScheme f).δ_comp_σ_succ (i := (0 : Fin 1))
  have hvt : v ≫ (vertexObj W).hom = t := by
    rw [h, Category.assoc, hσδ, Category.comp_id]
  have hvW : v ≫ W.over.hom = t ≫ proj f 0 0 := by
    rw [← vertexObj_proj W, ← Category.assoc, hvt]
  refine Eq.trans (action_transitionOverIso W (t ≫ (simplicialScheme f).σ (0 : Fin 1)) v h
    (t ≫ baseMap f 0) (by rw [Category.assoc, sigma_baseMap]) (v ≫ W.over.hom)
    (by rw [Category.assoc, sigma_zero_proj]; exact hvW.symm)
    (by rw [← Category.assoc, hvW, Category.assoc, proj_comp])
    (by rw [hvW, Category.assoc, proj_comp])) ?_
  exact pointAct_self W _ _ _ _

/-- **The action is transitive**: moving along `x₀ → x₁` and then `x₁ → x₂` is moving along
`x₀ → x₂`. -/
lemma transitionOverIso_action_trans {R : Scheme.{u}}
    (t : R ⟶ (simplicialScheme f).obj (op ⦋1 + 1⦌)) (v : R ⟶ W.over.left)
    (h1 : v ≫ (vertexObj W).hom =
      (t ≫ (simplicialScheme f).δ (1 : Fin 3)) ≫ (simplicialScheme f).δ (1 : Fin 2))
    (h2 : v ≫ (vertexObj W).hom =
      (t ≫ (simplicialScheme f).δ (2 : Fin 3)) ≫ (simplicialScheme f).δ (1 : Fin 2))
    (h3 : action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (2 : Fin 3)) v h2 ≫
        (vertexObj W).hom =
      (t ≫ (simplicialScheme f).δ (0 : Fin 3)) ≫ (simplicialScheme f).δ (1 : Fin 2)) :
    action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (1 : Fin 3)) v h1 =
      action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (0 : Fin 3))
        (action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (2 : Fin 3)) v h2) h3 := by
  have hvW : v ≫ W.over.hom = t ≫ proj f 2 0 := by
    rw [← vertexObj_proj W, ← Category.assoc, h2, Category.assoc, Category.assoc,
      delta_one_proj, delta_two_proj_zero]
  have hvb : v ≫ W.over.hom ≫ f = t ≫ baseMap f 2 := by
    rw [← Category.assoc, hvW, Category.assoc, proj_comp]
  have hxb (m : Fin 3) : (t ≫ proj f 2 m) ≫ f = t ≫ baseMap f 2 := by
    rw [Category.assoc, proj_comp]
  have hsb (jj : Fin 3) :
      (t ≫ (simplicialScheme f).δ jj) ≫ baseMap f 1 = t ≫ baseMap f 2 := by
    rw [Category.assoc, delta_baseMap]
  have hinner : action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (2 : Fin 3)) v h2 =
      pointAct W (t ≫ baseMap f 2) v (t ≫ proj f 2 1) hvb (hxb 1) :=
    action_transitionOverIso W _ v h2 _ (hsb 2) _
      (by rw [Category.assoc, delta_two_proj]) hvb (hxb 1)
  have hvo : action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (2 : Fin 3)) v h2 ≫
      W.over.hom ≫ f = t ≫ baseMap f 2 :=
    (congrArg (· ≫ W.over.hom ≫ f) hinner).trans (pointAct_comp_base W _ v _ hvb (hxb 1))
  refine Eq.trans (action_transitionOverIso W _ v h1 _ (hsb 1) _
    (by rw [Category.assoc, delta_one_proj_two]) hvb (hxb 2)) ?_
  refine Eq.trans (pointAct_act W _ v _ _ hvb (hxb 1) (hxb 2)).symm ?_
  refine Eq.trans (pointAct_congr W _ _ _ _
    (action (transitionOverIso W).hom (t ≫ (simplicialScheme f).δ (2 : Fin 3)) v h2) _ _ _
    hvo (hxb 2) rfl hinner.symm rfl) ?_
  exact (action_transitionOverIso W _ _ h3 _ (hsb 0) _
    (by rw [Category.assoc, delta_zero_proj_two]) hvo (hxb 2)).symm

/-- **The descent datum on `(X/S)_•` attached to a descent datum relative to `f`.** -/
def ofDescentDatumDatum : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f) :=
  descentDatumOfAction (simplicialScheme f) (vertexObj W) (transitionOverIso W)
    (fun _ t v h => transitionOverIso_action_self W t v h)
    (fun _ t v h₁ h₂ h₃ => transitionOverIso_action_trans W t v h₁ h₂ h₃)

/-- The object over `(X/S)_0` of the attached descent datum is `V`. -/
lemma ofDescentDatumDatum_V : (ofDescentDatumDatum W).V = vertexObj W := rfl

/-- The transition isomorphism of the attached descent datum. -/
lemma ofDescentDatumDatum_iso : (ofDescentDatumDatum W).iso = transitionOverIso W := rfl

/-- The scheme over `X` of the attached descent datum is `V` over `X`. -/
lemma ofDescentDatumDatum_descentObj_hom :
    (descentObj (ofDescentDatumDatum W)).hom = W.over.hom := vertexObj_proj W

/-- Transport in the attached descent datum is the action of `(V, φ)`. -/
lemma transport_ofDescentDatumDatum {R : Scheme.{u}} (xx yy : R ⟶ X) (hxy : xx ≫ f = yy ≫ f)
    (v : R ⟶ W.over.left) (hv : v ≫ (vertexObj W).hom ≫ proj f 0 0 = xx)
    (hv' : v ≫ W.over.hom ≫ f = xx ≫ f) (hy : yy ≫ f = xx ≫ f) :
    transport (ofDescentDatumDatum W) xx yy hxy v hv = pointAct W (xx ≫ f) v yy hv' hy :=
  action_transitionOverIso W (edgeSimplex f xx yy hxy) v
    (zero_hom_ext f (by
      rw [Category.assoc, Category.assoc, delta_one_proj, edgeSimplex_proj_zero]
      exact hv))
    (xx ≫ f) (by rw [← proj_comp f 1 0, ← Category.assoc, edgeSimplex_proj_zero]) yy
    (edgeSimplex_proj_one f xx yy hxy) hv' hy

/-- An isomorphism of descent data relative to `f` from an isomorphism of the underlying
`X`-schemes compatible with the gluing isomorphisms. -/
def descentIsoMk {D E : AlgebraicGeometry.DescentDatum f} (e : D.over ≅ E.over)
    (comm : prod.map ((Over.map f).map e.hom) (𝟙 (Over.mk f)) ≫ E.transition.hom.left =
      D.transition.hom.left ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map e.hom)) : D ≅ E where
  hom := { hom := fun _ => e.hom, comm := fun _ _ => comm }
  inv :=
    { hom := fun _ => e.inv
      comm := fun _ _ => by
        apply (cancel_epi (prod.map ((Over.map f).map e.hom) (𝟙 (Over.mk f)))).mp
        apply (cancel_mono (prod.map (𝟙 (Over.mk f)) ((Over.map f).map e.hom))).mp
        simpa [Category.assoc, prod.map_map, Functor.map_comp] using comm.symm }
  hom_inv_id := AlgebraicGeometry.DescentData.hom_ext fun _ => e.hom_inv_id
  inv_hom_id := AlgebraicGeometry.DescentData.hom_ext fun _ => e.inv_hom_id

/-- The `X`-scheme of the attached descent datum is `V`. -/
def ofDescentDatumOver : descentObj (ofDescentDatumDatum W) ≅ W.over :=
  Over.isoMk (Iso.refl W.over.left)
    ((Category.id_comp _).trans (ofDescentDatumDatum_descentObj_hom W).symm)

/-- **The descent datum relative to `f` attached to the descent datum on `(X/S)_•` built from
`(V, φ)` is `(V, φ)` again.** -/
def ofDescentDatumIso : toDescentDatum (ofDescentDatumDatum W) ≅ W := by
  refine descentIsoMk (ofDescentDatumOver W) ?_
  refine (AlgebraicGeometry.DescentDatum.hom_comm_iff (toDescentDatum (ofDescentDatumDatum W)) W
    (ofDescentDatumOver W).hom).mpr ?_
  intro R vv xx
  refine Over.OverMorphism.ext ?_
  have hdo : (descentObj (ofDescentDatumDatum W)).hom = W.over.hom :=
    ofDescentDatumDatum_descentObj_hom W
  have hvBase : vv.left ≫ (descentObj (ofDescentDatumDatum W)).hom ≫ f = R.hom := Over.w vv
  have hvW : vv.left ≫ W.over.hom ≫ f = R.hom :=
    (congrArg (fun kk => vv.left ≫ kk ≫ f) hdo).symm.trans hvBase
  have hv1 : vv.left ≫ W.over.hom ≫ f =
      (vv.left ≫ (descentObj (ofDescentDatumDatum W)).hom) ≫ f :=
    (congrArg (fun kk => vv.left ≫ kk ≫ f) hdo).symm.trans (Category.assoc _ _ _).symm
  have hx1 : xx.left ≫ f = (vv.left ≫ (descentObj (ofDescentDatumDatum W)).hom) ≫ f :=
    (lift_cond (ofDescentDatumDatum W) vv xx).symm
  have hs1 : (vv.left ≫ (descentObj (ofDescentDatumDatum W)).hom) ≫ f = R.hom :=
    (Category.assoc _ _ _).trans hvBase
  have hL : ((toDescentDatum (ofDescentDatumDatum W)).act vv xx ≫
        (Over.map f).map (ofDescentDatumOver W).hom).left =
      pointAct W ((vv.left ≫ (descentObj (ofDescentDatumDatum W)).hom) ≫ f) vv.left xx.left
        hv1 hx1 :=
    (congrArg (· ≫ (ofDescentDatumOver W).hom.left)
        (toDescentDatum_act_left (ofDescentDatumDatum W) vv xx)).trans
      ((Category.comp_id _).trans
        (transport_ofDescentDatumDatum W _ xx.left
          (lift_cond (ofDescentDatumDatum W) vv xx) vv.left rfl hv1 hx1))
  have hR : (W.act (vv ≫ (Over.map f).map (ofDescentDatumOver W).hom) xx).left =
      pointAct W R.hom vv.left xx.left hvW (Over.w xx) :=
    (act_left W _ xx).trans
      (pointAct_congr W _ _ _ R.hom vv.left xx.left _ _ hvW (Over.w xx) rfl
        (Category.comp_id _) rfl)
  exact hL.trans (Eq.trans
    (pointAct_congr W _ _ _ R.hom vv.left xx.left hv1 hx1 hvW (Over.w xx) hs1 rfl rfl) hR.symm)

end EssSurj

/-! ### The equivalence -/

/-- The functor `toDescentDatumFunctor f`, from descent data on `(X/S)_•` to descent data
relative to `f : X ⟶ S`, is an equivalence of categories. -/
instance toDescentDatumFunctor_isEquivalence (f : X ⟶ S) :
    (toDescentDatumFunctor f).IsEquivalence := by
  have : (toDescentDatumFunctor f).Full := (toDescentDatumFunctor_fullyFaithful f).full
  have : (toDescentDatumFunctor f).Faithful := (toDescentDatumFunctor_fullyFaithful f).faithful
  have : (toDescentDatumFunctor f).EssSurj :=
    ⟨fun W => ⟨ofDescentDatumDatum W, ⟨ofDescentDatumIso W⟩⟩⟩
  exact {}

/-- **The construction of Lemma 024B**: a cartesian simplicial scheme `Y` over `(X/S)_•` goes to
the descent datum `(Y_0, φ)` relative to `f : X ⟶ S`, as a functor. -/
def cartesianDescentDatumFunctor (f : X ⟶ S) :
    Stacks.Simplicial.Descent.Cartesian (simplicialScheme f) ⥤
      AlgebraicGeometry.DescentDatum f :=
  cartesianToDescent (simplicialScheme f) ⋙ toDescentDatumFunctor f

/-- On objects the functor is the construction of Lemma 024B. -/
@[simp] lemma cartesianDescentDatumFunctor_obj
    (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    (cartesianDescentDatumFunctor f).obj Y = cartesianDescentDatum Y := rfl

/-- On morphisms the functor is evaluation in degree zero. -/
@[simp] lemma cartesianDescentDatumFunctor_map_hom_left
    {Y Z : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)} (a : Y ⟶ Z) :
    (((cartesianDescentDatumFunctor f).map a).hom ()).left = a.hom.left.app (op ⦋0⦌) := rfl

/-- **The construction of Lemma 024B, from cartesian schemes over `(X/S)_•` to descent data
relative to `X/S`, is an equivalence of categories.** -/
@[stacks 024C]
instance cartesianDescentDatumFunctor_isEquivalence (f : X ⟶ S) :
    (cartesianDescentDatumFunctor f).IsEquivalence := by
  have : (cartesianToDescent (simplicialScheme f)).Full :=
    (cartesianToDescent_fullyFaithful (simplicialScheme f)).full
  have : (cartesianToDescent (simplicialScheme f)).Faithful :=
    (cartesianToDescent_fullyFaithful (simplicialScheme f)).faithful
  have : (cartesianToDescent (simplicialScheme f)).EssSurj :=
    ⟨fun D => ⟨reconstructedCartesian D, ⟨reconstructionDatumIso D⟩⟩⟩
  have : (cartesianToDescent (simplicialScheme f)).IsEquivalence := {}
  exact inferInstanceAs
    ((cartesianToDescent (simplicialScheme f) ⋙ toDescentDatumFunctor f).IsEquivalence)

/-- Cartesian simplicial schemes over `(X/S)_•` are equivalent to descent data relative to
`X/S`, by the construction of Lemma 024B. -/
def cartesianSchemesEquivalenceDescentData (f : X ⟶ S) :
    Stacks.Simplicial.Descent.Cartesian (simplicialScheme f) ≌
      AlgebraicGeometry.DescentDatum f :=
  (cartesianDescentDatumFunctor f).asEquivalence

end SimplicialScheme

end AlgebraicGeometry
