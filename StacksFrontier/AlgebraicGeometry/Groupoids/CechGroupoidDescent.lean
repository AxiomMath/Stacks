module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.GluingAction
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant

/-!
# Descent data as equivariant schemes for the Čech groupoid

Let `f : X ⟶ Y` be a morphism of schemes over a base scheme `S`. A descent datum for `f`
consists of a scheme `V` over `X` together with an isomorphism `V ×_Y X ≅ X ×_Y V` over
`X ×_Y X` satisfying the cocycle condition. Reading that isomorphism as an action of the
arrows of the Čech groupoid of `f` on `V` turns a descent datum into an equivariant scheme for
the Čech groupoid, hence into a groupoid scheme cartesian over it.

## Main definitions

* `AlgebraicGeometry.cechDescentObject` and `AlgebraicGeometry.cechDescentStructure` present
  the scheme of a descent datum and its structure morphism in the category of schemes over the
  base.
* `AlgebraicGeometry.cechDescentAct` and `AlgebraicGeometry.cechDescentActInv` are the gluing
  action and its inverse on generalized points, read in that category.
* `AlgebraicGeometry.cechDescentIso` is the isomorphism between the two base changes of `V`
  along the target and source maps of the Čech groupoid.
* `AlgebraicGeometry.cechDescentEquivariantScheme` is the equivariant scheme of a descent
  datum, and `AlgebraicGeometry.cechDescentCartesianOver` the groupoid scheme cartesian over
  the Čech groupoid that it determines.
* `AlgebraicGeometry.cechDescentEquivariantFunctor` and
  `AlgebraicGeometry.cechDescentCartesianOverFunctor` are those two constructions as functors
  out of the category of descent data.
* `AlgebraicGeometry.cechDescentCartesianOverObjectsIso` identifies the object scheme of that
  cartesian groupoid scheme with `V`, as a scheme over `X`.

## Main results

* `AlgebraicGeometry.DescentData.actInv_act`: the inverse gluing action undoes the gluing
  action.
* `AlgebraicGeometry.cechDescentEquivariantScheme_action`: the action of the equivariant scheme
  of a descent datum is the gluing action of that datum.

## Implementation notes

The gluing isomorphism of a descent datum is a morphism between fibre products of schemes,
while an equivariant scheme for a groupoid scheme over `S` is phrased with pullbacks in the
category of schemes over `S`; the two are compared once, in `cechDescentAct`, through
`AlgebraicGeometry.DescentData.act`.

The module `StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoidDescent` gives
`AlgebraicGeometry.DescentDatum.act` a different meaning from the one used here, so it is not
imported, and `cechDescentCartesianOverObjectsIso` writes out the relevant part of
`AlgebraicGeometry.EquivariantScheme.objIso` instead.

Only the construction from descent data to cartesian groupoid schemes is given; that it is an
equivalence of categories is not proved here.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 0APD](https://stacks.math.columbia.edu/tag/0APD)
* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

namespace DescentData

variable {S X : Scheme.{u}} {a : X ⟶ S} (D : DescentData (fun _ : Unit ↦ a))
  {T T' : Scheme.{u}}

/-- The inverse gluing action commutes with precomposition in the test object. -/
lemma comp_actInv (t : T' ⟶ T) (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a)
    (h' : (t ≫ x) ≫ a = (t ≫ v) ≫ (D.obj ()).hom ≫ a) :
    t ≫ D.actInv x v h = D.actInv (t ≫ x) (t ≫ v) h' := by
  have hl : t ≫ pullback.lift x v h = pullback.lift (t ≫ x) (t ≫ v) h' := by
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
  rw [actInv, actInv, ← Category.assoc, hl]

/-- The inverse gluing action undoes the gluing action: acting from `v` to `x` and then back
again returns `v`. -/
lemma actInv_act (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a)
    (h' : (v ≫ (D.obj ()).hom) ≫ a = D.act v x h ≫ (D.obj ()).hom ≫ a) :
    D.actInv (v ≫ (D.obj ()).hom) (D.act v x h) h' = v := by
  have hlift : pullback.lift (v ≫ (D.obj ()).hom) (D.act v x h) h' =
      pullback.lift v x h ≫ (D.gluingPullbackIso () ()).hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, D.gluingPullbackIso_hom_fst,
        pullback.lift_fst_assoc]
    · rw [pullback.lift_snd, Category.assoc]
      rfl
  rw [actInv, hlift, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

end DescentData

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

/-! ### The scheme of a descent datum, read over the base -/

section Object

variable (D : DescentDatum f.left)

/-- The scheme `V` of a descent datum for `f : X ⟶ Y`, viewed as a scheme over the base
scheme `S`. -/
abbrev cechDescentObject : Over S := Over.mk (D.over.hom ≫ X.hom)

/-- The structure morphism `V ⟶ X` of a descent datum, as a morphism of schemes over the base
scheme `S`. -/
abbrev cechDescentStructure : cechDescentObject f D ⟶ X := Over.homMk D.over.hom

/-- The structure morphism of `V` over the base is its structure morphism over `X`
followed by that of `X`. -/
theorem cechDescentObject_hom :
    (cechDescentObject f D).hom = D.over.hom ≫ X.hom := rfl

/-- The structure morphism of `V` over `X`, on underlying schemes, is that of the descent
datum. -/
theorem cechDescentStructure_left :
    (cechDescentStructure f D).left = D.over.hom := rfl

/-- Two generalized points of `V` and of `X` lying over the same point of `Y`, read on
underlying schemes. -/
theorem cechDescentStructure_comp_left {W : Over S} (v : W ⟶ cechDescentObject f D)
    (x : W ⟶ X) (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f) :
    v.left ≫ D.over.hom ≫ f.left = x.left ≫ f.left := by
  simpa [cechDescentStructure_left] using congrArg Over.Hom.left h

end Object

/-! ### The gluing action, read in the category of schemes over the base -/

section Action

variable (D : DescentDatum f.left) {W W' : Over S}

/-- The gluing action of a descent datum on generalized points, read in the category of
schemes over `S`: a point `v` of `V` and a point `x` of `X` with the same image in `Y` are
carried to the point of `V` over `x` that the gluing isomorphism attaches to `v`. -/
def cechDescentAct (v : W ⟶ cechDescentObject f D) (x : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f) : W ⟶ cechDescentObject f D :=
  Over.homMk (D.act v.left x.left (cechDescentStructure_comp_left f D v x h))
    (by
      have hact : D.act v.left x.left (cechDescentStructure_comp_left f D v x h) ≫
          D.over.hom = x.left :=
        D.act_hom v.left x.left (cechDescentStructure_comp_left f D v x h)
      rw [cechDescentObject_hom, ← Category.assoc, hact]
      exact Over.w x)

/-- The gluing action over the base, on underlying schemes, is the gluing action of the
descent datum. -/
@[simp]
theorem cechDescentAct_left (v : W ⟶ cechDescentObject f D) (x : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f) :
    (cechDescentAct f D v x h).left =
      D.act v.left x.left (cechDescentStructure_comp_left f D v x h) := rfl

/-- The gluing action depends only on the two points it is applied to. -/
theorem cechDescentAct_congr {v v' : W ⟶ cechDescentObject f D} {x x' : W ⟶ X}
    (hv : v = v') (hx : x = x')
    {h : v ≫ cechDescentStructure f D ≫ f = x ≫ f}
    {h' : v' ≫ cechDescentStructure f D ≫ f = x' ≫ f} :
    cechDescentAct f D v x h = cechDescentAct f D v' x' h' := by
  subst hv hx
  rfl

/-- The gluing action lands over the prescribed point of `X`. -/
@[reassoc (attr := simp)]
theorem cechDescentAct_comp_structure (v : W ⟶ cechDescentObject f D) (x : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f) :
    cechDescentAct f D v x h ≫ cechDescentStructure f D = x :=
  Over.OverMorphism.ext (D.act_hom v.left x.left (cechDescentStructure_comp_left f D v x h))

/-- The gluing action commutes with precomposition in the test object. -/
theorem comp_cechDescentAct (t : W' ⟶ W) (v : W ⟶ cechDescentObject f D) (x : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f)
    (h' : (t ≫ v) ≫ cechDescentStructure f D ≫ f = (t ≫ x) ≫ f) :
    t ≫ cechDescentAct f D v x h = cechDescentAct f D (t ≫ v) (t ≫ x) h' :=
  Over.OverMorphism.ext
    (D.comp_act t.left v.left x.left (cechDescentStructure_comp_left f D v x h))

/-- Acting along the structure morphism of the point itself is trivial. -/
theorem cechDescentAct_self (v : W ⟶ cechDescentObject f D)
    (h : v ≫ cechDescentStructure f D ≫ f = (v ≫ cechDescentStructure f D) ≫ f) :
    cechDescentAct f D v (v ≫ cechDescentStructure f D) h = v :=
  Over.OverMorphism.ext (D.act_self v.left)

/-- Acting twice is acting once: the cocycle condition for the gluing action. -/
theorem cechDescentAct_cechDescentAct (v : W ⟶ cechDescentObject f D) (x y : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f) (hxy : x ≫ f = y ≫ f)
    (h' : cechDescentAct f D v x h ≫ cechDescentStructure f D ≫ f = y ≫ f) :
    cechDescentAct f D (cechDescentAct f D v x h) y h' =
      cechDescentAct f D v y (h.trans hxy) := by
  refine Over.OverMorphism.ext ?_
  exact D.act_act v.left x.left y.left (cechDescentStructure_comp_left f D v x h)
    (by simpa using congrArg Over.Hom.left hxy)

/-- The inverse gluing action of a descent datum on generalized points, read in the category
of schemes over `S`. -/
def cechDescentActInv (x : W ⟶ X) (v : W ⟶ cechDescentObject f D)
    (h : x ≫ f = v ≫ cechDescentStructure f D ≫ f) : W ⟶ cechDescentObject f D :=
  Over.homMk (D.actInv x.left v.left (cechDescentStructure_comp_left f D v x h.symm).symm)
    (by
      have hact : D.actInv x.left v.left
          (cechDescentStructure_comp_left f D v x h.symm).symm ≫ D.over.hom = x.left :=
        D.actInv_hom x.left v.left (cechDescentStructure_comp_left f D v x h.symm).symm
      rw [cechDescentObject_hom, ← Category.assoc, hact]
      exact Over.w x)

/-- The inverse gluing action over the base, on underlying schemes, is the inverse gluing
action of the descent datum. -/
@[simp]
theorem cechDescentActInv_left (x : W ⟶ X) (v : W ⟶ cechDescentObject f D)
    (h : x ≫ f = v ≫ cechDescentStructure f D ≫ f) :
    (cechDescentActInv f D x v h).left =
      D.actInv x.left v.left (cechDescentStructure_comp_left f D v x h.symm).symm := rfl

/-- The inverse gluing action depends only on the two points it is applied to. -/
theorem cechDescentActInv_congr {x x' : W ⟶ X} {v v' : W ⟶ cechDescentObject f D}
    (hx : x = x') (hv : v = v')
    {h : x ≫ f = v ≫ cechDescentStructure f D ≫ f}
    {h' : x' ≫ f = v' ≫ cechDescentStructure f D ≫ f} :
    cechDescentActInv f D x v h = cechDescentActInv f D x' v' h' := by
  subst hx hv
  rfl

/-- The inverse gluing action lands over the prescribed point of `X`. -/
@[reassoc (attr := simp)]
theorem cechDescentActInv_comp_structure (x : W ⟶ X) (v : W ⟶ cechDescentObject f D)
    (h : x ≫ f = v ≫ cechDescentStructure f D ≫ f) :
    cechDescentActInv f D x v h ≫ cechDescentStructure f D = x :=
  Over.OverMorphism.ext
    (D.actInv_hom x.left v.left (cechDescentStructure_comp_left f D v x h.symm).symm)

/-- The inverse gluing action commutes with precomposition in the test object. -/
theorem comp_cechDescentActInv (t : W' ⟶ W) (x : W ⟶ X) (v : W ⟶ cechDescentObject f D)
    (h : x ≫ f = v ≫ cechDescentStructure f D ≫ f)
    (h' : (t ≫ x) ≫ f = (t ≫ v) ≫ cechDescentStructure f D ≫ f) :
    t ≫ cechDescentActInv f D x v h = cechDescentActInv f D (t ≫ x) (t ≫ v) h' :=
  Over.OverMorphism.ext
    (D.comp_actInv t.left x.left v.left
      (cechDescentStructure_comp_left f D v x h.symm).symm
      (cechDescentStructure_comp_left f D (t ≫ v) (t ≫ x) h'.symm).symm)

/-- The gluing action undoes the inverse gluing action. -/
theorem cechDescentAct_cechDescentActInv (x : W ⟶ X) (v : W ⟶ cechDescentObject f D)
    (h : x ≫ f = v ≫ cechDescentStructure f D ≫ f)
    (h' : cechDescentActInv f D x v h ≫ cechDescentStructure f D ≫ f =
      (v ≫ cechDescentStructure f D) ≫ f) :
    cechDescentAct f D (cechDescentActInv f D x v h) (v ≫ cechDescentStructure f D) h' = v :=
  Over.OverMorphism.ext
    (D.act_actInv x.left v.left (cechDescentStructure_comp_left f D v x h.symm).symm)

/-- The inverse gluing action undoes the gluing action. -/
theorem cechDescentActInv_cechDescentAct (v : W ⟶ cechDescentObject f D) (x : W ⟶ X)
    (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f)
    (h' : (v ≫ cechDescentStructure f D) ≫ f =
      cechDescentAct f D v x h ≫ cechDescentStructure f D ≫ f) :
    cechDescentActInv f D (v ≫ cechDescentStructure f D) (cechDescentAct f D v x h) h' = v :=
  Over.OverMorphism.ext
    (D.actInv_act v.left x.left (cechDescentStructure_comp_left f D v x h)
      (by
        rw [Category.assoc, cechDescentStructure_comp_left f D v x h, ← Category.assoc,
          D.act_hom]))

end Action

/-! ### The descent isomorphism over the arrow scheme of the Čech groupoid -/

section Iso

variable (D : DescentDatum f.left)

/-- The two projections of the kernel pair of `f` agree after composition with `f`. -/
@[reassoc (attr := simp)]
theorem cechKernelPair_condition :
    (pullback.fst f f : pullback f f ⟶ X) ≫ f = pullback.snd f f ≫ f :=
  pullback.condition

/-- A point of the base change of `V` along the target map lies over the target of its
arrow. -/
@[reassoc (attr := simp)]
theorem cechDescentTarget_condition :
    pullback.fst (cechDescentStructure f D) (pullback.fst f f) ≫ cechDescentStructure f D =
      pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.condition

/-- A point of the base change of `V` along the source map lies over the source of its
arrow. -/
@[reassoc (attr := simp)]
theorem cechDescentSource_condition :
    pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (cechDescentStructure f D) ≫ cechDescentStructure f D :=
  pullback.condition

/-- The action of the arrows of the Čech groupoid of `f` on the scheme of a descent datum:
an arrow together with a point of `V` over its target is carried to a point of `V` over its
source. -/
def cechDescentAction :
    pullback (cechDescentStructure f D) (pullback.fst f f) ⟶ cechDescentObject f D :=
  cechDescentAct f D (pullback.fst (cechDescentStructure f D) (pullback.fst f f))
    (pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫ pullback.snd f f)
    (by simp)

/-- The inverse action of the arrows of the Čech groupoid of `f` on the scheme of a descent
datum. -/
def cechDescentActionInv :
    pullback (pullback.snd f f) (cechDescentStructure f D) ⟶ cechDescentObject f D :=
  cechDescentActInv f D
    (pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫ pullback.fst f f)
    (pullback.snd (pullback.snd f f) (cechDescentStructure f D))
    (by simp)

/-- The action of an arrow on a point of `V` lies over the source of that arrow. -/
@[reassoc (attr := simp)]
theorem cechDescentAction_comp_structure :
    cechDescentAction f D ≫ cechDescentStructure f D =
      pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫ pullback.snd f f :=
  cechDescentAct_comp_structure f D _ _ _

/-- The inverse action of an arrow on a point of `V` lies over the target of that arrow. -/
@[reassoc (attr := simp)]
theorem cechDescentActionInv_comp_structure :
    cechDescentActionInv f D ≫ cechDescentStructure f D =
      pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫ pullback.fst f f :=
  cechDescentActInv_comp_structure f D _ _ _

/-- The gluing action of the Čech groupoid, evaluated at a generalized point of the base change
of `V` along the target map. -/
theorem comp_cechDescentAction {W : Over S}
    (t : W ⟶ pullback (cechDescentStructure f D) (pullback.fst f f))
    (h : (t ≫ pullback.fst (cechDescentStructure f D) (pullback.fst f f)) ≫
        cechDescentStructure f D ≫ f =
      (t ≫ pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫
        pullback.snd f f) ≫ f) :
    t ≫ cechDescentAction f D =
      cechDescentAct f D (t ≫ pullback.fst (cechDescentStructure f D) (pullback.fst f f))
        (t ≫ pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫ pullback.snd f f)
        h :=
  comp_cechDescentAct f D t _ _ _ h

/-- The inverse gluing action of the Čech groupoid, evaluated at a generalized point of the
base change of `V` along the source map. -/
theorem comp_cechDescentActionInv {W : Over S}
    (t : W ⟶ pullback (pullback.snd f f) (cechDescentStructure f D))
    (h : (t ≫ pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫
        pullback.fst f f) ≫ f =
      (t ≫ pullback.snd (pullback.snd f f) (cechDescentStructure f D)) ≫
        cechDescentStructure f D ≫ f) :
    t ≫ cechDescentActionInv f D =
      cechDescentActInv f D
        (t ≫ pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫ pullback.fst f f)
        (t ≫ pullback.snd (pullback.snd f f) (cechDescentStructure f D)) h :=
  comp_cechDescentActInv f D t _ _ _ h

/-- The comparison from the base change of `V` along the target map of the Čech groupoid to its
base change along the source map, given by the gluing action. -/
def cechDescentIsoHom :
    pullback (cechDescentStructure f D) (pullback.fst f f) ⟶
      pullback (pullback.snd f f) (cechDescentStructure f D) :=
  pullback.lift (pullback.snd (cechDescentStructure f D) (pullback.fst f f))
    (cechDescentAction f D) (cechDescentAction_comp_structure f D).symm

/-- The comparison in the other direction, given by the inverse gluing action. -/
def cechDescentIsoInv :
    pullback (pullback.snd f f) (cechDescentStructure f D) ⟶
      pullback (cechDescentStructure f D) (pullback.fst f f) :=
  pullback.lift (cechDescentActionInv f D)
    (pullback.fst (pullback.snd f f) (cechDescentStructure f D))
    (cechDescentActionInv_comp_structure f D)

/-- The comparison preserves the arrow of the Čech groupoid. -/
@[reassoc (attr := simp)]
theorem cechDescentIsoHom_fst :
    cechDescentIsoHom f D ≫ pullback.fst (pullback.snd f f) (cechDescentStructure f D) =
      pullback.snd (cechDescentStructure f D) (pullback.fst f f) :=
  pullback.lift_fst _ _ _

/-- The point-of-`V` component of the comparison is the gluing action. -/
@[reassoc (attr := simp)]
theorem cechDescentIsoHom_snd :
    cechDescentIsoHom f D ≫ pullback.snd (pullback.snd f f) (cechDescentStructure f D) =
      cechDescentAction f D :=
  pullback.lift_snd _ _ _

/-- The point-of-`V` component of the inverse comparison is the inverse gluing action. -/
@[reassoc (attr := simp)]
theorem cechDescentIsoInv_fst :
    cechDescentIsoInv f D ≫ pullback.fst (cechDescentStructure f D) (pullback.fst f f) =
      cechDescentActionInv f D :=
  pullback.lift_fst _ _ _

/-- The inverse comparison preserves the arrow of the Čech groupoid. -/
@[reassoc (attr := simp)]
theorem cechDescentIsoInv_snd :
    cechDescentIsoInv f D ≫ pullback.snd (cechDescentStructure f D) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (cechDescentStructure f D) :=
  pullback.lift_snd _ _ _

/-- The isomorphism between the two base changes of `V` to the arrow scheme of the Čech
groupoid of `f`, given by the gluing isomorphism of a descent datum. -/
def cechDescentIso :
    pullback (cechDescentStructure f D) (pullback.fst f f) ≅
      pullback (pullback.snd f f) (cechDescentStructure f D) where
  hom := cechDescentIsoHom f D
  inv := cechDescentIsoInv f D
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, cechDescentIsoInv_fst, Category.id_comp,
        comp_cechDescentActionInv f D _ (by simp)]
      exact Eq.trans
        (cechDescentActInv_congr f D (by simp) (cechDescentIsoHom_snd f D))
        (cechDescentActInv_cechDescentAct f D
          (pullback.fst (cechDescentStructure f D) (pullback.fst f f))
          (pullback.snd (cechDescentStructure f D) (pullback.fst f f) ≫ pullback.snd f f)
          (by simp) (by simp))
    · rw [Category.assoc, cechDescentIsoInv_snd, cechDescentIsoHom_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, cechDescentIsoHom_fst, cechDescentIsoInv_snd, Category.id_comp]
    · rw [Category.assoc, cechDescentIsoHom_snd, Category.id_comp,
        comp_cechDescentAction f D _ (by simp)]
      exact Eq.trans
        (cechDescentAct_congr f D (cechDescentIsoInv_fst f D) (by simp))
        (cechDescentAct_cechDescentActInv f D
          (pullback.fst (pullback.snd f f) (cechDescentStructure f D) ≫ pullback.fst f f)
          (pullback.snd (pullback.snd f f) (cechDescentStructure f D))
          (by simp) (by simp))

/-- The descent isomorphism of a descent datum is the comparison given by the gluing
action. -/
@[simp]
theorem cechDescentIso_hom : (cechDescentIso f D).hom = cechDescentIsoHom f D := rfl

/-- The inverse of the descent isomorphism is the comparison given by the inverse gluing
action. -/
@[simp]
theorem cechDescentIso_inv : (cechDescentIso f D).inv = cechDescentIsoInv f D := rfl

/-- The gluing action read off a generalized point of the base change of `V` along the target
map of the Čech groupoid. -/
theorem lift_cechDescentIso_hom_snd {T : Over S} (v : T ⟶ cechDescentObject f D)
    (b : T ⟶ pullback f f) (w : v ≫ cechDescentStructure f D = b ≫ pullback.fst f f)
    (h : v ≫ cechDescentStructure f D ≫ f = (b ≫ pullback.snd f f) ≫ f) :
    pullback.lift v b w ≫ (cechDescentIso f D).hom ≫
        pullback.snd (pullback.snd f f) (cechDescentStructure f D) =
      cechDescentAct f D v (b ≫ pullback.snd f f) h := by
  rw [cechDescentIso_hom, cechDescentIsoHom_snd,
    comp_cechDescentAction f D (pullback.lift v b w)
      (by rw [pullback.lift_fst, pullback.lift_snd_assoc]; exact h)]
  exact cechDescentAct_congr f D (pullback.lift_fst _ _ _) (pullback.lift_snd_assoc _ _ _ _)

/-- Two composable arrows of the Čech groupoid lie over the same point of `Y`. -/
theorem cechArrow_comp_condition {T : Over S} (b₁ b₂ : T ⟶ pullback f f)
    (w : b₁ ≫ pullback.snd f f = b₂ ≫ pullback.fst f f) :
    (b₁ ≫ pullback.snd f f) ≫ f = (b₂ ≫ pullback.snd f f) ≫ f := by
  rw [w, Category.assoc, cechKernelPair_condition, ← Category.assoc]

/-- A point of `V` and the target of an arrow over it lie over the same point of `Y`. -/
theorem cechDescentPoint_condition {T : Over S} (v : T ⟶ cechDescentObject f D)
    (b : T ⟶ pullback f f) (w : v ≫ cechDescentStructure f D = b ≫ pullback.fst f f) :
    v ≫ cechDescentStructure f D ≫ f = (b ≫ pullback.snd f f) ≫ f := by
  rw [← Category.assoc, w, Category.assoc, cechKernelPair_condition, ← Category.assoc]

/-- The cocycle condition for the gluing action, read off generalized points of the base
change of `V` along the target map of the Čech groupoid: acting by `b₁` and then by `b₂` is
acting by any arrow `c` with the target of `b₁` and the source of `b₂`. -/
theorem lift_cechDescentIso_cocycle {T : Over S} (v : T ⟶ cechDescentObject f D)
    (b₁ b₂ c : T ⟶ pullback f f)
    (w₁ : v ≫ cechDescentStructure f D = b₁ ≫ pullback.fst f f)
    (w₂ : b₁ ≫ pullback.snd f f = b₂ ≫ pullback.fst f f)
    (hct : c ≫ pullback.fst f f = b₁ ≫ pullback.fst f f)
    (hcs : c ≫ pullback.snd f f = b₂ ≫ pullback.snd f f) :
    pullback.lift
          (pullback.lift v b₁ w₁ ≫ (cechDescentIso f D).hom ≫
            pullback.snd (pullback.snd f f) (cechDescentStructure f D))
          b₂
          (by
            rw [lift_cechDescentIso_hom_snd f D v b₁ w₁
              (cechDescentPoint_condition f D v b₁ w₁), cechDescentAct_comp_structure]
            exact w₂) ≫
        (cechDescentIso f D).hom ≫
          pullback.snd (pullback.snd f f) (cechDescentStructure f D) =
      pullback.lift v c (by rw [hct]; exact w₁) ≫ (cechDescentIso f D).hom ≫
        pullback.snd (pullback.snd f f) (cechDescentStructure f D) := by
  have hA : v ≫ cechDescentStructure f D ≫ f = (b₁ ≫ pullback.snd f f) ≫ f :=
    cechDescentPoint_condition f D v b₁ w₁
  have hB : (b₁ ≫ pullback.snd f f) ≫ f = (b₂ ≫ pullback.snd f f) ≫ f :=
    cechArrow_comp_condition f b₁ b₂ w₂
  have hL := lift_cechDescentIso_hom_snd f D v b₁ w₁ hA
  have hO : (pullback.lift v b₁ w₁ ≫ (cechDescentIso f D).hom ≫
        pullback.snd (pullback.snd f f) (cechDescentStructure f D)) ≫
      cechDescentStructure f D ≫ f = (b₂ ≫ pullback.snd f f) ≫ f := by
    rwa [hL, cechDescentAct_comp_structure_assoc]
  have hM : cechDescentAct f D v (b₁ ≫ pullback.snd f f) hA ≫
      cechDescentStructure f D ≫ f = (b₂ ≫ pullback.snd f f) ≫ f := by
    rwa [cechDescentAct_comp_structure_assoc]
  rw [lift_cechDescentIso_hom_snd f D _ b₂ _ hO,
    lift_cechDescentIso_hom_snd f D v c _ (by rw [hcs]; exact hA.trans hB)]
  refine Eq.trans (cechDescentAct_congr f D (h := hO) (h' := hM) hL rfl) ?_
  refine Eq.trans
    (cechDescentAct_cechDescentAct f D v (b₁ ≫ pullback.snd f f) (b₂ ≫ pullback.snd f f)
      hA hB hM) ?_
  exact cechDescentAct_congr f D rfl hcs.symm

end Iso

/-! ### The equivariant scheme and the cartesian groupoid scheme of a descent datum -/

section Equivariant

variable (D : DescentDatum f.left)

/-- A descent datum for `f : X ⟶ Y`, read as an equivariant scheme for the Čech groupoid of
`f`: the scheme `V` over `X`, together with the gluing isomorphism as the comparison of the two
base changes of `V` to the arrow scheme `X ×_Y X`. -/
def cechDescentEquivariantScheme : EquivariantScheme (cechGroupoid f) where
  obj := Over.mk (cechDescentStructure f D)
  descentIso := cechDescentIso f D
  descentIso_over := cechDescentIsoHom_fst f D
  identity := fun T v =>
    Eq.trans
      (lift_cechDescentIso_hom_snd f D v
        (v ≫ cechDescentStructure f D ≫ pullback.lift (𝟙 X) (𝟙 X) rfl)
        (by simp [pullback.lift_fst]) (by simp [pullback.lift_snd]))
      (Eq.trans (cechDescentAct_congr f D rfl (by simp [pullback.lift_snd]))
        (cechDescentAct_self f D v (Category.assoc _ _ _).symm))
  cocycle := fun T v b₁ b₂ wvb wbb =>
    lift_cechDescentIso_cocycle f D v b₁ b₂ ((cechGroupoid f).compose b₁ b₂ wbb) wvb wbb
      (groupoidCompose_target (cechGroupoid f) b₁ b₂ wbb)
      (groupoidCompose_source (cechGroupoid f) b₁ b₂ wbb)

/-- The equivariant scheme of a descent datum has `V` for its scheme over `X`. -/
@[simp]
theorem cechDescentEquivariantScheme_obj :
    (cechDescentEquivariantScheme f D).obj = Over.mk (cechDescentStructure f D) := rfl

/-- The descent isomorphism of the equivariant scheme of a descent datum is the one built
from the gluing isomorphism. -/
@[simp]
theorem cechDescentEquivariantScheme_descentIso :
    (cechDescentEquivariantScheme f D).descentIso = cechDescentIso f D := rfl

/-- The action of the equivariant scheme of a descent datum is the gluing action of that
datum. -/
theorem cechDescentEquivariantScheme_action {T : Over S} (v : T ⟶ cechDescentObject f D)
    (b : T ⟶ pullback f f) (w : v ≫ cechDescentStructure f D = b ≫ pullback.fst f f)
    (h : v ≫ cechDescentStructure f D ≫ f = (b ≫ pullback.snd f f) ≫ f) :
    (cechDescentEquivariantScheme f D).action v b w =
      cechDescentAct f D v (b ≫ pullback.snd f f) h :=
  lift_cechDescentIso_hom_snd f D v b w h

/-- The groupoid scheme cartesian over the Čech groupoid of `f` attached to a descent datum
for `f`. -/
def cechDescentCartesianOver : CartesianOver (cechGroupoid f) :=
  (cartesianOverEquivalenceEquivariantScheme (cechGroupoid f)).inverse.obj
    (cechDescentEquivariantScheme f D)

/-- **The object scheme of the cartesian groupoid scheme of a descent datum is `V`.** The
isomorphism is one of schemes over the object scheme `X` of the Čech groupoid, so it also
identifies the two structure morphisms to `X`. -/
def cechDescentCartesianOverObjectsIso :
    Over.mk (cechDescentCartesianOver f D).hom.mapObjects ≅
      Over.mk (cechDescentStructure f D) :=
  let e := (cartesianOverEquivalenceEquivariantScheme (cechGroupoid f)).counitIso.app
    (cechDescentEquivariantScheme f D)
  eqToIso (cartesianOverEquivalenceEquivariantScheme_obj_eq (cechGroupoid f)
      (cechDescentCartesianOver f D)).symm ≪≫
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg (fun k : EquivariantScheme.Hom _ _ ↦ k.hom) e.hom_inv_id
      inv_hom_id := congrArg (fun k : EquivariantScheme.Hom _ _ ↦ k.hom) e.inv_hom_id }

end Equivariant

/-! ### Functoriality -/

section Functor

variable {D E : DescentDatum f.left}

/-- The morphism of schemes over `S` underlying a morphism of descent data. -/
def cechDescentMap (g : D ⟶ E) : cechDescentObject f D ⟶ cechDescentObject f E :=
  Over.homMk (g.hom ()).left
    (by
      rw [cechDescentObject_hom, cechDescentObject_hom, ← Category.assoc]
      exact congrArg (· ≫ X.hom) (Over.w (g.hom ())))

/-- The morphism over the base induced by a morphism of descent data, on underlying
schemes. -/
@[simp]
theorem cechDescentMap_left (g : D ⟶ E) : (cechDescentMap f g).left = (g.hom ()).left := rfl

/-- A morphism of descent data lies over `X`. -/
@[reassoc (attr := simp)]
theorem cechDescentMap_comp_structure (g : D ⟶ E) :
    cechDescentMap f g ≫ cechDescentStructure f E = cechDescentStructure f D :=
  Over.OverMorphism.ext (Over.w (g.hom ()))

/-- A morphism of descent data commutes with the gluing action. -/
theorem cechDescentAct_naturality (g : D ⟶ E) {W : Over S} (v : W ⟶ cechDescentObject f D)
    (x : W ⟶ X) (h : v ≫ cechDescentStructure f D ≫ f = x ≫ f)
    (h' : (v ≫ cechDescentMap f g) ≫ cechDescentStructure f E ≫ f = x ≫ f) :
    cechDescentAct f D v x h ≫ cechDescentMap f g =
      cechDescentAct f E (v ≫ cechDescentMap f g) x h' :=
  Over.OverMorphism.ext
    (D.act_naturality g v.left x.left (cechDescentStructure_comp_left f D v x h))

/-- A morphism of descent data commutes with the gluing action, read off generalized points of
the base change of `V` along the target map of the Čech groupoid. -/
theorem lift_cechDescentIso_hom_snd_comp_map (g : D ⟶ E) {T : Over S}
    (v : T ⟶ cechDescentObject f D) (b : T ⟶ pullback f f)
    (w : v ≫ cechDescentStructure f D = b ≫ pullback.fst f f) :
    (pullback.lift v b w ≫ (cechDescentIso f D).hom ≫
          pullback.snd (pullback.snd f f) (cechDescentStructure f D)) ≫ cechDescentMap f g =
      pullback.lift (v ≫ cechDescentMap f g) b
          (by rw [Category.assoc, cechDescentMap_comp_structure]; exact w) ≫
        (cechDescentIso f E).hom ≫
          pullback.snd (pullback.snd f f) (cechDescentStructure f E) := by
  have hA : v ≫ cechDescentStructure f D ≫ f = (b ≫ pullback.snd f f) ≫ f :=
    cechDescentPoint_condition f D v b w
  have hA' : (v ≫ cechDescentMap f g) ≫ cechDescentStructure f E ≫ f =
      (b ≫ pullback.snd f f) ≫ f :=
    cechDescentPoint_condition f E _ b (by rw [Category.assoc, cechDescentMap_comp_structure, w])
  rw [lift_cechDescentIso_hom_snd f D v b w hA,
    lift_cechDescentIso_hom_snd f E (v ≫ cechDescentMap f g) b _ hA']
  exact cechDescentAct_naturality f g v (b ≫ pullback.snd f f) hA hA'

/-- The equivariant morphism induced by a morphism of descent data. -/
def cechDescentEquivariantMap (g : D ⟶ E) :
    cechDescentEquivariantScheme f D ⟶ cechDescentEquivariantScheme f E where
  hom := Over.homMk (cechDescentMap f g) (cechDescentMap_comp_structure f g)
  comm := fun _ v b w => lift_cechDescentIso_hom_snd_comp_map f g v b w

/-- A descent datum for `f`, as an equivariant scheme for the Čech groupoid of `f`,
functorially in the descent datum. -/
def cechDescentEquivariantFunctor :
    DescentDatum f.left ⥤ EquivariantScheme (cechGroupoid f) where
  obj D := cechDescentEquivariantScheme f D
  map g := cechDescentEquivariantMap f g
  map_id _ :=
    EquivariantScheme.hom_ext _ _ (Over.OverMorphism.ext (Over.OverMorphism.ext rfl))
  map_comp _ _ :=
    EquivariantScheme.hom_ext _ _ (Over.OverMorphism.ext (Over.OverMorphism.ext rfl))

/-- A descent datum for `f`, as a groupoid scheme cartesian over the Čech groupoid of `f`,
functorially in the descent datum. -/
def cechDescentCartesianOverFunctor :
    DescentDatum f.left ⥤ CartesianOver (cechGroupoid f) :=
  cechDescentEquivariantFunctor f ⋙
    (cartesianOverEquivalenceEquivariantScheme (cechGroupoid f)).inverse

end Functor

end AlgebraicGeometry

end

end
