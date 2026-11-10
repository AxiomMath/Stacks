module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData

/-!
# The gluing action of a descent datum for a single morphism

A descent datum `D` for a single morphism `a : X ⟶ S` consists of a scheme `V` over `X`
together with an isomorphism over `X ×_S X` between the two pullbacks of `V`, subject to the
cocycle condition. Evaluating that isomorphism on the second factor turns it into an *action*:
a point of `V` lying over `x₀ : T ⟶ X` is carried to a point of `V` lying over any other
`x₁ : T ⟶ X` with `x₀ ≫ a = x₁ ≫ a`.

## Main definitions

* `AlgebraicGeometry.DescentData.gluingAction` is the action as a morphism of `S`-schemes
  `V ×_S X ⟶ V`, with `AlgebraicGeometry.DescentData.actOn` its transport to the literal
  fibre product.
* `AlgebraicGeometry.DescentData.act` applies it to a generalised point.

## Main results

* `AlgebraicGeometry.DescentData.act_act` is the cocycle condition in the form the action
  needs: acting twice is acting once.
* `AlgebraicGeometry.DescentData.act_self` says that the action along the structure morphism
  of the point itself is trivial.
* `AlgebraicGeometry.DescentData.act_naturality` says that a morphism of descent data
  commutes with the action.

## Implementation notes

The gluing isomorphism of `AlgebraicGeometry.DescentData` is phrased with binary products in
`Over S`, while the pullback functors on descent data are described by the literal fibre
products of schemes. The two models are compared by `CategoryTheory.Over.prodLeftIsoPullback`,
so the cocycle condition is first restated as an identity between `gluingAction` composed with
`CategoryTheory.Limits.prod.lift`s and then transported along that comparison. Phrasing the
action on generalised points keeps the triple products of the cocycle condition out of every
later argument: `act_act` and `act_self` are all that is needed.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

variable {S X : Scheme.{u}} {a : X ⟶ S} (D : DescentData (fun _ : Unit ↦ a))

/-- The gluing action of a descent datum for a single morphism, as a morphism of `S`-schemes
`V ×_S X ⟶ V`: it is the second component of the gluing isomorphism. -/
abbrev gluingAction :
    (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ (Over.map a).obj (D.obj ()) :=
  (D.gluing () ()).hom.left ≫ prod.snd

/-- The product `V ×_S X` formed in `Over S`, compared with the literal fibre product of
schemes. -/
abbrev sourceProdIso :
    ((Over.map a).obj (D.obj ()) ⨯ Over.mk a).left ≅ pullback ((D.obj ()).hom ≫ a) a :=
  Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)

/-- The comparison `sourceProdIso` followed by the first projection of the fibre product is the
first product projection. -/
@[reassoc]
lemma sourceProdIso_hom_fst :
    D.sourceProdIso.hom ≫ pullback.fst ((D.obj ()).hom ≫ a) a =
      (prod.fst : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ _).left :=
  Over.prodLeftIsoPullback_hom_fst _ _

/-- The comparison `sourceProdIso` followed by the second projection of the fibre product is
the second product projection. -/
@[reassoc]
lemma sourceProdIso_hom_snd :
    D.sourceProdIso.hom ≫ pullback.snd ((D.obj ()).hom ≫ a) a =
      (prod.snd : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ _).left :=
  Over.prodLeftIsoPullback_hom_snd _ _

/-- The gluing action on the literal fibre product `V ×_S X`. -/
def actOn : pullback ((D.obj ()).hom ≫ a) a ⟶ (D.obj ()).left :=
  (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _

/-- Under the comparison `sourceProdIso`, `actOn` is the gluing action `gluingAction`. -/
lemma sourceProdIso_hom_actOn :
    D.sourceProdIso.hom ≫ D.actOn = (D.gluingAction).left := by
  have h := Over.prodLeftIsoPullback_hom_snd (Over.mk a)
    ((Over.map a).obj (D.obj ()))
  change _ ≫ pullback.snd a ((D.obj ()).hom ≫ a) = _ at h
  simp [actOn, gluingPullbackIso, gluingIso, Category.assoc, h]

/-- The point `actOn` attaches to a point of `V ×_S X` lies over its second coordinate. -/
@[reassoc]
lemma actOn_hom : D.actOn ≫ (D.obj ()).hom = pullback.snd ((D.obj ()).hom ≫ a) a := by
  apply (cancel_epi D.sourceProdIso.hom).mp
  rw [← Category.assoc, sourceProdIso_hom_actOn]
  have h : (D.gluingAction).left ≫ (D.obj ()).hom =
      (prod.snd : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ _).left :=
    congrArg Over.Hom.left (D.gluing_hom_snd_structureMap () ())
  rw [h]
  exact (D.sourceProdIso_hom_snd).symm

/-- The gluing isomorphism on fibre products agrees, under the comparisons with the products in
`Over S`, with the gluing isomorphism of the descent datum. -/
lemma sourceProdIso_hom_gluingPullbackIso_hom :
    D.sourceProdIso.hom ≫ (D.gluingPullbackIso () ()).hom =
      (D.gluing () ()).hom.left.left ≫
        (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))).hom := by
  simp [gluingPullbackIso, gluingIso]

/-- The gluing isomorphism on fibre products is compatible with the projections to the first
factor `X`. -/
@[reassoc]
lemma gluingPullbackIso_hom_fst :
    (D.gluingPullbackIso () ()).hom ≫ pullback.fst a ((D.obj ()).hom ≫ a) =
      pullback.fst ((D.obj ()).hom ≫ a) a ≫ (D.obj ()).hom := by
  apply (cancel_epi D.sourceProdIso.hom).mp
  rw [← Category.assoc, sourceProdIso_hom_gluingPullbackIso_hom, Category.assoc]
  have h : (Over.prodLeftIsoPullback (Over.mk a)
        ((Over.map a).obj (D.obj ()))).hom ≫ pullback.fst a ((D.obj ()).hom ≫ a) =
      (prod.fst : Over.mk a ⨯ (Over.map a).obj (D.obj ()) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  rw [h]
  have hg : (D.gluing () ()).hom.left.left ≫
      (prod.fst : Over.mk a ⨯ (Over.map a).obj (D.obj ()) ⟶ _).left =
        (prod.fst : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶ _).left ≫ (D.obj ()).hom :=
    congrArg Over.Hom.left (D.gluing_hom_fst () ())
  rw [hg, ← Category.assoc]
  congr 1
  exact (D.sourceProdIso_hom_fst).symm

/-- The inverse gluing isomorphism on fibre products is compatible with the projections to the
first factor `X`. -/
@[reassoc]
lemma gluingPullbackIso_inv_fst :
    (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a ≫
        (D.obj ()).hom = pullback.fst a ((D.obj ()).hom ≫ a) := by
  rw [← D.gluingPullbackIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The inverse gluing isomorphism on fibre products is compatible with the projections to the
second factor `X`. -/
@[reassoc]
lemma gluingPullbackIso_inv_snd :
    (D.gluingPullbackIso () ()).inv ≫ pullback.snd ((D.obj ()).hom ≫ a) a =
      pullback.snd a ((D.obj ()).hom ≫ a) ≫ (D.obj ()).hom := by
  have h : (D.gluingPullbackIso () ()).hom ≫ pullback.snd a ((D.obj ()).hom ≫ a) ≫
      (D.obj ()).hom = pullback.snd ((D.obj ()).hom ≫ a) a := D.actOn_hom
  rw [← h, Iso.inv_hom_id_assoc]

section ProductCalculus

variable {C : Type*} [Category C] [HasBinaryProducts C]

private lemma lift_prodMapFirstThird_snd {A B W : C} (φ : A ⨯ B ⟶ B ⨯ A)
    (p : W ⟶ A ⨯ B) (q : W ⟶ B) :
    prod.lift p q ≫ prodMapFirstThird φ ≫ prod.snd =
      prod.lift (p ≫ prod.fst) q ≫ φ ≫ prod.snd := by
  simp [prodMapFirstThird, prodMapLastTwo, prod.braiding, prod.comp_lift,
    prod.comp_lift_assoc]

private lemma lift_prodMapLastTwo_snd {A B W : C} (φ : A ⨯ B ⟶ B ⨯ A)
    (p : W ⟶ A ⨯ B) (q : W ⟶ B) :
    prod.lift p q ≫ prod.map φ (𝟙 B) ≫ prodMapLastTwo φ ≫ prod.snd =
      prod.lift (p ≫ φ ≫ prod.snd) q ≫ φ ≫ prod.snd := by
  simp [prodMapLastTwo, prod.comp_lift, prod.comp_lift_assoc]

end ProductCalculus

/-- The cocycle condition, read off on the second factor: acting twice is acting once. -/
lemma lift_gluingAction_gluingAction {W : Over S}
    (p : W ⟶ (Over.map a).obj (D.obj ()) ⨯ Over.mk a) (q : W ⟶ Over.mk a) :
    prod.lift (p ≫ D.gluingAction) q ≫ D.gluingAction =
      prod.lift (p ≫ prod.fst) q ≫ D.gluingAction := by
  have hc := D.cocycle () () ()
  calc prod.lift (p ≫ D.gluingAction) q ≫ D.gluingAction
      = prod.lift p q ≫ prod.map (D.gluing () ()).hom.left (𝟙 (Over.mk a)) ≫
          prodMapLastTwo (D.gluing () ()).hom.left ≫ prod.snd :=
        (lift_prodMapLastTwo_snd _ p q).symm
    _ = prod.lift p q ≫ prodMapFirstThird (D.gluing () ()).hom.left ≫ prod.snd := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ prod.lift p q ≫ k ≫ prod.snd) hc
    _ = prod.lift (p ≫ prod.fst) q ≫ D.gluingAction :=
        lift_prodMapFirstThird_snd _ p q

section Act

variable {T : Scheme.{u}}

/-- The gluing action applied to a generalised point `v` of `V`: the result is the point of
`V` over `x` that the gluing isomorphism attaches to `v`. -/
def act (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) : T ⟶ (D.obj ()).left :=
  pullback.lift v x h ≫ D.actOn

/-- `act` depends only on the point and the target, not on the proof of compatibility. -/
lemma act_congr {v v' : T ⟶ (D.obj ()).left} {x x' : T ⟶ X} (hv : v = v') (hx : x = x')
    {h : v ≫ (D.obj ()).hom ≫ a = x ≫ a} {h' : v' ≫ (D.obj ()).hom ≫ a = x' ≫ a} :
    D.act v x h = D.act v' x' h' := by
  subst hv
  subst hx
  rfl

/-- The point `D.act v x h` lies over `x`. -/
@[reassoc]
lemma act_hom (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) :
    D.act v x h ≫ (D.obj ()).hom = x := by
  rw [act, Category.assoc, D.actOn_hom, pullback.lift_snd]

/-- If `x` and `y` have the same image in `S`, then so do `D.act v x h` and `y`. -/
lemma act_structure (v : T ⟶ (D.obj ()).left) (x y : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) (hxy : x ≫ a = y ≫ a) :
    D.act v x h ≫ (D.obj ()).hom ≫ a = y ≫ a := by
  rw [← Category.assoc, D.act_hom]
  exact hxy

/-- The action commutes with precomposition by a morphism `t : T' ⟶ T`. -/
lemma comp_act {T' : Scheme.{u}} (t : T' ⟶ T) (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) :
    t ≫ D.act v x h =
      D.act (t ≫ v) (t ≫ x) (by simp only [Category.assoc]; rw [h]) := by
  have hl : t ≫ pullback.lift v x h =
      pullback.lift (t ≫ v) (t ≫ x) (by simp only [Category.assoc]; rw [h]) := by
    apply pullback.hom_ext <;> simp
  rw [act, act, ← Category.assoc, hl]

/-- `actOn` evaluated at a generalised point of the fibre product is `act` applied to its two
coordinates. -/
lemma comp_actOn (t : T ⟶ pullback ((D.obj ()).hom ≫ a) a) :
    t ≫ D.actOn = D.act (t ≫ pullback.fst _ _) (t ≫ pullback.snd _ _)
      (by simp only [Category.assoc]; rw [pullback.condition]) := by
  rw [act]
  congr 1
  apply pullback.hom_ext <;> simp

/-- The comparison `sourceProdIso` carries the point `prod.lift v x` of the product in
`Over S` to the point `pullback.lift v.left x.left h` of the fibre product. -/
lemma lift_left_sourceProdIso {W : Over S}
    (v : W ⟶ (Over.map a).obj (D.obj ())) (x : W ⟶ Over.mk a)
    (h : v.left ≫ (D.obj ()).hom ≫ a = x.left ≫ a) :
    (prod.lift v x).left ≫ D.sourceProdIso.hom = pullback.lift v.left x.left h := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.sourceProdIso_hom_fst, pullback.lift_fst]
    exact congrArg Over.Hom.left (prod.lift_fst v x)
  · rw [Category.assoc, D.sourceProdIso_hom_snd, pullback.lift_snd]
    exact congrArg Over.Hom.left (prod.lift_snd v x)

/-- The action in the product model, transported to the pullback model. -/
lemma lift_gluingAction_left {W : Over S}
    (v : W ⟶ (Over.map a).obj (D.obj ())) (x : W ⟶ Over.mk a)
    (h : v.left ≫ (D.obj ()).hom ≫ a = x.left ≫ a) :
    (prod.lift v x ≫ D.gluingAction).left = D.act v.left x.left h := by
  rw [Over.comp_left, act, ← sourceProdIso_hom_actOn, ← Category.assoc,
    D.lift_left_sourceProdIso v x h]

/-- `lift_gluingAction_left`, with the point of `V` given up to equality. -/
private lemma lift_gluingAction_left_of {W : Over S}
    (v : W ⟶ (Over.map a).obj (D.obj ())) (x : W ⟶ Over.mk a) {w : W.left ⟶ (D.obj ()).left}
    (hw : v.left = w) (h : w ≫ (D.obj ()).hom ≫ a = x.left ≫ a) :
    (prod.lift v x ≫ D.gluingAction).left = D.act w x.left h := by
  subst hw
  exact D.lift_gluingAction_left v x h

/-- Acting twice is acting once: the cocycle condition for generalised points. -/
lemma act_act (v : T ⟶ (D.obj ()).left) (x y : T ⟶ X)
    (hv : v ≫ (D.obj ()).hom ≫ a = x ≫ a) (hxy : x ≫ a = y ≫ a) :
    D.act (D.act v x hv) y (D.act_structure v x y hv hxy) = D.act v y (hv.trans hxy) := by
  let W : Over S := Over.mk (x ≫ a)
  let vv : W ⟶ (Over.map a).obj (D.obj ()) := Over.homMk v hv
  let xx : W ⟶ Over.mk a := Over.homMk x rfl
  let yy : W ⟶ Over.mk a := Over.homMk y hxy.symm
  have e1 : (prod.lift vv xx ≫ D.gluingAction).left = D.act v x hv :=
    D.lift_gluingAction_left vv xx hv
  have e2 : (prod.lift vv xx ≫ prod.fst).left = v :=
    congrArg Over.Hom.left (prod.lift_fst vv xx)
  have hL := D.lift_gluingAction_left_of _ yy e1 (D.act_structure v x y hv hxy)
  have hR := D.lift_gluingAction_left_of _ yy e2 (hv.trans hxy)
  exact hL.symm.trans ((congrArg Over.Hom.left
    (D.lift_gluingAction_gluingAction (prod.lift vv xx) yy)).trans hR)

/-- Acting twice is acting once, with the inner action and the target given up to equality, so
that neither has to be put in normal form first. -/
lemma act_act_of {v w : T ⟶ (D.obj ()).left} {x y z : T ⟶ X}
    {hv : v ≫ (D.obj ()).hom ≫ a = x ≫ a} (hw : w = D.act v x hv) (hy : y = z)
    (hxz : x ≫ a = z ≫ a) {hwy : w ≫ (D.obj ()).hom ≫ a = y ≫ a} :
    D.act w y hwy = D.act v z (hv.trans hxz) := by
  subst hw
  subst hy
  exact D.act_act v x _ hv hxz

/-- The inverse gluing action applied to a generalised point. -/
def actInv (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a) : T ⟶ (D.obj ()).left :=
  pullback.lift x v h ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst _ _

/-- The point `D.actInv x v h` lies over `x`. -/
lemma actInv_hom (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a) :
    D.actInv x v h ≫ (D.obj ()).hom = x := by
  rw [actInv, Category.assoc, Category.assoc, D.gluingPullbackIso_inv_fst,
    pullback.lift_fst]

/-- The point `D.actInv x v h` and the image of `v` in `X` have the same image in `S`. -/
lemma actInv_structure (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a) :
    D.actInv x v h ≫ (D.obj ()).hom ≫ a = (v ≫ (D.obj ()).hom) ≫ a := by
  rw [← Category.assoc, D.actInv_hom, Category.assoc]
  exact h

/-- Acting on `D.actInv x v h` along the image of `v` in `X` recovers `v`. -/
lemma act_actInv (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a) :
    D.act (D.actInv x v h) (v ≫ (D.obj ()).hom) (D.actInv_structure x v h) = v := by
  have hlift : pullback.lift (D.actInv x v h) (v ≫ (D.obj ()).hom)
      (D.actInv_structure x v h) =
      pullback.lift x v h ≫ (D.gluingPullbackIso () ()).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, actInv, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, D.gluingPullbackIso_inv_snd,
        pullback.lift_snd_assoc]
  rw [act, hlift, actOn, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- Acting along the structure morphism of the point itself is trivial. -/
lemma act_self (v : T ⟶ (D.obj ()).left) :
    D.act v (v ≫ (D.obj ()).hom) (Category.assoc _ _ _).symm = v := by
  have h : (v ≫ (D.obj ()).hom) ≫ a = v ≫ (D.obj ()).hom ≫ a := Category.assoc _ _ _
  have hinv := D.act_actInv (v ≫ (D.obj ()).hom) v h
  have hcc := D.act_act (D.actInv (v ≫ (D.obj ()).hom) v h) (v ≫ (D.obj ()).hom)
    (v ≫ (D.obj ()).hom) (D.actInv_structure (v ≫ (D.obj ()).hom) v h) rfl
  exact ((D.act_congr hinv rfl).symm.trans hcc).trans hinv

/-- A morphism of descent data `g : D ⟶ E` preserves the compatibility of a point of `V` with a
point of `X` over `S`. -/
lemma map_act_structure {D E : DescentData (fun _ : Unit ↦ a)} (g : D ⟶ E)
    (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) :
    (v ≫ (g.hom ()).left) ≫ (E.obj ()).hom ≫ a = x ≫ a := by
  rw [Category.assoc, Over.w_assoc]
  exact h

/-- A morphism of descent data commutes with the gluing action. -/
lemma act_naturality {D E : DescentData (fun _ : Unit ↦ a)} (g : D ⟶ E)
    (v : T ⟶ (D.obj ()).left) (x : T ⟶ X)
    (h : v ≫ (D.obj ()).hom ≫ a = x ≫ a) :
    D.act v x h ≫ (g.hom ()).left =
      E.act (v ≫ (g.hom ()).left) x (map_act_structure g v x h) := by
  have hcomm : prod.map ((Over.map a).map (g.hom ())) (𝟙 (Over.mk a)) ≫ E.gluingAction =
      D.gluingAction ≫ (Over.map a).map (g.hom ()) := by
    simpa only [Category.assoc, prod.map_snd] using
      congrArg (fun k ↦ k ≫ prod.snd) (g.comm () ())
  let W : Over S := Over.mk (x ≫ a)
  let vv : W ⟶ (Over.map a).obj (D.obj ()) := Over.homMk v h
  let xx : W ⟶ Over.mk a := Over.homMk x rfl
  have hmap : prod.lift vv xx ≫ prod.map ((Over.map a).map (g.hom ())) (𝟙 (Over.mk a)) =
      prod.lift (vv ≫ (Over.map a).map (g.hom ())) xx := by
    simp
  have hmid : prod.lift (vv ≫ (Over.map a).map (g.hom ())) xx ≫ E.gluingAction =
      prod.lift vv xx ≫ D.gluingAction ≫ (Over.map a).map (g.hom ()) := by
    rw [← hmap, Category.assoc, hcomm]
  have hL : (prod.lift (vv ≫ (Over.map a).map (g.hom ())) xx ≫ E.gluingAction).left =
      E.act (v ≫ (g.hom ()).left) x (map_act_structure g v x h) :=
    E.lift_gluingAction_left (vv ≫ (Over.map a).map (g.hom ())) xx
      (map_act_structure g v x h)
  have hR : (prod.lift vv xx ≫ D.gluingAction ≫ (Over.map a).map (g.hom ())).left =
      D.act v x h ≫ (g.hom ()).left := by
    have h1 : (prod.lift vv xx ≫ D.gluingAction).left = D.act v x h :=
      D.lift_gluingAction_left vv xx h
    rw [← Category.assoc, Over.comp_left, h1, Over.map_map_left]
  exact hR.symm.trans ((congrArg Over.Hom.left hmid).symm.trans hL)

end Act

end AlgebraicGeometry.DescentData
