module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent

/-!
# The gluing action of the inductive step of Stacks 04DZ, on generalized points

Let `f : X ⟶ Y` be a morphism of schemes, let `w : W ⟶ Y`, `p : U ⟶ X` and `q : V ⟶ W` be
morphisms, and let

```
e : V ×_W (X ×_Y W) ≅ U ×_X (X ×_Y W)
```

be an isomorphism over `X ×_Y W`. That is the data the split of the inductive step of the second
proof of Stacks Project, Tag 04DZ produces, and it is what the descent of that step is built
from.

Read on generalized points, `e` says that a point `v` of `V` together with a point `x` of `X`
lying over the same point of `Y` names a point of `U` over `x`, and conversely. This file
introduces those two operations and the *action* they compose to: the point of `V` obtained from
`v`, an auxiliary point `x` of `X`, and a second point `w₂` of `W` over the same point of `Y`, by
passing to `U` over `x` and coming back over `w₂`.

The action is natural in the test scheme, lies over `w₂`, fixes `v` when `w₂` is the point of `W`
that `v` already lies over, and is unchanged by acting twice. Those are exactly the laws the
gluing isomorphism of the descent datum of the inductive step has to satisfy, and the reason for
working with generalized points rather than with the single universal point is that composing two
actions is otherwise not expressible.

## Main definitions

* `Stacks.Etale.vmPoint` and `Stacks.Etale.umPoint` — the points of `V ×_W (X ×_Y W)` and of
  `U ×_X (X ×_Y W)` named by the data above.
* `Stacks.Etale.uCoord` — the point of `U` named by a point of `V` and an auxiliary point of `X`.
* `Stacks.Etale.vCoord` — the point of `V` named by a point of `U`, the point of `X` it lies over
  and a point of `W` over the same point of `Y`.
* `Stacks.Etale.gluingAct` — the action: `Stacks.Etale.vCoord` applied to
  `Stacks.Etale.uCoord`.

## Main results

* `Stacks.Etale.uCoord_vCoord` and `Stacks.Etale.vCoord_uCoord` — the two operations are mutually
  inverse.
* `Stacks.Etale.gluingAct_comp_proj` — the acted point lies over the acting point of `W`.
* `Stacks.Etale.comp_gluingAct` — naturality in the test scheme.
* `Stacks.Etale.gluingAct_self` — the point of `W` beneath `v` fixes `v`.
* `Stacks.Etale.gluingAct_gluingAct` — acting twice is acting once.

## Implementation notes

No cartesian square is formed and no auxiliary identification of `V ×_Y X` with
`V ×_W (X ×_Y W)` is needed: a point of `V ×_W (X ×_Y W)` is literally a pair consisting of a
point of `V` and a point of `X ×_Y W` agreeing over `W`, and the `W`-coordinate of the second is
forced by the first, so the pair is named by a point of `V` and a point of `X`. Both operations
are therefore `CategoryTheory.Limits.pullback.lift` terms composed with `e`, and everything is
deduced from the uniqueness lemmas `Stacks.Etale.vmPoint_eq` and `Stacks.Etale.umPoint_eq`
together with `e.hom ≫ e.inv = 𝟙`.

`Stacks.Etale.gluingAct_gluingAct` needs nothing beyond `Stacks.Etale.uCoord_vCoord`: the point
of `U` is unchanged by the action, so acting again reads the same point of `U` over the new point
of `W`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y W U V : Scheme.{u}} (f : X ⟶ Y) (w : W ⟶ Y) (p : U ⟶ X) (q : V ⟶ W)
  (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w))
  (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w))

/-! ### The two kinds of point -/

/-- **The point of `V ×_W (X ×_Y W)` named by a point of `V` and a point of `X`** lying over the
same point of `Y`: the `W`-coordinate of the second factor is the one `v` lies over. -/
def vmPoint {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) :
    Z ⟶ pullback q (pullback.snd f w) :=
  pullback.lift v (pullback.lift x (v ≫ q) (by rw [Category.assoc]; exact h.symm))
    (pullback.lift_snd _ _ _).symm

/-- **The point of `U ×_X (X ×_Y W)` named by a point of `U`, the point of `X` it lies over, and
a point of `W`** over the same point of `Y`. -/
def umPoint {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W) (h₂ : x ≫ f = w₂ ≫ w)
    (h : uu ≫ p = x) : Z ⟶ pullback p (pullback.fst f w) :=
  pullback.lift uu (pullback.lift x w₂ h₂) (h.trans (pullback.lift_fst _ _ _).symm)

/-- The first component of `Stacks.Etale.vmPoint` is the given point of `V`. -/
@[simp]
lemma vmPoint_comp_fst {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) :
    vmPoint f w q v x h ≫ pullback.fst q (pullback.snd f w) = v :=
  pullback.lift_fst _ _ _

/-- The `X`-coordinate of the second component of `Stacks.Etale.vmPoint` is the given point of
`X`. -/
@[simp]
lemma vmPoint_comp_snd_fst {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) :
    vmPoint f w q v x h ≫ pullback.snd q (pullback.snd f w) ≫ pullback.fst f w = x := by
  rw [← Category.assoc, vmPoint, pullback.lift_snd, pullback.lift_fst]

/-- The `W`-coordinate of the second component of `Stacks.Etale.vmPoint` is the point of `W`
beneath the given point of `V`. -/
@[simp]
lemma vmPoint_comp_snd_snd {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) :
    vmPoint f w q v x h ≫ pullback.snd q (pullback.snd f w) ≫ pullback.snd f w = v ≫ q := by
  rw [← Category.assoc, vmPoint, pullback.lift_snd, pullback.lift_snd]

/-- The first component of `Stacks.Etale.umPoint` is the given point of `U`. -/
@[simp]
lemma umPoint_comp_fst {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) :
    umPoint f w p uu x w₂ h₂ h ≫ pullback.fst p (pullback.fst f w) = uu :=
  pullback.lift_fst _ _ _

/-- The `X`-coordinate of the second component of `Stacks.Etale.umPoint` is the given point of
`X`. -/
@[simp]
lemma umPoint_comp_snd_fst {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) :
    umPoint f w p uu x w₂ h₂ h ≫ pullback.snd p (pullback.fst f w) ≫ pullback.fst f w = x := by
  rw [← Category.assoc, umPoint, pullback.lift_snd, pullback.lift_fst]

/-- The `W`-coordinate of the second component of `Stacks.Etale.umPoint` is the given point of
`W`. -/
@[simp]
lemma umPoint_comp_snd_snd {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) :
    umPoint f w p uu x w₂ h₂ h ≫ pullback.snd p (pullback.fst f w) ≫ pullback.snd f w = w₂ := by
  rw [← Category.assoc, umPoint, pullback.lift_snd, pullback.lift_snd]

/-- **A point of `V ×_W (X ×_Y W)` is determined by its point of `V` and its point of `X`.** -/
lemma vmPoint_eq {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f)
    (pt : Z ⟶ pullback q (pullback.snd f w))
    (h₁ : pt ≫ pullback.fst q (pullback.snd f w) = v)
    (h₂ : pt ≫ pullback.snd q (pullback.snd f w) ≫ pullback.fst f w = x) :
    pt = vmPoint f w q v x h := by
  refine pullback.hom_ext (h₁.trans (vmPoint_comp_fst f w q v x h).symm) ?_
  refine pullback.hom_ext ?_ ?_
  · rw [← Category.assoc] at h₂
    rw [h₂, Category.assoc, vmPoint_comp_snd_fst]
  · simp only [Category.assoc]
    rw [vmPoint_comp_snd_snd, ← pullback.condition, ← Category.assoc, h₁]

/-- **A point of `U ×_X (X ×_Y W)` is determined by its point of `U` and its point of `W`.** -/
lemma umPoint_eq {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) (pt : Z ⟶ pullback p (pullback.fst f w))
    (hp₁ : pt ≫ pullback.fst p (pullback.fst f w) = uu)
    (hp₂ : pt ≫ pullback.snd p (pullback.fst f w) ≫ pullback.snd f w = w₂) :
    pt = umPoint f w p uu x w₂ h₂ h := by
  refine pullback.hom_ext (hp₁.trans (umPoint_comp_fst f w p uu x w₂ h₂ h).symm) ?_
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [umPoint_comp_snd_fst, ← pullback.condition, ← Category.assoc, hp₁, h]
  · rw [← Category.assoc] at hp₂
    rw [hp₂, Category.assoc, umPoint_comp_snd_snd]

/-- Naming a point of `V ×_W (X ×_Y W)` commutes with change of test scheme. -/
lemma comp_vmPoint {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V) (x : Z ⟶ X)
    (h : v ≫ q ≫ w = x ≫ f) (h' : (k ≫ v) ≫ q ≫ w = (k ≫ x) ≫ f) :
    k ≫ vmPoint f w q v x h = vmPoint f w q (k ≫ v) (k ≫ x) h' :=
  vmPoint_eq f w q _ _ h' _ (by rw [Category.assoc, vmPoint_comp_fst])
    (by rw [Category.assoc, vmPoint_comp_snd_fst])

/-- Naming a point of `U ×_X (X ×_Y W)` commutes with change of test scheme. -/
lemma comp_umPoint {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) (h₂' : (k ≫ x) ≫ f = (k ≫ w₂) ≫ w)
    (h' : (k ≫ uu) ≫ p = k ≫ x) :
    k ≫ umPoint f w p uu x w₂ h₂ h = umPoint f w p (k ≫ uu) (k ≫ x) (k ≫ w₂) h₂' h' :=
  umPoint_eq f w p _ _ _ h₂' h' _ (by rw [Category.assoc, umPoint_comp_fst])
    (by rw [Category.assoc, umPoint_comp_snd_snd])

/-! ### The two coordinate operations and their inverse laws -/

/-- **The point of `U` named by a point of `V` and an auxiliary point of `X`**: the
`U`-coordinate of the image under `e` of `Stacks.Etale.vmPoint`. -/
def uCoord {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) : Z ⟶ U :=
  vmPoint f w q v x h ≫ e.hom ≫ pullback.fst p (pullback.fst f w)

/-- **The point of `V` named by a point of `U`, the point of `X` it lies over, and a point of
`W`**: the `V`-coordinate of the image under the inverse of `e` of `Stacks.Etale.umPoint`. -/
def vCoord {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W) (h₂ : x ≫ f = w₂ ≫ w)
    (h : uu ≫ p = x) : Z ⟶ V :=
  umPoint f w p uu x w₂ h₂ h ≫ e.inv ≫ pullback.fst q (pullback.snd f w)

include he in
/-- The inverse of `e` carries the projection to `X ×_Y W` to the projection to `X ×_Y W`. -/
lemma isoBaseChange_inv_comp_snd :
    e.inv ≫ pullback.snd q (pullback.snd f w) = pullback.snd p (pullback.fst f w) := by
  rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

include he in
/-- **The point of `U` named by `v` and `x` lies over `x`.** -/
lemma uCoord_comp_proj {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f) :
    uCoord f w p q e v x h ≫ p = x := by
  rw [uCoord]
  simp only [Category.assoc]
  rw [pullback.condition, reassoc_of% he, vmPoint_comp_snd_fst]

include he in
/-- **The point of `V` named by `uu`, `x` and `w₂` lies over `w₂`.** -/
lemma vCoord_comp_proj {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) :
    vCoord f w p q e uu x w₂ h₂ h ≫ q = w₂ := by
  rw [vCoord]
  simp only [Category.assoc]
  rw [pullback.condition, reassoc_of% isoBaseChange_inv_comp_snd f w p q e he,
    umPoint_comp_snd_snd]

/-- The point of `U` named by a pair depends on the pair only through its two components. -/
lemma uCoord_congr {Z : Scheme.{u}} {v v' : Z ⟶ V} {x x' : Z ⟶ X} (hv : v = v') (hx : x = x')
    (h : v ≫ q ≫ w = x ≫ f) (h' : v' ≫ q ≫ w = x' ≫ f) :
    uCoord f w p q e v x h = uCoord f w p q e v' x' h' := by
  subst hv; subst hx; rfl

/-- The point of `V` named by a triple depends on the triple only through its three
components. -/
lemma vCoord_congr {Z : Scheme.{u}} {uu uu' : Z ⟶ U} {x x' : Z ⟶ X} {w₂ w₂' : Z ⟶ W}
    (hu : uu = uu') (hx : x = x') (hw : w₂ = w₂') (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x)
    (h₂' : x' ≫ f = w₂' ≫ w) (h' : uu' ≫ p = x') :
    vCoord f w p q e uu x w₂ h₂ h = vCoord f w p q e uu' x' w₂' h₂' h' := by
  subst hu; subst hx; subst hw; rfl

/-- Naming a point of `U` commutes with change of test scheme. -/
lemma comp_uCoord {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V) (x : Z ⟶ X)
    (h : v ≫ q ≫ w = x ≫ f) (h' : (k ≫ v) ≫ q ≫ w = (k ≫ x) ≫ f) :
    k ≫ uCoord f w p q e v x h = uCoord f w p q e (k ≫ v) (k ≫ x) h' := by
  rw [uCoord, uCoord, ← Category.assoc, comp_vmPoint f w q k v x h h']

/-- Naming a point of `V` commutes with change of test scheme. -/
lemma comp_vCoord {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x) (h₂' : (k ≫ x) ≫ f = (k ≫ w₂) ≫ w)
    (h' : (k ≫ uu) ≫ p = k ≫ x) :
    k ≫ vCoord f w p q e uu x w₂ h₂ h = vCoord f w p q e (k ≫ uu) (k ≫ x) (k ≫ w₂) h₂' h' := by
  rw [vCoord, vCoord, ← Category.assoc, comp_umPoint f w p k uu x w₂ h₂ h h₂' h']

include he in
/-- The image under `e` of the point of `V ×_W (X ×_Y W)` named by `v` and `x` is the point of
`U ×_X (X ×_Y W)` named by the point of `U` it determines. -/
lemma vmPoint_comp_hom {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h : v ≫ q ≫ w = x ≫ f)
    (h₂ : x ≫ f = (v ≫ q) ≫ w) :
    vmPoint f w q v x h ≫ e.hom =
      umPoint f w p (uCoord f w p q e v x h) x (v ≫ q) h₂
        (uCoord_comp_proj f w p q e he v x h) :=
  umPoint_eq f w p _ x (v ≫ q) h₂ _ _ (by rw [uCoord, Category.assoc])
    (by rw [Category.assoc, reassoc_of% he, vmPoint_comp_snd_snd])

include he in
/-- The image under the inverse of `e` of the point of `U ×_X (X ×_Y W)` named by `uu`, `x` and
`w₂` is the point of `V ×_W (X ×_Y W)` named by the point of `V` it determines. -/
lemma umPoint_comp_inv {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x)
    (h₁ : vCoord f w p q e uu x w₂ h₂ h ≫ q ≫ w = x ≫ f) :
    umPoint f w p uu x w₂ h₂ h ≫ e.inv = vmPoint f w q (vCoord f w p q e uu x w₂ h₂ h) x h₁ :=
  vmPoint_eq f w q _ x h₁ _ (by rw [vCoord, Category.assoc])
    (by rw [Category.assoc, reassoc_of% isoBaseChange_inv_comp_snd f w p q e he,
      umPoint_comp_snd_fst])

include he in
/-- **Reading the point of `U` back off the point of `V` it names.** -/
lemma uCoord_vCoord {Z : Scheme.{u}} (uu : Z ⟶ U) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₂ : x ≫ f = w₂ ≫ w) (h : uu ≫ p = x)
    (h₁ : vCoord f w p q e uu x w₂ h₂ h ≫ q ≫ w = x ≫ f) :
    uCoord f w p q e (vCoord f w p q e uu x w₂ h₂ h) x h₁ = uu := by
  rw [uCoord, ← umPoint_comp_inv f w p q e he uu x w₂ h₂ h h₁, Category.assoc,
    Iso.inv_hom_id_assoc, umPoint_comp_fst]

include he in
/-- **Reading the point of `V` back off the point of `U` it names.** -/
lemma vCoord_uCoord {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h₁ : v ≫ q ≫ w = x ≫ f)
    (h₂ : x ≫ f = (v ≫ q) ≫ w) (h : uCoord f w p q e v x h₁ ≫ p = x) :
    vCoord f w p q e (uCoord f w p q e v x h₁) x (v ≫ q) h₂ h = v := by
  rw [vCoord, ← vmPoint_comp_hom f w p q e he v x h₁ h₂, Category.assoc, Iso.hom_inv_id_assoc,
    vmPoint_comp_fst]

/-! ### The action -/

/-- **The gluing action of the inductive step of Stacks Project, Tag 04DZ.** The point of `V`
obtained from a point `v` of `V`, an auxiliary point `x` of `X` over the same point of `Y`, and a
second point `w₂` of `W` over that point of `Y`: pass to the point of `U` named by `v` and `x`,
and read it back over `w₂`. -/
def gluingAct {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w) : Z ⟶ V :=
  vCoord f w p q e (uCoord f w p q e v x h₁) x w₂ h₂ (uCoord_comp_proj f w p q e he v x h₁)

/-- **The acted point lies over the acting point of `W`.** -/
lemma gluingAct_comp_proj {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w) :
    gluingAct f w p q e he v x w₂ h₁ h₂ ≫ q = w₂ :=
  vCoord_comp_proj f w p q e he _ x w₂ h₂ _

/-- The acted point lies over the acting point of `Y`, which is the hypothesis a further action
consumes. -/
lemma gluingAct_comp_proj_comp {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w) :
    gluingAct f w p q e he v x w₂ h₁ h₂ ≫ q ≫ w = x ≫ f := by
  rw [← Category.assoc, gluingAct_comp_proj f w p q e he v x w₂ h₁ h₂, h₂]

/-- The action depends on its three points only through their values. -/
lemma gluingAct_congr {Z : Scheme.{u}} {v v' : Z ⟶ V} {x x' : Z ⟶ X} {w₂ w₂' : Z ⟶ W}
    (hv : v = v') (hx : x = x') (hw : w₂ = w₂') (h₁ : v ≫ q ≫ w = x ≫ f)
    (h₂ : x ≫ f = w₂ ≫ w) (h₁' : v' ≫ q ≫ w = x' ≫ f) (h₂' : x' ≫ f = w₂' ≫ w) :
    gluingAct f w p q e he v x w₂ h₁ h₂ = gluingAct f w p q e he v' x' w₂' h₁' h₂' := by
  subst hv; subst hx; subst hw; rfl

/-- **The action commutes with change of test scheme.** -/
lemma comp_gluingAct {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w)
    (h₁' : (k ≫ v) ≫ q ≫ w = (k ≫ x) ≫ f) (h₂' : (k ≫ x) ≫ f = (k ≫ w₂) ≫ w) :
    k ≫ gluingAct f w p q e he v x w₂ h₁ h₂ =
      gluingAct f w p q e he (k ≫ v) (k ≫ x) (k ≫ w₂) h₁' h₂' := by
  rw [gluingAct, gluingAct, comp_vCoord f w p q e k _ x w₂ h₂ _ h₂'
    (by rw [comp_uCoord f w p q e k v x h₁ h₁', uCoord_comp_proj f w p q e he])]
  exact vCoord_congr f w p q e (comp_uCoord f w p q e k v x h₁ h₁') rfl rfl _ _ _ _

/-- **The action does not change the point of `U`.** This is what makes acting twice the same as
acting once. -/
lemma uCoord_gluingAct {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w)
    (h₁' : gluingAct f w p q e he v x w₂ h₁ h₂ ≫ q ≫ w = x ≫ f) :
    uCoord f w p q e (gluingAct f w p q e he v x w₂ h₁ h₂) x h₁' = uCoord f w p q e v x h₁ :=
  uCoord_vCoord f w p q e he _ x w₂ h₂ _ h₁'

/-- **A point of `V` is fixed by the point of `W` it lies over.** -/
lemma gluingAct_self {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (h₁ : v ≫ q ≫ w = x ≫ f)
    (h₂ : x ≫ f = (v ≫ q) ≫ w) : gluingAct f w p q e he v x (v ≫ q) h₁ h₂ = v :=
  vCoord_uCoord f w p q e he v x h₁ h₂ _

/-- **Acting twice is acting once.** This is the cocycle condition of the gluing isomorphism of
the inductive step, read on generalized points. -/
lemma gluingAct_gluingAct {Z : Scheme.{u}} (v : Z ⟶ V) (x : Z ⟶ X) (w₂ w₃ : Z ⟶ W)
    (h₁ : v ≫ q ≫ w = x ≫ f) (h₂ : x ≫ f = w₂ ≫ w) (h₃ : x ≫ f = w₃ ≫ w)
    (h₁' : gluingAct f w p q e he v x w₂ h₁ h₂ ≫ q ≫ w = x ≫ f) :
    gluingAct f w p q e he (gluingAct f w p q e he v x w₂ h₁ h₂) x w₃ h₁' h₃ =
      gluingAct f w p q e he v x w₃ h₁ h₃ :=
  vCoord_congr f w p q e (uCoord_gluingAct f w p q e he v x w₂ h₁ h₂ h₁') rfl rfl _ _ _ _

end Stacks.Etale

end

end
