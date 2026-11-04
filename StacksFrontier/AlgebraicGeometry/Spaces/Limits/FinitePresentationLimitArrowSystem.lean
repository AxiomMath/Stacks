module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.Directed

/-!
# Base changing an inverse system of arrows to the base of its limit

Let `D` be an inverse system of arrows of a category `C` indexed by the opposite of a directed
preorder, let `c` be a limiting cone for it, and let `f : X ⟶ B` be an arrow isomorphic to the
vertex of `c`. Each projection of `c` has a right component `B ⟶ (D i).right`, and base changing
the stage `(D i).hom` along it gives an object `(D i).left ×_{(D i).right} B`. These objects form
an inverse system over the same index, and `X` is its limit.

This is the step of Stacks 09NS which the source records as "limits commute with limits": having
written a morphism `X ⟶ Y` as a limit of morphisms `X_i ⟶ Y_i`, base changing every stage back to
`Y` presents `X` as a limit of spaces over `Y`. Nothing of algebraic geometry enters, so
everything here is stated for an arbitrary category with pullbacks.

## Main definitions

* `CategoryTheory.Limits.arrowBaseMap`: the map `B ⟶ (D i).right` carried by a projection.
* `CategoryTheory.Limits.arrowPullbackSystem`: the inverse system of base changes.
* `CategoryTheory.Limits.arrowPullbackCone`: the cone on that system with vertex `X`.

## Main results

* `CategoryTheory.Limits.isLimit_arrowPullbackCone`: that cone is limiting.

## Implementation notes

The two projections out of a stage of the system are given names,
`CategoryTheory.Limits.arrowPullbackSystemFst` and
`CategoryTheory.Limits.arrowPullbackSystemSnd`, with the stage written as a value of the system
rather than as a pullback. They are the same morphisms, but the two spellings of their source are
only definitionally equal, and rewriting in a composite whose source is spelled the other way
fails.

The index preorder is directed and nonempty only for the limiting statement, where a cone on the
base-changed system has to be turned into a cone on `D` itself: its vertex maps to `B` through any
one stage, and directedness is what makes the resulting map independent of the stage
(`CategoryTheory.Limits.arrowPullbackCone_snd_eq`).

Uniqueness of the lift compares the right components of two morphisms into the limit, which is
done by promoting them to morphisms of arrows out of `initial.to B`; this is the only use of an
initial object, and it is only a device for building an arrow whose left component is forced.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section BaseMap

variable {I : Type v} [Category I] {X B : C} {D : I ⥤ Arrow C}

/-- The map from the base of the limit arrow to the right-hand object of a stage, read off the
right component of the projection of the limiting cone. -/
def arrowBaseMap (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) (i : I) :
    B ⟶ (D.obj i).right := (e.inv ≫ c.π.app i).right

/-- `CategoryTheory.Limits.arrowBaseMap` is the right component of `e.inv` followed by the right
component of the projection. -/
theorem arrowBaseMap_eq (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) (i : I) :
    arrowBaseMap f c e i = e.inv.right ≫ (c.π.app i).right := Arrow.comp_right _ _

/-- The maps `CategoryTheory.Limits.arrowBaseMap` form a cone on the right-hand objects of the
system. -/
theorem arrowBaseMap_comp_right (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) {i j : I}
    (a : i ⟶ j) : arrowBaseMap f c e i ≫ (D.map a).right = arrowBaseMap f c e j := by
  have hw : (c.π.app i).right ≫ (D.map a).right = (c.π.app j).right := by
    simpa only [Arrow.comp_right] using congrArg Arrow.Hom.right (c.w a)
  rw [arrowBaseMap_eq, arrowBaseMap_eq, Category.assoc, hw]

end BaseMap

section System

variable [HasPullbacks C] {I : Type v} [Category I] {X B : C} {D : I ⥤ Arrow C}

/-- The transition morphism of the base-changed system attached to a transition morphism of the
system of arrows. -/
def arrowPullbackMap (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j) {i j : I} (a : i ⟶ j) :
    pullback (D.obj i).hom (q i) ⟶ pullback (D.obj j).hom (q j) :=
  pullback.map (D.obj i).hom (q i) (D.obj j).hom (q j) (D.map a).left (𝟙 _) (D.map a).right
    (by simp) (by simpa using hq a)

/-- The transition morphism `CategoryTheory.Limits.arrowPullbackMap` followed by the first
projection is the first projection followed by the left component of the transition morphism of
`D`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackMap_fst (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j) {i j : I} (a : i ⟶ j) :
    arrowPullbackMap q hq a ≫ pullback.fst (D.obj j).hom (q j) =
      pullback.fst (D.obj i).hom (q i) ≫ (D.map a).left := by
  simp only [arrowPullbackMap, pullback.map, pullback.lift_fst]

/-- The transition morphism `CategoryTheory.Limits.arrowPullbackMap` commutes with the second
projections to `B`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackMap_snd (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j) {i j : I} (a : i ⟶ j) :
    arrowPullbackMap q hq a ≫ pullback.snd (D.obj j).hom (q j) =
      pullback.snd (D.obj i).hom (q i) := by
  simp only [arrowPullbackMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The inverse system of base changes of the stages of `D` to the base `B` of the limit arrow. -/
def arrowPullbackSystem (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) : I ⥤ C where
  obj i := pullback (D.obj i).hom (arrowBaseMap f c e i)
  map {_ _} a := arrowPullbackMap (arrowBaseMap f c e) (arrowBaseMap_comp_right f c e) a
  map_id i := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [arrowPullbackMap_fst, arrowPullbackMap_snd, Category.id_comp,
        CategoryTheory.Functor.map_id, Arrow.id_left, Category.comp_id]
  map_comp {i j k} a b := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [arrowPullbackMap_fst, arrowPullbackMap_snd, arrowPullbackMap_fst_assoc,
        Category.assoc, Functor.map_comp, Arrow.comp_left]

variable (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f)

/-- The left component of the inverse of the identification of the limit arrow with `f`. -/
def arrowLimitIn : X ⟶ c.pt.left := e.inv.left

/-- The left component of the identification of the limit arrow with `f`. -/
def arrowLimitOut : c.pt.left ⟶ X := e.hom.left

omit [HasPullbacks C] in
/-- `CategoryTheory.Limits.arrowLimitIn` followed by `CategoryTheory.Limits.arrowLimitOut` is the
identity of `X`. -/
theorem arrowLimitIn_comp_out : arrowLimitIn f c e ≫ arrowLimitOut f c e = 𝟙 X := by
  exact (Arrow.leftFunc.mapIso e).inv_hom_id

omit [HasPullbacks C] in
/-- `CategoryTheory.Limits.arrowLimitOut` followed by `CategoryTheory.Limits.arrowLimitIn` is the
identity of the source of the limit arrow. -/
theorem arrowLimitOut_comp_in : arrowLimitOut f c e ≫ arrowLimitIn f c e = 𝟙 c.pt.left := by
  exact (Arrow.leftFunc.mapIso e).hom_inv_id

omit [HasPullbacks C] in
/-- `CategoryTheory.Limits.arrowLimitIn` followed by the limit arrow is `f` followed by the right
component of `e.inv`. -/
theorem arrowLimitIn_comp_pt_hom :
    arrowLimitIn f c e ≫ c.pt.hom = f ≫ (e.inv.right : B ⟶ c.pt.right) := Arrow.w e.inv

/-- The first projection out of a stage of the base-changed system. -/
def arrowPullbackSystemFst (i : I) :
    (arrowPullbackSystem f c e).obj i ⟶ (D.obj i).left :=
  pullback.fst (D.obj i).hom (arrowBaseMap f c e i)

/-- The second projection out of a stage of the base-changed system, which is its structure
morphism to the base. -/
def arrowPullbackSystemSnd (i : I) : (arrowPullbackSystem f c e).obj i ⟶ B :=
  pullback.snd (D.obj i).hom (arrowBaseMap f c e i)

/-- The square of a stage of the base-changed system commutes. -/
theorem arrowPullbackSystem_condition (i : I) :
    arrowPullbackSystemFst f c e i ≫ (D.obj i).hom =
      arrowPullbackSystemSnd f c e i ≫ arrowBaseMap f c e i :=
  pullback.condition

/-- Two morphisms into a stage of the base-changed system are equal if they agree after both
projections. -/
theorem arrowPullbackSystem_hom_ext {W : C} {i : I}
    {k l : W ⟶ (arrowPullbackSystem f c e).obj i}
    (h₀ : k ≫ arrowPullbackSystemFst f c e i = l ≫ arrowPullbackSystemFst f c e i)
    (h₁ : k ≫ arrowPullbackSystemSnd f c e i = l ≫ arrowPullbackSystemSnd f c e i) : k = l :=
  pullback.hom_ext h₀ h₁

/-- A transition morphism of the base-changed system followed by the first projection is the first
projection followed by the left component of the transition morphism of `D`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackSystem_map_fst {i j : I} (a : i ⟶ j) :
    (arrowPullbackSystem f c e).map a ≫ arrowPullbackSystemFst f c e j =
      arrowPullbackSystemFst f c e i ≫ (D.map a).left :=
  arrowPullbackMap_fst (arrowBaseMap f c e) (arrowBaseMap_comp_right f c e) a

/-- The transition morphisms of the base-changed system commute with the second projections to
`B`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackSystem_map_snd {i j : I} (a : i ⟶ j) :
    (arrowPullbackSystem f c e).map a ≫ arrowPullbackSystemSnd f c e j =
      arrowPullbackSystemSnd f c e i :=
  arrowPullbackMap_snd (arrowBaseMap f c e) (arrowBaseMap_comp_right f c e) a

/-- The projection from `X` to a stage of the base-changed system: on the left it is the left
component of the projection of the limiting cone, on the right it is `f`. -/
def arrowPullbackProj (i : I) : X ⟶ (arrowPullbackSystem f c e).obj i :=
  pullback.lift (arrowLimitIn f c e ≫ (c.π.app i).left) f (by
    have h₁ : (c.π.app i).left ≫ (D.obj i).hom =
        (c.pt.hom : c.pt.left ⟶ c.pt.right) ≫ (c.π.app i).right := Arrow.w (c.π.app i)
    change (arrowLimitIn f c e ≫ (c.π.app i).left) ≫ (D.obj i).hom = f ≫ arrowBaseMap f c e i
    rw [arrowBaseMap_eq, Category.assoc, h₁, ← Category.assoc, arrowLimitIn_comp_pt_hom,
      Category.assoc])

/-- The first projection of `CategoryTheory.Limits.arrowPullbackProj` is
`CategoryTheory.Limits.arrowLimitIn` followed by the left component of the projection of `c`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackProj_fst (i : I) :
    arrowPullbackProj f c e i ≫ arrowPullbackSystemFst f c e i =
      arrowLimitIn f c e ≫ (c.π.app i).left :=
  pullback.lift_fst _ _ _

/-- The second projection of `CategoryTheory.Limits.arrowPullbackProj` is `f`. -/
@[reassoc (attr := simp)]
theorem arrowPullbackProj_snd (i : I) :
    arrowPullbackProj f c e i ≫ arrowPullbackSystemSnd f c e i = f :=
  pullback.lift_snd _ _ _

/-- The cone on the base-changed system with vertex `X`. -/
def arrowPullbackCone : Cone (arrowPullbackSystem f c e) where
  pt := X
  π :=
    { app := arrowPullbackProj f c e
      naturality := by
        intro i j a
        have hw : (c.π.app i).left ≫ (D.map a).left = (c.π.app j).left := by
          simpa only [Arrow.comp_left] using congrArg Arrow.Hom.left (c.w a)
        refine arrowPullbackSystem_hom_ext f c e ?_ ?_
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, arrowPullbackProj_fst, arrowPullbackSystem_map_fst,
            arrowPullbackProj_fst_assoc, hw]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, arrowPullbackProj_snd, arrowPullbackSystem_map_snd] }

/-- The vertex of `CategoryTheory.Limits.arrowPullbackCone` is `X`. -/
theorem arrowPullbackCone_pt : (arrowPullbackCone f c e).pt = X := rfl

/-- The projections of `CategoryTheory.Limits.arrowPullbackCone` are the morphisms
`CategoryTheory.Limits.arrowPullbackProj`. -/
theorem arrowPullbackCone_π (i : I) :
    (arrowPullbackCone f c e).π.app i = arrowPullbackProj f c e i := rfl

end System

section IsLimit

variable [HasPullbacks C] {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  {X B : C} {D : Jᵒᵖ ⥤ Arrow C} (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f)

omit [Nonempty J] in
/-- The second projection of a cone on the base-changed system does not depend on the stage: any
two stages are refined by a third, and the transition morphisms commute with the second
projections. -/
theorem arrowPullbackCone_snd_eq (s : Cone (arrowPullbackSystem f c e)) (i j : Jᵒᵖ) :
    s.π.app i ≫ arrowPullbackSystemSnd f c e i = s.π.app j ≫ arrowPullbackSystemSnd f c e j := by
  obtain ⟨k, hki, hkj⟩ := exists_ge_ge i.unop j.unop
  have key (l : Jᵒᵖ) (a : (Opposite.op k) ⟶ l) :
      s.π.app (Opposite.op k) ≫ arrowPullbackSystemSnd f c e (Opposite.op k) =
        s.π.app l ≫ arrowPullbackSystemSnd f c e l := by
    rw [← s.w a, Category.assoc, arrowPullbackSystem_map_snd]
  rw [← key i (homOfLE hki).op, key j (homOfLE hkj).op]

/-- The map to `B` attached to a cone on the base-changed system: its second projection at any
one stage, which by `CategoryTheory.Limits.arrowPullbackCone_snd_eq` does not depend on the
stage. -/
def arrowPullbackConeBase (s : Cone (arrowPullbackSystem f c e)) : s.pt ⟶ B :=
  s.π.app (Opposite.op (Classical.arbitrary J)) ≫
    arrowPullbackSystemSnd f c e (Opposite.op (Classical.arbitrary J))

/-- `CategoryTheory.Limits.arrowPullbackConeBase` is the second projection of the cone at any
stage. -/
theorem arrowPullbackConeBase_eq (s : Cone (arrowPullbackSystem f c e)) (i : Jᵒᵖ) :
    arrowPullbackConeBase f c e s = s.π.app i ≫ arrowPullbackSystemSnd f c e i :=
  arrowPullbackCone_snd_eq f c e s _ i

/-- The cone on the system of arrows attached to a cone on the base-changed system: on the right
it is the stage-independent map to `B`, on the left it is the first projection. -/
def arrowPullbackArrowCone (s : Cone (arrowPullbackSystem f c e)) : Cone D where
  pt := Arrow.mk (arrowPullbackConeBase f c e s)
  π :=
    { app := fun i => Arrow.homMk
        (s.π.app i ≫ arrowPullbackSystemFst f c e i) (arrowBaseMap f c e i) (by
          change (s.π.app i ≫ arrowPullbackSystemFst f c e i) ≫ (D.obj i).hom =
            arrowPullbackConeBase f c e s ≫ arrowBaseMap f c e i
          rw [Category.assoc, arrowPullbackSystem_condition, ← Category.assoc,
            ← arrowPullbackConeBase_eq f c e s i])
      naturality := by
        intro i j a
        refine Arrow.hom_ext _ _ ?_ ?_
        · simp only [Functor.const_obj_obj, Functor.const_obj_map,
            Arrow.comp_left, Arrow.homMk_left, Arrow.mk_left, Category.id_comp]
          rw [Category.assoc, ← arrowPullbackSystem_map_fst f c e a, ← Category.assoc, s.w a]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map,
            Arrow.comp_right, Arrow.homMk_right, Arrow.mk_right, Category.id_comp]
          exact (arrowBaseMap_comp_right f c e a).symm }

/-- The vertex of `CategoryTheory.Limits.arrowPullbackArrowCone` is the arrow
`CategoryTheory.Limits.arrowPullbackConeBase`. -/
theorem arrowPullbackArrowCone_pt_hom (s : Cone (arrowPullbackSystem f c e)) :
    ((arrowPullbackArrowCone f c e s).pt.hom : s.pt ⟶ B) = arrowPullbackConeBase f c e s := rfl

/-- The left component of a projection of `CategoryTheory.Limits.arrowPullbackArrowCone` is the
projection of the cone followed by the first projection. -/
theorem arrowPullbackArrowCone_π_left (s : Cone (arrowPullbackSystem f c e)) (i : Jᵒᵖ) :
    (((arrowPullbackArrowCone f c e s).π.app i).left :
        s.pt ⟶ (D.obj i).left) =
      s.π.app i ≫ arrowPullbackSystemFst f c e i := rfl

/-- The right component of a projection of `CategoryTheory.Limits.arrowPullbackArrowCone` is
`CategoryTheory.Limits.arrowBaseMap`. -/
theorem arrowPullbackArrowCone_π_right (s : Cone (arrowPullbackSystem f c e)) (i : Jᵒᵖ) :
    (((arrowPullbackArrowCone f c e s).π.app i).right : B ⟶ (D.obj i).right) =
      arrowBaseMap f c e i := rfl

variable [HasInitial C] (hc : IsLimit c)

/-- The left component of the lift of a cone on the base-changed system to the limiting cone of
the system of arrows: the morphism `X` is compared with through the identification `e`. -/
def arrowPullbackConeLift (s : Cone (arrowPullbackSystem f c e)) : s.pt ⟶ c.pt.left :=
  (hc.lift (arrowPullbackArrowCone f c e s)).left

omit [HasInitial C] in
/-- `CategoryTheory.Limits.arrowPullbackConeLift` followed by the left component of a projection
of `c` is the projection of the cone followed by the first projection. -/
theorem arrowPullbackConeLift_comp_π (s : Cone (arrowPullbackSystem f c e)) (i : Jᵒᵖ) :
    arrowPullbackConeLift f c e hc s ≫ (c.π.app i).left =
      s.π.app i ≫ arrowPullbackSystemFst f c e i := by
  have hh := congrArg Arrow.Hom.left (hc.fac (arrowPullbackArrowCone f c e s) i)
  rw [Arrow.comp_left] at hh
  exact hh.trans (arrowPullbackArrowCone_π_left f c e s i)

/-- The right component of the lift of `CategoryTheory.Limits.arrowPullbackArrowCone` to `c` is
the right component of `e.inv`. -/
theorem arrowPullbackConeLift_right (s : Cone (arrowPullbackSystem f c e)) :
    ((hc.lift (arrowPullbackArrowCone f c e s)).right : B ⟶ c.pt.right) = e.inv.right := by
  have hz : (Arrow.homMk (initial.to c.pt.left)
          ((hc.lift (arrowPullbackArrowCone f c e s)).right : B ⟶ c.pt.right)
          (initial.hom_ext _ _) : Arrow.mk (initial.to B) ⟶ c.pt) =
      (Arrow.homMk (initial.to c.pt.left) (e.inv.right : B ⟶ c.pt.right)
        (initial.hom_ext _ _) : Arrow.mk (initial.to B) ⟶ c.pt) := by
    refine hc.hom_ext fun j => Arrow.hom_ext _ _ (initial.hom_ext _ _) ?_
    simp only [Arrow.comp_right, Arrow.homMk_right]
    have hh := congrArg Arrow.Hom.right (hc.fac (arrowPullbackArrowCone f c e s) j)
    rw [Arrow.comp_right] at hh
    exact hh.trans
      ((arrowPullbackArrowCone_π_right f c e s j).trans (arrowBaseMap_eq f c e j))
  exact congrArg Arrow.Hom.right hz

/-- `CategoryTheory.Limits.arrowPullbackConeLift` followed by
`CategoryTheory.Limits.arrowLimitOut` and `f` is `CategoryTheory.Limits.arrowPullbackConeBase`. -/
theorem arrowPullbackConeLift_comp_base (s : Cone (arrowPullbackSystem f c e)) :
    arrowPullbackConeLift f c e hc s ≫ arrowLimitOut f c e ≫ f =
      arrowPullbackConeBase f c e s := by
  have hcr : ((hc.lift (arrowPullbackArrowCone f c e s) ≫ e.hom).right : B ⟶ B) =
      ((hc.lift (arrowPullbackArrowCone f c e s)).right : B ⟶ c.pt.right) ≫
        (e.hom.right : c.pt.right ⟶ B) := Arrow.comp_right _ _
  have hinv : ((e.inv.right : B ⟶ c.pt.right) ≫ (e.hom.right : c.pt.right ⟶ B)) = 𝟙 B :=
    (Arrow.rightFunc.mapIso e).inv_hom_id
  have hmright : ((hc.lift (arrowPullbackArrowCone f c e s) ≫ e.hom).right : B ⟶ B) = 𝟙 B := by
    rw [hcr, arrowPullbackConeLift_right f c e hc s]
    exact hinv
  have hw : (arrowPullbackConeLift f c e hc s ≫ arrowLimitOut f c e) ≫ f =
      arrowPullbackConeBase f c e s ≫
        ((hc.lift (arrowPullbackArrowCone f c e s) ≫ e.hom).right : B ⟶ B) :=
    Arrow.w (hc.lift (arrowPullbackArrowCone f c e s) ≫ e.hom)
  rw [hmright, Category.comp_id] at hw
  rw [← Category.assoc]
  exact hw

/-- **Base changing an inverse system of arrows to the base of its limit computes the source of
the limit.** If the arrow `f : X ⟶ B` is the limit of an inverse system `D` of arrows over the
opposite of a nonempty directed preorder, then `X` is the limit of the system of base changes
`(D i).left ×_{(D i).right} B`.

The lift of a cone `s` is obtained by lifting the cone
`CategoryTheory.Limits.arrowPullbackArrowCone` on `D` itself and taking the left component. Its
right component is forced to be `e.inv.right`, because `c` is limiting and the right components
of the two candidate morphisms of arrows out of `initial.to B` agree after every projection. -/
def isLimit_arrowPullbackCone : IsLimit (arrowPullbackCone f c e) where
  lift s := arrowPullbackConeLift f c e hc s ≫ arrowLimitOut f c e
  fac s i := by
    change (arrowPullbackConeLift f c e hc s ≫ arrowLimitOut f c e) ≫
      arrowPullbackProj f c e i = s.π.app i
    refine arrowPullbackSystem_hom_ext f c e ?_ ?_
    · rw [Category.assoc, arrowPullbackProj_fst, Category.assoc,
        ← Category.assoc (arrowLimitOut f c e), arrowLimitOut_comp_in, Category.id_comp]
      exact arrowPullbackConeLift_comp_π f c e hc s i
    · rw [Category.assoc, arrowPullbackProj_snd, Category.assoc,
        arrowPullbackConeLift_comp_base]
      exact arrowPullbackConeBase_eq f c e s i
  uniq s g hg := by
    have hg' (i : Jᵒᵖ) : g ≫ arrowPullbackProj f c e i = s.π.app i := hg i
    have hgfst (i : Jᵒᵖ) : (g ≫ arrowLimitIn f c e) ≫ (c.π.app i).left =
        s.π.app i ≫ arrowPullbackSystemFst f c e i :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => g ≫ z) (arrowPullbackProj_fst f c e i)).symm.trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ arrowPullbackSystemFst f c e i) (hg' i))))
    have hb : g ≫ f = arrowPullbackConeBase f c e s :=
      (congrArg (fun z => g ≫ z)
          (arrowPullbackProj_snd f c e (Opposite.op (Classical.arbitrary J)))).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫
                arrowPullbackSystemSnd f c e (Opposite.op (Classical.arbitrary J)))
              (hg' (Opposite.op (Classical.arbitrary J)))).trans
            (arrowPullbackConeBase_eq f c e s _).symm))
    have hwn : (g ≫ arrowLimitIn f c e) ≫ c.pt.hom =
        arrowPullbackConeBase f c e s ≫ (e.inv.right : B ⟶ c.pt.right) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => g ≫ z) (arrowLimitIn_comp_pt_hom f c e)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ (e.inv.right : B ⟶ c.pt.right)) hb)))
    have hn : (Arrow.homMk (g ≫ arrowLimitIn f c e) (e.inv.right : B ⟶ c.pt.right) hwn :
            Arrow.mk (arrowPullbackConeBase f c e s) ⟶ c.pt) =
          hc.lift (arrowPullbackArrowCone f c e s) := by
      refine hc.hom_ext fun i => Arrow.hom_ext _ _ ?_ ?_
      · simp only [Arrow.comp_left, Arrow.homMk_left]
        exact (hgfst i).trans (arrowPullbackConeLift_comp_π f c e hc s i).symm
      · simp only [Arrow.comp_right, Arrow.homMk_right]
        have hh := congrArg Arrow.Hom.right (hc.fac (arrowPullbackArrowCone f c e s) i)
        rw [Arrow.comp_right] at hh
        exact ((arrowBaseMap_eq f c e i).symm.trans
          ((arrowPullbackArrowCone_π_right f c e s i).symm.trans hh.symm))
    have hleftn : g ≫ arrowLimitIn f c e = arrowPullbackConeLift f c e hc s :=
      congrArg Arrow.Hom.left hn
    have hclean : arrowPullbackConeLift f c e hc s ≫ arrowLimitOut f c e = g :=
      (congrArg (fun z => z ≫ arrowLimitOut f c e) hleftn).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => g ≫ z) (arrowLimitIn_comp_out f c e)).trans (Category.comp_id g)))
    exact hclean.symm

end IsLimit

end CategoryTheory.Limits

end
