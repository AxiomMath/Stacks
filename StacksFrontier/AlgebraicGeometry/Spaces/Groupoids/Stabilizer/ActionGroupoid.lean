module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.CategoryTheory.Monoidal.ActionGroupoid

/-!
# The groupoid in algebraic spaces of a group action

Let `B` be an algebraic space over `S`, let `G` be a group object in the slice of presheaves
over `B` whose underlying presheaf is an algebraic space, and let `G` act on an algebraic space
`X` over `B`. Then `X` and `G ×_B X` are the objects and the arrows of a groupoid in algebraic
spaces over `B`: the source of `(g, x)` is `x`, its target is `g • x`, and composition is
multiplication in `G`.

## Main definitions

* `AlgebraicGeometry.Space.actionInverse`: the inverse of the action groupoid, as a morphism in
  the slice over `B`. Its composition and unit are the slice readings of
  `Stacks.Groupoids.ActionGroupoid.composition` and
  `Stacks.Groupoids.ActionGroupoid.identity`.
* `AlgebraicGeometry.Space.ActionGroupoidConstruction`: the resulting groupoid in algebraic
  spaces together with the identification of its object and arrow spaces and of all five of
  its structure maps.

## Main results

* `AlgebraicGeometry.Space.groupoidOfAction`: the action groupoid exists.

## Implementation notes

The slice over `B` carries the cartesian monoidal structure whose tensor product is the fibre
product over `B` (`AlgebraicGeometry.Space.overCartesianMonoidalCategory`), so the arrow object
is literally `G ⊗ X` and the group and action laws are available as the monoid-object API.
Source and target are the second projection and the action morphism, and the three structure
maps of the groupoid, together with the groupoid axioms they satisfy, are those of the action
groupoid of a group object in a cartesian monoidal category, read in that slice.

The composition of a groupoid in algebraic spaces is required on the *chosen* fibre product of
the source and the target, taken in presheaves, whereas the construction naturally produces a
morphism out of the fibre product taken in the slice. Those two objects are canonically
isomorphic because the forgetful functor from the slice preserves limits, and
`ActionGroupoidConstruction.compositionDomainIso` records the comparison, pinned down by its
two projection equations. The identifications of the structure maps are heterogeneous
equalities, which is what lets the construction name the chosen objects rather than replace
them by isomorphic ones.

That the evaluated category is a groupoid is checked one test object at a time, where a point
of the arrow presheaf over a point `x` of `X` is a point of `G` over the image of `x` in `B`,
so the arrows out of `x` form a copy of that group; the identity and the inverse of the
evaluated groupoid are then forced to be the values of
`Stacks.Groupoids.ActionGroupoid.identity` and `actionInverse`, which is the content of the last
two fields.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} (B : AlgebraicSpaces C S hS)
  (G X : Over B.obj) [GrpObj G] [ModObj G X]
  (hG : IsAlgebraicSpace C S hS G.left)
  (hX : IsAlgebraicSpace C S hS X.left)

/-- The inverse of `(g,x)` is `(g⁻¹,g • x)`. -/
noncomputable def actionInverse : G ⊗ X ⟶ G ⊗ X :=
  Stacks.Groupoids.ActionGroupoid.inverse G X

/-- Groupoid object data in presheaves over `B` with objects `X` and arrows `G ⊗ X`, the fibre
product `G ×_B X`. -/
abbrev ActionGroupoidData := Stacks.Groupoids.GroupoidObjectData X (G ⊗ X)

/-- The groupoid object data of the action of `G` on `X`: the source is the second projection,
the target is the action, the composition is multiplication in `G`, and the inverse is
`actionInverse`. -/
noncomputable def actionGroupoidData : ActionGroupoidData B G X where
  source := snd G X
  target := γ[G, X]
  comp := Stacks.Groupoids.ActionGroupoid.composition G X
  identity := Stacks.Groupoids.ActionGroupoid.identity G X
  inverse := actionInverse B G X
  source_identity := Stacks.Groupoids.ActionGroupoid.identity_source G X
  target_identity := Stacks.Groupoids.ActionGroupoid.identity_target G X
  source_inverse := Stacks.Groupoids.ActionGroupoid.inverse_source G X
  target_inverse := Stacks.Groupoids.ActionGroupoid.inverse_target G X
  source_comp := Stacks.Groupoids.ActionGroupoid.composition_source G X
  target_comp := Stacks.Groupoids.ActionGroupoid.composition_target G X
  left_identity := Stacks.Groupoids.ActionGroupoid.composition_left_identity G X
  right_identity := Stacks.Groupoids.ActionGroupoid.composition_right_identity G X
  left_inverse := Stacks.Groupoids.ActionGroupoid.composition_left_inverse G X
  right_inverse := Stacks.Groupoids.ActionGroupoid.composition_right_inverse G X
  assoc := Stacks.Groupoids.ActionGroupoid.composition_assoc G X

/-- For `T` over `B`, the groupoid of morphisms `T ⟶ X` over `B`, in which an arrow `x ⟶ y` is a
morphism `T ⟶ G ⊗ X` with source `x` and target `y`. -/
@[instance_reducible]
noncomputable def ActionGroupoidData.evaluationGroupoid
    (H : ActionGroupoidData B G X) (T : Over B.obj) :
    Groupoid.{u + 1, u + 1} (T ⟶ X) where
  Hom x y := { a : T ⟶ G ⊗ X // a ≫ H.source = x ∧ a ≫ H.target = y }
  id x := ⟨x ≫ H.identity, by simp [H.source_identity], by simp [H.target_identity]⟩
  comp f g := ⟨pullback.lift g.1 f.1 (g.2.1.trans f.2.2.symm) ≫ H.comp,
    by simp [H.source_comp, pullback.lift_snd_assoc, f.2.1],
    by simp [H.target_comp, pullback.lift_fst_assoc, g.2.2]⟩
  id_comp f := by
    apply Subtype.ext
    convert H.right_identity T f.1 (by
      calc
        f.1 ≫ H.source = (f.1 ≫ H.source) ≫ 𝟙 X := (Category.comp_id _).symm
        _ = (f.1 ≫ H.source) ≫ (H.identity ≫ H.target) :=
          congrArg ((f.1 ≫ H.source) ≫ ·) H.target_identity.symm
        _ = ((f.1 ≫ H.source) ≫ H.identity) ≫ H.target := (Category.assoc _ _ _).symm)
      using 1; simp only [← Category.assoc, f.2.1]
  comp_id f := by
    apply Subtype.ext
    convert H.left_identity T f.1 (by
      calc
        ((f.1 ≫ H.target) ≫ H.identity) ≫ H.source =
            (f.1 ≫ H.target) ≫ (H.identity ≫ H.source) := Category.assoc _ _ _
        _ = (f.1 ≫ H.target) ≫ 𝟙 X :=
          congrArg ((f.1 ≫ H.target) ≫ ·) H.source_identity
        _ = f.1 ≫ H.target := Category.comp_id _)
      using 1; simp only [← Category.assoc, f.2.2]
  assoc f g h := by
    apply Subtype.ext
    exact (H.assoc T h.1 g.1 f.1
      (h.2.1.trans g.2.2.symm) (g.2.1.trans f.2.2.symm)
      (by simp [H.source_comp, pullback.lift_snd_assoc, g.2.1, f.2.2])
      (by simp [H.target_comp, pullback.lift_fst_assoc, g.2.2, h.2.1])).symm
  inv f := ⟨f.1 ≫ H.inverse, by simp [H.source_inverse, f.2.2],
    by simp [H.target_inverse, f.2.1]⟩
  inv_comp f := by
    apply Subtype.ext
    convert H.right_inverse T f.1 (by simp [H.target_inverse, f.2.1])
      using 1; simp only [← Category.assoc, f.2.2]
  comp_inv f := by
    apply Subtype.ext
    convert H.left_inverse T f.1 (by simp [H.source_inverse, f.2.2])
      using 1; simp only [← Category.assoc, f.2.1]

/-- The presheaf represented by `T`, made an object over `B` by the morphism `b`. -/
noncomputable def ActionGroupoidData.testOver (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj) : Over B.obj := Over.mk b

/-- The image in `B` of a `T`-point `x` of an object `Y` over `B`, as a morphism from the presheaf
represented by `T`. -/
noncomputable def ActionGroupoidData.pointBase {T : BigFppfOver C S hS}
    (Y : Over B.obj) (x : Y.left.obj (Opposite.op T)) : yoneda.obj T ⟶ B.obj :=
  yonedaEquiv.symm x ≫ Y.hom

/-- A `T`-point of `Y` lying over `b`, as a morphism over `B` from `testOver B T b` to `Y`. -/
noncomputable def ActionGroupoidData.pointOver {T : BigFppfOver C S hS}
    (b : yoneda.obj T ⟶ B.obj) {Y : Over B.obj}
    (x : Y.left.obj (Opposite.op T))
    (hx : ActionGroupoidData.pointBase B Y x = b) : ActionGroupoidData.testOver B T b ⟶ Y :=
  Over.homMk (yonedaEquiv.symm x) (by
    change yonedaEquiv.symm x ≫ Y.hom = b
    exact hx)

/-- If a morphism `f` over `B` sends the `T`-point `a` to `x`, then `a` and `x` have the same
image in `B`. -/
theorem ActionGroupoidData.arrow_base_of_map {T : BigFppfOver C S hS}
    {Y Z : Over B.obj} (f : Y ⟶ Z)
    (a : Y.left.obj (Opposite.op T)) (x : Z.left.obj (Opposite.op T))
    (h : f.left.app (Opposite.op T) a = x) :
    ActionGroupoidData.pointBase B Y a = ActionGroupoidData.pointBase B Z x := by
  show yonedaEquiv.symm a ≫ Y.hom = yonedaEquiv.symm x ≫ Z.hom
  rw [← Over.w f, ← Category.assoc, yonedaEquiv_symm_naturality_right, h]

/-- The Yoneda correspondence over `B`: the `T`-points of `Y` lying over `b` are the morphisms
over `B` from `testOver B T b` to `Y`. -/
noncomputable def ActionGroupoidData.pointFiberEquiv
    (T : BigFppfOver C S hS) (Y : Over B.obj)
    (b : yoneda.obj T ⟶ B.obj) :
    {x : Y.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B Y x = b} ≃
      (ActionGroupoidData.testOver B T b ⟶ Y) where
  toFun x := ActionGroupoidData.pointOver B b x.1 x.2
  invFun f := by
    let q : yoneda.obj T ⟶ Y.left := f.left
    refine ⟨yonedaEquiv q, ?_⟩
    change yonedaEquiv.symm (yonedaEquiv q) ≫ Y.hom = b
    rw [Equiv.symm_apply_apply]
    change q ≫ Y.hom = (Over.mk b).hom
    exact Over.w f
  left_inv x := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ _
  right_inv f := by
    let q : yoneda.obj T ⟶ Y.left := f.left
    apply Over.OverMorphism.ext
    apply yonedaEquiv.injective
    change yonedaEquiv (yonedaEquiv.symm (yonedaEquiv q)) = yonedaEquiv q
    exact Equiv.apply_symm_apply _ _

/-- Evaluating the morphism `pointFiberEquiv B T Y b x` at the identity of `T` gives `x`. -/
theorem ActionGroupoidData.pointFiberEquiv_app
    (T : BigFppfOver C S hS) (Y : Over B.obj)
    (b : yoneda.obj T ⟶ B.obj)
    (x : {x : Y.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B Y x = b}) :
    (ActionGroupoidData.pointFiberEquiv B T Y b x).left.app (Opposite.op T)
      (yonedaEquiv (𝟙 (yoneda.obj T))) = x.1 := by
  show (yonedaEquiv.symm x.1).app (Opposite.op T)
    (𝟙 T) = x.1
  simp [CategoryTheory.yonedaEquiv_symm_app]

/-- Two pointwise groupoid structures with the same source, target and composition have the same
identity arrows. -/
theorem ActionGroupoidData.pointwiseGroupoid_identity_unique
    {U R : Type u} {source target : R → U}
    {comp : {p : R × R // source p.1 = target p.2} → R}
    (P Q : Deformation.PointwiseGroupoid source target comp) (x : U) :
    (P.arrowEquiv x x (@CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x)).1 =
      (Q.arrowEquiv x x (@CategoryStruct.id U Q.groupoid.toCategory.toCategoryStruct x)).1 := by
  let pId := P.arrowEquiv x x (@CategoryStruct.id U P.groupoid.toCategory.toCategoryStruct x)
  let qId := Q.arrowEquiv x x (@CategoryStruct.id U Q.groupoid.toCategory.toCategoryStruct x)
  have hbase : source qId.1 = target pId.1 := qId.2.1.trans pId.2.2.symm
  have hp : qId.1 = comp ⟨(qId.1, pId.1), hbase⟩ := by
    let : Groupoid U := P.groupoid
    let pHom := (P.arrowEquiv x x).symm pId
    let qHom := (P.arrowEquiv x x).symm qId
    simpa [pId, qId, pHom, qHom] using P.comp_eq pHom qHom
  have hq : pId.1 = comp ⟨(qId.1, pId.1), hbase⟩ := by
    let : Groupoid U := Q.groupoid
    let pHom := (Q.arrowEquiv x x).symm pId
    let qHom := (Q.arrowEquiv x x).symm qId
    simpa [pId, qId, pHom, qHom] using Q.comp_eq pHom qHom
  exact hq.trans hp.symm

/-- Two pointwise groupoid structures with the same source, target and composition have the same
inverses. -/
theorem ActionGroupoidData.pointwiseGroupoid_inverse_unique
    {U R : Type u} {source target : R → U}
    {comp : {p : R × R // source p.1 = target p.2} → R}
    (P Q : Deformation.PointwiseGroupoid source target comp) (r : R) :
    (P.arrowEquiv (target r) (source r)
      (@Groupoid.inv U P.groupoid _ _
        ((P.arrowEquiv (source r) (target r)).symm ⟨r, rfl, rfl⟩))).1 =
    (Q.arrowEquiv (target r) (source r)
      (@Groupoid.inv U Q.groupoid _ _
        ((Q.arrowEquiv (source r) (target r)).symm ⟨r, rfl, rfl⟩))).1 := by
  let : Groupoid U := P.groupoid
  let f := (P.arrowEquiv (source r) (target r)).symm ⟨r, rfl, rfl⟩
  let qf := (Q.arrowEquiv (source r) (target r)).symm ⟨r, rfl, rfl⟩
  let qi := Q.arrowEquiv (target r) (source r) (@Groupoid.inv U Q.groupoid _ _ qf)
  let g := (P.arrowEquiv (target r) (source r)).symm qi
  have hgf : g ≫ f = 𝟙 (target r) := by
    apply (P.arrowEquiv _ _).injective
    apply Subtype.ext
    rw [P.comp_eq]
    simp only [g, f, Equiv.apply_symm_apply]
    rw [ActionGroupoidData.pointwiseGroupoid_identity_unique P Q (target r)]
    symm
    simpa only [qf, qi, Equiv.apply_symm_apply, Groupoid.inv_comp] using
      Q.comp_eq (@Groupoid.inv U Q.groupoid _ _ qf) qf
  have hg : g = Groupoid.inv f := by
    calc
      g = g ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = g ≫ (f ≫ Groupoid.inv f) := by rw [Groupoid.comp_inv]
      _ = (g ≫ f) ≫ Groupoid.inv f := (Category.assoc _ _ _).symm
      _ = Groupoid.inv f := by rw [hgf, Category.id_comp]
  show (P.arrowEquiv _ _ (Groupoid.inv f)).1 = qi.1
  rw [← hg]
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ qi)

/-- `pointFiberEquiv` is natural: the morphism of the image of `x` under `f` is the morphism of
`x` followed by `f`. -/
theorem ActionGroupoidData.pointFiberEquiv_map
    (T : BigFppfOver C S hS) {Y Z : Over B.obj}
    (b : yoneda.obj T ⟶ B.obj) (f : Y ⟶ Z)
    (x : {x : Y.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B Y x = b}) :
    ActionGroupoidData.pointFiberEquiv B T Z b
        ⟨f.left.app (Opposite.op T) x.1,
          (ActionGroupoidData.arrow_base_of_map B f x.1
            (f.left.app (Opposite.op T) x.1) rfl).symm.trans x.2⟩ =
      ActionGroupoidData.pointFiberEquiv B T Y b x ≫ f := by
  apply Over.OverMorphism.ext
  apply yonedaEquiv.injective
  show yonedaEquiv (yonedaEquiv.symm (f.left.app (Opposite.op T) x.1)) =
    yonedaEquiv (yonedaEquiv.symm x.1 ≫ f.left)
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- A `T`-point `a` of `Y` and its image under a morphism `f` over `B` have the same image in
`B`. -/
theorem ActionGroupoidData.point_arrow_base {T : BigFppfOver C S hS}
    {Y Z : Over B.obj} (f : Y ⟶ Z)
    (a : Y.left.obj (Opposite.op T)) :
    ActionGroupoidData.pointBase B Y a =
      ActionGroupoidData.pointBase B Z (f.left.app (Opposite.op T) a) :=
  ActionGroupoidData.arrow_base_of_map B f a _ rfl

/-- The source of `H` on `T`-points lying over `b`. -/
noncomputable def ActionGroupoidData.pointFiberSource
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj) :
    {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b} →
      {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b} := fun a =>
  ⟨H.source.left.app (Opposite.op T) a.1,
    (ActionGroupoidData.point_arrow_base B H.source a.1).symm.trans a.2⟩

/-- The target of `H` on `T`-points lying over `b`. -/
noncomputable def ActionGroupoidData.pointFiberTarget
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj) :
    {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b} →
      {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b} := fun a =>
  ⟨H.target.left.app (Opposite.op T) a.1,
    (ActionGroupoidData.point_arrow_base B H.target a.1).symm.trans a.2⟩

omit [GrpObj G] [ModObj G X] in
/-- Under `pointFiberEquiv`, `pointFiberSource` is composition with the source of `H`. -/
theorem ActionGroupoidData.pointFiberSource_map
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (a : {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b}) :
    ActionGroupoidData.pointFiberEquiv B T X b (ActionGroupoidData.pointFiberSource B G X H T b a) =
      ActionGroupoidData.pointFiberEquiv B T (G ⊗ X) b a ≫ H.source :=
  ActionGroupoidData.pointFiberEquiv_map B T b H.source a

omit [GrpObj G] [ModObj G X] in
/-- Under `pointFiberEquiv`, `pointFiberTarget` is composition with the target of `H`. -/
theorem ActionGroupoidData.pointFiberTarget_map
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (a : {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b}) :
    ActionGroupoidData.pointFiberEquiv B T X b (ActionGroupoidData.pointFiberTarget B G X H T b a) =
      ActionGroupoidData.pointFiberEquiv B T (G ⊗ X) b a ≫ H.target :=
  ActionGroupoidData.pointFiberEquiv_map B T b H.target a

/-- The `T`-points of `G ⊗ X` over `b` with source `x` and target `y` are the arrows between the
corresponding objects of the evaluation groupoid at `testOver B T b`. -/
noncomputable def ActionGroupoidData.pointFiberArrowEquiv
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (x y : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}) :
    {a : {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y} ≃
      @Quiver.Hom (ActionGroupoidData.testOver B T b ⟶ X)
        (ActionGroupoidData.evaluationGroupoid B G X H
          (ActionGroupoidData.testOver B T b)).toCategory.toQuiver
        (ActionGroupoidData.pointFiberEquiv B T X b x)
        (ActionGroupoidData.pointFiberEquiv B T X b y) := by
  classical
  let eX := ActionGroupoidData.pointFiberEquiv B T X b
  let eA := ActionGroupoidData.pointFiberEquiv B T (G ⊗ X) b
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  refine Equiv.mk (fun a => ?_) (fun f => ?_) ?_ ?_
  · refine ⟨eA a.1, ?_, ?_⟩
    · calc
        eA a.1 ≫ H.source = eX (ActionGroupoidData.pointFiberSource B G X H T b a.1) :=
          (ActionGroupoidData.pointFiberSource_map B G X H T b a.1).symm
        _ = eX x := congrArg eX a.2.1
    · calc
        eA a.1 ≫ H.target = eX (ActionGroupoidData.pointFiberTarget B G X H T b a.1) :=
          (ActionGroupoidData.pointFiberTarget_map B G X H T b a.1).symm
        _ = eX y := congrArg eX a.2.2
  · refine ⟨eA.symm f.1, ?_, ?_⟩
    · apply eX.injective
      calc
        eX (ActionGroupoidData.pointFiberSource B G X H T b (eA.symm f.1)) =
            eA (eA.symm f.1) ≫ H.source :=
              ActionGroupoidData.pointFiberSource_map B G X H T b (eA.symm f.1)
        _ = f.1 ≫ H.source := by rw [Equiv.apply_symm_apply]
        _ = eX x := f.2.1
    · apply eX.injective
      calc
        eX (ActionGroupoidData.pointFiberTarget B G X H T b (eA.symm f.1)) =
            eA (eA.symm f.1) ≫ H.target :=
              ActionGroupoidData.pointFiberTarget_map B G X H T b (eA.symm f.1)
        _ = f.1 ≫ H.target := by rw [Equiv.apply_symm_apply]
        _ = eX y := f.2.2
  · intro a
    apply Subtype.ext
    simp [eA]
  · intro f
    apply Subtype.ext
    simp [eA]

omit [GrpObj G] [ModObj G X] in
/-- Evaluating the arrow `pointFiberArrowEquiv B G X H T b x y a` at the identity of `T` gives the
`T`-point underlying `a`. -/
theorem ActionGroupoidData.pointFiberArrowEquiv_app
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (x y : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b})
    (a : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y}) :
    ((ActionGroupoidData.pointFiberArrowEquiv B G X H T b x y a).1).left.app
      (Opposite.op T) (yonedaEquiv (𝟙 (yoneda.obj T))) = a.1.1 := by
  show (ActionGroupoidData.pointFiberEquiv B T (G ⊗ X) b a.1).left.app
      (Opposite.op T) (yonedaEquiv (𝟙 (yoneda.obj T))) = a.1.1
  exact ActionGroupoidData.pointFiberEquiv_app B T (G ⊗ X) b a.1

/-- The composite of `T`-point arrows `x ⟶ y ⟶ z` over `b`, the composite in the evaluation
groupoid transported along `pointFiberArrowEquiv`. -/
noncomputable def ActionGroupoidData.pointFiberRawComp
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    {x y z : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}}
    (g : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y})
    (f : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = y ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = z}) :
    {a : {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = z} := by
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  exact (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x z).symm
    (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x y g ≫
      ActionGroupoidData.pointFiberArrowEquiv B G X H T b y z f)

/-- The identity `T`-point arrow at `x` over `b`, the identity of the evaluation groupoid
transported along `pointFiberArrowEquiv`. -/
noncomputable def ActionGroupoidData.pointFiberRawId
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (x : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}) :
    {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = x} := by
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  exact (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x x).symm
    (𝟙 (ActionGroupoidData.pointFiberEquiv B T X b x))

/-- The inverse of a `T`-point arrow over `b`, the inverse in the evaluation groupoid transported
along `pointFiberArrowEquiv`. -/
noncomputable def ActionGroupoidData.pointFiberRawInv
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    {x y : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}}
    (f : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y}) :
    {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = y ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = x} := by
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  exact (ActionGroupoidData.pointFiberArrowEquiv B G X H T b y x).symm
    (Groupoid.inv (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x y f))

omit [GrpObj G] [ModObj G X] in
/-- The identity `T`-point arrow at `x` is the value at `x` of the identity of `H`. -/
theorem ActionGroupoidData.pointFiberRawId_val
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (x : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}) :
    (ActionGroupoidData.pointFiberRawId B G X H T b x).1.1 =
      H.identity.left.app (Opposite.op T) x.1 := by
  classical
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  let a : {a : (G ⊗ X).left.obj (Opposite.op T) //
      ActionGroupoidData.pointBase B (G ⊗ X) a = b} :=
    ⟨H.identity.left.app (Opposite.op T) x.1,
      (ActionGroupoidData.point_arrow_base B H.identity x.1).symm.trans x.2⟩
  have hsrc : ActionGroupoidData.pointFiberSource B G X H T b a = x := by
    apply Subtype.ext
    simpa [ActionGroupoidData.pointFiberSource, Over.comp_left] using
      congrArg (fun f => f.left.app (Opposite.op T) x.1) H.source_identity
  have htgt : ActionGroupoidData.pointFiberTarget B G X H T b a = x := by
    apply Subtype.ext
    simpa [ActionGroupoidData.pointFiberTarget, Over.comp_left] using
      congrArg (fun f => f.left.app (Opposite.op T) x.1) H.target_identity
  let aa := (⟨a, hsrc, htgt⟩ : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
      ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = x})
  have hmap :
      ActionGroupoidData.pointFiberArrowEquiv B G X H T b x x aa =
        𝟙 (ActionGroupoidData.pointFiberEquiv B T X b x) :=
    Subtype.ext (ActionGroupoidData.pointFiberEquiv_map B T b H.identity x)
  have heq : ActionGroupoidData.pointFiberRawId B G X H T b x = aa := by
    apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x x).injective
    calc
      ActionGroupoidData.pointFiberArrowEquiv B G X H T b x x
          (ActionGroupoidData.pointFiberRawId B G X H T b x) =
          𝟙 (ActionGroupoidData.pointFiberEquiv B T X b x) := by
            unfold ActionGroupoidData.pointFiberRawId
            exact Equiv.apply_symm_apply _ _
      _ = ActionGroupoidData.pointFiberArrowEquiv B G X H T b x x aa := hmap.symm
  exact congrArg (fun a => a.1.1) heq

omit [GrpObj G] [ModObj G X] in
/-- `pointFiberArrowEquiv` takes `pointFiberRawComp` to composition in the evaluation
groupoid. -/
theorem ActionGroupoidData.pointFiberRawComp_map
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    [Groupoid (ActionGroupoidData.testOver B T b ⟶ X)]
    {x y z : {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}}
    (g : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y})
    (f : {a : {a : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) a = b} //
      ActionGroupoidData.pointFiberSource B G X H T b a = y ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = z}) :
    ActionGroupoidData.pointFiberArrowEquiv B G X H T b x z
      (ActionGroupoidData.pointFiberRawComp B G X H T b g f) =
    @CategoryStruct.comp _
      (ActionGroupoidData.evaluationGroupoid B G X H
        (ActionGroupoidData.testOver B T b)).toCategory.toCategoryStruct
      _ _ _
      (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x y g)
      (ActionGroupoidData.pointFiberArrowEquiv B G X H T b y z f) := by
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  exact Equiv.apply_symm_apply
    (ActionGroupoidData.pointFiberArrowEquiv B G X H T b x z) _

/-- The groupoid of `T`-points of `X` lying over `b`, in which an arrow `x ⟶ y` is a `T`-point of
`G ⊗ X` over `b` with source `x` and target `y`. -/
@[instance_reducible]
noncomputable def ActionGroupoidData.pointFiberRawGroupoid
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj) :
    Groupoid.{u, u} {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b} := by
  classical
  let V := {x : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X x = b}
  let A := {a : (G ⊗ X).left.obj (Opposite.op T) // ActionGroupoidData.pointBase B (G ⊗ X) a = b}
  let eX := ActionGroupoidData.pointFiberEquiv B T X b
  let eA := ActionGroupoidData.pointFiberEquiv B T (G ⊗ X) b
  let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
    ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
  let eHom := fun x y => ActionGroupoidData.pointFiberArrowEquiv B G X H T b x y
  let : Category.{u, u} V := {
    Hom := fun x y => {a : A //
      ActionGroupoidData.pointFiberSource B G X H T b a = x ∧
      ActionGroupoidData.pointFiberTarget B G X H T b a = y}
    id := fun x => (eHom x x).symm (𝟙 (eX x))
    comp := fun {x y z} f g => ActionGroupoidData.pointFiberRawComp B G X H T b f g
    id_comp := by
      intro x y f
      apply (eHom x y).injective
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b
        ((eHom x x).symm (𝟙 (eX x))) f]
      change eHom x x ((eHom x x).symm (𝟙 (eX x))) ≫ eHom x y f = _
      rw [Equiv.apply_symm_apply]
      exact Category.id_comp (eHom x y f)
    comp_id := by
      intro x y f
      apply (eHom x y).injective
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b
        f ((eHom y y).symm (𝟙 (eX y)))]
      change eHom x y f ≫ eHom y y ((eHom y y).symm (𝟙 (eX y))) = _
      rw [Equiv.apply_symm_apply]
      exact Category.comp_id (eHom x y f)
    assoc := by
      intro x y z w f g h
      apply (eHom x w).injective
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b
        (ActionGroupoidData.pointFiberRawComp B G X H T b f g) h]
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b f g]
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b
        f (ActionGroupoidData.pointFiberRawComp B G X H T b g h)]
      rw [ActionGroupoidData.pointFiberRawComp_map B G X H T b g h]
      exact Category.assoc (eHom x y f) (eHom y z g) (eHom z w h)
  }
  let rawInv := fun {x y : V} (f : x ⟶ y) =>
    (eHom y x).symm (Groupoid.inv (eHom x y f))
  have hcomp {x y z : V} (f : x ⟶ y) (g : y ⟶ z) :
      eHom x z (f ≫ g) = eHom x y f ≫ eHom y z g :=
    ActionGroupoidData.pointFiberRawComp_map B G X H T b f g
  have hid (x : V) : eHom x x (𝟙 x) = 𝟙 (eX x) := by
    change eHom x x ((eHom x x).symm (𝟙 (eX x))) = _
    exact Equiv.apply_symm_apply (eHom x x) _
  have hinv {x y : V} (f : x ⟶ y) :
      eHom y x (rawInv f) = Groupoid.inv (eHom x y f) := by
    change eHom y x ((eHom y x).symm (Groupoid.inv (eHom x y f))) = _
    exact Equiv.apply_symm_apply (eHom y x) _
  let : Groupoid.{u, u} V := {
    inv := fun {x y} f => rawInv f
    inv_comp := by
      intro x y f
      apply (eHom y y).injective
      rw [hcomp, hinv, hid]
      exact Groupoid.inv_comp (eHom x y f)
    comp_inv := by
      intro x y f
      apply (eHom x x).injective
      rw [hcomp, hinv, hid]
      exact Groupoid.comp_inv (eHom x y f)
  }
  exact inferInstance

omit [GrpObj G] [ModObj G X] in
/-- The source `x` and the target `y` of a `T`-point of `G ⊗ X` have the same image in `B`. -/
theorem ActionGroupoidData.globalHom_base_eq
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y : X.left.obj (Opposite.op T)}
    (r : {a : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) a = x ∧
      H.target.left.app (Opposite.op T) a = y}) :
    ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x := by
  obtain ⟨r, rfl, rfl⟩ := r
  exact (ActionGroupoidData.point_arrow_base B H.target r).symm.trans
    (ActionGroupoidData.point_arrow_base B H.source r)

/-- For `T`-points `x` and `y` of `X` over `b`, the `T`-points of `G ⊗ X` with source `x` and
target `y` are the same as those among the `T`-points over `b`. -/
noncomputable def ActionGroupoidData.globalHomFiberEquiv
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    (x y : X.left.obj (Opposite.op T))
    (hx : ActionGroupoidData.pointBase B X x = b) (hy : ActionGroupoidData.pointBase B X y = b) :
    {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y} ≃
    {a : {r : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) r = b} //
      ActionGroupoidData.pointFiberSource B G X H T
          b a = ⟨x, hx⟩ ∧
      ActionGroupoidData.pointFiberTarget B G X H T
          b a = ⟨y, hy⟩} := by
  classical
  refine ⟨fun r => ?_, fun a => ?_, ?_, ?_⟩
  · have hb : ActionGroupoidData.pointBase B (G ⊗ X) r.1 = b := by
      calc
        ActionGroupoidData.pointBase B (G ⊗ X) r.1 =
          ActionGroupoidData.pointBase B X (H.source.left.app (Opposite.op T) r.1) :=
          ActionGroupoidData.point_arrow_base B H.source r.1
        _ = ActionGroupoidData.pointBase B X x := congrArg (ActionGroupoidData.pointBase B X) r.2.1
        _ = b := hx
    have hb' : ActionGroupoidData.pointBase B (G ⊗ X) r.1 = b := hb
    let a : {r : (G ⊗ X).left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B (G ⊗ X) r = b} := ⟨r.1, hb'⟩
    refine ⟨a, ?_, ?_⟩
    · apply Subtype.ext
      exact r.2.1
    · apply Subtype.ext
      exact r.2.2
  · refine ⟨a.1.1, ?_, ?_⟩
    · exact congrArg Subtype.val a.2.1
    · exact congrArg Subtype.val a.2.2
  · intro r
    apply Subtype.ext
    rfl
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The identity arrow at a `T`-point `x` of `X`: the value at `x` of the identity of `H`. -/
noncomputable def ActionGroupoidData.globalHomId
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (x : X.left.obj (Opposite.op T)) :
    {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = x} := by
  refine ⟨H.identity.left.app (Opposite.op T) x, ?_, ?_⟩
  · have hs := congrArg (fun f => f.left.app (Opposite.op T) x) H.source_identity
    simpa [Over.comp_left] using hs
  · have ht := congrArg (fun f => f.left.app (Opposite.op T) x) H.target_identity
    simpa [Over.comp_left] using ht

/-- The composite of arrows `x ⟶ y ⟶ z` between `T`-points of `X` lying over `b`, computed by
`pointFiberRawComp`. -/
noncomputable def ActionGroupoidData.globalHomCompAt
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    {x y z : X.left.obj (Opposite.op T)}
    (hx : ActionGroupoidData.pointBase B X x = b)
    (hy' : ActionGroupoidData.pointBase B X y = b)
    (hz' : ActionGroupoidData.pointBase B X z = b)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y})
    (g : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = z}) :
    {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = z} := by
  let ef := ActionGroupoidData.globalHomFiberEquiv B G X H T b x y hx hy' f
  let eg := ActionGroupoidData.globalHomFiberEquiv B G X H T b y z hy' hz' g
  exact (ActionGroupoidData.globalHomFiberEquiv B G X H T b x z hx hz').symm
    (ActionGroupoidData.pointFiberRawComp B G X H T b ef eg)

/-- The composite of arrows `x ⟶ y ⟶ z` between `T`-points of `X`, computed over the image of `x`
in `B`. -/
noncomputable def ActionGroupoidData.globalHomComp
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y z : X.left.obj (Opposite.op T)}
    (hy : ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x)
    (hz : ActionGroupoidData.pointBase B X z = ActionGroupoidData.pointBase B X y)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y})
    (g : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = z}) :
    {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = z} :=
  ActionGroupoidData.globalHomCompAt B G X H T (ActionGroupoidData.pointBase B X x)
    rfl hy (hz.trans hy) f g

/-- The inverse of an arrow `x ⟶ y` between `T`-points of `X`, computed over the image of `x` in
`B` by `pointFiberRawInv`. -/
noncomputable def ActionGroupoidData.globalHomInv
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y : X.left.obj (Opposite.op T)}
    (hy : ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y}) :
    {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = x} := by
  let b := ActionGroupoidData.pointBase B X x
  let fx : {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} := ⟨x, rfl⟩
  let fy : {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} := ⟨y, hy⟩
  let ef := ActionGroupoidData.globalHomFiberEquiv B G X H T b x y rfl hy f
  exact (ActionGroupoidData.globalHomFiberEquiv B G X H T b y x hy rfl).symm
    (ActionGroupoidData.pointFiberRawInv B G X H T b ef)

omit [GrpObj G] [ModObj G X] in
/-- The inverse of an arrow `f` is the value at `f` of the inverse of `H`. -/
theorem ActionGroupoidData.globalHomInv_val
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y : X.left.obj (Opposite.op T)}
    (hy : ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y}) :
    (ActionGroupoidData.globalHomInv B G X H T hy f).1 =
      H.inverse.left.app (Opposite.op T) f.1 := by
  show yonedaEquiv (yonedaEquiv.symm f.1 ≫ H.inverse.left) = _
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]

omit [GrpObj G] [ModObj G X] in
/-- The identity arrow at `x` is the value at `x` of the identity of `H`. -/
theorem ActionGroupoidData.globalHomId_val
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (x : X.left.obj (Opposite.op T)) :
    (ActionGroupoidData.globalHomId B G X H T x).1 =
      H.identity.left.app (Opposite.op T) x :=
  rfl

omit [GrpObj G] [ModObj G X] in
/-- `globalHomFiberEquiv` takes `globalHomId` to `pointFiberRawId`. -/
theorem ActionGroupoidData.globalHomFiberEquiv_id
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj) (x : X.left.obj (Opposite.op T))
    (hx : ActionGroupoidData.pointBase B X x = b) :
    ActionGroupoidData.globalHomFiberEquiv B G X H T b x x hx hx
      (ActionGroupoidData.globalHomId B G X H T x) =
      ActionGroupoidData.pointFiberRawId B G X H T b
        (⟨x, hx⟩ : {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b}) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (ActionGroupoidData.pointFiberRawId_val B G X H T b ⟨x, hx⟩).symm

omit [GrpObj G] [ModObj G X] in
/-- `globalHomFiberEquiv` takes `globalHomComp` to `pointFiberRawComp`. -/
theorem ActionGroupoidData.globalHomFiberEquiv_comp
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y z : X.left.obj (Opposite.op T)}
    (hy : ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x)
    (hz : ActionGroupoidData.pointBase B X z = ActionGroupoidData.pointBase B X y)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y})
    (g : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = z}) :
    ActionGroupoidData.globalHomFiberEquiv B G X H T
      (ActionGroupoidData.pointBase B X x) x z rfl (hz.trans hy)
      (ActionGroupoidData.globalHomComp B G X H T hy hz f g) =
      ActionGroupoidData.pointFiberRawComp B G X H T (ActionGroupoidData.pointBase B X x)
        (ActionGroupoidData.globalHomFiberEquiv B G X H T
          (ActionGroupoidData.pointBase B X x) x y rfl hy f)
        (ActionGroupoidData.globalHomFiberEquiv B G X H T
          (ActionGroupoidData.pointBase B X x) y z hy
          (hz.trans hy) g) :=
  Equiv.apply_symm_apply _ _

omit [GrpObj G] [ModObj G X] in
/-- `globalHomFiberEquiv` takes `globalHomCompAt` to `pointFiberRawComp`. -/
theorem ActionGroupoidData.globalHomFiberEquiv_compAt
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    (b : yoneda.obj T ⟶ B.obj)
    {x y z : X.left.obj (Opposite.op T)}
    (hx : ActionGroupoidData.pointBase B X x = b) (hy : ActionGroupoidData.pointBase B X y = b)
    (hz : ActionGroupoidData.pointBase B X z = b)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y})
    (g : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = z}) :
    ActionGroupoidData.globalHomFiberEquiv B G X H T b x z hx hz
      (ActionGroupoidData.globalHomCompAt B G X H T b hx hy hz f g) =
      ActionGroupoidData.pointFiberRawComp B G X H T b
        (ActionGroupoidData.globalHomFiberEquiv B G X H T b x y hx hy f)
        (ActionGroupoidData.globalHomFiberEquiv B G X H T b y z hy hz g) :=
  Equiv.apply_symm_apply _ _

omit [GrpObj G] [ModObj G X] in
/-- `globalHomCompAt` does not depend on the point `b` of `B` over which it is computed. -/
theorem ActionGroupoidData.globalHomCompAt_rebase
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {b c : yoneda.obj T ⟶ B.obj} (hbc : b = c)
    {x y z : X.left.obj (Opposite.op T)}
    (hx : ActionGroupoidData.pointBase B X x = b) (hy : ActionGroupoidData.pointBase B X y = b)
    (hz : ActionGroupoidData.pointBase B X z = b)
    (hx' : ActionGroupoidData.pointBase B X x = c) (hy' : ActionGroupoidData.pointBase B X y = c)
    (hz' : ActionGroupoidData.pointBase B X z = c)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y})
    (g : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = y ∧
      H.target.left.app (Opposite.op T) r = z}) :
    ActionGroupoidData.globalHomCompAt B G X H T b hx hy hz f g =
      ActionGroupoidData.globalHomCompAt B G X H T c hx' hy' hz' f g := by
  cases hbc
  apply Subtype.ext
  rfl

omit [GrpObj G] [ModObj G X] in
/-- `globalHomFiberEquiv` takes `globalHomInv` to `pointFiberRawInv`. -/
theorem ActionGroupoidData.globalHomFiberEquiv_inv
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS)
    {x y : X.left.obj (Opposite.op T)}
    (hy : ActionGroupoidData.pointBase B X y = ActionGroupoidData.pointBase B X x)
    (f : {r : (G ⊗ X).left.obj (Opposite.op T) //
      H.source.left.app (Opposite.op T) r = x ∧
      H.target.left.app (Opposite.op T) r = y}) :
    ActionGroupoidData.globalHomFiberEquiv B G X H T (ActionGroupoidData.pointBase B X x) y x hy rfl
      (ActionGroupoidData.globalHomInv B G X H T hy f) =
      ActionGroupoidData.pointFiberRawInv B G X H T (ActionGroupoidData.pointBase B X x)
        (ActionGroupoidData.globalHomFiberEquiv B G X H T
          (ActionGroupoidData.pointBase B X x) x y rfl hy f) :=
  Equiv.apply_symm_apply _ _

/-- The groupoid of `T`-points of `X`, in which an arrow `x ⟶ y` is a `T`-point of `G ⊗ X` with
source `x` and target `y`, composed over the common image of the points in `B`. -/
@[instance_reducible]
noncomputable def ActionGroupoidData.globalPointwiseRawGroupoid
    (H : ActionGroupoidData B G X) (T : BigFppfOver C S hS) :
    Groupoid.{u, u} (X.left.obj (Opposite.op T)) := by
  classical
  let V := X.left.obj (Opposite.op T)
  let rawHom := fun (x y : V) => {r : (G ⊗ X).left.obj (Opposite.op T) //
    H.source.left.app (Opposite.op T) r = x ∧ H.target.left.app (Opposite.op T) r = y}
  let : Category.{u, u} V := {
    Hom := rawHom
    id := fun x => ActionGroupoidData.globalHomId B G X H T x
    comp := fun {x y z} f g =>
      ActionGroupoidData.globalHomComp B G X H T
        (ActionGroupoidData.globalHom_base_eq B G X H T f)
        (ActionGroupoidData.globalHom_base_eq B G X H T g) f g
    id_comp := by
      intro x y f
      let b := ActionGroupoidData.pointBase B X x
      let hy := ActionGroupoidData.globalHom_base_eq B G X H T f
      let : Groupoid {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} :=
        ActionGroupoidData.pointFiberRawGroupoid B G X H T b
      let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
        ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
      apply (ActionGroupoidData.globalHomFiberEquiv B G X H T b x y rfl hy).injective
      apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨x, rfl⟩ ⟨y, hy⟩).injective
      have hid : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomId B G X H T x) = rfl := Subsingleton.elim _ _
      rw [hid,
        ActionGroupoidData.globalHomFiberEquiv_comp
          (H := H) (T := T) (hy := rfl) (hz := hy)
          (f := ActionGroupoidData.globalHomId B G X H T x) (g := f),
        ActionGroupoidData.globalHomFiberEquiv_id B G X H T b x rfl]
      rw [ActionGroupoidData.pointFiberRawComp_map]
      unfold ActionGroupoidData.pointFiberRawId
      rw [Equiv.apply_symm_apply]
      exact Category.id_comp _
    comp_id := by
      intro x y f
      let b := ActionGroupoidData.pointBase B X x
      let hy := ActionGroupoidData.globalHom_base_eq B G X H T f
      let : Groupoid {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} :=
        ActionGroupoidData.pointFiberRawGroupoid B G X H T b
      let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
        ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
      apply (ActionGroupoidData.globalHomFiberEquiv B G X H T b x y rfl hy).injective
      apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨x, rfl⟩ ⟨y, hy⟩).injective
      have hid : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomId B G X H T y) = rfl := Subsingleton.elim _ _
      rw [hid,
        ActionGroupoidData.globalHomFiberEquiv_comp
          (H := H) (T := T) (hy := hy) (hz := rfl)
          (f := f) (g := ActionGroupoidData.globalHomId B G X H T y),
        ActionGroupoidData.globalHomFiberEquiv_id B G X H T b y hy]
      rw [ActionGroupoidData.pointFiberRawComp_map]
      unfold ActionGroupoidData.pointFiberRawId
      rw [Equiv.apply_symm_apply]
      exact Category.comp_id _
    assoc := by
      intro x y z w f g h
      let b := ActionGroupoidData.pointBase B X x
      let hy := ActionGroupoidData.globalHom_base_eq B G X H T f
      let hz := ActionGroupoidData.globalHom_base_eq B G X H T g
      let hw := ActionGroupoidData.globalHom_base_eq B G X H T h
      let : Groupoid {v : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X v = b} :=
        ActionGroupoidData.pointFiberRawGroupoid B G X H T b
      let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
        ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
      apply (ActionGroupoidData.globalHomFiberEquiv B G X H T b x w rfl
        (hw.trans (hz.trans hy))).injective
      apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T (ActionGroupoidData.pointBase B X x)
        ⟨x, rfl⟩ ⟨w, hw.trans (hz.trans hy)⟩).injective
      have hfg : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomComp B G X H T hy hz f g) = hz.trans hy :=
        Subsingleton.elim _ _
      have hgh : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomComp B G X H T hz hw g h) = hw.trans hz :=
        Subsingleton.elim _ _
      rw [hfg, hgh]
      dsimp only [b]
      have hfg' := ActionGroupoidData.globalHomFiberEquiv_comp
        (H := H) (T := T) (hy := hy) (hz := hz) (f := f) (g := g)
      have hgh_rebase :
          ActionGroupoidData.globalHomComp B G X H T hz hw g h =
            ActionGroupoidData.globalHomCompAt B G X H T (ActionGroupoidData.pointBase B X x)
              hy (hz.trans hy) (hw.trans (hz.trans hy)) g h := by
        unfold ActionGroupoidData.globalHomComp
        exact ActionGroupoidData.globalHomCompAt_rebase B G X H T hy
          rfl hz (hw.trans hz) hy (hz.trans hy) (hw.trans (hz.trans hy)) g h
      have hgh_at := ActionGroupoidData.globalHomFiberEquiv_compAt
        (H := H) (T := T) (b := ActionGroupoidData.pointBase B X x)
        (hx := hy) (hy := hz.trans hy) (hz := hw.trans (hz.trans hy))
        (f := g) (g := h)
      have houterL := ActionGroupoidData.globalHomFiberEquiv_comp
        (H := H) (T := T) (hy := hz.trans hy) (hz := hw)
        (f := ActionGroupoidData.globalHomComp B G X H T hy hz f g) (g := h)
      have houterR := ActionGroupoidData.globalHomFiberEquiv_comp
        (H := H) (T := T) (hy := hy) (hz := hw.trans hz)
        (f := f) (g := ActionGroupoidData.globalHomComp B G X H T hz hw g h)
      rw [houterL, houterR]
      rw [hfg', hgh_rebase, hgh_at]
      let fx : {v : X.left.obj (Opposite.op T) //
        ActionGroupoidData.pointBase B X v = b} := ⟨x, rfl⟩
      let fy : {v : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X v = b} := ⟨y, hy⟩
      let fz : {v : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X v = b} :=
        ⟨z, hz.trans hy⟩
      let fw : {v : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X v = b} :=
        ⟨w, hw.trans (hz.trans hy)⟩
      let ef := ActionGroupoidData.globalHomFiberEquiv B G X H T b x y rfl hy f
      let eg := ActionGroupoidData.globalHomFiberEquiv B G X H T b y z hy
        (hz.trans hy) g
      let eh := ActionGroupoidData.globalHomFiberEquiv B G X H T b z w
        (hz.trans hy) (hw.trans (hz.trans hy)) h
      simpa only [ActionGroupoidData.pointFiberRawComp_map] using
        (Category.assoc (obj := ActionGroupoidData.testOver B T b ⟶ X)
          (ActionGroupoidData.pointFiberArrowEquiv B G X H T b fx fy ef)
          (ActionGroupoidData.pointFiberArrowEquiv B G X H T b fy fz eg)
          (ActionGroupoidData.pointFiberArrowEquiv B G X H T b fz fw eh))
  }
  let : Groupoid.{u, u} V := {
    inv := fun {x y} f =>
      ActionGroupoidData.globalHomInv B G X H T
        (ActionGroupoidData.globalHom_base_eq B G X H T f) f
    inv_comp := by
      intro x y f
      let b := ActionGroupoidData.pointBase B X x
      let hy := ActionGroupoidData.globalHom_base_eq B G X H T f
      let : Groupoid {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} :=
        ActionGroupoidData.pointFiberRawGroupoid B G X H T b
      let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
        ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
      apply (ActionGroupoidData.globalHomFiberEquiv B G X H T b y y hy hy).injective
      apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨y, hy⟩ ⟨y, hy⟩).injective
      have hinv : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomInv B G X H T hy f) = hy.symm :=
        Subsingleton.elim _ _
      have hfbase : ActionGroupoidData.globalHom_base_eq B G X H T f = hy :=
        Subsingleton.elim _ _
      change (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨y, hy⟩ ⟨y, hy⟩)
          (ActionGroupoidData.globalHomFiberEquiv B G X H T b y y hy hy
            (ActionGroupoidData.globalHomComp B G X H T
              (ActionGroupoidData.globalHom_base_eq B G X H T
                (ActionGroupoidData.globalHomInv B G X H T hy f))
              (ActionGroupoidData.globalHom_base_eq B G X H T f)
              (ActionGroupoidData.globalHomInv B G X H T hy f) f)) =
        (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
          ⟨y, hy⟩ ⟨y, hy⟩)
          (ActionGroupoidData.globalHomFiberEquiv B G X H T b y y hy hy
            (ActionGroupoidData.globalHomId B G X H T y))
      rw [hinv, hfbase]
      have hcomp_rebase :
          ActionGroupoidData.globalHomComp B G X H T hy.symm hy
              (ActionGroupoidData.globalHomInv B G X H T hy f) f =
            ActionGroupoidData.globalHomCompAt B G X H T b hy rfl hy
              (ActionGroupoidData.globalHomInv B G X H T hy f) f := by
        unfold ActionGroupoidData.globalHomComp
        exact ActionGroupoidData.globalHomCompAt_rebase B G X H T hy
          rfl hy.symm (hy.trans hy.symm) hy rfl hy
          (ActionGroupoidData.globalHomInv B G X H T hy f) f
      rw [hcomp_rebase]
      rw [ActionGroupoidData.globalHomFiberEquiv_compAt
          (H := H) (T := T) (b := b) (hx := hy) (hy := rfl) (hz := hy)
          (f := ActionGroupoidData.globalHomInv B G X H T hy f) (g := f),
        ActionGroupoidData.globalHomFiberEquiv_inv,
        ActionGroupoidData.globalHomFiberEquiv_id B G X H T b y hy]
      rw [ActionGroupoidData.pointFiberRawComp_map]
      unfold ActionGroupoidData.pointFiberRawInv
      unfold ActionGroupoidData.pointFiberRawId
      rw [Equiv.apply_symm_apply]
      simp [b]
    comp_inv := by
      intro x y f
      let b := ActionGroupoidData.pointBase B X x
      let hy := ActionGroupoidData.globalHom_base_eq B G X H T f
      let : Groupoid {w : X.left.obj (Opposite.op T) // ActionGroupoidData.pointBase B X w = b} :=
        ActionGroupoidData.pointFiberRawGroupoid B G X H T b
      let : Groupoid (ActionGroupoidData.testOver B T b ⟶ X) :=
        ActionGroupoidData.evaluationGroupoid B G X H (ActionGroupoidData.testOver B T b)
      apply (ActionGroupoidData.globalHomFiberEquiv B G X H T b x x rfl rfl).injective
      apply (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨x, rfl⟩ ⟨x, rfl⟩).injective
      have hinv : ActionGroupoidData.globalHom_base_eq B G X H T
          (ActionGroupoidData.globalHomInv B G X H T hy f) = hy.symm :=
        Subsingleton.elim _ _
      have hfbase : ActionGroupoidData.globalHom_base_eq B G X H T f = hy :=
        Subsingleton.elim _ _
      change (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
        ⟨x, rfl⟩ ⟨x, rfl⟩)
          (ActionGroupoidData.globalHomFiberEquiv B G X H T b x x rfl rfl
            (ActionGroupoidData.globalHomComp B G X H T
              (ActionGroupoidData.globalHom_base_eq B G X H T f)
              (ActionGroupoidData.globalHom_base_eq B G X H T
                (ActionGroupoidData.globalHomInv B G X H T hy f))
              f (ActionGroupoidData.globalHomInv B G X H T hy f))) =
        (ActionGroupoidData.pointFiberArrowEquiv B G X H T b
          ⟨x, rfl⟩ ⟨x, rfl⟩)
          (ActionGroupoidData.globalHomFiberEquiv B G X H T b x x rfl rfl
            (ActionGroupoidData.globalHomId B G X H T x))
      rw [hfbase, hinv]
      rw [ActionGroupoidData.globalHomFiberEquiv_comp
          (H := H) (T := T) (hy := hy) (hz := hy.symm) (f := f)
          (g := ActionGroupoidData.globalHomInv B G X H T hy f),
        ActionGroupoidData.globalHomFiberEquiv_inv,
        ActionGroupoidData.globalHomFiberEquiv_id B G X H T b x rfl]
      rw [ActionGroupoidData.pointFiberRawComp_map]
      unfold ActionGroupoidData.pointFiberRawInv
      unfold ActionGroupoidData.pointFiberRawId
      rw [Equiv.apply_symm_apply]
      simp [b]
  }
  exact inferInstance

/-- A groupoid in algebraic spaces with exactly the maps specified by the action. -/
structure ActionGroupoidConstruction where
  /-- The groupoid in algebraic spaces over `B`. -/
  groupoid : GroupoidInAlgebraicSpaces C S hS B
  /-- Its object space is `X`. -/
  objects_eq : groupoid.objects = ⟨X.left, hX⟩
  /-- Its arrow space is `G ×_B X`. -/
  arrows_eq : groupoid.arrows =
    AlgebraicSpaces.fiberProduct C S hS
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B)
  /-- Its object space maps to `B` by the structure morphism of `X`. -/
  objectsToBase_eq : HEq groupoid.objectsToBase.hom X.hom
  /-- Its arrow space maps to `B` by the structure morphism of `G ⊗ X`. -/
  arrowsToBase_eq : HEq groupoid.arrowsToBase.hom (G ⊗ X).hom
  /-- Its source is the second projection of `G ×_B X`. -/
  source_eq : HEq groupoid.source.hom (snd G X).left
  /-- Its target is the action morphism. -/
  target_eq : HEq groupoid.target.hom γ[G, X].left
  /-- The fibre product of the source and the target taken in presheaves is isomorphic to the
  underlying presheaf of their fibre product taken over `B`. -/
  compositionDomainIso :
    pullback (snd G X).left γ[G, X].left ≅
      (pullback (snd G X) γ[G, X]).left
  /-- `compositionDomainIso` commutes with the first projections. -/
  compositionDomainIso_fst :
    compositionDomainIso.hom ≫ (pullback.fst (snd G X) γ[G, X]).left =
      pullback.fst (snd G X).left γ[G, X].left
  /-- `compositionDomainIso` commutes with the second projections. -/
  compositionDomainIso_snd :
    compositionDomainIso.hom ≫ (pullback.snd (snd G X) γ[G, X]).left =
      pullback.snd (snd G X).left γ[G, X].left
  /-- Its composition is the composition of the action groupoid, through
  `compositionDomainIso`. -/
  comp_eq : HEq groupoid.comp.hom
    (compositionDomainIso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left)
  /-- At each test object its identity is the identity of the action groupoid. -/
  identity_eq : ∀ T, HEq (groupoid.toGroupoidInFunctors.identity T)
    (fun x => (Stacks.Groupoids.ActionGroupoid.identity G X).left.app T x)
  /-- At each test object its inverse is `actionInverse`. -/
  inverse_eq : ∀ T, HEq (Deformation.inverseArrow groupoid.toGroupoidInFunctors T)
    (fun r => (actionInverse B G X).left.app T r)

/-- The action groupoid in algebraic spaces of the action of `G` on `X`, with its object and
arrow spaces and its structure maps identified. -/
noncomputable def actionGroupoidConstruction :
    ActionGroupoidConstruction B G X hG hX := by
  classical
  let objects : AlgebraicSpaces C S hS := ⟨X.left, hX⟩
  let arrows : AlgebraicSpaces C S hS :=
    AlgebraicSpaces.fiberProduct C S hS
      (ObjectProperty.homMk G.hom :
        (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
      (ObjectProperty.homMk X.hom :
        (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B)
  let F := Over.forget B.obj
  let p : (G ⊗ X).left ⟶ X.left := (snd G X).left
  let q : (G ⊗ X).left ⟶ X.left := γ[G, X].left
  have hlim : IsLimit (F.mapCone (pullback.cone (snd G X) γ[G, X])) :=
    isLimitOfPreserves F (pullback.isLimit (snd G X) γ[G, X])
  have hpres : IsPullback
      (F.map (pullback.fst (snd G X) γ[G, X]))
      (F.map (pullback.snd (snd G X) γ[G, X])) p q :=
    IsPullback.of_isLimit_cone hlim
  let iso : pullback p q ≅ (pullback (snd G X) γ[G, X]).left :=
    (IsPullback.of_hasPullback p q).isoIsPullback _ _ hpres
  have hp : iso.hom ≫ (pullback.fst (snd G X) γ[G, X]).left =
      pullback.fst p q :=
    (IsPullback.of_hasPullback p q).isoIsPullback_hom_fst _ _ hpres
  have hq : iso.hom ≫ (pullback.snd (snd G X) γ[G, X]).left =
      pullback.snd p q :=
    (IsPullback.of_hasPullback p q).isoIsPullback_hom_snd _ _ hpres
  let sourceHom : arrows ⟶ objects := ObjectProperty.homMk (snd G X).left
  let targetHom : arrows ⟶ objects := ObjectProperty.homMk γ[G, X].left
  let compHom :
      AlgebraicSpaces.fiberProduct C S hS sourceHom targetHom ⟶ arrows :=
    ObjectProperty.homMk (iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left)
  let pointwise (T : (BigFppfOver C S hS)ᵒᵖ) :
      Deformation.PointwiseGroupoid ((snd G X).left.app T) (γ[G, X].left.app T)
        (fun p => (composableToPullback sourceHom.hom targetHom.hom ≫
          compHom.hom).app T p) := by
      refine {
        groupoid := ActionGroupoidData.globalPointwiseRawGroupoid B G X
          (actionGroupoidData B G X) (Opposite.unop T)
        arrowEquiv := fun x y =>
          Equiv.refl _
        comp_eq := by
          intro x y z g f
          let Hdata := actionGroupoidData B G X
          let T' := Opposite.unop T
          let hy := ActionGroupoidData.globalHom_base_eq B G X Hdata T' g
          let hz := ActionGroupoidData.globalHom_base_eq B G X Hdata T' f
          let b := ActionGroupoidData.pointBase B X x
          let eg := ActionGroupoidData.globalHomFiberEquiv B G X Hdata T' b x y rfl hy g
          let ef := ActionGroupoidData.globalHomFiberEquiv B G X Hdata T' b y z hy
            (hz.trans hy) f
          let : Groupoid (ActionGroupoidData.testOver B T' b ⟶ X) :=
            ActionGroupoidData.evaluationGroupoid B G X Hdata (ActionGroupoidData.testOver B T' b)
          let egHom := ActionGroupoidData.pointFiberArrowEquiv B G X Hdata T' b
            ⟨x, rfl⟩ ⟨y, hy⟩ eg
          let efHom := ActionGroupoidData.pointFiberArrowEquiv B G X Hdata T' b
            ⟨y, hy⟩ ⟨z, hz.trans hy⟩ ef
          have hcond : efHom.1 ≫ Hdata.source = egHom.1 ≫ Hdata.target :=
            efHom.2.1.trans egHom.2.2.symm
          let pairOver := pullback.lift efHom.1 egHom.1 hcond
          have hcondLeft : efHom.1.left ≫ p = egHom.1.left ≫ q := by
            change efHom.1.left ≫ Hdata.source.left =
              egHom.1.left ≫ Hdata.target.left
            exact congrArg Over.Hom.left hcond
          let pairFun := pullback.lift efHom.1.left egHom.1.left hcondLeft
          have hpairIso : pairFun ≫ iso.hom = pairOver.left := by
            apply hpres.hom_ext
            · calc
                pairFun ≫ iso.hom ≫ (pullback.fst (snd G X) γ).left =
                    pairFun ≫ pullback.fst p q := by rw [hp]
                _ = efHom.1.left := by
                  dsimp [pairFun]
                  exact pullback.lift_fst _ _ _
                _ = pairOver.left ≫ (pullback.fst (snd G X) γ).left := by
                  change efHom.1.left =
                    Over.Hom.left (pairOver ≫ pullback.fst (snd G X) γ)
                  exact (congrArg Over.Hom.left
                    (pullback.lift_fst efHom.1 egHom.1 hcond)).symm
            · calc
                pairFun ≫ iso.hom ≫ (pullback.snd (snd G X) γ).left =
                    pairFun ≫ pullback.snd p q := by rw [hq]
                _ = egHom.1.left := by
                  dsimp [pairFun]
                  exact pullback.lift_snd _ _ _
                _ = pairOver.left ≫ (pullback.snd (snd G X) γ).left := by
                  change egHom.1.left =
                    Over.Hom.left (pairOver ≫ pullback.snd (snd G X) γ)
                  exact (congrArg Over.Hom.left
                    (pullback.lift_snd efHom.1 egHom.1 hcond)).symm
          let compFun := Deformation.composableArrows X.left (G ⊗ X).left p q
          let cinput : compFun.obj T := ⟨(f.1, g.1), by
            change (snd G X).left.app T f.1 = γ[G, X].left.app T g.1
            exact f.2.1.trans g.2.2.symm⟩
          let cinputMap : yoneda.obj T' ⟶ compFun := yonedaEquiv.symm cinput
          let actualPair :=
            (composableToPullback p q).app T cinput
          have hpairMap : pairFun = cinputMap ≫
              composableToPullback p q := by
            apply pullback.hom_ext
            · have h : efHom.1.left =
                  (cinputMap ≫ composableToPullback p q) ≫
                    pullback.fst p q := by
                rw [Category.assoc]
                rw [show composableToPullback p q ≫ pullback.fst p q =
                  { app := fun _ => ↾ fun a => a.1.1, naturality := by intros; rfl }
                  from pullback.lift_fst _ _ _]
                rfl
              exact (pullback.lift_fst _ _ _).trans h
            · have h : egHom.1.left =
                  (cinputMap ≫ composableToPullback p q) ≫
                    pullback.snd p q := by
                rw [Category.assoc]
                rw [show composableToPullback p q ≫ pullback.snd p q =
                  { app := fun _ => ↾ fun a => a.1.2, naturality := by intros; rfl }
                  from pullback.lift_snd _ _ _]
                rfl
              exact (pullback.lift_snd _ _ _).trans h
          have hpairPoint :
              pairFun.app (Opposite.op T') (yonedaEquiv (𝟙 (yoneda.obj T'))) = actualPair := by
            have heval : cinputMap.app (Opposite.op T') (𝟙 T') = cinput := by
              change yonedaEquiv (yonedaEquiv.symm cinput) = cinput
              exact Equiv.apply_symm_apply _ _
            have h := congrArg (fun k : yoneda.obj T' ⟶ pullback p q =>
              k.app (Opposite.op T') (𝟙 T')) hpairMap
            change pairFun.app (Opposite.op T') (𝟙 T') =
              (composableToPullback p q).app (Opposite.op T')
                (cinputMap.app (Opposite.op T') (𝟙 T')) at h
            rw [heval] at h
            exact h
          have hcompPoint :
              (iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left).app T actualPair =
                (pairOver ≫ Hdata.comp).left.app (Opposite.op T')
                  (yonedaEquiv (𝟙 (yoneda.obj T'))) := by
            have h := congrArg (fun k : yoneda.obj T' ⟶
                (pullback (snd G X) γ[G, X]).left =>
              k.app (Opposite.op T') (𝟙 T')) hpairIso
            change iso.hom.app T (pairFun.app (Opposite.op T')
              (yonedaEquiv (𝟙 (yoneda.obj T')))) = _ at h
            rw [hpairPoint] at h
            exact congrArg ((Stacks.Groupoids.ActionGroupoid.composition G X).left.app T) h
          have hrawmap := ActionGroupoidData.pointFiberRawComp_map
            B G X Hdata T' b eg ef
          have hpoint :
              (ActionGroupoidData.pointFiberRawComp B G X Hdata T' b eg ef).1.1 =
                (pairOver ≫ Hdata.comp).left.app (Opposite.op T')
                  (yonedaEquiv (𝟙 (yoneda.obj T'))) := by
            have h := congrArg (fun q => q.1.left.app (Opposite.op T')
              (yonedaEquiv (𝟙 (yoneda.obj T')))) hrawmap
            rw [ActionGroupoidData.pointFiberArrowEquiv_app] at h
            simpa only [Over.comp_left, NatTrans.comp_app,
              ConcreteCategory.comp_apply, CategoryStruct.comp,
              ActionGroupoidData.evaluationGroupoid, pairOver,
              egHom, efHom] using h
          have hcompfib := ActionGroupoidData.globalHomFiberEquiv_comp
            (H := Hdata) (T := T') (hy := hy) (hz := hz) (f := g) (g := f)
          have hval₀ := congrArg (fun a => a.1.1) hcompfib
          have hval : (ActionGroupoidData.globalHomComp B G X Hdata T' hy hz g f).1 =
              (ActionGroupoidData.pointFiberRawComp B G X Hdata T'
                (ActionGroupoidData.pointBase B X x)
                (ActionGroupoidData.globalHomFiberEquiv B G X Hdata T'
                  (ActionGroupoidData.pointBase B X x) x y rfl hy g)
                (ActionGroupoidData.globalHomFiberEquiv B G X Hdata T'
                  (ActionGroupoidData.pointBase B X x) y z hy (hz.trans hy) f)).1.1 := by
            simpa [ActionGroupoidData.globalHomFiberEquiv] using hval₀
          change (ActionGroupoidData.globalHomComp B G X
            Hdata T' hy hz g f).1 = _
          exact hval.trans (hpoint.trans hcompPoint.symm)
      }
  let H : GroupoidInAlgebraicSpaces C S hS B := {
    objects := objects
    arrows := arrows
    objectsToBase := ObjectProperty.homMk X.hom
    arrowsToBase := ObjectProperty.homMk (G ⊗ X).hom
    source := ObjectProperty.homMk (snd G X).left
    target := ObjectProperty.homMk γ[G, X].left
    source_over := by
      apply ObjectProperty.hom_ext
      exact Over.w (snd G X)
    target_over := by
      apply ObjectProperty.hom_ext
      exact Over.w γ[G, X]
    comp := ObjectProperty.homMk (iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left)
    comp_over := by
      apply ObjectProperty.hom_ext
      change iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left ≫ (G ⊗ X).hom =
        pullback.fst p q ≫ (G ⊗ X).hom
      calc
        iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left ≫ (G ⊗ X).hom =
            iso.hom ≫ (pullback (snd G X) γ[G, X]).hom := by
              rw [Over.w (Stacks.Groupoids.ActionGroupoid.composition G X)]
        _ = iso.hom ≫ (pullback.fst (snd G X) γ[G, X]).left ≫ (G ⊗ X).hom :=
          congrArg (fun k => iso.hom ≫ k) (Over.w (pullback.fst (snd G X) γ[G, X])).symm
        _ = pullback.fst p q ≫ (G ⊗ X).hom :=
          congrArg (fun k => k ≫ (G ⊗ X).hom) hp
    pointwiseGroupoid := fun T => ⟨pointwise T⟩
  }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, iso, hp, hq, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro T
    apply heq_of_eq
    funext x
    exact ActionGroupoidData.pointwiseGroupoid_identity_unique
      (H.toGroupoidInFunctors.pointwiseData T) (pointwise T) x
  · intro T
    apply heq_of_eq
    funext r
    have hi := ActionGroupoidData.pointwiseGroupoid_inverse_unique
      (H.toGroupoidInFunctors.pointwiseData T) (pointwise T) r
    exact hi.trans (ActionGroupoidData.globalHomInv_val B G X
      (actionGroupoidData B G X) (Opposite.unop T) _ _)

/-- A group action gives the action groupoid,
with the stated object and arrow spaces and all five structure maps. -/
@[stacks 0444]
noncomputable def groupoidOfAction :
    ActionGroupoidConstruction B G X hG hX :=
  actionGroupoidConstruction B G X hG hX

/-! ### The structure maps of the action groupoid, as equations

The fields of `AlgebraicGeometry.Space.ActionGroupoidConstruction` record the five structure maps
of the action groupoid only as heterogeneous equalities, because the object and arrow spaces of a
groupoid in algebraic spaces are fields and so need not be the given ones. For the action groupoid
they *are* the given ones, so each structure map is pinned by an ordinary equation, and the five
below hold by definition.

They are what lets a consumer compute the evaluated groupoid of the action groupoid: its objects
are the `T`-points of `X`, and an arrow `x ⟶ y` is a `T`-point of `G ×_B X` whose second
projection is `x` and whose action value is `y`, by
`CategoryTheory.Deformation.GroupoidInFunctors.evaluationArrowEquiv` read through
`AlgebraicGeometry.Space.groupoidOfAction_source` and
`AlgebraicGeometry.Space.groupoidOfAction_target`. -/

/-- The object space of the action groupoid is `X`. -/
theorem groupoidOfAction_objects :
    (groupoidOfAction B G X hG hX).groupoid.objects = ⟨X.left, hX⟩ := rfl

/-- The arrow space of the action groupoid is `G ×_B X`. -/
theorem groupoidOfAction_arrows :
    (groupoidOfAction B G X hG hX).groupoid.arrows =
      AlgebraicSpaces.fiberProduct C S hS
        (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
        (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B) := rfl

/-- The source of the action groupoid is the second projection of `G ×_B X`. -/
theorem groupoidOfAction_source :
    (groupoidOfAction B G X hG hX).groupoid.source = ObjectProperty.homMk (snd G X).left := rfl

/-- The target of the action groupoid is the action morphism. -/
theorem groupoidOfAction_target :
    (groupoidOfAction B G X hG hX).groupoid.target = ObjectProperty.homMk γ[G, X].left := rfl

/-- The objects of the groupoid obtained by evaluating the action groupoid at a test object are
the points of `X` there. -/
theorem groupoidOfAction_evaluation (T : (BigFppfOver C S hS)ᵒᵖ) :
    (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.Evaluation T =
      X.left.obj T := rfl

/-- **An arrow `x ⟶ y` of the evaluated action groupoid is a point of `G ×_B X` whose second
projection is `x` and whose action value is `y`.** This is
`CategoryTheory.Deformation.GroupoidInFunctors.evaluationArrowEquiv` with the arrow space, the
source and the target of the action groupoid read off by
`AlgebraicGeometry.Space.groupoidOfAction_arrows`,
`AlgebraicGeometry.Space.groupoidOfAction_source` and
`AlgebraicGeometry.Space.groupoidOfAction_target`.

The composite of two arrows is computed by the composition morphism of the action groupoid under
this identification: that is the third clause of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.points_isGroupoid`, which holds for every groupoid in
algebraic spaces and so needs no action-specific statement. In particular the identification does
not depend on the choice of pointwise groupoid structure that
`CategoryTheory.Deformation.GroupoidInFunctors.pointwiseData` makes: its target subtype is
determined by the source and the target alone. -/
noncomputable def groupoidOfAction_evaluationArrowEquiv (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.Evaluation T) :
    (x ⟶ y) ≃ {r : (G ⊗ X).left.obj T //
        (snd G X).left.app T r = x ∧ γ[G, X].left.app T r = y} :=
  (groupoidOfAction B G X hG hX).groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y


end AlgebraicGeometry.Space
