module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
import Mathlib.CategoryTheory.Filtered.Final
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Limit preservation on objects and local finite presentation (Stacks 06CX)

A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces is limit preserving on objects exactly when it is locally of
finite presentation in the sense of Stacks 03YK, that is when every algebraic space representing
a base change of it along a scheme-valued point of the target has locally finitely presented
structural morphism.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`:
  **Stacks 06CX**.

## Implementation notes

The right-hand side is the relative property of Stacks 03YK,
`AlgebraicGeometry.Stack.HasRelativeProperty`, with local finite presentation of Stacks 03XP for
the property, written out longhand so that no fppf-locality or base-change instance for that
property is needed merely to state the equivalence.

Index categories are taken in the universe of the schemes. That is the size at which both
external inputs are available: the implication from local finite presentation uses the forward
half of Stacks 04AK,
`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`, and the converse
uses the surjective affine-limit criterion of Stacks 0CM6,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, both of which
quantify over cofiltered index categories in that universe.

The source's route through Limits of Spaces, Remark 05N0 and the converse half of Stacks 04AK is
replaced by a change of base scheme for the every-étale-chart condition,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`: local finite presentation
of the structural morphism of an algebraic space over `U`, read over `S` through the forward
functor of Stacks 04SG, is the same condition as over `U` itself. That keeps the proof free of
the scheme-level implication of Stacks 01ZC, which the source's own argument for the converse
half of Stacks 04AK rests on. It is a choice of route and not a way round a gap: the converse
half of Stacks 04AK is proved, unconditionally, as
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`, which is
routed through the same criterion of Stacks 0CM6 that is used here.

The 2-Yoneda translation between objects of the 2-fibre product over a scheme and sections of the
representing algebraic space is carried by the mutually inverse `pointOfObj` and `objectOfPoint`
below: they read an object of the 2-fibre product lying over an object of the site through the
equivalence exhibiting the representing presheaf, using
`CategoryTheory.PresheafOfCategories.objEquiv`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Cat.category StrictBicategory.category
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  Pseudofunctor.CoGrothendieck.forget BasedCategory.ofFunctor
  PresheafOfCategories.objEquiv Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.sliceFunctor TwoFibreProductOver.fst

namespace AlgebraicGeometry.Stack

universe u v w w' z

private def pointOfObj {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x : p.Fiber U) : F.obj (Opposite.op U) := by
  let z := (PresheafOfCategories.objEquiv (F ⋙ typeToCat)) (e.hom.functor.obj x.1)
  have hz : z.1 = U := by
    dsimp [z]
    exact (congrArg (fun (G : P ⥤ C) => G.obj x.1) e.hom.w).trans x.2
  exact hz ▸ z.2.as

private def objectOfPoint {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (a : F.obj (Opposite.op U)) : p.Fiber U := by
  let qObj : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).symm ⟨U, Discrete.mk a⟩
  refine ⟨e.inv.functor.obj qObj, ?_⟩
  have hb : p.obj (e.inv.functor.obj qObj) =
      (presheafOfCategories (F ⋙ typeToCat)).p.obj qObj := by
    simpa only [Functor.comp_obj] using congrArg (fun G : _ ⥤ C => G.obj qObj) e.inv.w
  have hq : (presheafOfCategories (F ⋙ typeToCat)).p.obj qObj = U := by
    change ((PresheafOfCategories.objEquiv (F ⋙ typeToCat)) qObj).1 = U
    rfl
  exact hb.trans hq

private theorem eqToHom_map_apply {C : Type u} [Category.{w, u} C]
    (F : Cᵒᵖ ⥤ Type v) {X Y : C} (h : X = Y) (x : F.obj (Opposite.op Y)) :
    h ▸ F.map (eqToHom h).op x = x := by
  cases h
  simp

private theorem discrete_cast_as {C : Type u} (P : C → Type v) {X Y : C}
    (h : X = Y) (x : P X) :
    (cast (congrArg (fun Z => Discrete (P Z)) h) (Discrete.mk x)).as =
      cast (congrArg P h) x := by
  cases h
  rfl

private theorem cast_eq_transport {C : Sort u} (P : C → Sort v) {X Y : C}
    (h : X = Y) (x : P X) : cast (congrArg P h) x = h ▸ x := by
  cases h
  rfl

private theorem cast_symm_cancel {C : Sort u} (P : C → Sort v) {X Y : C}
    (h : X = Y) (x : P X) : h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl

private theorem pointOfObj_objectOfPoint {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (a : F.obj (Opposite.op U)) :
    pointOfObj (F := F) (p := p) (e := e)
        (objectOfPoint (F := F) (p := p) e a) = a := by
  let qObj : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).symm ⟨U, Discrete.mk a⟩
  let c := e.counitIso.hom.app qObj
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  have hc : q.IsHomLift (𝟙 U) c := e.isHomLift_counitIso_hom_app qObj
  let z := (PresheafOfCategories.objEquiv (F ⋙ typeToCat))
    (e.hom.functor.obj (e.inv.functor.obj qObj))
  have hbaseEq : (e.hom.functor.obj (e.inv.functor.obj qObj)).base = U := by
    simpa only [q, presheafOfCategories, BasedCategory.ofFunctor,
      Pseudofunctor.CoGrothendieck.forget_obj, Functor.comp_obj] using
      (@IsHomLift.domain_eq C _ _ _ q U U
        ((e.inv.functor ⋙ e.hom.functor).obj qObj) qObj (𝟙 U) c hc)
  have hcodEq : q.obj qObj = U := rfl
  have hdom : z.1 = U := by
    change (e.hom.functor.obj (e.inv.functor.obj qObj)).base = U
    exact hbaseEq
  have hfac : c.base = eqToHom hbaseEq ≫ eqToHom hcodEq.symm := by
    simpa only [q, presheafOfCategories, BasedCategory.ofFunctor,
      Pseudofunctor.CoGrothendieck.forget_obj,
      Pseudofunctor.CoGrothendieck.forget_map, Functor.comp_obj,
      Category.id_comp, Category.comp_id] using
      @IsHomLift.fac' C _ _ _ q U U ((e.inv.functor ⋙ e.hom.functor).obj qObj) qObj (𝟙 U) c hc
  have hfib := (PresheafOfCategories.homEquiv (F ⋙ typeToCat)
    (e.hom.functor.obj (e.inv.functor.obj qObj)) qObj c).2
  let aTarget : F.obj (Opposite.op (q.obj qObj)) := qObj.fiber.as
  have hpts₀ :
      (PresheafOfCategories.objEquiv (F ⋙ typeToCat)
        (e.hom.functor.obj (e.inv.functor.obj qObj))).2.as =
      F.map (c.base).op aTarget := by
    dsimp [PresheafOfCategories.homEquiv] at hfib
    exact Discrete.eq_of_hom hfib
  have hcodMap : F.map (eqToHom hcodEq.symm).op aTarget = a := by
    have hcodEq' : hcodEq = rfl := Subsingleton.elim _ _
    rw [hcodEq']
    change F.map (𝟙 (Opposite.op U)) a = a
    simp
  have hbaseEq_dom : hdom = hbaseEq := Subsingleton.elim _ _
  have hpts :
      (PresheafOfCategories.objEquiv (F ⋙ typeToCat)
        (e.hom.functor.obj (e.inv.functor.obj qObj))).2.as =
      F.map (eqToHom hbaseEq).op a := by
    rw [hpts₀, hfac, op_comp, Functor.map_comp]
    change F.map (eqToHom hbaseEq).op
        (F.map (eqToHom hcodEq.symm).op aTarget) = _
    rw [hcodMap]
  calc
    pointOfObj (F := F) (p := p) (e := e)
        (objectOfPoint (F := F) (p := p) e a) = hdom ▸
          (PresheafOfCategories.objEquiv (F ⋙ typeToCat)
            (e.hom.functor.obj (e.inv.functor.obj qObj))).2.as := by
      simp [pointOfObj, objectOfPoint, qObj, z]
    _ = hdom ▸ (F.map (eqToHom hbaseEq).op a) := congrArg (fun x => hdom ▸ x) hpts
    _ = a := by
      rw [hbaseEq_dom]
      exact eqToHom_map_apply F hbaseEq a

private theorem objectOfPoint_pointOfObj_iso {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x : p.Fiber U) :
    Nonempty (objectOfPoint (F := F) (p := p) e
        (pointOfObj (F := F) (p := p) (e := e) x) ≅ x) := by
  rcases x with ⟨x₀, hx₀⟩
  cases hx₀
  let qObj : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).symm
      ⟨p.obj x₀, Discrete.mk (pointOfObj (F := F) (p := p) (e := e)
        (⟨x₀, rfl⟩ : p.Fiber (p.obj x₀)))⟩
  let z := (PresheafOfCategories.objEquiv (F ⋙ typeToCat))
    (e.hom.functor.obj x₀)
  have hz : z.1 = p.obj x₀ := by
    dsimp [z]
    exact congrArg (fun (G : P ⥤ C) => G.obj x₀) e.hom.w
  have hq : qObj = e.hom.functor.obj x₀ := by
    apply (PresheafOfCategories.objEquiv (F ⋙ typeToCat)).injective
    apply Sigma.ext
    · exact hz.symm
    · change HEq (Discrete.mk (hz ▸ z.2.as)) z.2
      let htype := congrArg (fun V : C => Discrete (F.obj (Opposite.op V))) hz
      have hcast : cast htype (Discrete.mk z.2.as) = Discrete.mk (hz ▸ z.2.as) := by
        apply Discrete.ext
        calc
          (cast htype (Discrete.mk z.2.as)).as =
              cast (congrArg (fun V : C => F.obj (Opposite.op V)) hz) z.2.as :=
            discrete_cast_as (fun V : C => F.obj (Opposite.op V)) hz z.2.as
          _ = hz ▸ z.2.as :=
            cast_eq_transport (fun V : C => F.obj (Opposite.op V)) hz z.2.as
      rw [← hcast]
      exact cast_heq htype (Discrete.mk z.2.as)
  subst qObj
  have hf : p.IsHomLift (𝟙 (p.obj x₀)) (e.unitIso.inv.app x₀) :=
    e.isHomLift_unitIso_inv_app x₀
  let x' := objectOfPoint (F := F) (p := p) e
    (pointOfObj (F := F) (p := p) (e := e) ⟨x₀, rfl⟩)
  have hx' : x'.1 = e.inv.functor.obj (e.hom.functor.obj x₀) := by
    dsimp [x', objectOfPoint]
    congr 1
  exact ⟨by
    let f : x'.1 ≅ x₀ := eqToIso hx' ≪≫ e.unitIso.symm.app x₀
    have hfl : p.IsHomLift (𝟙 (p.obj x₀)) f.hom := by
      have hfac := IsHomLift.fac' p (𝟙 (p.obj x₀)) (e.unitIso.inv.app x₀)
      apply IsHomLift.of_fac' p (𝟙 (p.obj x₀)) f.hom x'.2 rfl
      dsimp [f]
      rw [Functor.map_comp, eqToHom_map, hfac]
      simp [eqToHom_trans]
    exact Functor.fiberIsoOfLift p f hfl⟩

private theorem fiberIso_of_point_eq {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x y : p.Fiber U)
    (h : pointOfObj (F := F) (p := p) (e := e) x =
      pointOfObj (F := F) (p := p) (e := e) y) : Nonempty (x ≅ y) := by
  obtain ⟨iA⟩ := objectOfPoint_pointOfObj_iso F p e x
  obtain ⟨iB⟩ := objectOfPoint_pointOfObj_iso F p e y
  exact ⟨iA.symm ≪≫ eqToIso (congrArg (objectOfPoint (F := F) (p := p) e) h) ≪≫ iB⟩

private theorem pointOfObj_map_of_lift {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {V W : C} {x : p.Fiber V} {y : p.Fiber W}
    (f : V ⟶ W) (g : x.1 ⟶ y.1) (hg : p.IsHomLift f g) :
    pointOfObj (F := F) (p := p) (e := e) x =
      F.map f.op (pointOfObj (F := F) (p := p) (e := e) y) := by
  let zx := (PresheafOfCategories.objEquiv (F ⋙ typeToCat))
    (e.hom.functor.obj x.1)
  let zy := (PresheafOfCategories.objEquiv (F ⋙ typeToCat))
    (e.hom.functor.obj y.1)
  have hx : zx.1 = V := by
    dsimp [zx]
    exact (congrArg (fun H : P ⥤ C => H.obj x.1) e.hom.w).trans x.2
  have hy : zy.1 = W := by
    dsimp [zy]
    exact (congrArg (fun H : P ⥤ C => H.obj y.1) e.hom.w).trans y.2
  have hq : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift f
      (e.hom.functor.map g) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w f g
  have hmap : (e.hom.functor.map g).base =
      eqToHom hx ≫ f ≫ eqToHom hy.symm := by
    have h₁ := IsHomLift.domain_eq (presheafOfCategories (F ⋙ typeToCat)).p
      f (e.hom.functor.map g)
    have h₂ := IsHomLift.codomain_eq (presheafOfCategories (F ⋙ typeToCat)).p
      f (e.hom.functor.map g)
    have h := IsHomLift.fac' (presheafOfCategories (F ⋙ typeToCat)).p f
      (e.hom.functor.map g)
    change (e.hom.functor.map g).base = _ at h
    simpa [h₁, h₂, Category.assoc] using h
  have hval := (PresheafOfCategories.homEquiv (F ⋙ typeToCat)
    (e.hom.functor.obj x.1) (e.hom.functor.obj y.1) (e.hom.functor.map g)).2
  dsimp [PresheafOfCategories.homEquiv] at hval
  have hval'' : zx.2.as = F.map (eqToHom hx ≫ f ≫ eqToHom hy.symm).op zy.2.as := by
    rw [← hmap]
    exact Discrete.eq_of_hom hval
  have hcomp : F.map (eqToHom hx ≫ f ≫ eqToHom hy.symm).op zy.2.as =
      F.map (eqToHom hx).op
        (F.map f.op (F.map (eqToHom hy.symm).op zy.2.as)) := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have htransport := congrArg (fun z => hy ▸ z) (eqToHom_map_apply F hy.symm zy.2.as)
  change hx ▸ zx.2.as = F.map f.op (hy ▸ zy.2.as)
  calc
    hx ▸ zx.2.as = hx ▸ F.map (eqToHom hx).op
        (F.map f.op (F.map (eqToHom hy.symm).op zy.2.as)) := by
      congr 1
      rw [hval'', hcomp]
    _ = F.map f.op (F.map (eqToHom hy.symm).op zy.2.as) :=
      eqToHom_map_apply F hx _
    _ = F.map f.op (hy ▸ zy.2.as) := by
      congr 1
      calc
        F.map (eqToHom hy.symm).op zy.2.as =
            hy ▸ (hy.symm ▸ F.map (eqToHom hy.symm).op zy.2.as) :=
          (cast_symm_cancel (fun V : C => F.obj (Opposite.op V)) hy.symm _).symm
        _ = hy ▸ zy.2.as := htransport

private theorem exists_homLift_of_point_eq {C : Type u} [Category.{w, u} C]
    {P : Type v} [Category.{w', v} P] (F : Cᵒᵖ ⥤ Type z)
    (p : P ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {V W : C} (x : p.Fiber V) (y : p.Fiber W) (f : V ⟶ W)
    (h : pointOfObj F p e x = F.map f.op (pointOfObj F p e y)) :
    ∃ g : x.1 ⟶ y.1, p.IsHomLift f g := by
  have hq : (presheafOfCategories (F ⋙ typeToCat)).p.IsFiberedInGroupoids := by
    apply Functor.IsFiberedInGroupoids.mk'
    intro U
    have : IsGroupoid ((F ⋙ typeToCat).toPseudofunctor'.obj ⟨Opposite.op U⟩) :=
      inferInstanceAs (IsGroupoid (Discrete (F.obj (Opposite.op U))))
    exact isGroupoid_of_reflects_iso
      (Functor.Fiber.inducedFunctor
        (Pseudofunctor.CoGrothendieck.comp_const
          (F ⋙ typeToCat).toPseudofunctor' U)).asEquivalence.inverse
  have hp : p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e hq
  obtain ⟨x', g, hg⟩ := hp.exists_lift f y.1 y.2
  let xf : p.Fiber V := ⟨x', IsHomLift.domain_eq p f g⟩
  have hx : pointOfObj F p e xf = pointOfObj F p e x :=
    (pointOfObj_map_of_lift F p e f g hg).trans h.symm
  obtain ⟨α⟩ := fiberIso_of_point_eq F p e x xf hx.symm
  have hα : p.IsHomLift (𝟙 V) α.hom.1 := α.hom.2
  refine ⟨α.hom.1 ≫ g, ?_⟩
  simpa using (inferInstance : p.IsHomLift (𝟙 V ≫ f) (α.hom.1 ≫ g))

/-- View an object over `U.left` as an object over `U` in the slice category.
This is the canonical functor from the site over a base object to the slice of
the site over its base. -/
@[implicit_reducible]
private def nestedOverObject {C : Type u} [Category.{w, u} C]
    {S : C} (U : Over S) (X : Over U.left) : Over U := by
  let W : Over S := Over.mk (X.hom ≫ U.hom)
  let h : W ⟶ U := by
    refine Over.homMk (U := W) (V := U) X.hom ?_
    change X.hom ≫ U.hom = W.hom
    rfl
  exact Over.mk h

@[implicit_reducible]
private def nestedOverToOver {C : Type u} [Category.{w, u} C]
    {S : C} (U : Over S) : Over U.left ⥤ Over U where
  obj X := nestedOverObject U X
  map {X Y} f := by
    let WX : Over S := Over.mk (X.hom ≫ U.hom)
    let WY : Over S := Over.mk (Y.hom ≫ U.hom)
    let g : WX ⟶ WY := by
      refine Over.homMk (U := WX) (V := WY) f.left ?_
      change f.left ≫ (Y.hom ≫ U.hom) = X.hom ≫ U.hom
      rw [← Category.assoc, f.w]
    refine Over.homMk (U := nestedOverObject U X)
      (V := nestedOverObject U Y) g ?_
    apply Over.OverMorphism.ext
    change f.left ≫ Y.hom = X.hom
    exact f.w
  map_id X := by
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    rfl
  map_comp {X Y Z} f g := by
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    rfl

/-- The functor from the slice over the underlying scheme of `U` to the site
over `S`, followed by forgetting to schemes, is just the usual forgetful
functor from that slice. -/
private theorem nestedSlice_toScheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    nestedOverToOver U ⋙ Over.forget U ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS =
      Over.forget U.left ⋙ B.inclusion :=
  rfl

/-- Re-index a diagram in the slice over the underlying scheme of `U` as a
diagram of affine objects over `S`.  Affineness of the cone point and the
stage objects is inherited from their underlying schemes. -/
@[implicit_reducible]
private noncomputable def nestedSliceAffineDiagram
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    {I : Type v} [Category.{w, v} I]
    (D : I ⥤ Over U.left)
    (hD : ∀ i, IsAffine
      ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i))) :
    I ⥤ AlgebraicGeometry.BigAffineFppf B S hS :=
  ObjectProperty.lift (AlgebraicGeometry.IsAffineOver B S hS)
    (D ⋙ nestedOverToOver U ⋙ Over.forget U) hD

/-- Lift a cone in the nested slice to the full subcategory of affine
objects. -/
@[implicit_reducible]
private noncomputable def nestedSliceAffineCone
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    {I : Type v} [Category.{w, v} I]
    (D : I ⥤ Over U.left) (c : Cone D)
    (hD : ∀ i, IsAffine
      ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i)))
    (hc : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c.pt)) :
    Cone (nestedSliceAffineDiagram B S hS U D hD) := by
  let E := nestedOverToOver U ⋙ Over.forget U
  let P := AlgebraicGeometry.IsAffineOver B S hS
  let pt : P.FullSubcategory := ⟨E.obj c.pt, by
    change IsAffine
      ((nestedOverToOver U ⋙ Over.forget U ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj c.pt)
    rw [nestedSlice_toScheme B S hS U]
    exact hc⟩
  refine { pt := pt, π := ?_ }
  refine { app := fun i => P.homMk (E.map (c.π.app i)), naturality := ?_ }
  intro i j f
  apply P.hom_ext
  change E.map (c.π.app j) =
    E.map (c.π.app i) ≫ E.map (D.map f)
  rw [← E.map_comp, c.w f]

/-- The affine diagram obtained from a nested slice diagram has the same
scheme-level cone as the original diagram. -/
private noncomputable def nestedSliceAffineDiagram_mapCone
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    {I : Type v} [Category.{w, v} I]
    (D : I ⥤ Over U.left) (c : Cone D)
    (hD : ∀ i, IsAffine
      ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i)))
    (hlim : IsLimit ((Over.forget U.left ⋙ B.inclusion).mapCone c))
    (hc : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c.pt)) :
    IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone
      (nestedSliceAffineCone B S hS U D c hD hc)) := by
  let P := AlgebraicGeometry.IsAffineOver B S hS
  let E := nestedOverToOver U ⋙ Over.forget U
  let c' := nestedSliceAffineCone B S hS U D c hD hc
  have hEq : E ⋙ Over.forget (B.obj hS) ⋙ B.inclusion =
      Over.forget U.left ⋙ B.inclusion := by
    change nestedOverToOver U ⋙ Over.forget U ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS = _
    exact nestedSlice_toScheme B S hS U
  have hlimComp : IsLimit
      ((E ⋙ Over.forget (B.obj hS) ⋙ B.inclusion).mapCone c) := by
    rw [hEq]
    exact hlim
  have hlim' : IsLimit
      ((Over.forget (B.obj hS) ⋙ B.inclusion).mapCone (E.mapCone c)) :=
    IsLimit.ofIsoLimit hlimComp (Functor.mapConeMapCone c).symm
  have hcone : (Over.forget (B.obj hS) ⋙ B.inclusion).mapCone
      (E.mapCone c) ≅
      ((P.ι ⋙ Over.forget (B.obj hS) ⋙ B.inclusion).mapCone c') := by
    refine Cone.ext (Iso.refl _) ?_
    intro i
    simp [c', nestedSliceAffineCone, nestedSliceAffineDiagram, P, E]
  have hlimScheme : IsLimit
      ((P.ι ⋙ Over.forget (B.obj hS) ⋙ B.inclusion).mapCone c') :=
    IsLimit.ofIsoLimit hlim' hcone.symm
  simpa [AlgebraicGeometry.BigAffineFppf.toScheme] using hlimScheme

/-- Two strongly Cartesian arrows over the same base arrow have isomorphic domains, by an
isomorphism lying over the identity and compatible with the arrows. -/
private theorem exists_iso_isHomLift_id_comp_eq {C : Type u} [Category.{w} C]
    {D : Type v} [Category.{w'} D] (p : D ⥤ C) {R T : C} {f : R ⟶ T} {a a' b : D}
    (φ : a ⟶ b) (φ' : a' ⟶ b) [p.IsStronglyCartesian f φ] [p.IsStronglyCartesian f φ'] :
    ∃ η : a' ≅ a, p.IsHomLift (𝟙 R) η.hom ∧ η.hom ≫ φ = φ' := by
  have hf : f = (Iso.refl R).hom ≫ f := by simp
  exact ⟨Functor.IsStronglyCartesian.domainIsoOfBaseIso p hf φ φ',
    Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p hf φ φ',
    Functor.IsStronglyCartesian.fac p f φ hf φ'⟩

section

open CategoryTheory.Functor

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {X : Type u₃} [Category.{v₃} X] {Y : Type u₄} [Category.{v₄} Y]

/-- A compatible comparison at a stage produces a morphism to the corresponding
object of the two-fibre product. -/
private theorem exists_twoFibreProduct_morphism
    (q : D ⥤ C) (pX : X ⥤ C) (pY : Y ⥤ C) (G : D ⥤ Y) (H : X ⥤ Y)
    (hG : G ⋙ pY = q) (hH : H ⋙ pY = pX) (hY : pY.IsFiberedInGroupoids)
    (z : TwoFibreProductOver q pX pY G H)
    {W T : D} (f : z.x ⟶ W) (j : W ⟶ T)
    (x' : pX.Fiber (q.obj W)) (b : z.y ⟶ x'.1)
    (hb : pX.IsHomLift (q.map f) b)
    (γ : H.obj x'.1 ⟶ G.obj T) (hγ : pY.IsHomLift (q.map j) γ)
    (hsq : H.map b ≫ γ = z.iso.inv ≫ G.map (f ≫ j)) :
    ∃ (z' : TwoFibreProductOver q pX pY G H) (a : z ⟶ z'),
      ∃ hx : z'.x = W, z'.y = x'.1 ∧ a.a = f ≫ eqToHom hx.symm := by
  have hg : pY.IsHomLift (q.map j) (G.map j) :=
    Functor.isHomLift_map_of_comp_eq hG (q.map j) j
  have : pY.IsStronglyCartesian (q.map j) γ :=
    hY.isStronglyCartesian_homLift (q.map j) γ
  have : pY.IsStronglyCartesian (q.map j) (G.map j) :=
    hY.isStronglyCartesian_homLift (q.map j) (G.map j)
  obtain ⟨η, hη, hηfac⟩ := exists_iso_isHomLift_id_comp_eq pY (f := q.map j) γ (G.map j)
  let z' : TwoFibreProductOver q pX pY G H :=
    ⟨q.obj W, W, x'.1, rfl, x'.2, η, hη⟩
  have hbase : z.base = q.obj z.x := z.hx.symm
  have hHb : pY.IsHomLift (q.map f) (H.map b) :=
    Functor.isHomLift_map_of_comp_eq hH (q.map f) b
  have hz : pY.IsHomLift (𝟙 (q.obj z.x)) z.iso.hom := by
    rw [← hbase]
    exact z.vertical
  have hGf : pY.IsHomLift (q.map f) (G.map f) :=
    Functor.isHomLift_map_of_comp_eq hG (q.map f) f
  have hw : G.map f ≫ η.hom = z.iso.hom ≫ H.map b := by
    apply IsStronglyCartesian.ext pY (q.map j) γ (q.map f)
    simp only [Category.assoc, hηfac, hsq, Iso.hom_inv_id_assoc, Functor.map_comp]
  let a : z ⟶ z' := TwoFibreProductOver.Hom.mk' f b (by
    rw [IsHomLift.fac' pX (q.map f) b]
    simp [z']) hw
  exact ⟨z', a, rfl, rfl, by simp [a]⟩

end

section

open Opposite

private lemma over_map_apply_heq {C : Type*} [Category C] {U V W : C}
    (F : (Over U)ᵒᵖ ⥤ Type u) {a a' : V ⟶ U} {b : W ⟶ U}
    (f : V ⟶ W) (h : f ≫ b = a) (h' : f ≫ b = a')
    (t : F.obj (op (Over.mk b))) :
    HEq (F.map (Over.homMk f h : Over.mk a ⟶ Over.mk b).op t)
      (F.map (Over.homMk f h' : Over.mk a' ⟶ Over.mk b).op t) := by
  have he : a = a' := h.symm.trans h'
  cases he
  rfl

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicGeometry.BigFppfOver B S hS)
  (F : (AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
  (X : AlgebraicGeometry.SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom)
  (ι : X.1.left ≅ (OverShriek.relocalizePresheafFunctor U.hom).obj F)
  (hι : ∀ W t, X.1.hom.app W (ι.inv.app W t) = Over.homMk t.1.1 t.2)

private def sectionPoint {V : AlgebraicGeometry.BigFppfOver B S hS} (a : V ⟶ U)
    (t : F.obj (op (Over.mk a.left))) : X.1.left.obj (op V) :=
  ι.inv.app (op V) ⟨⟨a.left, t⟩, a.w⟩

private lemma sectionPoint_injective {V : AlgebraicGeometry.BigFppfOver B S hS} (a : V ⟶ U) :
    Function.Injective (sectionPoint B S hS U F X ι a) := by
  intro s t h
  have hh := (ConcreteCategory.bijective_of_isIso (ι.inv.app (op V))).1 h
  have hh' := congrArg Subtype.val hh
  exact eq_of_heq (Sigma.mk.inj hh').2

include hι in
private lemma sectionPoint_surjective {V : AlgebraicGeometry.BigFppfOver B S hS} (a : V ⟶ U)
    (s : X.1.left.obj (op V)) (hs : X.1.hom.app (op V) s = a) :
    ∃ t, sectionPoint B S hS U F X ι a t = s := by
  let r := ι.hom.app (op V) s
  have hr : X.1.hom.app (op V) s = Over.homMk r.1.1 r.2 := by
    simpa [r] using hι (op V) r
  have heq : r.1.1 = a.left := congrArg Over.Hom.left (hr.symm.trans hs)
  have herr : ∃ t : F.obj (op (Over.mk a.left)),
      r = (⟨⟨a.left, t⟩, a.w⟩ :
        ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (op V)) := by
    rcases r with ⟨⟨b,t⟩,hb⟩
    dsimp at heq
    subst b
    exact ⟨t, rfl⟩
  obtain ⟨t, ht⟩ := herr
  refine ⟨t, ?_⟩
  dsimp [sectionPoint]
  rw [← ht]
  simp [r]

private noncomputable def sectionPointEquiv {V : AlgebraicGeometry.BigFppfOver B S hS} (a : V ⟶ U) :
    F.obj (op (Over.mk a.left)) ≃
      {s : X.1.left.obj (op V) // X.1.hom.app (op V) s = a} := by
  refine Equiv.ofBijective (fun t => ⟨sectionPoint B S hS U F X ι a t, ?_⟩) ⟨?_, ?_⟩
  · exact hι (op V) _
  · intro t s h
    exact sectionPoint_injective B S hS U F X ι a (congrArg Subtype.val h)
  · rintro ⟨s,hs⟩
    obtain ⟨t, ht⟩ := sectionPoint_surjective B S hS U F X ι hι a s hs
    exact ⟨t, Subtype.ext ht⟩

private noncomputable def sectionFiberIso (V : AlgebraicGeometry.BigFppfOver B S hS) (a : V ⟶ U) :
    (Over.post (AlgebraicGeometry.BigFppfOver.forget B S hS) ⋙ Over.map a.left).op ⋙ F ≅
      AlgebraicGeometry.sectionFiber B S hS X.1.hom V a :=
  NatIso.ofComponents (fun W => (sectionPointEquiv B S hS U F X ι hι
    (W.unop.hom ≫ a)).toIso) (by
      intro W Z f
      ext t
      apply Subtype.ext
      change ι.inv.app (op Z.unop.left)
        ⟨⟨(Z.unop.hom ≫ a).left, F.map
          ((Over.map a.left).map
            ((Over.post (AlgebraicGeometry.BigFppfOver.forget B S hS)).map f.unop)).op t⟩,
          (Z.unop.hom ≫ a).w⟩ =
        X.1.left.map f.unop.left.op (ι.inv.app (op W.unop.left)
          ⟨⟨(W.unop.hom ≫ a).left, t⟩, (W.unop.hom ≫ a).w⟩)
      have h := NatTrans.naturality_apply ι.inv f.unop.left.op
        (⟨⟨(W.unop.hom ≫ a).left, t⟩, (W.unop.hom ≫ a).w⟩ :
          ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (op W.unop.left))
      rw [← h]
      congr 1
      apply Subtype.ext
      apply Sigma.ext
      · change Z.unop.hom.left ≫ a.left = f.unop.left.left ≫ (W.unop.hom.left ≫ a.left)
        have hw := congrArg Over.Hom.left (Over.w f.unop)
        simpa only [Over.comp_left, Category.assoc] using congrArg (· ≫ a.left) hw.symm
      · refine over_map_apply_heq F f.unop.left.left ?_ rfl t
        change f.unop.left.left ≫ (W.unop.hom.left ≫ a.left) = Z.unop.hom.left ≫ a.left
        simpa only [Over.comp_left, Category.assoc] using
          congrArg (· ≫ a.left) (congrArg Over.Hom.left f.unop.w))
include hι in
/-- The sections of `F` over a cofiltered system of affines in the slice over `U` form a colimit
diagram over the sections at the limit, once the structural morphism of the representing space is
relatively limit preserving. Both halves of the descent -- surjectivity and injectivity -- are
read off this one colimit. -/
private theorem nonempty_isColimit_of_relativelyLimitPreserving
    (hrel : AlgebraicGeometry.RelativelyLimitPreserving.{u, u, max u v w, max u w} B S hS X.1.hom)
    {I : Type (max u v w)} [Category.{max u w} I] [IsCofiltered I]
    (D : I ⥤ Over U.left) (c : Cone D)
    (hc : IsLimit ((Over.forget U.left ⋙ B.inclusion).mapCone c))
    (hD : ∀ i, IsAffine ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i)))
    (hpt : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c.pt)) :
    Nonempty (IsColimit (F.mapCocone c.op)) := by
  let E := nestedOverToOver U
  let R := Over.post (AlgebraicGeometry.BigFppfOver.forget B S hS) ⋙ Over.map (𝟙 U.left)
  let Q := AlgebraicGeometry.sectionFiber B S hS X.1.hom U (𝟙 U)
  have hER : E ⋙ R = 𝟭 (Over U.left) := by
    refine CategoryTheory.Functor.ext (fun W => ?_) ?_
    · change Over.mk (W.hom ≫ 𝟙 U.left) = W
      simp only [Category.comp_id]
      rfl
    · intro W W' f
      apply Over.OverMorphism.ext
      simp [E, R, nestedOverToOver, nestedOverObject]
  have hFR : E.op ⋙ R.op ⋙ F = F := by
    change (E ⋙ R).op ⋙ F = F
    rw [hER]
    rfl
  let e : F ≅ E.op ⋙ Q := eqToIso hFR.symm ≪≫
    Functor.isoWhiskerLeft E.op (sectionFiberIso B S hS U F X ι hι U (𝟙 U))
  have he : E ⋙ Over.forget U ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS =
      Over.forget U.left ⋙ B.inclusion := nestedSlice_toScheme B S hS U
  have hc' : IsLimit ((Over.forget U ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      (E.mapCone c)) := by
    apply IsLimit.ofIsoLimit _ (Functor.mapConeMapCone c).symm
    rw [he]
    exact hc
  obtain ⟨hq⟩ := hrel U (𝟙 U) I (D ⋙ E) (E.mapCone c) hc' hD hpt
  have hq' : IsColimit ((E.op ⋙ Q).mapCocone c.op) :=
    IsColimit.ofIsoColimit hq
      ((Cocone.functoriality _ Q).mapIso (Functor.mapConeOp E c) ≪≫
        Functor.mapCoconeMapCocone c.op)
  exact ⟨IsColimit.mapCoconeEquiv e.symm hq'⟩

include hι in
private theorem exists_stage_of_relativelyLimitPreserving
    (hrel : AlgebraicGeometry.RelativelyLimitPreserving.{u, u, max u v w, max u w} B S hS X.1.hom)
    {I : Type (max u v w)} [Category.{max u w} I] [IsCofiltered I]
    (D : I ⥤ Over U.left) (c : Cone D)
    (hc : IsLimit ((Over.forget U.left ⋙ B.inclusion).mapCone c))
    (hD : ∀ i, IsAffine ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i)))
    (hpt : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c.pt))
    (t : F.obj (op c.pt)) :
    ∃ (i : I) (s : F.obj (op (D.obj i))), F.map (c.π.app i).op s = t := by
  obtain ⟨hq⟩ := nonempty_isColimit_of_relativelyLimitPreserving.{u, v, w} B S hS U F X ι hι hrel
    D c hc hD hpt
  obtain ⟨i, s, hs⟩ := Types.jointly_surjective _ hq t
  exact ⟨i.unop, s, hs⟩

end

private theorem exists_stage_of_limitPreservingOnObjects
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids (AlgebraicGeometry.BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴)
    (hlim : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, max u v w, max u w}
      B S hS 𝒳 𝒴 p)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (y : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor p))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {I : Type (max u v w)} [Category.{max u w} I] [IsCofiltered I]
    (D₀ : I ⥤ Over U.left) (c₀ : Cone D₀)
    (hc₀ : IsLimit ((Over.forget U.left ⋙ B.inclusion).mapCone c₀))
    (hAffine₀ : ∀ i, IsAffine ((Over.forget U.left ⋙ B.inclusion).obj (D₀.obj i)))
    (hAffinePt₀ : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c₀.pt))
    (t : F.obj (Opposite.op c₀.pt)) :
    ∃ (i : I) (t' : F.obj (Opposite.op (D₀.obj i))), F.map (c₀.π.app i).op t' = t := by
  classical
  let Daff := nestedSliceAffineDiagram B S hS U D₀ hAffine₀
  let caff := nestedSliceAffineCone B S hS U D₀ c₀ hAffine₀ hAffinePt₀
  have hcaff := nestedSliceAffineDiagram_mapCone B S hS U D₀ c₀
    hAffine₀ hc₀ hAffinePt₀
  let z₀ := objectOfPoint (F := F) (p :=
    TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor p)) e t
  let i₀ : I := Classical.choice (IsCofiltered.nonempty : Nonempty I)
  let T := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  have hzbase : z₀.1.base = (Over.map U.hom).obj z₀.1.x := z₀.1.hx.symm
  have hxobj : z₀.1.x = c₀.pt := by
    simpa [TwoFibreProductOver.fst] using z₀.2
  have hbase : z₀.1.base = T.obj caff.pt := by
    rw [hzbase, hxobj]
    rfl
  have hx₀ : 𝒳.val.p.obj z₀.1.y = T.obj caff.pt := z₀.1.hy.trans hbase
  have hyᵢ : 𝒴.val.p.obj (y.obj (D₀.obj i₀)) = T.obj (Daff.obj i₀) := by
    have hh := congrArg (fun g : _ ⥤ _ => g.obj (D₀.obj i₀)) hy
    have hd : (Over.map U.hom).obj (D₀.obj i₀) = T.obj (Daff.obj i₀) := by
      rfl
    simpa [Functor.comp_obj] using hh.trans hd
  let x₀ : 𝒳.val.p.Fiber (T.obj caff.pt) := ⟨z₀.1.y, hx₀⟩
  let yᵢ : 𝒴.val.p.Fiber (T.obj (Daff.obj i₀)) :=
    ⟨y.obj (D₀.obj i₀), hyᵢ⟩
  let leg := c₀.π.app i₀
  let leg' := eqToHom hxobj ≫ leg
  let gamma : (CatFiberedInGroupoids.homFunctor p).obj x₀.1 ⟶ yᵢ.1 :=
    z₀.1.iso.inv ≫ y.map leg'
  let gbase := T.map (caff.π.app i₀)
  have hyMap : 𝒴.val.p.IsHomLift ((Over.map U.hom).map leg') (y.map leg') :=
    Functor.isHomLift_map_of_comp_eq hy ((Over.map U.hom).map leg') leg'
  have : 𝒴.val.p.IsHomLift (𝟙 z₀.1.base) z₀.1.iso.hom := z₀.1.vertical
  have hIsoInv : 𝒴.val.p.IsHomLift (𝟙 z₀.1.base) z₀.1.iso.inv :=
    IsHomLift.lift_id_inv 𝒴.val.p z₀.1.base z₀.1.iso
  have hMap' : 𝒴.val.p.IsHomLift
      (eqToHom z₀.1.hx.symm ≫ (Over.map U.hom).map leg') (y.map leg') := by
    infer_instance
  have hbaseMap : eqToHom hbase ≫ gbase =
      eqToHom z₀.1.hx.symm ≫ (Over.map U.hom).map leg' := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    dsimp [gbase, leg', leg, T, caff, Daff,
      nestedSliceAffineCone, nestedSliceAffineDiagram,
      nestedOverToOver, nestedOverObject]
    simp
  have hgamma : 𝒴.val.p.IsHomLift gbase gamma := by
    have h2 : 𝒴.val.p.IsHomLift (eqToHom hbase ≫ gbase) (y.map leg') := by
      rw [hbaseMap]
      exact hMap'
    have h3 : 𝒴.val.p.IsHomLift gbase (y.map leg') :=
      (IsHomLift.lift_eqToHom_comp_iff 𝒴.val.p gbase (y.map leg') hbase).1 h2
    change 𝒴.val.p.IsHomLift gbase (z₀.1.iso.inv ≫ y.map leg')
    exact IsHomLift.comp_lift_id_left' 𝒴.val.p z₀.1.base z₀.1.iso.inv gbase (y.map leg')
  have hgammaSC : 𝒴.val.p.IsStronglyCartesian gbase gamma :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift gbase gamma
  rcases hlim I Daff caff hcaff i₀ yᵢ x₀ gamma hgammaSC with
    ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hsq⟩
  let b : z₀.1.y ⟶ x'.1 := inv β ≫ δ
  let f₀ : z₀.1.x ⟶ D₀.obj i' := eqToHom hxobj ≫ c₀.π.app i'
  have hb : 𝒳.val.p.IsHomLift ((Over.map U.hom).map f₀) b := by
    have : 𝒳.val.p.IsHomLift (𝟙 (T.obj caff.pt)) (asIso β).hom := hβ
    have hβinv : 𝒳.val.p.IsHomLift (𝟙 (T.obj caff.pt)) (inv β) :=
      IsHomLift.lift_id_inv 𝒳.val.p (T.obj caff.pt) (asIso β)
    have hb' : 𝒳.val.p.IsHomLift (T.map (caff.π.app i')) b := by
      have hh : 𝒳.val.p.IsHomLift
          (𝟙 (T.obj caff.pt) ≫ T.map (caff.π.app i')) b := inferInstance
      simpa using hh
    have hf : (Over.map U.hom).map f₀ =
        eqToHom (congrArg (Over.map U.hom).obj hxobj) ≫ T.map (caff.π.app i') := by
      simp only [f₀, Functor.map_comp, eqToHom_map]
      rfl
    rw [hf]
    exact (IsHomLift.lift_eqToHom_comp_iff 𝒳.val.p (T.map (caff.π.app i')) b
      (congrArg (Over.map U.hom).obj hxobj)).2 hb'
  have hg : 𝒴.val.p.IsHomLift ((Over.map U.hom).map (D₀.map j)) γ' :=
    hγ'.toIsHomLift
  have hsquare : (CatFiberedInGroupoids.homFunctor p).map b ≫ γ' =
      z₀.1.iso.inv ≫ y.map (f₀ ≫ D₀.map j) := by
    dsimp [b]
    rw [Functor.map_comp, Category.assoc, hsq]
    simp only [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
    dsimp [gamma, f₀, leg', leg]
    rw [Category.assoc, c₀.w j]
    simp
  obtain ⟨z', a', hz', _, ha'⟩ := exists_twoFibreProduct_morphism
    (Over.map U.hom) 𝒳.val.p 𝒴.val.p y (CatFiberedInGroupoids.homFunctor p)
    hy p.hom.w 𝒴.isFiberedInGroupoids z₀.1 f₀ (D₀.map j)
    x' b hb γ' hg hsquare
  let zf : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor p)).Fiber (D₀.obj i') := ⟨z', hz'⟩
  refine ⟨i', pointOfObj F _ e zf, ?_⟩
  have ha : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor p)).IsHomLift (c₀.π.app i') a' := by
    apply IsHomLift.of_fac' _ _ _ hxobj hz'
    simpa [f₀, Category.assoc] using ha'
  rw [← pointOfObj_map_of_lift F _ e (c₀.π.app i') a' ha]
  exact pointOfObj_objectOfPoint F _ e t

@[implicit_reducible]
private def stageCone {C : Type u} [Category.{w} C] {S : C}
    {I : Type v} [Category.{w'} I] (D : I ⥤ Over S) (c : Cone D) (i : I) :
    Cone (Over.post D ⋙ Over.post (Over.forget S) : Over i ⥤ Over (D.obj i).left) where
  pt := Over.mk (c.π.app i).left
  π := {
    app j := Over.homMk (c.π.app j.left).left (congrArg Over.Hom.left (c.w j.hom))
    naturality := by
      intro j k f
      apply Over.OverMorphism.ext
      change 𝟙 _ ≫ (c.π.app k.left).left = (c.π.app j.left).left ≫ (D.map f.left).left
      simpa only [Category.id_comp, Over.comp_left] using
        (congrArg Over.Hom.left (c.w f.left)).symm }

private noncomputable def stageCone_isLimit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ AlgebraicGeometry.BigFppfOver B S hS) (c : Cone D) (i : I)
    (hc : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((Over.forget (D.obj i).left ⋙ B.inclusion).mapCone (stageCone D c i)) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have h := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (T.mapCone c)).symm hc
  exact IsLimit.ofIsoLimit h (Cone.ext (Iso.refl _) (fun j => by simp [T, stageCone]))

/-! ### The two external inputs, read at the shape this proof needs -/

/-- A filtered colimit of subsingletons is a subsingleton. -/
private theorem subsingleton_colimit_of_subsingleton {J : Type u} [Category.{u} J] [IsFiltered J]
    (K : J ⥤ Type u) (h : ∀ j, Subsingleton (K.obj j)) : Subsingleton (colimit K) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective' a
  obtain ⟨k, y, hy⟩ := Types.jointly_surjective' b
  rw [← hx, ← hy, ← colimit.w_apply K (IsFiltered.leftToMax j k) x,
    ← colimit.w_apply K (IsFiltered.rightToMax j k) y]
  exact congrArg _ ((h _).elim _ _)

/-- **Local finite presentation of the structural morphism of an algebraic space over `U`, read
over `S`, is the same condition as over `U` itself.** The every-étale-chart condition of
Stacks 03MJ for the image of the forward functor of Stacks 04SG does not see the base. -/
private theorem holdsOnEveryEtaleChart_spacesOverSmallerBase_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (W S : Scheme.{u})
    (hW : B.Contains W) (hS : B.Contains S) (h : B.obj hW ⟶ B.obj hS)
    (P : MorphismProperty Scheme.{u})
    (F : (AlgebraicGeometry.BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B W hW F) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P
        (((AlgebraicGeometry.spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) ↔
      AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B W hW P
        (AlgebraicGeometry.Space.toYonedaId B W hW F) := by
  rw [← AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P
      ((AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app
        ⟨F, hF⟩) _,
    AlgebraicGeometry.Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩]
  exact AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S hW hS h P F

/-! ### Stacks 06CX -/

/-- **Stacks 06CX.** A 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces is limit preserving on objects exactly when it is
locally of finite presentation in the sense of Stacks 03YK: every algebraic space representing a
base change of it along a scheme-valued point of the target has locally finitely presented
structural morphism. -/
@[stacks 06CX "index categories in the universe of the schemes"]
theorem isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids (AlgebraicGeometry.BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴)
    (hp : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom) :
    AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 p ↔
      ∀ (U : AlgebraicGeometry.BigFppfOver B S hS)
        (y : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor p))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS
          (AlgebraicGeometry.algebraicSpaceMap B S hS U
            ((AlgebraicGeometry.spacesOverSmallerBaseFunctor
              B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  constructor
  · intro hlim U y hy F hF ⟨e⟩
    have hfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B U.left.1 U.left.2
        (AlgebraicGeometry.Space.toYonedaId B U.left.1 U.left.2 F) := by
      apply AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective
        B U.left.1 U.left.2 hF
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
      intro I _ _ D c hc hD hpt t t' _
      obtain ⟨i, s, hs⟩ := exists_stage_of_limitPreservingOnObjects.{u, u, u}
        B S hS 𝒳 𝒴 p hlim U y hy F e D c hc hD hpt t
      refine ⟨colimit.ι (D.op ⋙ F) (Opposite.op i) s, ?_, ?_⟩
      · simpa using hs
      · refine (subsingleton_colimit_of_subsingleton _ (fun j => ⟨fun f g => ?_⟩)).elim _ _
        refine Over.OverMorphism.ext ?_
        have hf : Over.Hom.left f = (D.obj j.unop).hom := by simpa using Over.w f
        have hg : Over.Hom.left g = (D.obj j.unop).hom := by simpa using Over.w g
        rw [hf, hg]
    exact (holdsOnEveryEtaleChart_spacesOverSmallerBase_iff B U.left.1 S U.left.2 hS U.hom
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) F hF).2 hfp
  · intro hlp I _ _ D c hc i yi x γ hγ
    have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
    let T := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
    let Ds := D ⋙ T
    let cs := T.mapCone c
    let U := Ds.obj i
    let q := Over.map U.hom
    let cy := 𝒴.val.p.chosenPullbacks
    let E := nestedOverToOver U
    let y := E ⋙ cy.sliceFunctor yi
    have hy : y ⋙ 𝒴.val.p = q := by
      change E ⋙ cy.sliceFunctor yi ⋙ 𝒴.val.p = q
      rw [Functor.ChoiceOfPullbacks.sliceFunctor_comp]
      rfl
    obtain ⟨F, hF, ⟨e⟩⟩ := hp U y hy
    let X := (AlgebraicGeometry.spacesOverSmallerBaseFunctor
      B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
    have hrel : AlgebraicGeometry.RelativelyLimitPreserving.{u, u, u, u} B S hS X.1.hom :=
      AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS
        X.property (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Over.mk U.hom))
        (hlp U y hy F hF ⟨e⟩)
    let D₀ : Over i ⥤ Over U.left :=
      Over.post Ds ⋙ Over.post (AlgebraicGeometry.BigFppfOver.forget B S hS)
    let c₀ := stageCone Ds cs i
    have hc₀ := stageCone_isLimit B S hS Ds cs i
      (IsLimit.ofIsoLimit hc (Functor.mapConeMapCone c).symm)
    have hD₀ : ∀ j, IsAffine ((Over.forget U.left ⋙ B.inclusion).obj (D₀.obj j)) :=
      fun j => (D.obj j.left).property
    have hpt₀ : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c₀.pt) := c.pt.property
    have hbase₀ : q.obj c₀.pt = cs.pt := by
      change Over.mk ((cs.π.app i).left ≫ U.hom) = cs.pt
      rw [(cs.π.app i).w]
      rfl
    let k₀ := (E.obj c₀.pt).hom
    have hk₀ : k₀ = eqToHom hbase₀ ≫ cs.π.app i := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.eqToHom_left]
      simp [k₀, E, nestedOverToOver, nestedOverObject, c₀, stageCone]
    have hγlift : 𝒴.val.p.IsHomLift k₀ γ := by
      rw [hk₀]
      have : 𝒴.val.p.IsHomLift (cs.π.app i) γ := by
        simpa [cs, T] using hγ.toIsHomLift
      infer_instance
    have hγcart : 𝒴.val.p.IsStronglyCartesian k₀ γ :=
      𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift k₀ γ
    obtain ⟨η, hη, hηfac⟩ := exists_iso_isHomLift_id_comp_eq 𝒴.val.p (f := k₀) γ (cy.map k₀ yi)
    let z : TwoFibreProductOver q 𝒳.val.p 𝒴.val.p y (CatFiberedInGroupoids.homFunctor p) :=
      ⟨q.obj c₀.pt, c₀.pt, x.1, rfl, x.2.trans hbase₀.symm, η, hη⟩
    let P := TwoFibreProductOver.fst q 𝒳.val.p 𝒴.val.p y (CatFiberedInGroupoids.homFunctor p)
    let zf : P.Fiber c₀.pt := ⟨z, rfl⟩
    obtain ⟨j, t', ht'⟩ := exists_stage_of_relativelyLimitPreserving.{u, u, u}
      B S hS U F X ((AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso
          B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩)
      (AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
        B U.left.1 S U.left.2 hS U.hom ⟨F, hF⟩) hrel
      D₀ c₀ hc₀ hD₀ hpt₀ (pointOfObj F P e zf)
    let zf' := objectOfPoint F P e t'
    obtain ⟨a, ha⟩ := exists_homLift_of_point_eq F P e zf zf' (c₀.π.app j) (by
      rw [pointOfObj_objectOfPoint]
      exact ht'.symm)
    have hz' : zf'.1.x = D₀.obj j := zf'.2
    have hbase' : q.obj (D₀.obj j) = Ds.obj j.left := by
      change Over.mk ((Ds.map j.hom).left ≫ U.hom) = Ds.obj j.left
      rw [(Ds.map j.hom).w]
      rfl
    have hzbase : zf'.1.base = Ds.obj j.left :=
      zf'.1.hx.symm.trans ((congrArg q.obj hz').trans hbase')
    let x' : 𝒳.val.p.Fiber (T.obj (D.obj j.left)) :=
      ⟨zf'.1.y, zf'.1.hy.trans hzbase⟩
    have habase : a.hbase = eqToHom hbase₀ ≫ cs.π.app j.left ≫ eqToHom hzbase.symm := by
      rw [a.hbase_eq]
      have haa := IsHomLift.fac' P (c₀.π.app j) a
      change a.a = eqToHom zf.2 ≫ c₀.π.app j ≫ eqToHom zf'.2.symm at haa
      rw [haa]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.eqToHom_left]
      simp [q, c₀, stageCone, P, zf, z]
    have hδ : 𝒳.val.p.IsHomLift (T.map (c.π.app j.left)) a.b := by
      have := a.hb
      have hh : 𝒳.val.p.IsHomLift
          (eqToHom hbase₀.symm ≫ a.hbase ≫ eqToHom hzbase) a.b := inferInstance
      rw [habase] at hh
      simpa [cs, Ds] using hh
    let k' := (E.obj zf'.1.x).hom
    let γ' := zf'.1.iso.inv ≫ cy.map k' yi
    have hγ' : 𝒴.val.p.IsHomLift (T.map (D.map j.hom)) γ' := by
      have hiv : 𝒴.val.p.IsHomLift (𝟙 zf'.1.base) zf'.1.iso.inv := by
        have := zf'.1.vertical
        exact IsHomLift.lift_id_inv 𝒴.val.p zf'.1.base zf'.1.iso
      have hmap : 𝒴.val.p.IsHomLift
          (eqToHom zf'.1.hx.symm ≫ k') (cy.map k' yi) := inferInstance
      have hh : 𝒴.val.p.IsHomLift
          (eqToHom zf'.1.hx.symm ≫ k') γ' := by
        simpa using (inferInstance : 𝒴.val.p.IsHomLift
          (𝟙 zf'.1.base ≫ (eqToHom zf'.1.hx.symm ≫ k')) γ')
      have hb : eqToHom hzbase ≫ Ds.map j.hom = eqToHom zf'.1.hx.symm ≫ k' := by
        have hk' : k' = q.map (eqToHom hz') ≫ (E.obj (D₀.obj j)).hom :=
          (E.map (eqToHom hz')).w.symm
        have hstage : (E.obj (D₀.obj j)).hom = eqToHom hbase' ≫ Ds.map j.hom := by
          apply Over.OverMorphism.ext
          simp [E, nestedOverToOver, nestedOverObject, D₀]
        rw [hk', hstage]
        simp only [eqToHom_map, ← Category.assoc, eqToHom_trans]
      rw [← hb] at hh
      simpa [Ds, U] using hh
    have hsq : (CatFiberedInGroupoids.homFunctor p).map a.b ≫ γ' = γ := by
      have hw : (CatFiberedInGroupoids.homFunctor p).map a.b ≫ zf'.1.iso.inv =
          z.iso.inv ≫ y.map a.a := by
        rw [← cancel_mono zf'.1.iso.hom]
        simpa [Category.assoc] using congrArg (z.iso.inv ≫ ·) a.w.symm
      dsimp [γ']
      rw [← Category.assoc, hw, Category.assoc]
      have hfac : y.map a.a ≫ cy.map k' yi = cy.map k₀ yi :=
        Functor.ChoiceOfPullbacks.sliceFunctor_map_fac cy yi (E.map a.a)
      rw [hfac, ← hηfac]
      simp [z]
    refine ⟨j.left, j.hom, x', x, a.b, 𝟙 x.1, γ', ?_, ?_, inferInstance, ?_, ?_⟩
    · exact 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
    · exact IsHomLift.id x.2
    · exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
    · simpa using hsq

end AlgebraicGeometry.Stack

end
