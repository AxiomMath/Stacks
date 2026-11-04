module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.PointwiseBaseChange

/-!
# Base change of a groupoid in algebraic spaces (Stacks 0DTA)

A groupoid in algebraic spaces over `B` pulls back along any morphism `B' ⟶ B` of algebraic
spaces, and the projections are a morphism of groupoids: `AlgebraicGeometry.Space.BaseChange`
and **Stacks 0DTA** `AlgebraicGeometry.Space.baseChange`. Then the source, target and composition
of the base change against the two projections of the chosen fibre products.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- A groupoid obtained by base change, together with its projection functor. -/
structure BaseChange {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) where
  /-- The groupoid over the new base. -/
  groupoid : GroupoidInAlgebraicSpaces C S hS B'
  /-- Its object space is the chosen base change. -/
  objects_eq : groupoid.objects = AlgebraicSpaces.fiberProduct C S hS f G.objectsToBase
  /-- Its arrow space is the chosen base change. -/
  arrows_eq : groupoid.arrows = AlgebraicSpaces.fiberProduct C S hS f G.arrowsToBase
  /-- The projections define a functor on the underlying groupoids. -/
  projection : Deformation.GroupoidInFunctors.Hom
    groupoid.toGroupoidInFunctors G.toGroupoidInFunctors
  /-- The map on objects is the canonical second pullback projection. -/
  mapObjects_eq : projection.mapObjects =
    (objects_eq.symm ▸
      (ObjectProperty.homMk (pullback.snd f.hom G.objectsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f G.objectsToBase ⟶ G.objects)).hom
  /-- The structure map on objects is the canonical first pullback projection. -/
  objectsToBase_eq : groupoid.objectsToBase =
    (objects_eq.symm ▸
      (ObjectProperty.homMk (pullback.fst f.hom G.objectsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f G.objectsToBase ⟶ B'))
  /-- The map on arrows is the canonical second pullback projection. -/
  mapArrows_eq : projection.mapArrows =
    (arrows_eq.symm ▸
      (ObjectProperty.homMk (pullback.snd f.hom G.arrowsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f G.arrowsToBase ⟶ G.arrows)).hom
  /-- The structure map on arrows is the canonical first pullback projection. -/
  arrowsToBase_eq : groupoid.arrowsToBase =
    (arrows_eq.symm ▸
      (ObjectProperty.homMk (pullback.fst f.hom G.arrowsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f G.arrowsToBase ⟶ B'))
  /-- The canonical projection square on objects is cartesian. -/
  objects_isPullback : IsPullback
    (ObjectProperty.homMk projection.mapObjects : groupoid.objects ⟶ G.objects)
    groupoid.objectsToBase G.objectsToBase f
  /-- The canonical projection square on arrows is cartesian. -/
  arrows_isPullback : IsPullback
    (ObjectProperty.homMk projection.mapArrows : groupoid.arrows ⟶ G.arrows)
    groupoid.arrowsToBase G.arrowsToBase f

/-- Pull back a groupoid in algebraic spaces along a morphism of bases. -/
@[stacks 0DTA]
noncomputable def baseChange {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    BaseChange G f := by
  classical
  let U' := AlgebraicSpaces.fiberProduct C S hS f G.objectsToBase
  let R' := AlgebraicSpaces.fiberProduct C S hS f G.arrowsToBase
  let objBase : U' ⟶ B' :=
    ObjectProperty.homMk (pullback.fst f.hom G.objectsToBase.hom)
  let mapObj : U' ⟶ G.objects :=
    ObjectProperty.homMk (pullback.snd f.hom G.objectsToBase.hom)
  let arrBase : R' ⟶ B' :=
    ObjectProperty.homMk (pullback.fst f.hom G.arrowsToBase.hom)
  let mapArr : R' ⟶ G.arrows :=
    ObjectProperty.homMk (pullback.snd f.hom G.arrowsToBase.hom)
  let source' := pullbackMapOver f G.objectsToBase G.arrowsToBase G.source G.source_over
  let target' := pullbackMapOver f G.objectsToBase G.arrowsToBase G.target G.target_over
  let Q' := AlgebraicSpaces.fiberProduct C S hS source' target'
  let Q := AlgebraicSpaces.fiberProduct C S hS G.source G.target
  let p₁ : Q' ⟶ R' := ObjectProperty.homMk (pullback.fst source'.hom target'.hom)
  let p₂ : Q' ⟶ R' := ObjectProperty.homMk (pullback.snd source'.hom target'.hom)
  let oldFst : Q ⟶ G.arrows := ObjectProperty.homMk
    (pullback.fst G.source.hom G.target.hom)
  let oldSnd : Q ⟶ G.arrows := ObjectProperty.homMk
    (pullback.snd G.source.hom G.target.hom)
  let toOldComp := mapComposableToOld G.source G.target source' target' mapObj mapArr
    (by
      exact pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.source G.source_over)
    (by
      exact pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.target G.target_over)
  have hToOld : toOldComp ≫ oldFst = p₁ ≫ mapArr := by
    simp [toOldComp, mapComposableToOld, oldFst, p₁]
  have hToOldSnd : toOldComp ≫ oldSnd = p₂ ≫ mapArr := by
    simp [toOldComp, mapComposableToOld, oldSnd, p₂]
  have hArrowBase := AlgebraicSpaces.isPullback_fiberProduct C S hS f G.arrowsToBase
  let comp' : Q' ⟶ R' := hArrowBase.lift (p₁ ≫ arrBase) (toOldComp ≫ G.comp) (by
    calc
      (p₁ ≫ arrBase) ≫ f = (p₁ ≫ mapArr) ≫ G.arrowsToBase := by
        simpa [Category.assoc] using congrArg (fun k => p₁ ≫ k) hArrowBase.w
      _ = (toOldComp ≫ oldFst) ≫ G.arrowsToBase := by rw [← hToOld]
      _ = (toOldComp ≫ G.comp) ≫ G.arrowsToBase := by
        simpa [Category.assoc] using congrArg (fun k => toOldComp ≫ k)
          G.comp_over.symm)
  let groupoid : GroupoidInAlgebraicSpaces C S hS B' := {
    objects := U'
    arrows := R'
    objectsToBase := objBase
    arrowsToBase := arrBase
    source := source'
    target := target'
    source_over := pullbackMapOver_fst f G.objectsToBase G.arrowsToBase
      G.source G.source_over
    target_over := pullbackMapOver_fst f G.objectsToBase G.arrowsToBase
      G.target G.target_over
    comp := comp'
    comp_over := by
      dsimp [comp']
      apply ObjectProperty.hom_ext
      exact congrArg (fun k => k.hom) (hArrowBase.lift_fst _ _ _)
    pointwiseGroupoid := by
      intro T
      let fT := f.hom.app T
      let qT := G.objectsToBase.hom.app T
      let rT := G.arrowsToBase.hom.app T
      let sT := G.source.hom.app T
      let tT := G.target.hom.app T
      let cT := fun p => G.toGroupoidInFunctors.comp.app T p
      let P := G.toGroupoidInFunctors.pointwiseData T
      have hs : ∀ a, qT (sT a) = rT a := by
        intro a
        have h := congrArg (fun k => k.hom.app T a) G.source_over
        simpa [sT, qT, rT] using h
      have ht : ∀ a, qT (tT a) = rT a := by
        intro a
        have h := congrArg (fun k => k.hom.app T a) G.target_over
        simpa [tT, qT, rT] using h
      have hc : ∀ p, rT (cT p) = rT p.1.1 := by
        intro p
        have hfst :
            (pullback.fst G.source.hom G.target.hom).app T
                ((composableToPullback G.source.hom G.target.hom).app T p) =
              p.1.1 := by
          change (composableToPullback G.source.hom G.target.hom ≫
            pullback.fst G.source.hom G.target.hom).app T p = p.1.1
          rw [composableToPullback]
          rw [pullback.lift_fst]
          rfl
        have hcomp' : rT (cT p) = rT
            ((pullback.fst G.source.hom G.target.hom).app T
              ((composableToPullback G.source.hom G.target.hom).app T p)) := by
          dsimp [cT, GroupoidInAlgebraicSpaces.toGroupoidInFunctors]
          have h₁ := congrArg (fun k => k.hom) G.comp_over
          rw [ObjectProperty.FullSubcategory.comp_hom] at h₁
          have h₂ := congrArg (fun k => (k.app T)
            ((composableToPullback G.source.hom G.target.hom).app T p)) h₁
          change G.arrowsToBase.hom.app T
              (G.toGroupoidInFunctors.comp.app T p) =
            G.arrowsToBase.hom.app T
              ((pullback.fst G.source.hom G.target.hom).app T
                ((composableToPullback G.source.hom G.target.hom).app T p))
          exact h₂
        exact hcomp'.trans (congrArg rT hfst)
      let P' := @FiberBaseChange.pointwise
        (B'.obj.obj T) (G.objects.obj.obj T) (G.arrows.obj.obj T) (B.obj.obj T)
        fT qT rT sT tT cT P hs ht hc
      let eU := fiberProductAtEquiv f G.objectsToBase T
      let eR := fiberProductAtEquiv f G.arrowsToBase T
      exact ⟨(show Deformation.PointwiseGroupoid
          (source'.hom.app T) (target'.hom.app T)
          (fun p => (composableToPullback source'.hom target'.hom ≫
            comp'.hom).app T p) from @transportPointwise _ _ _ _ _ _ _ _ _ _ eU eR (by
        intro a
        apply Subtype.ext
        apply Prod.ext
        · have h₁ := congrArg (fun k => k.hom)
            (pullbackMapOver_fst f G.objectsToBase G.arrowsToBase G.source G.source_over)
          rw [ObjectProperty.FullSubcategory.comp_hom] at h₁
          have h₂ := congrArg (fun k => (k.app T) a) h₁
          change (pullback.fst f.hom G.objectsToBase.hom).app T
              ((pullbackMapOver f G.objectsToBase G.arrowsToBase G.source
                G.source_over).hom.app T a) =
            (pullback.fst f.hom G.arrowsToBase.hom).app T a at h₂
          change (fiberProductAtEquiv f G.objectsToBase T (source'.hom.app T a)).val.1 =
            (fiberProductAtEquiv f G.arrowsToBase T a).val.1
          rw [fiberProductAtEquiv_fst, fiberProductAtEquiv_fst]
          simpa [ObjectProperty.homMk, NatTrans.comp_app,
            ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.comp_apply,
            ConcreteCategory.comp_apply] using h₂
        · have h₁ := congrArg (fun k => k.hom)
            (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.source G.source_over)
          rw [ObjectProperty.FullSubcategory.comp_hom] at h₁
          have h₂ := congrArg (fun k => (k.app T) a) h₁
          change (pullback.snd f.hom G.objectsToBase.hom).app T
              ((pullbackMapOver f G.objectsToBase G.arrowsToBase G.source
                G.source_over).hom.app T a) =
            G.source.hom.app T ((pullback.snd f.hom G.arrowsToBase.hom).app T a) at h₂
          change (fiberProductAtEquiv f G.objectsToBase T (source'.hom.app T a)).val.2 =
            G.source.hom.app T ((fiberProductAtEquiv f G.arrowsToBase T a).val.2)
          rw [fiberProductAtEquiv_snd, fiberProductAtEquiv_snd]
          simpa [ObjectProperty.homMk, NatTrans.comp_app,
            ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.comp_apply,
            ConcreteCategory.comp_apply] using h₂) (by
        intro a
        apply Subtype.ext
        apply Prod.ext
        · have h₁ := congrArg (fun k => k.hom)
            (pullbackMapOver_fst f G.objectsToBase G.arrowsToBase G.target G.target_over)
          rw [ObjectProperty.FullSubcategory.comp_hom] at h₁
          have h₂ := congrArg (fun k => (k.app T) a) h₁
          change (pullback.fst f.hom G.objectsToBase.hom).app T
              ((pullbackMapOver f G.objectsToBase G.arrowsToBase G.target
                G.target_over).hom.app T a) =
            (pullback.fst f.hom G.arrowsToBase.hom).app T a at h₂
          change (fiberProductAtEquiv f G.objectsToBase T (target'.hom.app T a)).val.1 =
            (fiberProductAtEquiv f G.arrowsToBase T a).val.1
          rw [fiberProductAtEquiv_fst, fiberProductAtEquiv_fst]
          simpa [ObjectProperty.homMk, NatTrans.comp_app,
            ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.comp_apply,
            ConcreteCategory.comp_apply] using h₂
        · have h₁ := congrArg (fun k => k.hom)
            (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.target G.target_over)
          rw [ObjectProperty.FullSubcategory.comp_hom] at h₁
          have h₂ := congrArg (fun k => (k.app T) a) h₁
          change (pullback.snd f.hom G.objectsToBase.hom).app T
              ((pullbackMapOver f G.objectsToBase G.arrowsToBase G.target
                G.target_over).hom.app T a) =
            G.target.hom.app T ((pullback.snd f.hom G.arrowsToBase.hom).app T a) at h₂
          change (fiberProductAtEquiv f G.objectsToBase T (target'.hom.app T a)).val.2 =
            G.target.hom.app T ((fiberProductAtEquiv f G.arrowsToBase T a).val.2)
          rw [fiberProductAtEquiv_snd, fiberProductAtEquiv_snd]
          simpa [ObjectProperty.homMk, NatTrans.comp_app,
            ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.comp_apply,
            ConcreteCategory.comp_apply] using h₂) (by
        intro p
        let q : Q'.obj.obj T :=
          (composableToPullback source'.hom target'.hom).app T p
        have hqFst : (pullback.fst source'.hom target'.hom).app T q = p.1.1 := by
          change ((composableToPullback source'.hom target'.hom ≫
            pullback.fst source'.hom target'.hom).app T) p = p.1.1
          rw [composableToPullback, pullback.lift_fst]
          rfl
        have hqSnd : (pullback.snd source'.hom target'.hom).app T q = p.1.2 := by
          change ((composableToPullback source'.hom target'.hom ≫
            pullback.snd source'.hom target'.hom).app T) p = p.1.2
          rw [composableToPullback, pullback.lift_snd]
          rfl
        apply Subtype.ext
        apply Prod.ext
        · change (eR ((comp'.hom.app T) q)).val.1 = _
          have eRf (x : R'.obj.obj T) : (eR x).val.1 = arrBase.hom.app T x := by
            change (fiberProductAtEquiv f G.arrowsToBase T x).val.1 =
              (pullback.fst f.hom G.arrowsToBase.hom).app T x
            exact fiberProductAtEquiv_fst f G.arrowsToBase T x
          have hLiftFst : comp' ≫ arrBase = p₁ ≫ arrBase := by
            dsimp [comp']
            exact hArrowBase.lift_fst _ _ _
          have hFst := congrArg (fun k => k.hom.app T q) hLiftFst
          have hFst' : arrBase.hom.app T ((comp'.hom.app T) q) =
              arrBase.hom.app T (p₁.hom.app T q) := by
            simpa [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
              CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hFst
          have hP₁ : p₁.hom.app T q = p.1.1 := by
            change (pullback.fst source'.hom target'.hom).app T q = p.val.1
            exact hqFst
          rw [eRf, hFst', hP₁]
          change arrBase.hom.app T (p.val.1) = (eR (p.val.1)).val.1
          rw [eRf]
        · change (eR ((comp'.hom.app T) q)).val.2 = _
          have eRs (x : R'.obj.obj T) : (eR x).val.2 = mapArr.hom.app T x :=
            fiberProductAtEquiv_snd f G.arrowsToBase T x
          have hLiftSnd : comp' ≫ mapArr = toOldComp ≫ G.comp := by
            dsimp [comp']
            exact hArrowBase.lift_snd _ _ _
          have hSnd := congrArg (fun k => k.hom.app T q) hLiftSnd
          have hSnd' : mapArr.hom.app T ((comp'.hom.app T) q) =
              G.comp.hom.app T (toOldComp.hom.app T q) := by
            simpa [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
              CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hSnd
          rw [eRs, hSnd']
          let qOld : Q.obj.obj T := toOldComp.hom.app T q
          let eQ := fiberProductAtEquiv G.source G.target T
          have hP₁ : p₁.hom.app T q = p.val.1 :=
            hqFst
          have hP₂ : p₂.hom.app T q = p.val.2 :=
            hqSnd
          have hOldFstMap : oldFst.hom.app T qOld =
              mapArr.hom.app T (p₁.hom.app T q) := by
            have h := congrArg (fun k => k.hom.app T q) hToOld
            simpa [qOld, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
              CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using h
          have hOldSndMap : oldSnd.hom.app T qOld =
              mapArr.hom.app T (p₂.hom.app T q) := by
            have h := congrArg (fun k => k.hom.app T q) hToOldSnd
            simpa [qOld, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
              CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using h
          have hOldFst : (eQ qOld).val.1 = (eR (p.val.1)).val.2 := by
            calc
              (eQ qOld).val.1 = oldFst.hom.app T qOld :=
                fiberProductAtEquiv_fst G.source G.target T qOld
              _ = mapArr.hom.app T (p₁.hom.app T q) := hOldFstMap
              _ = mapArr.hom.app T (p.val.1) :=
                congrArg (fun z => mapArr.hom.app T z) hP₁
              _ = (eR (p.val.1)).val.2 := (eRs (p.val.1)).symm
          have hOldSnd : (eQ qOld).val.2 = (eR (p.val.2)).val.2 := by
            calc
              (eQ qOld).val.2 = oldSnd.hom.app T qOld :=
                fiberProductAtEquiv_snd G.source G.target T qOld
              _ = mapArr.hom.app T (p₂.hom.app T q) := hOldSndMap
              _ = mapArr.hom.app T (p.val.2) :=
                congrArg (fun z => mapArr.hom.app T z) hP₂
              _ = (eR (p.val.2)).val.2 := (eRs (p.val.2)).symm
          have hOldPair : eQ qOld =
              ⟨((eR (p.val.1)).val.2, (eR (p.val.2)).val.2), by
                calc
                  (G.source.hom.app T) ((eR (p.val.1)).val.2) =
                      (G.source.hom.app T) ((eQ qOld).val.1) := congrArg _ hOldFst.symm
                  _ = (G.target.hom.app T) ((eQ qOld).val.2) := (eQ qOld).property
                  _ = (G.target.hom.app T) ((eR (p.val.2)).val.2) := congrArg _ hOldSnd⟩ :=
            Subtype.ext (Prod.ext hOldFst hOldSnd)
          have hCompFst :
              (pullback.fst G.source.hom G.target.hom).app T
                ((composableToPullback G.source.hom G.target.hom).app T
                  (eQ qOld)) = (eQ qOld).val.1 := by
            change ((composableToPullback G.source.hom G.target.hom ≫
              pullback.fst G.source.hom G.target.hom).app T) (eQ qOld) =
                (eQ qOld).val.1
            rw [composableToPullback]
            rw [pullback.lift_fst]
            rfl
          have hCompSnd :
              (pullback.snd G.source.hom G.target.hom).app T
                ((composableToPullback G.source.hom G.target.hom).app T
                  (eQ qOld)) = (eQ qOld).val.2 := by
            change ((composableToPullback G.source.hom G.target.hom ≫
              pullback.snd G.source.hom G.target.hom).app T) (eQ qOld) =
                (eQ qOld).val.2
            rw [composableToPullback]
            rw [pullback.lift_snd]
            rfl
          have hQBack :
              (composableToPullback G.source.hom G.target.hom).app T
                (eQ qOld) = qOld := by
            apply eQ.injective
            apply Subtype.ext
            apply Prod.ext
            · calc
                (eQ ((composableToPullback G.source.hom G.target.hom).app T
                    (eQ qOld))).val.1 =
                    (pullback.fst G.source.hom G.target.hom).app T
                      ((composableToPullback G.source.hom G.target.hom).app T
                        (eQ qOld)) :=
                          fiberProductAtEquiv_fst G.source G.target T _
                _ = (eQ qOld).val.1 := hCompFst
            · calc
                (eQ ((composableToPullback G.source.hom G.target.hom).app T
                    (eQ qOld))).val.2 =
                    (pullback.snd G.source.hom G.target.hom).app T
                      ((composableToPullback G.source.hom G.target.hom).app T
                        (eQ qOld)) :=
                          fiberProductAtEquiv_snd G.source G.target T _
                _ = (eQ qOld).val.2 := hCompSnd
          have hCompOld : cT (eQ qOld) = G.comp.hom.app T qOld := by
            dsimp [cT, GroupoidInAlgebraicSpaces.toGroupoidInFunctors]
            change G.comp.hom.app T
              ((composableToPullback G.source.hom G.target.hom).app T
                (eQ qOld)) = G.comp.hom.app T qOld
            rw [hQBack]
          change G.comp.hom.app T qOld =
            cT ⟨((eR (p.val.1)).val.2, (eR (p.val.2)).val.2), _⟩
          rw [← hCompOld]
          exact congrArg cT hOldPair) P')⟩
  }
  have map_source : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (a : R'.obj.obj T),
      G.source.hom.app T (mapArr.hom.app T a) =
        mapObj.hom.app T (source'.hom.app T a) := fun T a =>
    (congrArg (fun k => k.hom.app T a)
      (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.source G.source_over)).symm
  have map_target : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (a : R'.obj.obj T),
      G.target.hom.app T (mapArr.hom.app T a) =
        mapObj.hom.app T (target'.hom.app T a) := fun T a =>
    (congrArg (fun k => k.hom.app T a)
      (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.target G.target_over)).symm
  have map_comp : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (a b : R'.obj.obj T) (h : source'.hom.app T a = target'.hom.app T b),
      G.toGroupoidInFunctors.compose T (mapArr.hom.app T a) (mapArr.hom.app T b)
        ((map_source T a).trans ((congrArg (mapObj.hom.app T) h).trans
          (map_target T b).symm)) =
        mapArr.hom.app T (groupoid.toGroupoidInFunctors.compose T a b h) := by
    intro T a b h
    let q : Q'.obj.obj T :=
      (composableToPullback source'.hom target'.hom).app T ⟨(a, b), h⟩
    let oldPair : Q.obj.obj T := toOldComp.hom.app T q
    let oldEndpoints : G.source.hom.app T (mapArr.hom.app T a) =
        G.target.hom.app T (mapArr.hom.app T b) :=
      (map_source T a).trans ((congrArg (mapObj.hom.app T) h).trans
        (map_target T b).symm)
    let canonicalQ : Q.obj.obj T :=
      (composableToPullback G.source.hom G.target.hom).app T
        ⟨(mapArr.hom.app T a, mapArr.hom.app T b), oldEndpoints⟩
    have hqFst : p₁.hom.app T q = a := by
      change (pullback.fst source'.hom target'.hom).app T q = a
      change ((composableToPullback source'.hom target'.hom ≫
        pullback.fst source'.hom target'.hom).app T) ⟨(a, b), h⟩ = a
      rw [composableToPullback, pullback.lift_fst]
      rfl
    have hqSnd : p₂.hom.app T q = b := by
      change (pullback.snd source'.hom target'.hom).app T q = b
      change ((composableToPullback source'.hom target'.hom ≫
        pullback.snd source'.hom target'.hom).app T) ⟨(a, b), h⟩ = b
      rw [composableToPullback, pullback.lift_snd]
      rfl
    have hToOldFst : oldFst.hom.app T oldPair = mapArr.hom.app T a := by
      have h₁ := congrArg (fun k => k.hom.app T q) hToOld
      have h₂ : oldFst.hom.app T oldPair = mapArr.hom.app T (p₁.hom.app T q) := by
        simpa [oldPair, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
          CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using h₁
      exact h₂.trans (congrArg (mapArr.hom.app T) hqFst)
    have hToOldSnd' : oldSnd.hom.app T oldPair = mapArr.hom.app T b := by
      have h₁ := congrArg (fun k => k.hom.app T q) hToOldSnd
      have h₂ : oldSnd.hom.app T oldPair = mapArr.hom.app T (p₂.hom.app T q) := by
        simpa [oldPair, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
          CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using h₁
      exact h₂.trans (congrArg (mapArr.hom.app T) hqSnd)
    let eQ := fiberProductAtEquiv G.source G.target T
    have hCanonicalFst : (eQ canonicalQ).val.1 = mapArr.hom.app T a := by
      calc
        (eQ canonicalQ).val.1 = oldFst.hom.app T canonicalQ := by
          change (fiberProductAtEquiv G.source G.target T canonicalQ).val.1 = _
          exact fiberProductAtEquiv_fst G.source G.target T canonicalQ
        _ = mapArr.hom.app T a := by
          change ((composableToPullback G.source.hom G.target.hom ≫
            pullback.fst G.source.hom G.target.hom).app T)
              ⟨(mapArr.hom.app T a, mapArr.hom.app T b), oldEndpoints⟩ = _
          rw [composableToPullback, pullback.lift_fst]
          rfl
    have hCanonicalSnd : (eQ canonicalQ).val.2 = mapArr.hom.app T b := by
      calc
        (eQ canonicalQ).val.2 = oldSnd.hom.app T canonicalQ := by
          change (fiberProductAtEquiv G.source G.target T canonicalQ).val.2 = _
          exact fiberProductAtEquiv_snd G.source G.target T canonicalQ
        _ = mapArr.hom.app T b := by
          change ((composableToPullback G.source.hom G.target.hom ≫
            pullback.snd G.source.hom G.target.hom).app T)
              ⟨(mapArr.hom.app T a, mapArr.hom.app T b), oldEndpoints⟩ = _
          rw [composableToPullback, pullback.lift_snd]
          rfl
    have hOldPair : oldPair = canonicalQ := by
      apply eQ.injective
      apply Subtype.ext
      apply Prod.ext
      · calc
          (eQ oldPair).val.1 = oldFst.hom.app T oldPair := by
            change (fiberProductAtEquiv G.source G.target T oldPair).val.1 = _
            exact fiberProductAtEquiv_fst G.source G.target T oldPair
          _ = mapArr.hom.app T a := hToOldFst
          _ = (eQ canonicalQ).val.1 := hCanonicalFst.symm
      · calc
          (eQ oldPair).val.2 = oldSnd.hom.app T oldPair := by
            change (fiberProductAtEquiv G.source G.target T oldPair).val.2 = _
            exact fiberProductAtEquiv_snd G.source G.target T oldPair
          _ = mapArr.hom.app T b := hToOldSnd'
          _ = (eQ canonicalQ).val.2 := hCanonicalSnd.symm
    have hCompLift : mapArr.hom.app T (comp'.hom.app T q) =
        G.comp.hom.app T oldPair := by
      have hLiftSnd : comp' ≫ mapArr = toOldComp ≫ G.comp := by
        dsimp [comp']
        exact hArrowBase.lift_snd _ _ _
      have h := congrArg (fun k => k.hom.app T q) hLiftSnd
      simpa [oldPair, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using h
    change G.comp.hom.app T
        ((composableToPullback G.source.hom G.target.hom).app T
          ⟨(mapArr.hom.app T a, mapArr.hom.app T b), oldEndpoints⟩) =
      mapArr.hom.app T (comp'.hom.app T q)
    calc
      _ = G.comp.hom.app T oldPair := congrArg (G.comp.hom.app T) hOldPair.symm
      _ = mapArr.hom.app T (comp'.hom.app T q) := hCompLift.symm
  let projection : Deformation.GroupoidInFunctors.Hom
      groupoid.toGroupoidInFunctors G.toGroupoidInFunctors := {
    mapObjects := mapObj.hom
    mapArrows := mapArr.hom
    map_source := map_source
    map_target := map_target
    map_id := mapIdentityOfMapComp
      (D := (BigFppfOver C S hS)ᵒᵖ)
      (G := groupoid.toGroupoidInFunctors) (H := G.toGroupoidInFunctors)
      (mapObjects := mapObj.hom) (mapArrows := mapArr.hom)
      (map_source := map_source) (map_target := map_target) (map_comp := map_comp)
    map_comp := map_comp
  }
  refine ⟨groupoid, rfl, rfl, projection, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (AlgebraicSpaces.isPullback_fiberProduct C S hS f G.objectsToBase).flip
  · exact (AlgebraicSpaces.isPullback_fiberProduct C S hS f G.arrowsToBase).flip

/-! ### The source and target of a base-changed groupoid against the projections

The source and target of `AlgebraicGeometry.Space.baseChange` are built by
`AlgebraicGeometry.Space.pullbackMapOver`, so their composites with the two projections of the
chosen fibre product are the ones `AlgebraicGeometry.Space.pullbackMapOver_hom_comp_fst` and
`…_comp_snd` record. Naming them here saves a consumer from unfolding `baseChange`, which cannot
be done by `rw` — the structure's `source_over` field depends on `source`, so the rewrite motive
is not type correct.
-/

/-- The source of a base-changed groupoid covers the first projection. -/
theorem baseChange_source_comp_fst {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.source.hom ≫ pullback.fst f.hom G.objectsToBase.hom =
      pullback.fst f.hom G.arrowsToBase.hom :=
  pullbackMapOver_hom_comp_fst f G.objectsToBase G.arrowsToBase G.source G.source_over

/-- The source of a base-changed groupoid is the source of the original on second
projections. -/
theorem baseChange_source_comp_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.source.hom ≫ pullback.snd f.hom G.objectsToBase.hom =
      pullback.snd f.hom G.arrowsToBase.hom ≫ G.source.hom :=
  pullbackMapOver_hom_comp_snd f G.objectsToBase G.arrowsToBase G.source G.source_over

/-- The target of a base-changed groupoid covers the first projection. -/
theorem baseChange_target_comp_fst {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.target.hom ≫ pullback.fst f.hom G.objectsToBase.hom =
      pullback.fst f.hom G.arrowsToBase.hom :=
  pullbackMapOver_hom_comp_fst f G.objectsToBase G.arrowsToBase G.target G.target_over

/-- The target of a base-changed groupoid is the target of the original on second
projections. -/
theorem baseChange_target_comp_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.target.hom ≫ pullback.snd f.hom G.objectsToBase.hom =
      pullback.snd f.hom G.arrowsToBase.hom ≫ G.target.hom :=
  pullbackMapOver_hom_comp_snd f G.objectsToBase G.arrowsToBase G.target G.target_over

/-! ### The composition of a base-changed groupoid against the projections

The composition of `AlgebraicGeometry.Space.baseChange` is the lift into the chosen fibre product
of the new base with the old arrow space whose component on the new base is the one carried by the
first of the two arrows, and whose component on the old arrow space is the composition of the
original groupoid applied to the two underlying old arrows. The five declarations below name that
description: `AlgebraicGeometry.Space.baseChangeComposableToOld` is the map on composable pairs
induced by the two projections, with its own two components, and then the two components of the
lift. As in the previous section none of this can be reached by unfolding `baseChange` with `rw`.
-/

/-- A composite with `ObjectProperty.homMk` in `AlgebraicSpaces` is an equation of the underlying
morphisms. -/
private theorem hom_comp_eq_of_comp_homMk {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {X Y Z : AlgebraicSpaces C S hS} {a : X ⟶ Y} {b : X ⟶ Z}
    {g : Y.obj ⟶ Z.obj} (h : a ≫ ObjectProperty.homMk g = b) : a.hom ≫ g = b.hom :=
  congrArg (·.hom) h

/-- **The composable pairs of a base-changed groupoid map to those of the original.** The
projections on objects and on arrows of `AlgebraicGeometry.Space.baseChange` carry the source and
the target of the base change to the source and the target of the original groupoid, so by
`AlgebraicGeometry.Space.mapComposableToOld` they induce a map of the chosen fibre products of the
source with the target. This is the map the composition of the base change is built from. -/
noncomputable def baseChangeComposableToOld {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    AlgebraicSpaces.fiberProduct C S hS (baseChange G f).groupoid.source
        (baseChange G f).groupoid.target ⟶
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  mapComposableToOld G.source G.target
    (baseChange G f).groupoid.source (baseChange G f).groupoid.target
    (ObjectProperty.homMk (pullback.snd f.hom G.objectsToBase.hom))
    (ObjectProperty.homMk (pullback.snd f.hom G.arrowsToBase.hom))
    (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.source G.source_over)
    (pullbackMapOver_snd f G.objectsToBase G.arrowsToBase G.target G.target_over)

/-- The first arrow of a composable pair of a base-changed groupoid is the first arrow of its
image in the original groupoid. -/
theorem baseChangeComposableToOld_comp_fst {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChangeComposableToOld G f).hom ≫ pullback.fst G.source.hom G.target.hom =
      pullback.fst (baseChange G f).groupoid.source.hom
          (baseChange G f).groupoid.target.hom ≫
        pullback.snd f.hom G.arrowsToBase.hom :=
  hom_comp_eq_of_comp_homMk
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _)

/-- The second arrow of a composable pair of a base-changed groupoid is the second arrow of its
image in the original groupoid. -/
theorem baseChangeComposableToOld_comp_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChangeComposableToOld G f).hom ≫ pullback.snd G.source.hom G.target.hom =
      pullback.snd (baseChange G f).groupoid.source.hom
          (baseChange G f).groupoid.target.hom ≫
        pullback.snd f.hom G.arrowsToBase.hom :=
  hom_comp_eq_of_comp_homMk
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _)

/-- The composite of a composable pair of a base-changed groupoid lies over the point of the new
base carried by the first of the two arrows. -/
theorem baseChange_comp_comp_fst {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.comp.hom ≫ pullback.fst f.hom G.arrowsToBase.hom =
      pullback.fst (baseChange G f).groupoid.source.hom
          (baseChange G f).groupoid.target.hom ≫
        pullback.fst f.hom G.arrowsToBase.hom :=
  hom_comp_eq_of_comp_homMk
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS f G.arrowsToBase).lift_fst _ _ _)

/-- The old arrow underlying the composite of a composable pair of a base-changed groupoid is the
composite, in the original groupoid, of the two old arrows underlying the pair. -/
theorem baseChange_comp_comp_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (f : B' ⟶ B) :
    (baseChange G f).groupoid.comp.hom ≫ pullback.snd f.hom G.arrowsToBase.hom =
      (baseChangeComposableToOld G f).hom ≫ G.comp.hom :=
  hom_comp_eq_of_comp_homMk
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS f G.arrowsToBase).lift_snd _ _ _)

end Space

end AlgebraicGeometry

end
