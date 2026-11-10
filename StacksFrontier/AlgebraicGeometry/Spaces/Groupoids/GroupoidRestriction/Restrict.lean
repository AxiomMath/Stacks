module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction.Composition

/-!
# Restriction of a groupoid in algebraic spaces: the restriction (Stacks 044B)

Part of the restriction of a groupoid in algebraic spaces along a morphism `g : U' ⟶ G.objects`.
This file contains the specification `Restriction` of the restriction, its construction
`restrict`, and **Stacks 044B**, `restrict_isRestriction`: the restriction is a groupoid in
algebraic spaces over `B` with objects `U'` and arrows the fibre product
`U' ×_{g, U, t} R ×_{s, U, g} U'`, and on `T`-points, and on `T`-points over any point of `B(T)`,
its canonical morphism to `G` is the restriction of the groupoid of points of `G` along
`U'(T) ⟶ U(T)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace GroupoidInAlgebraicSpaces

/-- Specification of the canonical restriction of a groupoid in algebraic spaces. -/
public structure Restriction
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) where
  /-- The restricted groupoid, with object space `U'`. -/
  groupoid : GroupoidInAlgebraicSpaces C S hS B
  objects_eq : groupoid.objects = U'
  arrows_eq : groupoid.arrows = restrictionArrows G g
  objectsToBase_eq : groupoid.objectsToBase =
    eqToHom objects_eq ≫ g ≫ G.objectsToBase
  arrowsToBase_eq : groupoid.arrowsToBase =
    eqToHom arrows_eq ≫ restrictionArrowsToArrows G g ≫ G.arrowsToBase
  source_eq : groupoid.source =
    eqToHom arrows_eq ≫ restrictionSource G g ≫ eqToHom objects_eq.symm
  target_eq : groupoid.target =
    eqToHom arrows_eq ≫ restrictionTarget G g ≫ eqToHom objects_eq.symm
  /-- The morphism from the restricted groupoid to `G`. -/
  hom : GroupoidInAlgebraicSpaces.Hom groupoid G
  mapObjects_eq : hom.toGroupoidHom.mapObjects = (eqToHom objects_eq ≫ g).hom
  mapArrows_eq : hom.toGroupoidHom.mapArrows =
    (eqToHom arrows_eq ≫ restrictionArrowsToArrows G g).hom
  /-- On sections over every `T`, the functor induced by `hom` is fully faithful. -/
  evaluation_fullyFaithful :
    ∀ T : (BigFppfOver C S hS)ᵒᵖ,
      Nonempty (hom.toGroupoidHom.evaluation T).FullyFaithful

/-- Restriction along an arbitrary map to the object space, with its canonical
composition law and functor to the original groupoid. -/
@[stacks 044C "the restriction of the groupoid to U'",
  stacks 04RN "the fibre-product diagram defining R' with its source and target maps"]
public noncomputable def restrict
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    Restriction G g := by
  classical
  let P := restrictionArrows G g
  let src := restrictionSource G g
  let tgt := restrictionTarget G g
  let arr := restrictionArrowsToArrows G g
  let H : GroupoidInAlgebraicSpaces C S hS B := {
    objects := U'
    arrows := P
    objectsToBase := g ≫ G.objectsToBase
    arrowsToBase := arr ≫ G.arrowsToBase
    source := src
    target := tgt
    source_over := by
      calc
        src ≫ (g ≫ G.objectsToBase) = (src ≫ g) ≫ G.objectsToBase := by
          simp [Category.assoc]
        _ = (arr ≫ G.source) ≫ G.objectsToBase := by
          rw [restriction_condition]
        _ = arr ≫ G.arrowsToBase := by
          calc
            (arr ≫ G.source) ≫ G.objectsToBase =
                arr ≫ (G.source ≫ G.objectsToBase) := Category.assoc _ _ _
            _ = arr ≫ G.arrowsToBase := congrArg (arr ≫ ·) G.source_over
    target_over := by
      calc
        tgt ≫ (g ≫ G.objectsToBase) = (tgt ≫ g) ≫ G.objectsToBase := by
          simp [Category.assoc]
        _ = (arr ≫ G.target) ≫ G.objectsToBase := by
          rw [(restriction_condition' G g).symm]
        _ = arr ≫ G.arrowsToBase := by
          calc
            (arr ≫ G.target) ≫ G.objectsToBase =
                arr ≫ (G.target ≫ G.objectsToBase) := Category.assoc _ _ _
            _ = arr ≫ G.arrowsToBase := congrArg (arr ≫ ·) G.target_over
    comp := restrictionComp G g
    comp_over := by
      change ((restrictionCompositionData G g).hom ≫
        restrictionArrowsToArrows G g) ≫ G.arrowsToBase = _
      rw [((restrictionCompositionData G g).hom_comp)]
      apply ObjectProperty.hom_ext
      ext T z
      let a := arr.hom.app T ((pullback.fst src.hom tgt.hom).app T z)
      let b := arr.hom.app T ((pullback.snd src.hom tgt.hom).app T z)
      have hab : G.source.hom.app T a = G.target.hom.app T b := by
        calc
          G.source.hom.app T a = g.hom.app T (src.hom.app T
              ((pullback.fst src.hom tgt.hom).app T z)) := by
            exact congrArg (fun f => f.hom.app T ((pullback.fst src.hom tgt.hom).app T z))
              (restriction_condition G g).symm
          _ = g.hom.app T (tgt.hom.app T
              ((pullback.snd src.hom tgt.hom).app T z)) := by
            exact congrArg (g.hom.app T)
              (pullback_condition_app src.hom tgt.hom T z)
          _ = G.target.hom.app T b := by
            exact (congrArg (fun f => f.hom.app T ((pullback.snd src.hom tgt.hom).app T z))
              (restriction_condition' G g)).symm
      let p : (Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom).obj T := ⟨(a, b), hab⟩
      let cp := composableToPullback G.source.hom G.target.hom
      let firstMap : Deformation.composableArrows G.objects.obj G.arrows.obj
        G.source.hom G.target.hom ⟶ G.arrows.obj := {
        app := fun _ => ↾ fun p => p.1.1
        naturality := by intro X Y f; ext q; rfl }
      have hcomp := congrArg
        (fun f => f.hom.app T (cp.app T p))
        G.comp_over
      have hlift : cp ≫ pullback.fst G.source.hom G.target.hom = firstMap := by
        dsimp [cp, composableToPullback]
        simp [firstMap]
      have hcp : (cp ≫ pullback.fst G.source.hom G.target.hom).app T p = p.val.1 := by
        have heq := congrArg (fun k => (ConcreteCategory.hom (k.app T)) p) hlift
        simpa [firstMap] using heq
      have hfst : (pullback.fst G.source.hom G.target.hom).app T
          (cp.app T p) = a := by
        calc
          _ = (cp ≫ pullback.fst G.source.hom G.target.hom).app T p := by
            simp [NatTrans.comp_app]
          _ = p.val.1 := hcp
          _ = a := rfl
      have hbase : G.arrowsToBase.hom.app T (G.comp.hom.app T (cp.app T p)) =
          G.arrowsToBase.hom.app T a := by
        calc
          _ = (G.comp ≫ G.arrowsToBase).hom.app T (cp.app T p) := by
            rfl
          _ = (fiberProductFst G.source G.target ≫
              G.arrowsToBase).hom.app T (cp.app T p) := hcomp
          _ = G.arrowsToBase.hom.app T
              ((pullback.fst G.source.hom G.target.hom).app T (cp.app T p)) := by
            rfl
          _ = G.arrowsToBase.hom.app T a :=
            congrArg (G.arrowsToBase.hom.app T) hfst
      have hcompApp := congrArg (fun k => k p)
        (NatTrans.comp_app cp G.comp.hom T)
      calc
        _ = G.arrowsToBase.hom.app T (G.comp.hom.app T (cp.app T p)) :=
          congrArg (G.arrowsToBase.hom.app T) hcompApp
        _ = _ := hbase
    pointwiseGroupoid := fun T => by
      let : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
      let F : U'.obj.obj T → G.objects.obj.obj T := g.hom.app T
      let : Groupoid (U'.obj.obj T) := InducedCategory.groupoid _ F
      refine ⟨{
        groupoid := inferInstance
        arrowEquiv := fun x y =>
          (InducedCategory.homEquiv (F := F)).trans
            (restrictionHomEquiv G g T x y)
        comp_eq := by
          intro x y z f h
          simp only [InducedCategory.homEquiv, Equiv.trans_apply]
          apply (restrictionArrowDataEquiv G g T).injective
          let e := restrictionArrowDataEquiv G g T
          let q := G.toGroupoidInFunctors.evaluationArrowEquiv T (F x) (F z)
          let f₀ := (InducedCategory.homEquiv (F := F) (X := x) (Y := y)) f
          let h₀ := (InducedCategory.homEquiv (F := F) (X := y) (Y := z)) h
          let qR := G.toGroupoidInFunctors.evaluationArrowEquiv T (F y) (F z)
          let qL := G.toGroupoidInFunctors.evaluationArrowEquiv T (F x) (F y)
          let d₀ : RestrictionArrowData G g T :=
            ⟨x, (q (f₀ ≫ h₀)).1, z, (q (f₀ ≫ h₀)).2.2.symm,
              (q (f₀ ≫ h₀)).2.1⟩
          let dR : RestrictionArrowData G g T :=
            ⟨y, (qR h₀).1, z, (qR h₀).2.2.symm, (qR h₀).2.1⟩
          let dL : RestrictionArrowData G g T :=
            ⟨x, (qL f₀).1, y, (qL f₀).2.2.symm, (qL f₀).2.1⟩
          let rh := restrictionHomEquiv G g T y z h₀
          let rf := restrictionHomEquiv G g T x y f₀
          have rhData : e rh.1 = dR := by
            exact e.apply_symm_apply dR
          have rfData : e rf.1 = dL := by
            exact e.apply_symm_apply dL
          have hmid : src.hom.app T rh.1 = tgt.hom.app T rf.1 :=
            rh.2.1.trans rf.2.2.symm
          let pH : (Deformation.composableArrows U'.obj P.obj src.hom tgt.hom).obj T :=
            ⟨(rh.1, rf.1), hmid⟩
          let cp := composableToPullback src.hom tgt.hom
          let zH : (AlgebraicSpaces.fiberProduct C S hS src tgt).obj.obj T := cp.app T pH
          let firstMap : Deformation.composableArrows U'.obj P.obj src.hom tgt.hom ⟶
              P.obj := {
            app := fun _ => ↾ fun p => p.1.1
            naturality := by intro X Y f; ext q; rfl }
          let secondMap : Deformation.composableArrows U'.obj P.obj src.hom tgt.hom ⟶
              P.obj := {
            app := fun _ => ↾ fun p => p.1.2
            naturality := by intro X Y f; ext q; rfl }
          have hcpFst : cp ≫ pullback.fst src.hom tgt.hom = firstMap := by
            dsimp [cp, composableToPullback]
            simp [firstMap]
          have hcpSnd : cp ≫ pullback.snd src.hom tgt.hom = secondMap := by
            dsimp [cp, composableToPullback]
            simp [secondMap]
          have hfst : (pullback.fst src.hom tgt.hom).app T (cp.app T pH) = rh.1 := by
            have hh := congrArg (fun k => (ConcreteCategory.hom (k.app T)) pH) hcpFst
            simpa [firstMap, pH] using hh
          have hsnd : (pullback.snd src.hom tgt.hom).app T (cp.app T pH) = rf.1 := by
            have hh := congrArg (fun k => (ConcreteCategory.hom (k.app T)) pH) hcpSnd
            simpa [secondMap, pH] using hh
          have hfst' : (fiberProductFst src tgt).hom.app T zH = rh.1 := by
            change (pullback.fst src.hom tgt.hom).app T zH = rh.1
            simpa [zH] using hfst
          have hsnd' : (fiberProductSnd src tgt).hom.app T zH = rf.1 := by
            change (pullback.snd src.hom tgt.hom).app T zH = rf.1
            simpa [zH] using hsnd
          have hrh : arr.hom.app T rh.1 =
              (qR h₀).1 := by
            calc
              _ = (e rh.1).arrow := (restrictionArrowDataEquiv_arrow G g T rh.1).symm
              _ = dR.arrow := congrArg RestrictionArrowData.arrow rhData
              _ = _ := rfl
          have hrf : arr.hom.app T rf.1 =
              (qL f₀).1 := by
            calc
              _ = (e rf.1).arrow := (restrictionArrowDataEquiv_arrow G g T rf.1).symm
              _ = dL.arrow := congrArg RestrictionArrowData.arrow rfData
              _ = _ := rfl
          have hleft : e ((restrictionHomEquiv G g T x z (f₀ ≫ h₀)).1) = d₀ := by
            exact e.apply_symm_apply d₀
          change e ((restrictionHomEquiv G g T x z (f₀ ≫ h₀)).1) =
            e ((restrictionCompForGroupoid G g).hom.app T zH)
          rw [hleft]
          apply RestrictionArrowData.ext
          · rw [restrictionArrowDataEquiv_source]
            change x = src.hom.app T
              ((restrictionCompositionData G g).hom.hom.app T zH)
            rw [restrictionCompositionData_hom_source_app, hsnd']
            exact rf.2.1.symm
          · rw [restrictionArrowDataEquiv_arrow]
            change (q (f₀ ≫ h₀)).1 = arr.hom.app T
              ((restrictionCompositionData G g).hom.hom.app T zH)
            rw [restrictionCompositionData_hom_arrow_app]
            let aa := arr.hom.app T
              ((fiberProductFst src tgt).hom.app T zH)
            let bb := arr.hom.app T
              ((fiberProductSnd src tgt).hom.app T zH)
            have haa : aa = (qR h₀).1 := by
              exact (congrArg (arr.hom.app T) hfst').trans (by simpa using hrh)
            have hbb : bb = (qL f₀).1 := by
              exact (congrArg (arr.hom.app T) hsnd').trans (by simpa using hrf)
            have hAA : G.source.hom.app T aa = G.target.hom.app T bb := by
              calc
                G.source.hom.app T aa = g.hom.app T (src.hom.app T
                    ((fiberProductFst src tgt).hom.app T zH)) := by
                  exact congrArg (fun f => f.hom.app T
                    ((fiberProductFst src tgt).hom.app T zH))
                    (restriction_condition G g).symm
                _ = g.hom.app T (tgt.hom.app T
                    ((fiberProductSnd src tgt).hom.app T zH)) := by
                  exact congrArg (g.hom.app T)
                    (pullback_condition_app src.hom tgt.hom T zH)
                _ = G.target.hom.app T bb := by
                  exact (congrArg (fun f => f.hom.app T
                    ((fiberProductSnd src tgt).hom.app T zH))
                    (restriction_condition' G g)).symm
            have hQ : G.source.hom.app T (qR h₀).1 =
                G.target.hom.app T (qL f₀).1 :=
              (qR h₀).2.1.trans (qL f₀).2.2.symm
            have hpair :
                (⟨(aa, bb), hAA⟩ :
                  (Deformation.composableArrows G.objects.obj G.arrows.obj
                    G.source.hom G.target.hom).obj T) =
                ⟨((qR h₀).1, (qL f₀).1), hQ⟩ := by
              apply Subtype.ext
              exact Prod.ext haa hbb
            have hlast : G.toGroupoidInFunctors.comp.app T ⟨(aa, bb), hAA⟩ =
                (restrictionCompositionData G g).underlying.hom.app T zH := by
              simpa only [aa, bb,
                GroupoidInAlgebraicSpaces.toGroupoidInFunctors] using
                (restrictionCompositionData_underlying_comp_app G g T zH).symm
            exact (G.toGroupoidInFunctors.evaluationArrowEquiv_comp T f₀ h₀).trans
              ((congrArg (fun p => G.toGroupoidInFunctors.comp.app T p) hpair.symm).trans
                hlast)
          · rw [restrictionArrowDataEquiv_target]
            change z = tgt.hom.app T
              ((restrictionCompositionData G g).hom.hom.app T zH)
            rw [restrictionCompositionData_hom_target_app, hfst']
            exact rh.2.2.symm
      }⟩ }
  have compMap : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (a b : P.obj.obj T) (h : src.hom.app T a = tgt.hom.app T b)
      (hG : G.source.hom.app T (arr.hom.app T a) =
        G.target.hom.app T (arr.hom.app T b)),
      G.toGroupoidInFunctors.compose T (arr.hom.app T a) (arr.hom.app T b) hG =
        arr.hom.app T (H.toGroupoidInFunctors.compose T a b h) := by
    intro T a b h hG
    let cp := composableToPullback src.hom tgt.hom
    let p : (Deformation.composableArrows U'.obj P.obj src.hom tgt.hom).obj T :=
      ⟨(a, b), h⟩
    let z : (AlgebraicSpaces.fiberProduct C S hS src tgt).obj.obj T := cp.app T p
    let firstMap : Deformation.composableArrows U'.obj P.obj src.hom tgt.hom ⟶ P.obj := {
      app := fun _ => ↾ fun p => p.1.1
      naturality := by intro X Y f; ext q; rfl }
    let secondMap : Deformation.composableArrows U'.obj P.obj src.hom tgt.hom ⟶ P.obj := {
      app := fun _ => ↾ fun p => p.1.2
      naturality := by intro X Y f; ext q; rfl }
    have hcpFst : cp ≫ pullback.fst src.hom tgt.hom = firstMap := by
      dsimp [cp, composableToPullback]
      simp [firstMap]
    have hcpSnd : cp ≫ pullback.snd src.hom tgt.hom = secondMap := by
      dsimp [cp, composableToPullback]
      simp [secondMap]
    have hfst : (pullback.fst src.hom tgt.hom).app T (cp.app T p) = a := by
      have hh := congrArg (fun k => (ConcreteCategory.hom (k.app T)) p) hcpFst
      simpa [firstMap, p] using hh
    have hsnd : (pullback.snd src.hom tgt.hom).app T (cp.app T p) = b := by
      have hh := congrArg (fun k => (ConcreteCategory.hom (k.app T)) p) hcpSnd
      simpa [secondMap, p] using hh
    have hfst' : (fiberProductFst src tgt).hom.app T z = a := by
      change (pullback.fst src.hom tgt.hom).app T z = a
      simpa [z] using hfst
    have hsnd' : (fiberProductSnd src tgt).hom.app T z = b := by
      change (pullback.snd src.hom tgt.hom).app T z = b
      simpa [z] using hsnd
    let aa := arr.hom.app T ((fiberProductFst src tgt).hom.app T z)
    let bb := arr.hom.app T ((fiberProductSnd src tgt).hom.app T z)
    have haa : aa = arr.hom.app T a := by
      exact congrArg (arr.hom.app T) hfst'
    have hbb : bb = arr.hom.app T b := by
      exact congrArg (arr.hom.app T) hsnd'
    have hAA : G.source.hom.app T aa = G.target.hom.app T bb := by
      calc
        G.source.hom.app T aa = g.hom.app T
            (src.hom.app T ((fiberProductFst src tgt).hom.app T z)) := by
          exact congrArg (fun f => f.hom.app T
            ((fiberProductFst src tgt).hom.app T z)) (restriction_condition G g).symm
        _ = g.hom.app T
            (tgt.hom.app T ((fiberProductSnd src tgt).hom.app T z)) := by
          exact congrArg (g.hom.app T)
            (pullback_condition_app src.hom tgt.hom T z)
        _ = G.target.hom.app T bb := by
          exact (congrArg (fun f => f.hom.app T
            ((fiberProductSnd src tgt).hom.app T z)) (restriction_condition' G g)).symm
    have hpair :
        (⟨(aa, bb), hAA⟩ :
          (Deformation.composableArrows G.toGroupoidInFunctors.objects
            G.toGroupoidInFunctors.arrows G.toGroupoidInFunctors.source
            G.toGroupoidInFunctors.target).obj T) =
        ⟨(arr.hom.app T a, arr.hom.app T b), hG⟩ := by
      apply Subtype.ext
      exact Prod.ext haa hbb
    have hlast : G.toGroupoidInFunctors.comp.app T ⟨(aa, bb), hAA⟩ =
        (restrictionCompositionData G g).underlying.hom.app T z := by
      simpa only [aa, bb,
        GroupoidInAlgebraicSpaces.toGroupoidInFunctors] using
        (restrictionCompositionData_underlying_comp_app G g T z).symm
    have hcompData : G.toGroupoidInFunctors.comp.app T
        ⟨(arr.hom.app T a, arr.hom.app T b), hG⟩ =
        (restrictionCompositionData G g).underlying.hom.app T z := by
      exact (congrArg (fun p => G.toGroupoidInFunctors.comp.app T p)
        hpair.symm).trans hlast
    exact hcompData.trans
      ((restrictionCompositionData_hom_arrow_app G g T z).symm.trans rfl)
  have mapSource : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (z : P.obj.obj T),
      G.source.hom.app T (arr.hom.app T z) = g.hom.app T (src.hom.app T z) := by
    intro T z
    exact congrArg (fun f => f.hom.app T z) (restriction_condition G g).symm
  have mapTarget : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (z : P.obj.obj T),
      G.target.hom.app T (arr.hom.app T z) = g.hom.app T (tgt.hom.app T z) := by
    intro T z
    exact congrArg (fun f => f.hom.app T z) (restriction_condition' G g)
  let F : Deformation.GroupoidInFunctors.Hom
      H.toGroupoidInFunctors G.toGroupoidInFunctors := {
    mapObjects := g.hom
    mapArrows := arr.hom
    map_source := mapSource
    map_target := mapTarget
    map_id := by
      intro T x
      let : Groupoid (H.objects.obj.obj T) := H.toGroupoidInFunctors.evaluationGroupoid T
      let : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
      let ih := H.toGroupoidInFunctors.identity T x
      let im := arr.hom.app T ih
      have hsource : H.toGroupoidInFunctors.source.app T ih = x := by
        change H.toGroupoidInFunctors.source.app T
          (H.toGroupoidInFunctors.identity T x) = x
        unfold Deformation.GroupoidInFunctors.identity
        exact (H.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.1
      have htarget : H.toGroupoidInFunctors.target.app T ih = x := by
        change H.toGroupoidInFunctors.target.app T
          (H.toGroupoidInFunctors.identity T x) = x
        unfold Deformation.GroupoidInFunctors.identity
        exact (H.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.2
      have hxx : src.hom.app T ih = tgt.hom.app T ih := hsource.trans htarget.symm
      have himSource : G.source.hom.app T im = g.hom.app T x := by
        calc
          G.source.hom.app T im = g.hom.app T (src.hom.app T ih) := mapSource T ih
          _ = g.hom.app T x := congrArg (g.hom.app T) hsource
      have himTarget : G.target.hom.app T im = g.hom.app T x := by
        calc
          G.target.hom.app T im = g.hom.app T (tgt.hom.app T ih) := mapTarget T ih
          _ = g.hom.app T x := congrArg (g.hom.app T) htarget
      have hG : G.source.hom.app T im = G.target.hom.app T im :=
        himSource.trans himTarget.symm
      have hHcomp : H.toGroupoidInFunctors.compose T ih ih hxx = ih := by
        have hc := H.toGroupoidInFunctors.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)
        simpa only [Category.id_comp,
          Deformation.GroupoidInFunctors.evaluationArrowEquiv_id] using hc.symm
      have hImComp :
          G.toGroupoidInFunctors.compose T im im hG = im := by
        exact (compMap T ih ih hxx hG).trans (congrArg (arr.hom.app T) hHcomp)
      let qG := G.toGroupoidInFunctors.evaluationArrowEquiv T
        (g.hom.app T x) (g.hom.app T x)
      let fcat := qG.symm ⟨im, himSource, himTarget⟩
      have hfa : (qG fcat).1 = im := by
        exact congrArg Subtype.val (qG.apply_symm_apply ⟨im, himSource, himTarget⟩)
      have hIdem : fcat ≫ fcat = fcat := by
        apply qG.injective
        apply Subtype.ext
        have hc := G.toGroupoidInFunctors.evaluationArrowEquiv_comp T fcat fcat
        have hEval :
            (qG (fcat ≫ fcat)).1 =
              G.toGroupoidInFunctors.compose T im im hG := by
          calc
            _ = G.toGroupoidInFunctors.compose T (qG fcat).1 (qG fcat).1 _ := hc
            _ = G.toGroupoidInFunctors.compose T im im hG := by
              congr 1
        exact hEval.trans (hImComp.trans hfa.symm)
      have hfcat : fcat = 𝟙 (g.hom.app T x) :=
        eq_id_of_idempotent_isIso fcat hIdem
      have himId : im = G.toGroupoidInFunctors.identity T (g.hom.app T x) := by
        have hv := congrArg (fun f => (qG f).1) hfcat
        exact hfa.symm.trans hv
      exact himId
    map_comp := by
      intro T a b h
      let hG : G.source.hom.app T (arr.hom.app T a) =
          G.target.hom.app T (arr.hom.app T b) :=
        (mapSource T a).trans ((congrArg (g.hom.app T) h).trans (mapTarget T b).symm)
      exact compMap T a b h hG }
  let hom : GroupoidInAlgebraicSpaces.Hom H G := {
    toGroupoidHom := F
    mapObjects_over := by
      rfl
    mapArrows_over := by
      rfl }
  refine {
    groupoid := H
    objects_eq := rfl
    arrows_eq := rfl
    objectsToBase_eq := ?_
    arrowsToBase_eq := ?_
    source_eq := ?_
    target_eq := ?_
    hom := hom
    mapObjects_eq := by
      change g.hom = (eqToHom rfl ≫ g).hom
      simp
    mapArrows_eq := by
      change arr.hom = (eqToHom rfl ≫ arr).hom
      simp
    evaluation_fullyFaithful := fun T => by
      let : Groupoid (H.objects.obj.obj T) := H.toGroupoidInFunctors.evaluationGroupoid T
      let : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
      let qH := H.toGroupoidInFunctors.evaluationArrowEquiv T
      let qG := G.toGroupoidInFunctors.evaluationArrowEquiv T
      let e := restrictionArrowDataEquiv G g T
      have hArrowObj : H.toGroupoidInFunctors.arrows.obj T = P.obj.obj T := by
        rfl
      let : Functor.Full (F.evaluation T) := ⟨by
        intro x y f
        let q := G.toGroupoidInFunctors.evaluationArrowEquiv T
          (g.hom.app T x) (g.hom.app T y)
        let d : RestrictionArrowData G g T :=
          ⟨x, (q f).1, y, (q f).2.2.symm, (q f).2.1⟩
        let zval := e.symm d
        have hzs : src.hom.app T zval = x := by
          rw [← restrictionArrowDataEquiv_source]
          rw [e.apply_symm_apply d]
        have hzt : tgt.hom.app T zval = y := by
          rw [← restrictionArrowDataEquiv_target]
          rw [e.apply_symm_apply d]
        let z : {z : P.obj.obj T // src.hom.app T z = x ∧ tgt.hom.app T z = y} :=
          ⟨zval, hzs, hzt⟩
        let f' := (qH x y).symm z
        refine ⟨f', ?_⟩
        apply q.injective
        apply Subtype.ext
        have hm := Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow F T f'
        have hdata : (e zval).arrow = (q f).1 := by
          rw [e.apply_symm_apply]
        have harr : arr.hom.app T zval = (q f).1 := by
          simpa only [e, restrictionArrowDataEquiv_arrow] using hdata
        have hq : (qH x y) f' = z := (qH x y).apply_symm_apply z
        have harr' : arr.hom.app T ((qH x y) f').1 = (q f).1 := by
          exact (congrArg (fun w : {z : P.obj.obj T //
            src.hom.app T z = x ∧ tgt.hom.app T z = y} => arr.hom.app T w.1) hq).trans harr
        exact hm.trans harr'
      ⟩
      let : Functor.Faithful (F.evaluation T) := ⟨by
        intro x y f h hEq
        apply (qH x y).injective
        apply Subtype.ext
        let zf : P.obj.obj T := hArrowObj ▸ ((qH x y) f).1
        let zh : P.obj.obj T := hArrowObj ▸ ((qH x y) h).1
        apply e.injective
        apply RestrictionArrowData.ext
        · change (e zf).sourceLift = (e zh).sourceLift
          rw [restrictionArrowDataEquiv_source, restrictionArrowDataEquiv_source]
          have hsf : src.hom.app T zf = x := by
            exact ((qH x y) f).2.1
          have hsh : src.hom.app T zh = x := by
            exact ((qH x y) h).2.1
          exact hsf.trans hsh.symm
        · have hm := congrArg
            (fun k => (G.toGroupoidInFunctors.evaluationArrowEquiv T
              ((F.evaluation T).obj x) ((F.evaluation T).obj y) k).1) hEq
          have hf := Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow F T f
          have hh := Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow F T h
          have hzf : zf = ((qH x y) f).1 := by
            dsimp only [zf]
          have hzh : zh = ((qH x y) h).1 := by
            dsimp only [zh]
          have hm' := hm
          rw [hf, hh] at hm'
          have hArr : arr.hom.app T zf = arr.hom.app T zh := by
            calc
              arr.hom.app T zf = arr.hom.app T ((qH x y) f).1 :=
                congrArg (arr.hom.app T) hzf
              _ = arr.hom.app T ((qH x y) h).1 := by
                exact hm'
              _ = arr.hom.app T zh := congrArg (arr.hom.app T) hzh.symm
          change (e zf).arrow = (e zh).arrow
          rw [restrictionArrowDataEquiv_arrow, restrictionArrowDataEquiv_arrow]
          exact hArr
        · change (e zf).targetLift = (e zh).targetLift
          rw [restrictionArrowDataEquiv_target, restrictionArrowDataEquiv_target]
          have htf : tgt.hom.app T zf = y := by
            exact ((qH x y) f).2.2
          have hth : tgt.hom.app T zh = y := by
            exact ((qH x y) h).2.2
          exact htf.trans hth.symm
      ⟩
      exact ⟨Functor.FullyFaithful.ofFullyFaithful (F.evaluation T)⟩ }
  · simp [H]
  · simp [H, arr]
  · simp [H, src]
  · simp [H, tgt]

/-- **Stacks 044B.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `B` and let
`g : U' ⟶ U` be a morphism of algebraic spaces. Form the fibre product squares
`P₁ = U' ×_{g, U, t} R` (projections `pU`, `pR`), `P₂ = R ×_{s, U, g} U'` (projections `qR`,
`qU`), and `R' = P₁ ×_{pR, R, qR} P₂` (projections `a`, `b`), and put `t' = a ≫ pU`,
`s' = b ≫ qU`. Then the restriction `(restrict G g).groupoid` is a groupoid in algebraic spaces
over `B` whose space of objects is `U'` (over `B` through `g`), whose space of arrows is `R'`
(over `B` through `R`), whose source and target are `s'` and `t'`, and whose composition law
`c' : R' ×_{s', U', t'} R' ⟶ R'` keeps the target of the first arrow and the source of the second
and composes the two underlying arrows by `c`. The maps `g : U' ⟶ U` and `a ≫ pR : R' ⟶ R` are
the two components of the morphism `(restrict G g).hom` of groupoids in algebraic spaces over `B`.

Moreover, for every scheme `T` of the site, the functor of groupoids
`(U'(T), R'(T), s', t', c') ⟶ (U(T), R(T), s, t, c)` is the restriction of `(U(T), R(T), s, t, c)`
via `U'(T) ⟶ U(T)`: an element of `R'(T)` is exactly a triple `(x, r, y)` with `x, y ∈ U'(T)`,
`r ∈ R(T)`, `t(r) = g(x)` and `s(r) = g(y)`, with `t'` and `s'` the outer projections and the
composite of `(x, r, y)` and `(y, r'', z)` equal to `(x, c(r, r''), z)`; the functor is `g` on
objects and is fully faithful.

The same holds for the `T`-points over `B`, in the source's sense of a scheme `T` over `B`: for a
scheme `T` of the site and a point `b ∈ B(T)`, the groupoid `(U'(T), R'(T), s', t', c')` of
`T`-points of the restriction lying over `b` maps to the groupoid `(U(T), R(T), s, t, c)` of
`T`-points of `G` lying over `b`, and this functor is the restriction along `U'(T) ⟶ U(T)`: an
arrow over `b` is exactly a triple `(x, r, y)` over `b` as above, the composite of two arrows over
`b` lies over `b` and is computed as above, and the functor, which is `g` on objects and the
functor on all `T`-points on arrows, is fully faithful. -/
@[stacks 044B]
public theorem restrict_isRestriction
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    let H := (restrict G g).groupoid
    let φ := (restrict G g).hom
    ∃ (P₁ : AlgebraicSpaces C S hS) (pU : P₁ ⟶ U') (pR : P₁ ⟶ G.arrows)
      (P₂ : AlgebraicSpaces C S hS) (qR : P₂ ⟶ G.arrows) (qU : P₂ ⟶ U')
      (a : H.arrows ⟶ P₁) (b : H.arrows ⟶ P₂),
      IsPullback pU pR g G.target ∧ IsPullback qR qU G.source g ∧ IsPullback a b pR qR ∧
      H.objects = U' ∧ H.target = a ≫ pU ∧ H.source = b ≫ qU ∧
      H.objectsToBase = g ≫ G.objectsToBase ∧
      H.arrowsToBase = (a ≫ pR) ≫ G.arrowsToBase ∧
      H.comp ≫ H.target = fiberProductFst H.source H.target ≫ H.target ∧
      H.comp ≫ H.source = fiberProductSnd H.source H.target ≫ H.source ∧
      (∃ m : AlgebraicSpaces.fiberProduct C S hS H.source H.target ⟶
          AlgebraicSpaces.fiberProduct C S hS G.source G.target,
        m ≫ fiberProductFst G.source G.target = fiberProductFst H.source H.target ≫ a ≫ pR ∧
        m ≫ fiberProductSnd G.source G.target = fiberProductSnd H.source H.target ≫ a ≫ pR ∧
        H.comp ≫ a ≫ pR = m ≫ G.comp) ∧
      φ.toGroupoidHom.mapObjects = g.hom ∧
      φ.toGroupoidHom.mapArrows = (a ≫ pR).hom ∧
      (∀ T : (BigFppfOver C S hS)ᵒᵖ,
        (∀ (x y : U'.obj.obj T) (r : G.arrows.obj.obj T),
          G.target.hom.app T r = g.hom.app T x → G.source.hom.app T r = g.hom.app T y →
          ∃! z : H.arrows.obj.obj T, H.target.hom.app T z = x ∧
            (a ≫ pR).hom.app T z = r ∧ H.source.hom.app T z = y) ∧
        (∀ (z w : H.arrows.obj.obj T) (h : H.source.hom.app T z = H.target.hom.app T w)
          (h' : G.source.hom.app T ((a ≫ pR).hom.app T z) =
            G.target.hom.app T ((a ≫ pR).hom.app T w)),
          H.target.hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              H.target.hom.app T z ∧
            (a ≫ pR).hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              G.toGroupoidInFunctors.compose T ((a ≫ pR).hom.app T z)
                ((a ≫ pR).hom.app T w) h' ∧
            H.source.hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              H.source.hom.app T w) ∧
        (∀ x : U'.obj.obj T, (φ.toGroupoidHom.evaluation T).obj x = g.hom.app T x) ∧
        Nonempty (φ.toGroupoidHom.evaluation T).FullyFaithful) ∧
      ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (b : B.obj.obj T),
        (∀ (x y : U'.obj.obj T) (r : G.arrows.obj.obj T),
          H.objectsToBase.hom.app T x = b → H.objectsToBase.hom.app T y = b →
          G.arrowsToBase.hom.app T r = b →
          G.target.hom.app T r = g.hom.app T x → G.source.hom.app T r = g.hom.app T y →
          ∃! z : H.arrows.obj.obj T, H.arrowsToBase.hom.app T z = b ∧
            H.target.hom.app T z = x ∧ (a ≫ pR).hom.app T z = r ∧
            H.source.hom.app T z = y) ∧
        (∀ (z w : H.arrows.obj.obj T) (h : H.source.hom.app T z = H.target.hom.app T w)
          (h' : G.source.hom.app T ((a ≫ pR).hom.app T z) =
            G.target.hom.app T ((a ≫ pR).hom.app T w)),
          H.arrowsToBase.hom.app T z = b → H.arrowsToBase.hom.app T w = b →
          H.arrowsToBase.hom.app T (H.toGroupoidInFunctors.compose T z w h) = b ∧
          H.target.hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              H.target.hom.app T z ∧
            (a ≫ pR).hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              G.toGroupoidInFunctors.compose T ((a ≫ pR).hom.app T z)
                ((a ≫ pR).hom.app T w) h' ∧
            H.source.hom.app T (H.toGroupoidInFunctors.compose T z w h) =
              H.source.hom.app T w) ∧
        ∃ F : ObjectProperty.FullSubcategory
              (fun x : H.toGroupoidInFunctors.Evaluation T => H.objectsToBase.hom.app T x = b) ⥤
            ObjectProperty.FullSubcategory
              (fun x : G.toGroupoidInFunctors.Evaluation T => G.objectsToBase.hom.app T x = b),
          (∀ x, (F.obj x).obj = g.hom.app T x.obj) ∧
          F ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ φ.toGroupoidHom.evaluation T ∧
          Nonempty F.FullyFaithful := by
  intro H φ
  let p := fiberProductSnd g G.target
  let q := fiberProductFst G.source g
  let arr := restrictionArrowsToArrows G g
  let src := restrictionSource G g
  let tgt := restrictionTarget G g
  have hw : (fiberProductFst src tgt ≫ arr) ≫ G.source =
      (fiberProductSnd src tgt ≫ arr) ≫ G.target := by
    rw [Category.assoc, Category.assoc, ← restriction_condition, restriction_condition',
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ g) (fiberProduct_condition src tgt)
  let m := (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (fiberProductFst src tgt ≫ arr) (fiberProductSnd src tgt ≫ arr) hw
  have hm₁ : m ≫ fiberProductFst G.source G.target = fiberProductFst src tgt ≫ arr :=
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _
  have hm₂ : m ≫ fiberProductSnd G.source G.target = fiberProductSnd src tgt ≫ arr :=
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _
  have hcomp : restrictionComp G g ≫ arr = m ≫ G.comp := by
    rw [show restrictionComp G g ≫ arr = (restrictionCompositionData G g).underlying from
      (restrictionCompositionData G g).hom_comp]
    apply ObjectProperty.hom_ext
    ext T z
    refine (restrictionCompositionData_underlying_comp_app G g T z).trans ?_
    change G.comp.hom.app T ((composableToPullback G.source.hom G.target.hom).app T _) =
      G.comp.hom.app T (m.hom.app T z)
    congr 1
    refine (pullbackAppEquiv G.source.hom G.target.hom T).injective
      (Subtype.ext (Prod.ext ?_ ?_))
    · simp only [pullbackAppEquiv_fst]
      exact (congrArg (fun k : Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom ⟶ G.arrows.obj => k.app T _)
          (pullback.lift_fst _ _ _)).trans
        ((congrArg (fun k => k.hom.app T z) hm₁).symm.trans
          (pullbackAppEquiv_fst _ _ T _).symm)
    · simp only [pullbackAppEquiv_snd]
      exact (congrArg (fun k : Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom ⟶ G.arrows.obj => k.app T _)
          (pullback.lift_snd _ _ _)).trans
        ((congrArg (fun k => k.hom.app T z) hm₂).symm.trans
          (pullbackAppEquiv_snd _ _ T _).symm)
  have key : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (x y : U'.obj.obj T) (r : G.arrows.obj.obj T),
      G.target.hom.app T r = g.hom.app T x → G.source.hom.app T r = g.hom.app T y →
      ∃! z : (restrictionArrows G g).obj.obj T,
        tgt.hom.app T z = x ∧ arr.hom.app T z = r ∧ src.hom.app T z = y := by
    intro T x y r ht hs
    let e := restrictionArrowDataEquiv G g T
    let d : RestrictionArrowData G g T := ⟨y, r, x, ht.symm, hs⟩
    refine ⟨e.symm d, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← restrictionArrowDataEquiv_target, Equiv.apply_symm_apply]
    · rw [← restrictionArrowDataEquiv_arrow, Equiv.apply_symm_apply]
    · rw [← restrictionArrowDataEquiv_source, Equiv.apply_symm_apply]
    · rintro z ⟨h₁, h₂, h₃⟩
      apply e.injective
      rw [Equiv.apply_symm_apply]
      apply RestrictionArrowData.ext
      · exact (restrictionArrowDataEquiv_source G g T z).trans h₃
      · exact (restrictionArrowDataEquiv_arrow G g T z).trans h₂
      · exact (restrictionArrowDataEquiv_target G g T z).trans h₁
  refine ⟨_, fiberProductFst g G.target, p, _, q, fiberProductSnd G.source g,
    fiberProductFst p q, fiberProductSnd p q,
    AlgebraicSpaces.isPullback_fiberProduct C S hS _ _,
    AlgebraicSpaces.isPullback_fiberProduct C S hS _ _,
    AlgebraicSpaces.isPullback_fiberProduct C S hS _ _,
    rfl, rfl, rfl, rfl, rfl,
    (restrictionCompositionData G g).hom_target,
    (restrictionCompositionData G g).hom_source,
    ⟨m, hm₁, hm₂, hcomp⟩, rfl, rfl, fun T => ⟨?_, ?_, fun _ => rfl, ?_⟩,
    fun T b => ⟨?_, ?_, ?_⟩⟩
  · exact key T
  · intro z w h h'
    exact ⟨functorGroupoid_comp_target H.toGroupoidInFunctors T z w h,
      ((restrict G g).hom.toGroupoidHom.map_comp T z w h).symm,
      functorGroupoid_comp_source H.toGroupoidInFunctors T z w h⟩
  · exact (restrict G g).evaluation_fullyFaithful T
  · intro x y r _ _ hr ht hs
    obtain ⟨z, ⟨h₁, h₂, h₃⟩, hu⟩ := key T x y r ht hs
    refine ⟨z, ⟨?_, h₁, h₂, h₃⟩, fun z' ⟨_, h₁', h₂', h₃'⟩ => hu z' ⟨h₁', h₂', h₃'⟩⟩
    change G.arrowsToBase.hom.app T (arr.hom.app T z) = b
    rw [h₂, hr]
  · intro z w h h' hz _
    have ht := functorGroupoid_comp_target H.toGroupoidInFunctors T z w h
    refine ⟨?_, ht, ((restrict G g).hom.toGroupoidHom.map_comp T z w h).symm,
      functorGroupoid_comp_source H.toGroupoidInFunctors T z w h⟩
    calc
      H.arrowsToBase.hom.app T (H.toGroupoidInFunctors.compose T z w h) =
          H.objectsToBase.hom.app T
            (H.target.hom.app T (H.toGroupoidInFunctors.compose T z w h)) :=
        (congrArg (fun k => k.hom.app T (H.toGroupoidInFunctors.compose T z w h))
          H.target_over).symm
      _ = H.objectsToBase.hom.app T (H.target.hom.app T z) :=
        congrArg (H.objectsToBase.hom.app T) ht
      _ = H.arrowsToBase.hom.app T z :=
        congrArg (fun k => k.hom.app T z) H.target_over
      _ = b := hz
  · obtain ⟨hFF⟩ := (restrict G g).evaluation_fullyFaithful T
    refine ⟨ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ φ.toGroupoidHom.evaluation T) (fun x => x.property),
      fun _ => rfl, rfl, ⟨?_⟩⟩
    exact Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
      ((ObjectProperty.fullyFaithfulι _).comp hFF)

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
