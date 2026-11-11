module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackFunctor

/-!
# Pullback of descent data along a commutative square

A commutative square of schemes induces a pullback functor between the categories of descent
data for its two vertical arrows. On underlying schemes it is base change along the upper
horizontal arrow, and the gluing isomorphism is pulled back along the induced map of
self-fibre products.

## Main definitions

* `AlgebraicGeometry.DescentData.PullbackFunctor` records the pullback functor together with
  its action on objects and arrows and the description of its gluing isomorphism.
* `AlgebraicGeometry.DescentData.pullbackFunctor` constructs it.

## Implementation notes

Descent data for a single morphism are represented by `DescentData` indexed by `Unit`. The
construction is obtained from the pullback functor for a morphism of families by taking both
families to be singletons, which are indexed by `ULift Unit`; the two `Unit` conventions are
reconciled by transporting descent data and their morphisms along `ULift.up` and
`ULift.down`. The fields of `PullbackFunctor` specify the usual base-change object and arrow
together with the square saying that the gluing isomorphism is the pullback of the original
one.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits
open MorphismOfSchemeFamilies

private lemma eqToHom_symm_comp_id {C : Type*} [Category C] {A B : C} (h : A = B) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 B := by
  cases h
  simp

private lemma conjugate_comp {C : Type*} [Category C]
    {A A' B B' C₀ C₀' : C} (hA : A = A') (hB : B = B') (hC : C₀ = C₀')
    (f : A ⟶ B) (g : B ⟶ C₀) :
    (eqToHom hA.symm ≫ f ≫ eqToHom hB) ≫
      (eqToHom hB.symm ≫ g ≫ eqToHom hC) =
        eqToHom hA.symm ≫ (f ≫ g) ≫ eqToHom hC := by
  cases hA
  cases hB
  cases hC
  simp

/-- A pullback functor on descent data, together with the equations specifying the source
construction. -/
public structure PullbackFunctor
    {S S' X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (comm : f ≫ a = a' ≫ h) where
  /-- The functor on descent data. -/
  functor :
    DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a) ⥤
      DescentData (S := S') (X := fun _ : Unit ↦ X') (fun _ ↦ a')
  /-- The underlying object is the usual base change `X' ×_X V`. -/
  objIso (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    (functor.obj D).obj () ≅ (Over.pullback f).obj (D.obj ())
  /-- The map from the source of the pulled-back gluing map to the source of the original
  gluing map. -/
  sourceMap (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    pullback (((functor.obj D).obj ()).hom ≫ a') a' ⟶
      pullback ((D.obj ()).hom ≫ a) a
  sourceMap_fst (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    sourceMap D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (objIso D).hom.left ≫ pullback.fst _ _
  sourceMap_snd (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    sourceMap D ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f
  /-- The corresponding map between the targets of the gluing maps. -/
  targetMap (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    pullback a' (((functor.obj D).obj ()).hom ≫ a') ⟶
      pullback a ((D.obj ()).hom ≫ a)
  targetMap_fst (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    targetMap D ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f
  targetMap_snd (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    targetMap D ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (objIso D).hom.left ≫ pullback.fst _ _
  /-- The gluing isomorphism is the pullback of the original one along the induced map of
  self-fibre products. -/
  gluing (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    ((functor.obj D).gluingPullbackIso () ()).hom ≫ targetMap D =
      sourceMap D ≫ (D.gluingPullbackIso () ()).hom
  /-- The functor acts on arrows by ordinary base change. -/
  map {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)} (g : D ⟶ E) :
    (objIso D).hom ≫ (Over.pullback f).map (g.hom ()) =
      (functor.map g).hom () ≫ (objIso E).hom

/-- Pullback of descent data along a commutative square of schemes. On underlying schemes this
is base change along `f`; the gluing isomorphism is pulled back along the induced map of
self-fibre products. -/
@[stacks 02VR "the pullback functor on descent data"]
noncomputable def pullbackFunctor
    {S S' X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (comm : f ≫ a = a' ≫ h) :
    PullbackFunctor a a' h f comm :=
  by
    let fam : PreZeroHypercover.{u} S :=
      { I₀ := ULift.{u} Unit, X := fun _ => X, f := fun _ => a }
    let fam' : PreZeroHypercover.{u} S' :=
      { I₀ := ULift.{u} Unit, X := fun _ => X', f := fun _ => a' }
    let G : MorphismOfSchemeFamilies.{u} :=
      { sourceBase := S', targetBase := S, sourceFamily := fam', targetFamily := fam,
        baseHom := h,
        familyHom := { s₀ := fun _ => ULift.up (), h₀ := fun _ => f, w₀ := fun _ => comm } }
    let up : DescentData (fun _ : Unit => a) → DescentData fam.f := fun D =>
      { obj := fun i => D.obj i.down
        gluing := fun i j => D.gluing i.down j.down
        cocycle := fun i j k => D.cocycle i.down j.down k.down }
    let down : DescentData fam'.f → DescentData (fun _ : Unit => a') := fun D =>
      { obj := fun i => D.obj (ULift.up i)
        gluing := fun i j => D.gluing (ULift.up i) (ULift.up j)
        cocycle := fun i j k => D.cocycle (ULift.up i) (ULift.up j) (ULift.up k) }
    let upHom {D E : DescentData (fun _ : Unit => a)} (g : D ⟶ E) : up D ⟶ up E :=
      { hom := fun i => g.hom i.down
        comm := fun i j => g.comm i.down j.down }
    let downHom {D E : DescentData fam'.f} (g : D ⟶ E) : down D ⟶ down E :=
      { hom := fun i => g.hom (ULift.up i)
        comm := fun i j => g.comm (ULift.up i) (ULift.up j) }
    let Q := MorphismOfSchemeFamilies.pullbackFunctor G
    let pulled (D : DescentData (fun _ : Unit => a)) :=
      pulledBackDatum G (up D)
    let qMap {D E : DescentData (fun _ : Unit => a)} (g : D ⟶ E) :
        pulled D ⟶ pulled E :=
      eqToHom (Q.obj_eq (up D)).symm ≫ Q.functor.map (upHom g) ≫
        eqToHom (Q.obj_eq (up E))
    let objIso (D : DescentData (fun _ : Unit => a)) :
        (down (pulled D)).obj () ≅ (Over.pullback f).obj (D.obj ()) :=
      pulledBackDatumObjIso G (up D) (ULift.up ())
    let srcMap (D : DescentData (fun _ : Unit => a)) :
        pullback (((down (pulled D)).obj ()).hom ≫ a') a' ⟶
          pullback ((D.obj ()).hom ≫ a) a :=
      pullback.lift
        (pullback.fst _ _ ≫ (objIso D).hom.left ≫ pullback.fst _ _)
        (pullback.snd _ _ ≫ f) (by
          simp only [Category.assoc, pullback.condition_assoc, comm]
          rw [← Over.pullback_obj_hom, Over.w_assoc]
          simpa only [Category.assoc] using congrArg (fun k => k ≫ h)
            (pullback.condition (f := ((down (pulled D)).obj ()).hom ≫ a')
              (g := a')))
    let tgtMap (D : DescentData (fun _ : Unit => a)) :
        pullback a' (((down (pulled D)).obj ()).hom ≫ a') ⟶
          pullback a ((D.obj ()).hom ≫ a) :=
      pullback.lift (pullback.fst _ _ ≫ f)
        (pullback.snd _ _ ≫ (objIso D).hom.left ≫ pullback.fst _ _) (by
          simp only [Category.assoc, pullback.condition_assoc, comm]
          rw [← Over.pullback_obj_hom, Over.w_assoc])
    refine
      { functor :=
          { obj := fun D => down (pulled D)
            map := fun {D E} g => downHom (qMap g)
            map_id := by
              intro D
              apply DescentData.hom_ext
              intro i
              dsimp [downHom, qMap]
              have hid : upHom (𝟙 D) = 𝟙 (up D) := by
                apply DescentData.hom_ext
                intro j
                rfl
              rw [hid, Q.functor.map_id]
              have hcancel := congrArg (fun q => q.hom (ULift.up i))
                (eqToHom_symm_comp_id (Q.obj_eq (up D)))
              simpa only [DescentData.comp_hom, DescentData.id_hom,
                Category.id_comp, Category.comp_id] using hcancel
            map_comp := by
              intro D E H g k
              apply DescentData.hom_ext
              intro i
              dsimp [downHom, qMap]
              have hcomp : upHom (g ≫ k) = upHom g ≫ upHom k := by
                apply DescentData.hom_ext
                intro j
                rfl
              rw [hcomp, Q.functor.map_comp]
              have hconj := congrArg (fun q => q.hom (ULift.up i))
                (conjugate_comp (Q.obj_eq (up D)) (Q.obj_eq (up E))
                  (Q.obj_eq (up H)) (Q.functor.map (upHom g))
                  (Q.functor.map (upHom k)))
              simpa only [DescentData.comp_hom] using hconj.symm }
        objIso := objIso
        sourceMap := srcMap
        sourceMap_fst := by intros; simp [srcMap]
        sourceMap_snd := by intros; simp [srcMap]
        targetMap := tgtMap
        targetMap_fst := by intros; simp [tgtMap]
        targetMap_snd := by intros; simp [tgtMap]
        gluing := by
          intro D
          have hs : srcMap D = pulledBackDatumSourceMap G
              (up D) (ULift.up ()) (ULift.up ()) := by rfl
          have ht : tgtMap D = pulledBackDatumTargetMap G
              (up D) (ULift.up ()) (ULift.up ()) := by rfl
          rw [hs, ht]
          exact pulledBackDatum_gluing G (up D)
            (ULift.up ()) (ULift.up ())
        map := by
          intro D E g
          have hQ := Q.map (up D) (up E) (upHom g) (ULift.up ())
          have hQ' := congrArg
            (fun z => (eqToHom (Q.obj_eq (up D)).symm).hom (ULift.up ()) ≫ z) hQ
          have hcancel0 := congrArg (fun z => z.hom (ULift.up ()))
            (eqToHom_symm_comp_id (Q.obj_eq (up D)))
          have hcancel :
              (eqToHom (Q.obj_eq (up D)).symm).hom (ULift.up ()) ≫
                (eqToHom (Q.obj_eq (up D))).hom (ULift.up ()) = 𝟙 _ := by
            simpa only [DescentData.comp_hom, DescentData.id_hom] using hcancel0
          rw [← Category.assoc, hcancel, Category.id_comp] at hQ'
          exact hQ' }

end AlgebraicGeometry.DescentData
