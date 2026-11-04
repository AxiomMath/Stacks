module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.DescentIso

/-!
# Independence of the pullback functor on descent data from the chosen horizontal arrow

Two morphisms `f₀, f₁ : X' ⟶ X` completing the same commutative square induce canonically
isomorphic pullback functors on descent data. The component of the comparison at a descent
datum `D` is the base-change comparison `f₀^* V ≅ f₁^* V` supplied by the gluing isomorphism
of `D`.

## Main definitions

* `AlgebraicGeometry.DescentData.PullbackFunctorIso` records the comparison together with the
  equations identifying its components.
* `AlgebraicGeometry.DescentData.pullbackFunctorIsoOfSpec` constructs it for any two
  specified pullback functors, and
  `AlgebraicGeometry.DescentData.pullbackFunctorIso` for the canonical ones.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

/-- The canonical comparison between two specified pullback functors. The
`comparisonSourceMap` is the map to `V ×_S X` induced by `(v, x') ↦ (v, f₁ x')`; the last
equation says that the component is obtained by applying the original gluing isomorphism to
this map. -/
structure PullbackFunctorIso
    {S S' X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f₀ f₁ : X' ⟶ X) (comm₀ : f₀ ≫ a = a' ≫ h) (comm₁ : f₁ ≫ a = a' ≫ h)
    (P₀ : PullbackFunctor a a' h f₀ comm₀) (P₁ : PullbackFunctor a a' h f₁ comm₁) where
  /-- The natural isomorphism between the two pullback functors. -/
  iso : P₀.functor ≅ P₁.functor
  /-- Its component transported to the standard pullback models. -/
  comparisonMap (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    (Over.pullback f₀).obj (D.obj ()) ⟶ (Over.pullback f₁).obj (D.obj ())
  component (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    (P₀.objIso D).hom ≫ comparisonMap D = (iso.hom.app D).hom () ≫ (P₁.objIso D).hom
  /-- The map used to pull the gluing isomorphism back along `(f₀, f₁)`. -/
  comparisonSourceMap (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    ((Over.pullback f₀).obj (D.obj ())).left ⟶ pullback ((D.obj ()).hom ≫ a) a
  comparisonSourceMap_fst (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    comparisonSourceMap D ≫ pullback.fst _ _ = pullback.fst _ _
  comparisonSourceMap_snd (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    comparisonSourceMap D ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f₁
  comparison_gluing (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    (comparisonMap D).left ≫ pullback.fst _ _ =
      comparisonSourceMap D ≫ (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _

section Comparison

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {hS : S' ⟶ S}
  {f₀ f₁ : X' ⟶ X} {comm₀ : f₀ ≫ a = a' ≫ hS} {comm₁ : f₁ ≫ a = a' ≫ hS}
  (P₀ : PullbackFunctor a a' hS f₀ comm₀) (P₁ : PullbackFunctor a a' hS f₁ comm₁)
  (D : DescentData (fun _ : Unit ↦ a))

/-- The comparison of the two pulled-back descent data on underlying objects: base change
along `f₀`, then the gluing action, then base change along `f₁` read backwards. -/
def baseChangeObjIso : (P₀.functor.obj D).obj () ≅ (P₁.functor.obj D).obj () :=
  P₀.objIso D ≪≫ D.baseChangeIso f₀ f₁ (comm₀.trans comm₁.symm) ≪≫ (P₁.objIso D).symm

/-- Under the identifications `objIso` with the standard pullback models, `baseChangeObjIso` is
`baseChangeMap`. -/
lemma baseChangeObjIso_hom_objIso :
    (baseChangeObjIso P₀ P₁ D).hom ≫ (P₁.objIso D).hom =
      (P₀.objIso D).hom ≫ D.baseChangeMap f₀ f₁ (comm₀.trans comm₁.symm) := by
  simp [baseChangeObjIso, baseChangeIso, Category.assoc]

/-- The equation `baseChangeObjIso_hom_objIso` on underlying morphisms of schemes. -/
@[reassoc]
lemma baseChangeObjIso_hom_left_objIso :
    (baseChangeObjIso P₀ P₁ D).hom.left ≫ (P₁.objIso D).hom.left =
      (P₀.objIso D).hom.left ≫
        (D.baseChangeMap f₀ f₁ (comm₀.trans comm₁.symm)).left := by
  simpa only [Over.comp_left] using
    congrArg Over.Hom.left (baseChangeObjIso_hom_objIso P₀ P₁ D)

section Conditions

private lemma fst_base_cond :
    pullback.fst (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫
        ((P₀.functor.obj D).obj ()).hom ≫ a' ≫ hS =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ a' ≫ hS := by
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ hS)
    (pullback.condition (f := ((P₀.functor.obj D).obj ()).hom ≫ a') (g := a'))

include comm₀ in
private lemma fst_objIso_fst_cond :
    (pullback.fst (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ (P₀.objIso D).hom.left ≫
        pullback.fst (D.obj ()).hom f₀) ≫ (D.obj ()).hom ≫ a =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ a' ≫ hS := by
  simp only [Category.assoc]
  rw [← Category.assoc (pullback.fst (D.obj ()).hom f₀), pullback.condition]
  simp only [Category.assoc]
  rw [comm₀, P₀.objIso_hom_left_snd_assoc]
  exact fst_base_cond P₀ D

private lemma snd_comp_cond (f : X' ⟶ X) (comm : f ≫ a = a' ≫ hS) :
    (pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ f) ≫ a =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ a' ≫ hS := by
  rw [Category.assoc, comm]

private lemma fst_structure_cond (f : X' ⟶ X) (comm : f ≫ a = a' ≫ hS) :
    (pullback.fst (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫
        ((P₀.functor.obj D).obj ()).hom ≫ f) ≫ a =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ a' ≫ hS := by
  simpa only [Category.assoc, comm] using fst_base_cond P₀ D

end Conditions

/-- The gluing action of `D` applied to the tautological point of the source of the gluing
isomorphism of the datum pulled back along `f₀`, with a prescribed target `w`. -/
private def commonAct (w : pullback (((P₀.functor.obj D).obj ()).hom ≫ a') a' ⟶ X)
    (hw : w ≫ a = pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ a' ≫ hS) :
    pullback (((P₀.functor.obj D).obj ()).hom ≫ a') a' ⟶ (D.obj ()).left :=
  D.act (pullback.fst (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫
    (P₀.objIso D).hom.left ≫ pullback.fst (D.obj ()).hom f₀) w
    ((fst_objIso_fst_cond P₀ D).trans hw.symm)

private lemma actOn_objIso_fst_eq :
    ((P₀.functor.obj D).actOn ≫ (P₀.objIso D).hom.left) ≫
        pullback.fst (D.obj ()).hom f₀ =
      commonAct P₀ D _ (snd_comp_cond P₀ D f₀ comm₀) := by
  rw [Category.assoc, P₀.actOn_objIso_fst, D.comp_actOn, commonAct]
  exact D.act_congr (P₀.sourceMap_fst D) (P₀.sourceMap_snd D)

private lemma actOn_objIso_snd_eq :
    ((P₀.functor.obj D).actOn ≫ (P₀.objIso D).hom.left) ≫
        (pullback.snd (D.obj ()).hom f₀ ≫ f₁) =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ f₁ := by
  rw [Category.assoc, P₀.objIso_hom_left_snd_assoc, ← Category.assoc,
    DescentData.actOn_hom]

private lemma actOnMap_sourceMap_fst_eq :
    (actOnMap (baseChangeObjIso P₀ P₁ D).hom ≫ P₁.sourceMap D) ≫
        pullback.fst ((D.obj ()).hom ≫ a) a =
      commonAct P₀ D _ (fst_structure_cond P₀ D f₁ comm₁) := by
  rw [Category.assoc, P₁.sourceMap_fst D,
    ← Category.assoc (actOnMap (baseChangeObjIso P₀ P₁ D).hom), actOnMap_fst,
    Category.assoc, baseChangeObjIso_hom_left_objIso_assoc, D.baseChangeMap_left_fst,
    ← Category.assoc (pullback.fst (((P₀.functor.obj D).obj ()).hom ≫ a') a'),
    baseChangeAct, D.comp_act, commonAct]
  refine D.act_congr (Category.assoc _ _ _) ?_
  rw [Category.assoc, P₀.objIso_hom_left_snd_assoc]

private lemma actOnMap_sourceMap_snd_eq :
    (actOnMap (baseChangeObjIso P₀ P₁ D).hom ≫ P₁.sourceMap D) ≫
        pullback.snd ((D.obj ()).hom ≫ a) a =
      pullback.snd (((P₀.functor.obj D).obj ()).hom ≫ a') a' ≫ f₁ := by
  rw [Category.assoc, P₁.sourceMap_snd D,
    ← Category.assoc (actOnMap (baseChangeObjIso P₀ P₁ D).hom), actOnMap_snd]

/-- `baseChangeObjIso` intertwines the gluing actions of the two pulled-back descent data. -/
lemma baseChangeObjIso_actOn :
    (P₀.functor.obj D).actOn ≫ (baseChangeObjIso P₀ P₁ D).hom.left =
      actOnMap (baseChangeObjIso P₀ P₁ D).hom ≫ (P₁.functor.obj D).actOn := by
  apply (cancel_mono ((Over.forget X').map (P₁.objIso D).hom)).mp
  simp only [Over.forget_map]
  apply pullback.hom_ext
  · have hL : (((P₀.functor.obj D).actOn ≫ (baseChangeObjIso P₀ P₁ D).hom.left) ≫
          (P₁.objIso D).hom.left) ≫ pullback.fst (D.obj ()).hom f₁ =
        commonAct P₀ D _ (snd_comp_cond P₀ D f₁ comm₁) := by
      simp only [Category.assoc]
      rw [baseChangeObjIso_hom_left_objIso_assoc, D.baseChangeMap_left_fst,
        ← Category.assoc ((P₀.functor.obj D).actOn), baseChangeAct, D.comp_act]
      exact D.act_act_of (actOn_objIso_fst_eq P₀ D) (actOn_objIso_snd_eq P₀ D)
        ((snd_comp_cond P₀ D f₀ comm₀).trans (snd_comp_cond P₀ D f₁ comm₁).symm)
    have hR : ((actOnMap (baseChangeObjIso P₀ P₁ D).hom ≫ (P₁.functor.obj D).actOn) ≫
          (P₁.objIso D).hom.left) ≫ pullback.fst (D.obj ()).hom f₁ =
        commonAct P₀ D _ (snd_comp_cond P₀ D f₁ comm₁) := by
      simp only [Category.assoc]
      rw [P₁.actOn_objIso_fst,
        ← Category.assoc (actOnMap (baseChangeObjIso P₀ P₁ D).hom), D.comp_actOn]
      exact D.act_act_of (actOnMap_sourceMap_fst_eq P₀ P₁ D)
        (actOnMap_sourceMap_snd_eq P₀ P₁ D)
        ((fst_structure_cond P₀ D f₁ comm₁).trans (snd_comp_cond P₀ D f₁ comm₁).symm)
    exact hL.trans hR.symm
  · simp only [Category.assoc, P₁.objIso_hom_left_snd]
    rw [Over.w (baseChangeObjIso P₀ P₁ D).hom, DescentData.actOn_hom,
      DescentData.actOn_hom, actOnMap_snd]

/-- The comparison of the two pulled-back descent data. -/
def baseChangeDatumIso : P₀.functor.obj D ≅ P₁.functor.obj D :=
  isoOfActOn (baseChangeObjIso P₀ P₁ D) (baseChangeObjIso_actOn P₀ P₁ D)

/-- The underlying morphism of `baseChangeDatumIso` is that of `baseChangeObjIso`. -/
lemma baseChangeDatumIso_hom_hom :
    ((baseChangeDatumIso P₀ P₁ D).hom.hom ()) = (baseChangeObjIso P₀ P₁ D).hom := rfl

/-- Two morphisms completing the same commutative square induce isomorphic pullback functors
on descent data. -/
def baseChangeFunctorIso : P₀.functor ≅ P₁.functor :=
  NatIso.ofComponents (baseChangeDatumIso P₀ P₁) (by
    intro D E g
    refine DescentData.hom_ext fun ⟨⟩ ↦ ?_
    change ((P₀.functor.map g).hom ()) ≫ (baseChangeObjIso P₀ P₁ E).hom =
      (baseChangeObjIso P₀ P₁ D).hom ≫ ((P₁.functor.map g).hom ())
    have hP₁ : (Over.pullback f₁).map (g.hom ()) ≫ (P₁.objIso E).inv =
        (P₁.objIso D).inv ≫ (P₁.functor.map g).hom () := by
      rw [Iso.eq_inv_comp, ← Category.assoc, P₁.map g, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [baseChangeObjIso, baseChangeObjIso]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc ((P₀.functor.map g).hom ()), ← P₀.map g]
    simp only [Category.assoc]
    rw [show (D.baseChangeIso f₀ f₁ (comm₀.trans comm₁.symm)).hom =
      D.baseChangeMap f₀ f₁ (comm₀.trans comm₁.symm) from rfl,
      show (E.baseChangeIso f₀ f₁ (comm₀.trans comm₁.symm)).hom =
      E.baseChangeMap f₀ f₁ (comm₀.trans comm₁.symm) from rfl,
      ← Category.assoc ((Over.pullback f₀).map (g.hom ())),
      ← baseChangeMap_naturality f₀ f₁ (comm₀.trans comm₁.symm) g]
    simp only [Category.assoc, hP₁])

/-- For arbitrary specified pullback functors, the canonical natural isomorphism between the
pullback functors associated to two morphisms which complete the same commutative square. -/
def pullbackFunctorIsoOfSpec :
    PullbackFunctorIso a a' hS f₀ f₁ comm₀ comm₁ P₀ P₁ where
  iso := baseChangeFunctorIso P₀ P₁
  comparisonMap D := D.baseChangeMap f₀ f₁ (comm₀.trans comm₁.symm)
  component D := by
    rw [← baseChangeObjIso_hom_objIso P₀ P₁ D]
    rfl
  comparisonSourceMap D := D.baseChangeSourceMap f₀ f₁ (comm₀.trans comm₁.symm)
  comparisonSourceMap_fst D := D.baseChangeSourceMap_fst f₀ f₁ (comm₀.trans comm₁.symm)
  comparisonSourceMap_snd D := D.baseChangeSourceMap_snd f₀ f₁ (comm₀.trans comm₁.symm)
  comparison_gluing D := by
    rw [D.baseChangeMap_left_fst, baseChangeAct_eq, actOn]

end Comparison

/-- The canonical natural isomorphism between the pullback functors associated to two morphisms
which complete the same commutative square. Its components are the pullbacks of the original
gluing isomorphisms along the maps induced by `(f₀, f₁)`. -/
@[stacks 023Y "part (2)"]
def pullbackFunctorIso {S S' X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f₀ f₁ : X' ⟶ X) (comm₀ : f₀ ≫ a = a' ≫ h) (comm₁ : f₁ ≫ a = a' ≫ h) :
    PullbackFunctorIso a a' h f₀ f₁ comm₀ comm₁
      (pullbackFunctor a a' h f₀ comm₀) (pullbackFunctor a a' h f₁ comm₁) :=
  pullbackFunctorIsoOfSpec _ _

end AlgebraicGeometry.DescentData
