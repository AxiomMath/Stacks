module

public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Limits.VanKampen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre product of two universal colimits

Let `c₁` and `c₂` be cocones on diagrams `F₁ : I₁ ⥤ Q` and `F₂ : I₂ ⥤ Q` in a category with
fibre products, and let `a : c₁.pt ⟶ Z` and `b : c₂.pt ⟶ Z` be morphisms out of their vertices.
The fibre products `F₁ i ×_Z F₂ j` form a diagram indexed by `I₁ × I₂`, and if both cocones are
*universal* colimit cocones (`CategoryTheory.Limits.IsUniversalColimit`) then

`c₁.pt ×_Z c₂.pt = colim_{i, j} (F₁ i ×_Z F₂ j)`.

## Main definitions

* `CategoryTheory.Limits.relativeProductDiagram`: the two-variable diagram
  `(i, j) ↦ F₁ i ×_Z F₂ j`, in curried form.
* `CategoryTheory.Limits.relativeStageCocone`: for fixed `i`, the cocone on
  `j ↦ F₁ i ×_Z F₂ j` with vertex `F₁ i ×_Z c₂.pt`.
* `CategoryTheory.Limits.relativeProductDiagramOfCocones`: those cocones, as a
  `CategoryTheory.Limits.DiagramOfCocones`; its cocone points are the `F₁ i ×_Z c₂.pt`.
* `CategoryTheory.Limits.relativeProductBaseCocone`: the cocone on `i ↦ F₁ i ×_Z c₂.pt` with
  vertex `c₁.pt ×_Z c₂.pt`.
* `CategoryTheory.Limits.relativeProductCocone`: the cocone on the uncurried two-variable
  diagram with vertex `c₁.pt ×_Z c₂.pt`.

## Main results

* `CategoryTheory.Limits.isColimit_relativeStageCocone`: the stage cocone is a colimit, by
  universality of `c₂`.
* `CategoryTheory.Limits.isColimit_relativeProductBaseCocone`: the base cocone is a colimit, by
  universality of `c₁`.
* `CategoryTheory.Limits.isColimit_relativeProductCocone`: the cocone on the two-variable
  diagram is a colimit.

## Implementation notes

Only one of the two colimits can be base changed at a time: the comparison squares of the
two-variable diagram over a single one of the two diagrams are not cartesian, since cutting
`F₁` down to a stage leaves the second variable untouched. So the argument is the usual one for
"filtered colimits commute with fibre products": first cut the first colimit, obtaining
`c₁.pt ×_Z c₂.pt = colim_i (F₁ i ×_Z c₂.pt)`, then cut the second inside each stage, obtaining
`F₁ i ×_Z c₂.pt = colim_j (F₁ i ×_Z F₂ j)`, and then combine the two by the Fubini theorem for
colimits, `CategoryTheory.Limits.IsColimit.ofCoconeUncurry`. No cofinality of a diagonal is
needed because the conclusion is stated over the product index `I₁ × I₂` rather than over a
single index.

Each of the two cuts is an application of `IsUniversalColimit` to a hand-built diagram rather
than to the chosen pullbacks of `CategoryTheory.Limits.baseChangeDiagram`: the hypotheses it
asks for — that the comparison transformation is equifibered and that each leg sits in a
cartesian square — are both instances of `CategoryTheory.IsPullback.of_right`, and building the
diagram by hand keeps the cospans in the shape the conclusion wants.

Every structure map is given a name of its own, with its two projections recorded as simp
lemmas, and the commutations the fibre products need are the four lemmas
`CategoryTheory.Limits.relativeProduct_cond_left` and companions. Both are needed for the
proofs to go through on well-typed goals: a morphism built by `pullback.lift` inside a diagram
or cocone under construction carries the type of a field of that structure, and neither
rewriting nor simplification sees through such a type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ w₁ w₂

namespace CategoryTheory.Limits

variable {Q : Type w₁} [Category.{w₂} Q] [HasPullbacks Q]
  {I₁ : Type v₁} [Category.{v₂} I₁] {I₂ : Type v₃} [Category.{v₄} I₂]
  {F₁ : I₁ ⥤ Q} {F₂ : I₂ ⥤ Q} (c₁ : Cocone F₁) (c₂ : Cocone F₂)
  {Z : Q} (a : c₁.pt ⟶ Z) (b : c₂.pt ⟶ Z)

section Conditions

variable {c₁ c₂ a b}

/-- Transporting a commutation over `c₁.ι.app i ≫ a` along a transition of the first
diagram. -/
theorem relativeProduct_cond_left {i i' : I₁} (f : i ⟶ i') {W X : Q} (v : X ⟶ Z)
    (p : W ⟶ F₁.obj i) (q : W ⟶ X) (h : p ≫ c₁.ι.app i ≫ a = q ≫ v) :
    (p ≫ F₁.map f) ≫ c₁.ι.app i' ≫ a = q ≫ v := by
  rw [Category.assoc, ← Category.assoc (F₁.map f) (c₁.ι.app i') a, c₁.w f]
  exact h

/-- Transporting a commutation over `c₂.ι.app j ≫ b` along a transition of the second
diagram. -/
theorem relativeProduct_cond_right {j j' : I₂} (g : j ⟶ j') {W X : Q} (u : X ⟶ Z)
    (p : W ⟶ X) (q : W ⟶ F₂.obj j) (h : p ≫ u = q ≫ c₂.ι.app j ≫ b) :
    p ≫ u = (q ≫ F₂.map g) ≫ c₂.ι.app j' ≫ b := by
  rw [Category.assoc, ← Category.assoc (F₂.map g) (c₂.ι.app j') b, c₂.w g]
  exact h

/-- Reading a commutation over `c₁.ι.app i ≫ a` as one over `a`. -/
theorem relativeProduct_cond_vertexLeft {i : I₁} {W X : Q} (v : X ⟶ Z)
    (p : W ⟶ F₁.obj i) (q : W ⟶ X) (h : p ≫ c₁.ι.app i ≫ a = q ≫ v) :
    (p ≫ c₁.ι.app i) ≫ a = q ≫ v := by
  rw [Category.assoc]; exact h

/-- Reading a commutation over `c₂.ι.app j ≫ b` as one over `b`. -/
theorem relativeProduct_cond_vertexRight {j : I₂} {W X : Q} (u : X ⟶ Z)
    (p : W ⟶ X) (q : W ⟶ F₂.obj j) (h : p ≫ u = q ≫ c₂.ι.app j ≫ b) :
    p ≫ u = (q ≫ c₂.ι.app j) ≫ b := by
  rw [Category.assoc]; exact h

/-- `CategoryTheory.IsPullback.of_right` with the two horizontal composites named: the form in
which it applies to a goal whose morphisms are fields of a diagram or a cocone. -/
theorem isPullback_of_right_of_eq {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : Q} {h₁₁ : X₁₁ ⟶ X₁₂}
    {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂}
    {v₁₃ : X₁₃ ⟶ X₂₃} {k : X₁₁ ⟶ X₁₃} {l : X₂₁ ⟶ X₂₃} (hk : h₁₁ ≫ h₁₂ = k) (hl : h₂₁ ≫ h₂₂ = l)
    (s : IsPullback k v₁₁ v₁₃ l) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  IsPullback.of_right (by rw [hk, hl]; exact s) p t

/-- A map of fibre products over `w` that is `F₁.map f` on first projections and the identity on
second projections is a base change of `F₁.map f`. -/
private theorem isPullback_of_fst_eq_map_of_snd_eq {i i' : I₁} (f : i ⟶ i') {Y : Q} (w : Y ⟶ Z)
    (T : pullback (c₁.ι.app i ≫ a) w ⟶ pullback (c₁.ι.app i' ≫ a) w)
    (hfst : T ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F₁.map f)
    (hsnd : T ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsPullback T (pullback.fst _ _) (pullback.fst _ _) (F₁.map f) :=
  isPullback_of_right_of_eq hsnd (by rw [← Category.assoc, c₁.w f])
    (IsPullback.of_hasPullback _ _).flip hfst (IsPullback.of_hasPullback _ _).flip

end Conditions

/-! ### The two-variable diagram -/

/-- The transition of the two-variable diagram in the second variable. -/
def relativeStageTransition (i : I₁) {j j' : I₂} (g : j ⟶ j') :
    pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ⟶
      pullback (c₁.ι.app i ≫ a) (c₂.ι.app j' ≫ b) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ F₂.map g)
    (relativeProduct_cond_right g _ _ _ pullback.condition)

/-- The transition in the second variable commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem relativeStageTransition_fst (i : I₁) {j j' : I₂} (g : j ⟶ j') :
    relativeStageTransition c₁ c₂ a b i g ≫
        pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j' ≫ b) =
      pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) :=
  pullback.lift_fst _ _ _

/-- The transition in the second variable followed by the second projection is the second
projection followed by `F₂.map g`. -/
@[reassoc (attr := simp)]
theorem relativeStageTransition_snd (i : I₁) {j j' : I₂} (g : j ⟶ j') :
    relativeStageTransition c₁ c₂ a b i g ≫
        pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j' ≫ b) =
      pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ≫ F₂.map g :=
  pullback.lift_snd _ _ _

/-- The diagram `j ↦ F₁ i ×_Z F₂ j` attached to a stage `i` of the first diagram. -/
def relativeProductDiagramObj (i : I₁) : I₂ ⥤ Q where
  obj j := pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b)
  map g := relativeStageTransition c₁ c₂ a b i g
  map_id _ := by refine pullback.hom_ext ?_ ?_ <;> simp
  map_comp _ _ := by refine pullback.hom_ext ?_ ?_ <;> simp

/-- The value of `relativeProductDiagramObj` at `j` is `F₁ i ×_Z F₂ j`. -/
@[simp]
theorem relativeProductDiagramObj_obj (i : I₁) (j : I₂) :
    (relativeProductDiagramObj c₁ c₂ a b i).obj j =
      pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) := rfl

/-- The maps of `relativeProductDiagramObj` are the transitions in the second variable. -/
@[simp]
theorem relativeProductDiagramObj_map (i : I₁) {j j' : I₂} (g : j ⟶ j') :
    (relativeProductDiagramObj c₁ c₂ a b i).map g =
      relativeStageTransition c₁ c₂ a b i g := rfl

/-- The transition of the two-variable diagram in the first variable. -/
def relativeBaseTransition {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ⟶
      pullback (c₁.ι.app i' ≫ a) (c₂.ι.app j ≫ b) :=
  pullback.lift (pullback.fst _ _ ≫ F₁.map f) (pullback.snd _ _)
    (relativeProduct_cond_left f _ _ _ pullback.condition)

/-- The transition in the first variable followed by the first projection is the first projection
followed by `F₁.map f`. -/
@[reassoc (attr := simp)]
theorem relativeBaseTransition_fst {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    relativeBaseTransition c₁ c₂ a b f j ≫
        pullback.fst (c₁.ι.app i' ≫ a) (c₂.ι.app j ≫ b) =
      pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ≫ F₁.map f :=
  pullback.lift_fst _ _ _

/-- The transition in the first variable commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem relativeBaseTransition_snd {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    relativeBaseTransition c₁ c₂ a b f j ≫
        pullback.snd (c₁.ι.app i' ≫ a) (c₂.ι.app j ≫ b) =
      pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) :=
  pullback.lift_snd _ _ _

/-- The transition of the two-variable diagram in the first variable, as a transformation of
diagrams in the second. -/
def relativeProductDiagramMap {i i' : I₁} (f : i ⟶ i') :
    relativeProductDiagramObj c₁ c₂ a b i ⟶ relativeProductDiagramObj c₁ c₂ a b i' where
  app j := relativeBaseTransition c₁ c₂ a b f j
  naturality _ _ _ := by refine pullback.hom_ext ?_ ?_ <;> simp

/-- The components of `relativeProductDiagramMap` are the transitions in the first variable. -/
@[simp]
theorem relativeProductDiagramMap_app {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    (relativeProductDiagramMap c₁ c₂ a b f).app j = relativeBaseTransition c₁ c₂ a b f j := rfl

/-- The two-variable diagram of fibre products `F₁ i ×_Z F₂ j`, in curried form. -/
def relativeProductDiagram : I₁ ⥤ I₂ ⥤ Q where
  obj i := relativeProductDiagramObj c₁ c₂ a b i
  map f := relativeProductDiagramMap c₁ c₂ a b f
  map_id _ := by
    apply NatTrans.ext
    funext j
    refine pullback.hom_ext ?_ ?_ <;> simp
  map_comp _ _ := by
    apply NatTrans.ext
    funext j
    refine pullback.hom_ext ?_ ?_ <;> simp

/-- The value of the curried two-variable diagram at `i` is `relativeProductDiagramObj`. -/
@[simp]
theorem relativeProductDiagram_obj (i : I₁) :
    (relativeProductDiagram c₁ c₂ a b).obj i = relativeProductDiagramObj c₁ c₂ a b i := rfl

/-- The maps of the curried two-variable diagram are given by `relativeProductDiagramMap`. -/
@[simp]
theorem relativeProductDiagram_map {i i' : I₁} (f : i ⟶ i') :
    (relativeProductDiagram c₁ c₂ a b).map f = relativeProductDiagramMap c₁ c₂ a b f := rfl

/-! ### The stage cocones -/

/-- The leg of the stage cocone at `j`: the comparison `F₁ i ×_Z F₂ j ⟶ F₁ i ×_Z c₂.pt`. -/
def relativeStageLeg (i : I₁) (j : I₂) :
    pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ⟶ pullback (c₁.ι.app i ≫ a) b :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c₂.ι.app j)
    (relativeProduct_cond_vertexRight _ _ _ pullback.condition)

/-- The stage leg commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem relativeStageLeg_fst (i : I₁) (j : I₂) :
    relativeStageLeg c₁ c₂ a b i j ≫ pullback.fst (c₁.ι.app i ≫ a) b =
      pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) :=
  pullback.lift_fst _ _ _

/-- The stage leg followed by the second projection is the second projection followed by
`c₂.ι.app j`. -/
@[reassoc (attr := simp)]
theorem relativeStageLeg_snd (i : I₁) (j : I₂) :
    relativeStageLeg c₁ c₂ a b i j ≫ pullback.snd (c₁.ι.app i ≫ a) b =
      pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ≫ c₂.ι.app j :=
  pullback.lift_snd _ _ _

/-- For a fixed stage `i` of the first diagram, the cocone on `j ↦ F₁ i ×_Z F₂ j` with vertex
`F₁ i ×_Z c₂.pt`. -/
def relativeStageCocone (i : I₁) : Cocone (relativeProductDiagramObj c₁ c₂ a b i) where
  pt := pullback (c₁.ι.app i ≫ a) b
  ι :=
    { app := fun j => relativeStageLeg c₁ c₂ a b i j
      naturality := fun _ _ _ => by refine pullback.hom_ext ?_ ?_ <;> simp }

/-- The vertex of the stage cocone is `F₁ i ×_Z c₂.pt`. -/
@[simp]
theorem relativeStageCocone_pt (i : I₁) :
    (relativeStageCocone c₁ c₂ a b i).pt = pullback (c₁.ι.app i ≫ a) b := rfl

/-- The legs of the stage cocone are the stage legs. -/
@[simp]
theorem relativeStageCocone_ι_app (i : I₁) (j : I₂) :
    (relativeStageCocone c₁ c₂ a b i).ι.app j = relativeStageLeg c₁ c₂ a b i j := rfl

/-- The transition of the stage vertices `F₁ i ×_Z c₂.pt`. -/
def relativeStageVertexMap {i i' : I₁} (f : i ⟶ i') :
    pullback (c₁.ι.app i ≫ a) b ⟶ pullback (c₁.ι.app i' ≫ a) b :=
  pullback.lift (pullback.fst _ _ ≫ F₁.map f) (pullback.snd _ _)
    (relativeProduct_cond_left f _ _ _ pullback.condition)

/-- The transition of the stage vertices followed by the first projection is the first projection
followed by `F₁.map f`. -/
@[reassoc (attr := simp)]
theorem relativeStageVertexMap_fst {i i' : I₁} (f : i ⟶ i') :
    relativeStageVertexMap c₁ c₂ a b f ≫ pullback.fst (c₁.ι.app i' ≫ a) b =
      pullback.fst (c₁.ι.app i ≫ a) b ≫ F₁.map f :=
  pullback.lift_fst _ _ _

/-- The transition of the stage vertices commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem relativeStageVertexMap_snd {i i' : I₁} (f : i ⟶ i') :
    relativeStageVertexMap c₁ c₂ a b f ≫ pullback.snd (c₁.ι.app i' ≫ a) b =
      pullback.snd (c₁.ι.app i ≫ a) b :=
  pullback.lift_snd _ _ _

/-- The stage legs are compatible with the transitions of the stage vertices. -/
theorem relativeStageLeg_comp_vertexMap {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    relativeStageLeg c₁ c₂ a b i j ≫ relativeStageVertexMap c₁ c₂ a b f =
      relativeBaseTransition c₁ c₂ a b f j ≫ relativeStageLeg c₁ c₂ a b i' j := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The stage cocones of `CategoryTheory.Limits.relativeStageCocone`, assembled into a diagram
of cocones over the curried two-variable diagram. -/
def relativeProductDiagramOfCocones : DiagramOfCocones (relativeProductDiagram c₁ c₂ a b) where
  obj i := relativeStageCocone c₁ c₂ a b i
  map f :=
    { hom := relativeStageVertexMap c₁ c₂ a b f
      w := fun j => relativeStageLeg_comp_vertexMap c₁ c₂ a b f j }
  id _ := by refine pullback.hom_ext ?_ ?_ <;> simp
  comp _ _ := by refine pullback.hom_ext ?_ ?_ <;> simp

/-- The cocone morphisms of `relativeProductDiagramOfCocones` are the transitions of the stage
vertices. -/
@[simp]
theorem relativeProductDiagramOfCocones_map_hom {i i' : I₁} (f : i ⟶ i') :
    ((relativeProductDiagramOfCocones c₁ c₂ a b).map f).hom =
      relativeStageVertexMap c₁ c₂ a b f := rfl

/-- The cocone point of `relativeProductDiagramOfCocones` at `i` is `F₁ i ×_Z c₂.pt`. -/
@[simp]
theorem relativeProductDiagramOfCocones_coconePoints_obj (i : I₁) :
    (relativeProductDiagramOfCocones c₁ c₂ a b).coconePoints.obj i =
      pullback (c₁.ι.app i ≫ a) b := rfl

/-- The maps between the cocone points of `relativeProductDiagramOfCocones` are the transitions of
the stage vertices. -/
@[simp]
theorem relativeProductDiagramOfCocones_coconePoints_map {i i' : I₁} (f : i ⟶ i') :
    (relativeProductDiagramOfCocones c₁ c₂ a b).coconePoints.map f =
      relativeStageVertexMap c₁ c₂ a b f := rfl

/-! ### The cocones with vertex the fibre product of the two vertices -/

/-- The leg of the base cocone at `i`: the comparison `F₁ i ×_Z c₂.pt ⟶ c₁.pt ×_Z c₂.pt`. -/
def relativeProductBaseLeg (i : I₁) : pullback (c₁.ι.app i ≫ a) b ⟶ pullback a b :=
  pullback.lift (pullback.fst _ _ ≫ c₁.ι.app i) (pullback.snd _ _)
    (relativeProduct_cond_vertexLeft _ _ _ pullback.condition)

/-- The base leg followed by the first projection is the first projection followed by
`c₁.ι.app i`. -/
@[reassoc (attr := simp)]
theorem relativeProductBaseLeg_fst (i : I₁) :
    relativeProductBaseLeg c₁ c₂ a b i ≫ pullback.fst a b =
      pullback.fst (c₁.ι.app i ≫ a) b ≫ c₁.ι.app i :=
  pullback.lift_fst _ _ _

/-- The base leg commutes with the second projections. -/
@[reassoc (attr := simp)]
theorem relativeProductBaseLeg_snd (i : I₁) :
    relativeProductBaseLeg c₁ c₂ a b i ≫ pullback.snd a b =
      pullback.snd (c₁.ι.app i ≫ a) b :=
  pullback.lift_snd _ _ _

/-- The transitions of the stage vertices are compatible with the base legs. -/
theorem relativeStageVertexMap_comp_baseLeg {i i' : I₁} (f : i ⟶ i') :
    relativeStageVertexMap c₁ c₂ a b f ≫ relativeProductBaseLeg c₁ c₂ a b i' =
      relativeProductBaseLeg c₁ c₂ a b i := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The cocone on `i ↦ F₁ i ×_Z c₂.pt` with vertex `c₁.pt ×_Z c₂.pt`. -/
def relativeProductBaseCocone :
    Cocone (relativeProductDiagramOfCocones c₁ c₂ a b).coconePoints where
  pt := pullback a b
  ι :=
    { app := fun i => relativeProductBaseLeg c₁ c₂ a b i
      naturality := fun _ _ f =>
        (relativeStageVertexMap_comp_baseLeg c₁ c₂ a b f).trans (Category.comp_id _).symm }

/-- The vertex of the base cocone is `c₁.pt ×_Z c₂.pt`. -/
@[simp]
theorem relativeProductBaseCocone_pt :
    (relativeProductBaseCocone c₁ c₂ a b).pt = pullback a b := rfl

/-- The legs of the base cocone are the base legs. -/
@[simp]
theorem relativeProductBaseCocone_ι_app (i : I₁) :
    (relativeProductBaseCocone c₁ c₂ a b).ι.app i = relativeProductBaseLeg c₁ c₂ a b i := rfl

/-- The leg of the total cocone at `(i, j)`: the comparison
`F₁ i ×_Z F₂ j ⟶ c₁.pt ×_Z c₂.pt`. -/
def relativeProductLeg (i : I₁) (j : I₂) :
    pullback (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ⟶ pullback a b :=
  pullback.lift (pullback.fst _ _ ≫ c₁.ι.app i) (pullback.snd _ _ ≫ c₂.ι.app j)
    (relativeProduct_cond_vertexRight _ _ _
      (relativeProduct_cond_vertexLeft _ _ _ pullback.condition))

/-- The total leg followed by the first projection is the first projection followed by
`c₁.ι.app i`. -/
@[reassoc (attr := simp)]
theorem relativeProductLeg_fst (i : I₁) (j : I₂) :
    relativeProductLeg c₁ c₂ a b i j ≫ pullback.fst a b =
      pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ≫ c₁.ι.app i :=
  pullback.lift_fst _ _ _

/-- The total leg followed by the second projection is the second projection followed by
`c₂.ι.app j`. -/
@[reassoc (attr := simp)]
theorem relativeProductLeg_snd (i : I₁) (j : I₂) :
    relativeProductLeg c₁ c₂ a b i j ≫ pullback.snd a b =
      pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) ≫ c₂.ι.app j :=
  pullback.lift_snd _ _ _

/-- The stage leg followed by the base leg is the total leg. -/
theorem relativeStageLeg_comp_baseLeg (i : I₁) (j : I₂) :
    relativeStageLeg c₁ c₂ a b i j ≫ relativeProductBaseLeg c₁ c₂ a b i =
      relativeProductLeg c₁ c₂ a b i j := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The cocone on the uncurried two-variable diagram with vertex `c₁.pt ×_Z c₂.pt`. -/
def relativeProductCocone : Cocone (Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)) where
  pt := pullback a b
  ι :=
    { app := fun p => relativeProductLeg c₁ c₂ a b p.1 p.2
      naturality := fun _ _ _ => by
        refine pullback.hom_ext ?_ ?_ <;> simp [Functor.uncurry] }

/-- A map of the uncurried two-variable diagram followed by the first projection is the first
projection followed by `F₁.map f.1`. -/
@[reassoc (attr := simp)]
theorem uncurry_relativeProductDiagram_map_fst {p q : I₁ × I₂} (f : p ⟶ q) :
    (Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)).map f ≫
        pullback.fst (c₁.ι.app q.1 ≫ a) (c₂.ι.app q.2 ≫ b) =
      pullback.fst (c₁.ι.app p.1 ≫ a) (c₂.ι.app p.2 ≫ b) ≫ F₁.map f.1 := by
  show (relativeBaseTransition c₁ c₂ a b f.1 p.2 ≫
    relativeStageTransition c₁ c₂ a b q.1 f.2) ≫ _ = _
  simp

/-- A map of the uncurried two-variable diagram followed by the second projection is the second
projection followed by `F₂.map f.2`. -/
@[reassoc (attr := simp)]
theorem uncurry_relativeProductDiagram_map_snd {p q : I₁ × I₂} (f : p ⟶ q) :
    (Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)).map f ≫
        pullback.snd (c₁.ι.app q.1 ≫ a) (c₂.ι.app q.2 ≫ b) =
      pullback.snd (c₁.ι.app p.1 ≫ a) (c₂.ι.app p.2 ≫ b) ≫ F₂.map f.2 := by
  show (relativeBaseTransition c₁ c₂ a b f.1 p.2 ≫
    relativeStageTransition c₁ c₂ a b q.1 f.2) ≫ _ = _
  simp

/-- The vertex of the total cocone is `c₁.pt ×_Z c₂.pt`. -/
@[simp]
theorem relativeProductCocone_pt : (relativeProductCocone c₁ c₂ a b).pt = pullback a b := rfl

/-- The legs of the total cocone are the total legs. -/
@[simp]
theorem relativeProductCocone_ι_app (p : I₁ × I₂) :
    (relativeProductCocone c₁ c₂ a b).ι.app p = relativeProductLeg c₁ c₂ a b p.1 p.2 := rfl

/-! ### The two base changes -/

/-- The second projections of the two-variable diagram, as a transformation to the second
diagram. -/
def relativeStageSnd (i : I₁) : relativeProductDiagramObj c₁ c₂ a b i ⟶ F₂ where
  app j := pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b)
  naturality _ _ g := relativeStageTransition_snd c₁ c₂ a b i g

/-- The components of `relativeStageSnd` are the second projections. -/
@[simp]
theorem relativeStageSnd_app (i : I₁) (j : I₂) :
    (relativeStageSnd c₁ c₂ a b i).app j =
      pullback.snd (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b) := rfl

/-- The first projections of the stage vertices, as a transformation to the first diagram. -/
def relativeBaseFst : (relativeProductDiagramOfCocones c₁ c₂ a b).coconePoints ⟶ F₁ where
  app i := pullback.fst (c₁.ι.app i ≫ a) b
  naturality _ _ f := relativeStageVertexMap_fst c₁ c₂ a b f

/-- The components of `relativeBaseFst` are the first projections. -/
@[simp]
theorem relativeBaseFst_app (i : I₁) :
    (relativeBaseFst c₁ c₂ a b).app i = pullback.fst (c₁.ι.app i ≫ a) b := rfl

/-- The second projections of the two-variable diagram are equifibered over the second
diagram. -/
theorem equifibered_relativeStageSnd (i : I₁) :
    NatTrans.Equifibered (relativeStageSnd c₁ c₂ a b i) := fun _ _ g =>
  isPullback_of_right_of_eq (relativeStageTransition_fst c₁ c₂ a b i g)
    (by rw [← Category.assoc, c₂.w g]) (IsPullback.of_hasPullback _ _)
    (relativeStageTransition_snd c₁ c₂ a b i g) (IsPullback.of_hasPullback _ _)

/-- **The transition of the two-variable diagram in the first variable is a base change of the
transition of the first diagram**, the mirror image of
`CategoryTheory.Limits.equifibered_relativeStageSnd`, which says the same of the second variable
and the second diagram. There is no natural transformation to carry it, the diagram
`i ↦ F₁ i ×_Z F₂ j` at a fixed second index not being one of the functors built here, so it is
stated as the bare cartesian square. -/
@[ega "I 3.3.9" "Objectwise transitivity"]
theorem isPullback_relativeBaseTransition {i i' : I₁} (f : i ⟶ i') (j : I₂) :
    IsPullback (relativeBaseTransition c₁ c₂ a b f j)
      (pullback.fst (c₁.ι.app i ≫ a) (c₂.ι.app j ≫ b))
      (pullback.fst (c₁.ι.app i' ≫ a) (c₂.ι.app j ≫ b)) (F₁.map f) :=
  isPullback_of_fst_eq_map_of_snd_eq f _ _ (relativeBaseTransition_fst c₁ c₂ a b f j)
    (relativeBaseTransition_snd c₁ c₂ a b f j)

/-- **The transition of the uncurried two-variable diagram is the transition in the first
variable followed by the transition in the second.** This is the factorization through the
intermediate stage `F₁ q.1 ×_Z F₂ p.2`, and with
`CategoryTheory.Limits.isPullback_relativeBaseTransition` and
`CategoryTheory.Limits.equifibered_relativeStageSnd` it exhibits every transition of the
two-variable diagram as a composite of two base changes, one of a transition of each diagram. -/
theorem uncurry_relativeProductDiagram_map {p q : I₁ × I₂} (f : p ⟶ q) :
    (Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b)).map f =
      relativeBaseTransition c₁ c₂ a b f.1 p.2 ≫
        relativeStageTransition c₁ c₂ a b q.1 f.2 :=
  rfl

/-- Each stage of the two-variable diagram sits in a cartesian square over the corresponding
stage of the second diagram. -/
theorem isPullback_relativeStageCocone_ι (i : I₁) (j : I₂) :
    IsPullback ((relativeStageCocone c₁ c₂ a b i).ι.app j)
      ((relativeStageSnd c₁ c₂ a b i).app j)
      (pullback.snd (c₁.ι.app i ≫ a) b) (c₂.ι.app j) :=
  isPullback_of_right_of_eq (relativeStageLeg_fst c₁ c₂ a b i j) rfl
    (IsPullback.of_hasPullback _ _) (relativeStageLeg_snd c₁ c₂ a b i j)
    (IsPullback.of_hasPullback _ _)

/-- **The stage cocone is a colimit**: it is the base change of the second colimit along the
projection `F₁ i ×_Z c₂.pt ⟶ c₂.pt`. -/
def isColimit_relativeStageCocone (h₂ : IsUniversalColimit c₂) (i : I₁) :
    IsColimit (relativeStageCocone c₁ c₂ a b i) :=
  (h₂ (relativeStageCocone c₁ c₂ a b i) (relativeStageSnd c₁ c₂ a b i)
    (pullback.snd (c₁.ι.app i ≫ a) b)
    (by
      apply NatTrans.ext
      funext j
      exact (relativeStageLeg_snd c₁ c₂ a b i j).symm)
    (equifibered_relativeStageSnd c₁ c₂ a b i)
    (isPullback_relativeStageCocone_ι c₁ c₂ a b i)).some

/-- The first projections of the stage vertices are equifibered over the first diagram. -/
theorem equifibered_relativeBaseFst : NatTrans.Equifibered (relativeBaseFst c₁ c₂ a b) :=
  fun _ _ f => isPullback_of_fst_eq_map_of_snd_eq f b _ (relativeStageVertexMap_fst c₁ c₂ a b f)
    (relativeStageVertexMap_snd c₁ c₂ a b f)

/-- Each stage vertex sits in a cartesian square over the corresponding stage of the first
diagram. -/
theorem isPullback_relativeProductBaseCocone_ι (i : I₁) :
    IsPullback ((relativeProductBaseCocone c₁ c₂ a b).ι.app i)
      ((relativeBaseFst c₁ c₂ a b).app i) (pullback.fst a b) (c₁.ι.app i) :=
  isPullback_of_right_of_eq (relativeProductBaseLeg_snd c₁ c₂ a b i) rfl
    (IsPullback.of_hasPullback _ _).flip (relativeProductBaseLeg_fst c₁ c₂ a b i)
    (IsPullback.of_hasPullback a b).flip

/-- **The base cocone is a colimit**: it is the base change of the first colimit along the
projection `c₁.pt ×_Z c₂.pt ⟶ c₁.pt`. -/
def isColimit_relativeProductBaseCocone (h₁ : IsUniversalColimit c₁) :
    IsColimit (relativeProductBaseCocone c₁ c₂ a b) :=
  (h₁ (relativeProductBaseCocone c₁ c₂ a b) (relativeBaseFst c₁ c₂ a b) (pullback.fst a b)
    (by
      apply NatTrans.ext
      funext i
      exact (relativeProductBaseLeg_fst c₁ c₂ a b i).symm)
    (equifibered_relativeBaseFst c₁ c₂ a b)
    (isPullback_relativeProductBaseCocone_ι c₁ c₂ a b)).some

/-- The stage cocone, with its type read off the diagram of cocones. -/
def isColimit_relativeStageCocone' (h₂ : IsUniversalColimit c₂) (i : I₁) :
    IsColimit ((relativeProductDiagramOfCocones c₁ c₂ a b).obj i) :=
  isColimit_relativeStageCocone c₁ c₂ a b h₂ i

/-- The transitions in the second variable are compatible with the total legs. -/
theorem relativeStageTransition_comp_productLeg (i : I₁) {j j' : I₂} (g : j ⟶ j') :
    relativeStageTransition c₁ c₂ a b i g ≫ relativeProductLeg c₁ c₂ a b i j' =
      relativeProductLeg c₁ c₂ a b i j := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The slice of the total cocone at a stage `i` of the first diagram: the cocone on
`j ↦ F₁ i ×_Z F₂ j` with vertex `c₁.pt ×_Z c₂.pt`. This is the cocone the Fubini comparison
descends along. -/
def relativeProductSliceCocone (i : I₁) : Cocone (relativeProductDiagramObj c₁ c₂ a b i) where
  pt := pullback a b
  ι :=
    { app := fun j => relativeProductLeg c₁ c₂ a b i j
      naturality := fun _ _ g =>
        (relativeStageTransition_comp_productLeg c₁ c₂ a b i g).trans
          (Category.comp_id _).symm }

/-- **The fibre product of two universal colimits is the colimit of the fibre products**:
`c₁.pt ×_Z c₂.pt = colim_{i, j} (F₁ i ×_Z F₂ j)`, the colimit being taken over the product of
the two index categories. -/
def isColimit_relativeProductCocone (h₁ : IsUniversalColimit c₁) (h₂ : IsUniversalColimit c₂) :
    IsColimit (relativeProductCocone c₁ c₂ a b) := by
  refine IsColimit.ofCoconeUncurry (isColimit_relativeStageCocone' c₁ c₂ a b h₂) ?_
  refine IsColimit.ofIsoColimit (isColimit_relativeProductBaseCocone c₁ c₂ a b h₁)
    (Cocone.ext (Iso.refl _) (fun i => ?_))
  refine ((Category.comp_id _).trans ?_)
  refine (isColimit_relativeStageCocone' c₁ c₂ a b h₂ i).hom_ext (fun j => ?_)
  exact (relativeStageLeg_comp_baseLeg c₁ c₂ a b i j).trans
    ((isColimit_relativeStageCocone' c₁ c₂ a b h₂ i).fac
      (relativeProductSliceCocone c₁ c₂ a b i) j).symm

/-- **A diagram whose stages sit in cartesian squares over the legs of the two cocones is the
two-variable diagram of fibre products**, reindexed along any functor into the product of the
two index categories. -/
def isoUncurryRelativeProductDiagram {J : Type*} [Category J] (Ψ : J ⥤ I₁ × I₂) {K : J ⥤ Q}
    (u : K ⟶ Ψ ⋙ Prod.fst I₁ I₂ ⋙ F₁) (v : K ⟶ Ψ ⋙ Prod.snd I₁ I₂ ⋙ F₂)
    (h : ∀ j : J, IsPullback (u.app j) (v.app j)
      (c₁.ι.app (Ψ.obj j).1 ≫ a) (c₂.ι.app (Ψ.obj j).2 ≫ b)) :
    K ≅ Ψ ⋙ Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b) :=
  NatIso.ofComponents (fun j => (h j).isoPullback) (by
    intro i j f
    refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans
        ((congrArg (fun z => K.map f ≫ z) (h j).isoPullback_hom_fst).trans
          ((u.naturality f).trans ?_))
      refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg
        (fun z => (h i).isoPullback.hom ≫ z)
          (uncurry_relativeProductDiagram_map_fst c₁ c₂ a b (Ψ.map f))).trans ?_))
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ F₁.map (Ψ.map f).1) (h i).isoPullback_hom_fst)
    · refine (Category.assoc _ _ _).trans
        ((congrArg (fun z => K.map f ≫ z) (h j).isoPullback_hom_snd).trans
          ((v.naturality f).trans ?_))
      refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg
        (fun z => (h i).isoPullback.hom ≫ z)
          (uncurry_relativeProductDiagram_map_snd c₁ c₂ a b (Ψ.map f))).trans ?_))
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ F₂.map (Ψ.map f).2) (h i).isoPullback_hom_snd))

/-! ### The fibre product of two diagrams over a third -/

section FibreProductDiagram

variable {J : Type v₁} [Category.{v₂} J] {G₁ G₂ G₃ : J ⥤ Q} (α : G₁ ⟶ G₃) (β : G₂ ⟶ G₃)

/-- The diagram of fibre products of two diagrams over a third: the stage at `j` is
`G₁ j ×_{G₃ j} G₂ j`. Building the diagram once, for diagrams in an arbitrary category with
fibre products, is what keeps the chosen pullbacks of the ambient category out of the
functoriality proofs at the point of use. -/
def fibreProductDiagram : J ⥤ Q where
  obj j := pullback (α.app j) (β.app j)
  map f := pullback.map _ _ _ _ (G₁.map f) (G₂.map f) (G₃.map f)
    (α.naturality f).symm (β.naturality f).symm
  map_id _ := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  map_comp _ _ := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]

/-- The stage of `fibreProductDiagram` at `j` is `G₁ j ×_{G₃ j} G₂ j`. -/
@[simp]
theorem fibreProductDiagram_obj (j : J) :
    (fibreProductDiagram α β).obj j = pullback (α.app j) (β.app j) := rfl

/-- A map of `fibreProductDiagram` followed by the first projection is the first projection
followed by `G₁.map f`. -/
@[reassoc (attr := simp)]
theorem fibreProductDiagram_map_fst {i j : J} (f : i ⟶ j) :
    (fibreProductDiagram α β).map f ≫ pullback.fst (α.app j) (β.app j) =
      pullback.fst (α.app i) (β.app i) ≫ G₁.map f :=
  pullback.lift_fst _ _ _

/-- A map of `fibreProductDiagram` followed by the second projection is the second projection
followed by `G₂.map f`. -/
@[reassoc (attr := simp)]
theorem fibreProductDiagram_map_snd {i j : J} (f : i ⟶ j) :
    (fibreProductDiagram α β).map f ≫ pullback.snd (α.app j) (β.app j) =
      pullback.snd (α.app i) (β.app i) ≫ G₂.map f :=
  pullback.lift_snd _ _ _

/-- The first projection of the diagram of fibre products. -/
def fibreProductDiagramFst : fibreProductDiagram α β ⟶ G₁ where
  app j := pullback.fst (α.app j) (β.app j)
  naturality _ _ f := fibreProductDiagram_map_fst α β f

/-- The second projection of the diagram of fibre products. -/
def fibreProductDiagramSnd : fibreProductDiagram α β ⟶ G₂ where
  app j := pullback.snd (α.app j) (β.app j)
  naturality _ _ f := fibreProductDiagram_map_snd α β f

/-- The components of `fibreProductDiagramFst` are the first projections. -/
@[simp]
theorem fibreProductDiagramFst_app (j : J) :
    (fibreProductDiagramFst α β).app j = pullback.fst (α.app j) (β.app j) := rfl

/-- The components of `fibreProductDiagramSnd` are the second projections. -/
@[simp]
theorem fibreProductDiagramSnd_app (j : J) :
    (fibreProductDiagramSnd α β).app j = pullback.snd (α.app j) (β.app j) := rfl

/-- Each stage of `fibreProductDiagram` is the fibre product of `α.app j` and `β.app j`. -/
theorem isPullback_fibreProductDiagram (j : J) :
    IsPullback ((fibreProductDiagramFst α β).app j) ((fibreProductDiagramSnd α β).app j)
      (α.app j) (β.app j) :=
  IsPullback.of_hasPullback _ _

end FibreProductDiagram

end CategoryTheory.Limits

end
