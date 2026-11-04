module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralAffineLimit09YZ
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The limit presentation of an integral square with affine corners

This file provides the geometric setup of [Stacks, Tag 0EYP] in the case where all four corners
of the square are affine. Let

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

be a cartesian square of schemes with `f` integral and `Y`, `Y'` affine (whence `X`, `X'` affine
as well). Then `f` is a directed inverse limit of *finite* morphisms `X_i ⟶ Y`, and base changing
that system along `g` presents `f'` as the limit of the finite morphisms `X'_i = X_i ×_Y Y' ⟶ Y'`,
each square `X'_i ⟶ X_i` over `g` being cartesian. The levelwise cartesian squares are what allows
[Stacks, Tag 0959] to be invoked at each stage of the system.

All of this is bundled as `Stacks.EtaleCohomology.IntegralSquareLimitData`, produced by
`Stacks.EtaleCohomology.nonempty_integralSquareLimitData`.

## Main definitions

* `Stacks.EtaleCohomology.baseChangeDiagram`, `Stacks.EtaleCohomology.baseChangeStructureMap`,
  `Stacks.EtaleCohomology.baseChangeHorizontal`,
  `Stacks.EtaleCohomology.baseChangeProjection` — the base change along `g : Y' ⟶ Y` of an inverse
  system of schemes over `Y`, its structure morphisms to `Y'`, its horizontal morphisms to the
  original system, and the induced cone from `X'`.
* `Stacks.EtaleCohomology.IntegralSquareLimitData` — the bundled datum described above.

## Main results

* `Stacks.EtaleCohomology.isLimit_of_isPullback_stages` — if an inverse system over `Y'` is
  levelwise the base change of an inverse system over `Y` along `g`, and the square on the limits
  is cartesian, then the cone from `X'` is a limit cone.
* `Stacks.EtaleCohomology.nonempty_integralSquareLimitData` — the existence of the datum.

## Implementation notes

The base-changed diagram is built by hand out of `CategoryTheory.Limits.pullback.lift`, and is
`@[reducible]`, rather than being produced as `CategoryTheory.Over.pullback` applied to the lift
of the system to `CategoryTheory.Over Y`. This is the choice already made, for the same reason,
in `AlgebraicGeometry.LimitDescent.bcDiagram`: with the functorial definition the objects of the
diagram are not syntactically pullbacks, and `rw` and `simp` assemble congruences at reducible
transparency only, so without reducibility they fail to relate `(baseChangeDiagram D st g).obj j`
with the pullback it is. With `Over.pullback` the situation is worse still: the structure morphism
of the lifted object appears as `((Over.lift D st).obj j).hom` rather than `st.app j`, and a
statement phrased in the latter is not even type-correct at implicit transparency.

No field of `IntegralSquareLimitData` carries a transport along `Category.assoc` or
`Functor.map_comp`: the morphism `f` is identified with the composites `p_i ≫ st_i` by the
equations `compatible` and `compatible'` rather than being written out, and likewise `g' ≫ p_i`
is identified with `p'_i ≫ g'_i` by `horizontalCompatible`. This is the convention of this
development; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/DirectImageSystem.lean`.

The structure morphisms are carried as natural transformations to a constant functor, as in
`AlgebraicGeometry.IntegralLimitPresentation`, so that the compatibility of a transition morphism
with the structure morphisms is naturality and needs no separate field.

**No `@[stacks 0EYP]` attribute is attached here.** This file is the geometric setup for that tag,
not a proof of it: nothing about étale cohomology sheaves appears below. Whoever proves 0EYP
should assess its covering set and place the attribute.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Stacks.EtaleCohomology

/-! ### Base change of an inverse system over a fixed base -/

section BaseChange

variable {J : Type w} [Category J] {Y Y' : Scheme.{u}} (D : J ⥤ Scheme.{u})
  (st : D ⟶ (Functor.const J).obj Y) (g : Y' ⟶ Y)

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- Passing from a stage of an inverse system to a later one and then to the base is passing to
the base: the naturality of the structure morphisms, with the identity on the base cancelled. -/
lemma map_comp_structureMap {i j : J} (a : i ⟶ j) : D.map a ≫ st.app j = st.app i := by simp

/-- A transition morphism of an inverse system whose structure morphisms to the base are affine
is itself affine: it is a morphism over the base, so it is cancelled from an affine composite. -/
lemma isAffineHom_map_of_structureMap [∀ j, IsAffineHom (st.app j)] {i j : J} (a : i ⟶ j) :
    IsAffineHom (D.map a) := by
  have : IsAffineHom (D.map a ≫ st.app j) := by
    rw [map_comp_structureMap D st a]; infer_instance
  exact IsAffineHom.of_comp (D.map a) (st.app j)

/-- A stage of an inverse system which is affine over an affine base is affine. -/
lemma isAffine_obj_of_structureMap [∀ j, IsAffineHom (st.app j)] [IsAffine Y] (j : J) :
    IsAffine (D.obj j) :=
  have : IsAffine (((Functor.const J).obj Y).obj j) := inferInstanceAs (IsAffine Y)
  isAffine_of_isAffineHom (st.app j)

/-- The square identity making the transition morphisms of the base-changed system well defined. -/
lemma baseChangeCondition {i j : J} (a : i ⟶ j) :
    (pullback.fst (st.app i) g ≫ D.map a) ≫ st.app j = pullback.snd (st.app i) g ≫ g := by
  rw [Category.assoc, map_comp_structureMap D st a]; exact pullback.condition

/-- **The base change of an inverse system along a morphism into its base.** For an inverse system
`D` of schemes over `Y` and a morphism `g : Y' ⟶ Y`, the system `j ↦ D_j ×_Y Y'`. -/
@[reducible]
def baseChangeDiagram : J ⥤ Scheme.{u} where
  obj j := Limits.pullback (st.app j) g
  map {i j} a :=
    pullback.lift (pullback.fst (st.app i) g ≫ D.map a) (pullback.snd (st.app i) g)
      (baseChangeCondition D st g a)
  map_id j := pullback.hom_ext (by simp) (by simp)
  map_comp a b := pullback.hom_ext (by simp) (by simp)

/-- The stage `j` of the base-changed system is the pullback `D_j ×_Y Y'`. -/
lemma baseChangeDiagram_obj (j : J) :
    (baseChangeDiagram D st g).obj j = Limits.pullback (st.app j) g := rfl

/-- A transition morphism of the base-changed system followed by the first projection is the
first projection followed by the transition morphism of the original system. -/
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {i j : J} (a : i ⟶ j) :
    (baseChangeDiagram D st g).map a ≫ pullback.fst (st.app j) g
      = pullback.fst (st.app i) g ≫ D.map a :=
  pullback.lift_fst _ _ _

/-- A transition morphism of the base-changed system followed by the second projection to `Y'` is
the second projection. -/
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {i j : J} (a : i ⟶ j) :
    (baseChangeDiagram D st g).map a ≫ pullback.snd (st.app j) g = pullback.snd (st.app i) g :=
  pullback.lift_snd _ _ _

/-- The structure morphisms `D_j ×_Y Y' ⟶ Y'` of the base-changed system. -/
def baseChangeStructureMap : baseChangeDiagram D st g ⟶ (Functor.const J).obj Y' where
  app j := pullback.snd (st.app j) g
  naturality i j a := by simp

/-- The horizontal morphisms `D_j ×_Y Y' ⟶ D_j` from the base-changed system to the original
one. -/
def baseChangeHorizontal : baseChangeDiagram D st g ⟶ D where
  app j := pullback.fst (st.app j) g
  naturality i j a := by simp

/-- Every stage of the base-changed system sits in a cartesian square over `g`. -/
lemma isPullback_baseChangeStage (j : J) :
    IsPullback ((baseChangeHorizontal D st g).app j) ((baseChangeStructureMap D st g).app j)
      (st.app j) g :=
  IsPullback.of_hasPullback _ _

/-- The base change along `g` of a system of schemes finite over `Y` is finite over `Y'`. -/
instance isFinite_baseChangeStructureMap [∀ j, IsFinite (st.app j)] (j : J) :
    IsFinite ((baseChangeStructureMap D st g).app j) :=
  inferInstanceAs (IsFinite (pullback.snd (st.app j) g))

/-- Each stage of the base change along `g` of a system affine over `Y` is affine when `Y'` is
affine. -/
instance isAffine_baseChangeDiagram_obj [∀ j, IsAffineHom (st.app j)] [IsAffine Y'] (j : J) :
    IsAffine ((baseChangeDiagram D st g).obj j) :=
  inferInstanceAs (IsAffine (Limits.pullback (st.app j) g))

variable {X X' : Scheme.{u}} (p : (Functor.const J).obj X ⟶ D) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- The cone from `X'` on the base-changed system, induced by `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. -/
def baseChangeProjection (hw : ∀ j, (g' ≫ p.app j) ≫ st.app j = f' ≫ g) :
    (Functor.const J).obj X' ⟶ baseChangeDiagram D st g where
  app j := pullback.lift (g' ≫ p.app j) f' (hw j)
  naturality i j a := by
    have hpa : p.app i ≫ D.map a = p.app j := by simpa using (p.naturality a).symm
    refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_).symm
    · rw [Category.assoc, baseChangeDiagram_map_fst, ← Category.assoc, pullback.lift_fst,
        pullback.lift_fst, Category.assoc, hpa]
    · rw [Category.assoc, baseChangeDiagram_map_snd, pullback.lift_snd, pullback.lift_snd]

/-- The induced cone from `X'` followed by a structure morphism to `Y'` is `f'`. -/
@[simp]
lemma baseChangeProjection_comp_structureMap (hw) (j : J) :
    (baseChangeProjection D st g p g' f' hw).app j ≫ (baseChangeStructureMap D st g).app j = f' :=
  pullback.lift_snd _ _ _

/-- The induced cone from `X'` followed by a horizontal morphism to `D_j` is `g' ≫ p_j`. -/
@[simp]
lemma baseChangeProjection_comp_horizontal (hw) (j : J) :
    (baseChangeProjection D st g p g' f' hw).app j ≫ (baseChangeHorizontal D st g).app j
      = g' ≫ p.app j :=
  pullback.lift_fst _ _ _

end BaseChange

/-! ### The limit of a base-changed system -/

section Limit

variable {J : Type w} [Category J] [IsConnected J] {X X' Y Y' : Scheme.{u}}
  {D D' : J ⥤ Scheme.{u}} {st : D ⟶ (Functor.const J).obj Y}
  {st' : D' ⟶ (Functor.const J).obj Y'} {horiz : D' ⟶ D}
  {p : (Functor.const J).obj X ⟶ D} {p' : (Functor.const J).obj X' ⟶ D'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}

omit [IsConnected J] in
/-- The square comparing the two cones at a stage is cartesian: it is the left half of a
horizontal pasting whose right half is the cartesian square at that stage and whose composite is
the cartesian square on the limits. -/
lemma isPullback_projection_of_stages
    (hsq : ∀ j, IsPullback (horiz.app j) (st'.app j) (st.app j) g)
    (hsqL : IsPullback g' f' f g)
    (hp : ∀ j, p.app j ≫ st.app j = f) (hp' : ∀ j, p'.app j ≫ st'.app j = f')
    (hph : ∀ j, p'.app j ≫ horiz.app j = g' ≫ p.app j) (j : J) :
    IsPullback (p'.app j) g' (horiz.app j) (p.app j) :=
  IsPullback.of_right (by rw [hp' j, hp j]; exact hsqL.flip) (hph j) (hsq j).flip

/-- **A base change of a limit cone is a limit cone.** If `D'` is levelwise the base change of `D`
along `g : Y' ⟶ Y`, if `X = lim D`, and if the square on the limits is cartesian, then
`X' = lim D'`.

Pullbacks commute with connected limits, which is
`CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected`; its hypothesis is exactly
`isPullback_projection_of_stages`. -/
@[sga "4 I 2.5.0" "special case"]
def isLimit_of_isPullback_stages
    (hsq : ∀ j, IsPullback (horiz.app j) (st'.app j) (st.app j) g)
    (hsqL : IsPullback g' f' f g)
    (hp : ∀ j, p.app j ≫ st.app j = f) (hp' : ∀ j, p'.app j ≫ st'.app j = f')
    (hph : ∀ j, p'.app j ≫ horiz.app j = g' ≫ p.app j)
    (hX : IsLimit (Cone.mk X p)) :
    IsLimit (Cone.mk X' p') :=
  isLimitOfIsPullbackOfIsConnected horiz (Cone.mk X' p') (Cone.mk X p)
    { hom := g', w := fun j => by simpa using (hph j).symm }
    (isPullback_projection_of_stages hsq hsqL hp hp' hph) hX

end Limit

/-! ### The bundled datum -/

/-- **The limit presentation of an integral square with affine corners**, the geometric setup of
[Stacks, Tag 0EYP] in the all-affine case.

For a cartesian square with `f` integral and all four corners affine, this bundles: a directed
index, an inverse system `diagram` of schemes *finite* over `Y` with limit `X`, its base change
`diagram'` along `g`, which is an inverse system of schemes finite over `Y'` with limit `X'`, and
the cartesian square relating the two systems at each stage.

No field carries a transport along `Category.assoc` or `Functor.map_comp`; the composites are
identified with `f`, `f'` and `g' ≫ projection` by the equation fields. -/
structure IntegralSquareLimitData {X X' Y Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) where
  /-- The type indexing the inverse systems. -/
  indexType : Type u
  /-- The order making the index type a directed preorder. -/
  [indexPreorder : Preorder indexType]
  [indexNonempty : Nonempty indexType]
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The inverse system `X_i` of schemes over `Y`. -/
  diagram : indexTypeᵒᵖ ⥤ Scheme.{u}
  /-- The structure morphisms `st_i : X_i ⟶ Y`. -/
  structureMap : diagram ⟶ (Functor.const indexTypeᵒᵖ).obj Y
  /-- The projections `p_i : X ⟶ X_i`. -/
  projection : (Functor.const indexTypeᵒᵖ).obj X ⟶ diagram
  /-- Passing from `X` through any stage induces `f`. -/
  compatible : ∀ i, projection.app i ≫ structureMap.app i = f
  /-- The projections exhibit `X` as the limit of the system. -/
  isLimit : IsLimit (Cone.mk X projection)
  /-- Every stage is finite over `Y`. -/
  stageFinite : ∀ i, IsFinite (structureMap.app i)
  /-- Every stage is affine. -/
  stageAffine : ∀ i, IsAffine (diagram.obj i)
  /-- Every transition morphism is affine. -/
  transitionAffine : ∀ {i j : indexTypeᵒᵖ} (a : i ⟶ j), IsAffineHom (diagram.map a)
  /-- The base-changed inverse system `X'_i`, an inverse system of schemes over `Y'`. -/
  diagram' : indexTypeᵒᵖ ⥤ Scheme.{u}
  /-- The structure morphisms `st'_i : X'_i ⟶ Y'`. -/
  structureMap' : diagram' ⟶ (Functor.const indexTypeᵒᵖ).obj Y'
  /-- The horizontal morphisms `g'_i : X'_i ⟶ X_i`. -/
  horizontal : diagram' ⟶ diagram
  /-- The projections `p'_i : X' ⟶ X'_i`. -/
  projection' : (Functor.const indexTypeᵒᵖ).obj X' ⟶ diagram'
  /-- Passing from `X'` through any stage induces `f'`. -/
  compatible' : ∀ i, projection'.app i ≫ structureMap'.app i = f'
  /-- The projections of the two systems are compatible with `g'`. -/
  horizontalCompatible : ∀ i, projection'.app i ≫ horizontal.app i = g' ≫ projection.app i
  /-- The projections exhibit `X'` as the limit of the base-changed system. -/
  isLimit' : IsLimit (Cone.mk X' projection')
  /-- Every stage of the base-changed system is finite over `Y'`. -/
  stageFinite' : ∀ i, IsFinite (structureMap'.app i)
  /-- Every stage of the base-changed system is affine. -/
  stageAffine' : ∀ i, IsAffine (diagram'.obj i)
  /-- Every transition morphism of the base-changed system is affine. -/
  transitionAffine' : ∀ {i j : indexTypeᵒᵖ} (a : i ⟶ j), IsAffineHom (diagram'.map a)
  /-- Each stage sits in a cartesian square over `g`. -/
  isPullbackStage :
    ∀ i, IsPullback (horizontal.app i) (structureMap'.app i) (structureMap.app i) g

attribute [instance] IntegralSquareLimitData.indexPreorder
  IntegralSquareLimitData.indexNonempty IntegralSquareLimitData.indexDirected

namespace IntegralSquareLimitData

variable {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (S : IntegralSquareLimitData g' f' f g)

/-- The index category is connected, being the opposite of a nonempty directed preorder. -/
instance isConnected_indexTypeOp : IsConnected (S.indexTypeᵒᵖ) := IsCofiltered.isConnected _

/-- A transition morphism followed by a structure morphism is a structure morphism. -/
lemma map_comp_structureMap {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.diagram.map a ≫ S.structureMap.app j = S.structureMap.app i :=
  Stacks.EtaleCohomology.map_comp_structureMap S.diagram S.structureMap a

/-- A transition morphism of the base-changed system followed by a structure morphism is a
structure morphism. -/
lemma map_comp_structureMap' {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.diagram'.map a ≫ S.structureMap'.app j = S.structureMap'.app i :=
  Stacks.EtaleCohomology.map_comp_structureMap S.diagram' S.structureMap' a

/-- A cone component followed by a transition morphism is the component at the target. -/
private lemma app_comp_map_of_const {J : Type*} [Category J] {X : Scheme.{u}} {D : J ⥤ Scheme.{u}}
    (p : (Functor.const J).obj X ⟶ D) {i j : J} (a : i ⟶ j) : p.app i ≫ D.map a = p.app j := by
  simpa using (p.naturality a).symm

/-- A projection followed by a transition morphism is a projection. -/
lemma projection_comp_map {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.projection.app i ≫ S.diagram.map a = S.projection.app j :=
  app_comp_map_of_const S.projection a

/-- A projection of the base-changed system followed by a transition morphism is a projection. -/
lemma projection'_comp_map {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.projection'.app i ≫ S.diagram'.map a = S.projection'.app j :=
  app_comp_map_of_const S.projection' a

/-- The horizontal morphisms are natural. -/
lemma map_comp_horizontal {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.diagram'.map a ≫ S.horizontal.app j = S.horizontal.app i ≫ S.diagram.map a :=
  S.horizontal.naturality a

/-- The square comparing the two systems of projections at a stage is cartesian. -/
lemma isPullback_projection (sq : IsPullback g' f' f g) (i : S.indexTypeᵒᵖ) :
    IsPullback (S.projection'.app i) g' (S.horizontal.app i) (S.projection.app i) :=
  isPullback_projection_of_stages S.isPullbackStage sq S.compatible S.compatible'
    S.horizontalCompatible i

/-! ### The data of a stage, with the corners written plainly

The structure morphisms and the projections are components of natural transformations to and from
*constant* functors, so the target of `S.structureMap.app i` is
`((CategoryTheory.Functor.const S.indexTypeᵒᵖ).obj Y).obj i` rather than `Y`, and the source of
`S.projection.app i` is `((CategoryTheory.Functor.const S.indexTypeᵒᵖ).obj X).obj i` rather than
`X`. Each pair of spellings is definitionally equal, but not at the transparency typeclass
inference uses, and — worse — a construction elaborated against the first spelling carries it in
the *implicit* arguments of everything the morphism is substituted into. Two terms that differ
only there are then not syntactically equal, and deciding them forces the kernel through whatever
definition stands in between; for
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange`, the mate of the square comparison of composite
direct images, that is fatal.

The four definitions below are those morphisms with their sources and targets written plainly.
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` is the same device introduced for the
same reason one chapter over, where the symptom was a `synthInstance` timeout instead; see the
module docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean`.

**Any signature mentioning a stage of this presentation must use these, never the components of
the natural transformations.** The horizontal morphisms `S.horizontal.app i` need no such
wrapper: `horizontal` goes between two honest functors, so its components already have plain
sources and targets.
-/

/-- **The structure morphism `st_i : X_i ⟶ Y` of a stage**, with its target written as `Y`. -/
def structureMapAt (i : S.indexTypeᵒᵖ) : S.diagram.obj i ⟶ Y := S.structureMap.app i

/-- **The structure morphism `st'_i : X'_i ⟶ Y'` of a stage of the base-changed system**, with
its target written as `Y'`. -/
def structureMapAt' (i : S.indexTypeᵒᵖ) : S.diagram'.obj i ⟶ Y' := S.structureMap'.app i

/-- **The projection `p_i : X ⟶ X_i`**, with its source written as `X`. -/
def projectionAt (i : S.indexTypeᵒᵖ) : X ⟶ S.diagram.obj i := S.projection.app i

/-- **The projection `p'_i : X' ⟶ X'_i` of the base-changed system**, with its source written as
`X'`. -/
def projectionAt' (i : S.indexTypeᵒᵖ) : X' ⟶ S.diagram'.obj i := S.projection'.app i

/-- `Stacks.EtaleCohomology.IntegralSquareLimitData.compatible` over the plain corners. -/
lemma projectionAt_comp_structureMapAt (i : S.indexTypeᵒᵖ) :
    S.projectionAt i ≫ S.structureMapAt i = f := S.compatible i

/-- `Stacks.EtaleCohomology.IntegralSquareLimitData.compatible'` over the plain corners. -/
lemma projectionAt'_comp_structureMapAt' (i : S.indexTypeᵒᵖ) :
    S.projectionAt' i ≫ S.structureMapAt' i = f' := S.compatible' i

/-- `Stacks.EtaleCohomology.IntegralSquareLimitData.horizontalCompatible` over the plain
corners. -/
lemma projectionAt'_comp_horizontal (i : S.indexTypeᵒᵖ) :
    S.projectionAt' i ≫ S.horizontal.app i = g' ≫ S.projectionAt i := S.horizontalCompatible i

/-- `Stacks.EtaleCohomology.IntegralSquareLimitData.isPullbackStage` over the plain corners. -/
lemma isPullbackStageAt (i : S.indexTypeᵒᵖ) :
    IsPullback (S.horizontal.app i) (S.structureMapAt' i) (S.structureMapAt i) g :=
  S.isPullbackStage i

/-- `Stacks.EtaleCohomology.IntegralSquareLimitData.stageFinite` over the plain corners. It is a
lemma rather than an instance: the plain spelling is a definition, so instance search does not
see through it, which is the whole point of the spelling. -/
lemma isFinite_structureMapAt (i : S.indexTypeᵒᵖ) : IsFinite (S.structureMapAt i) :=
  S.stageFinite i

/-- A projection followed by a transition morphism is a projection, over the plain corners. -/
lemma projectionAt_comp_map {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.projectionAt i ≫ S.diagram.map a = S.projectionAt j := S.projection_comp_map a

/-- A transition morphism followed by a structure morphism is a structure morphism, over the
plain corners. -/
lemma map_comp_structureMapAt {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    S.diagram.map a ≫ S.structureMapAt j = S.structureMapAt i := S.map_comp_structureMap a

/-- The square comparing the two systems of projections at a stage is cartesian, over the plain
corners. -/
lemma isPullback_projectionAt (sq : IsPullback g' f' f g) (i : S.indexTypeᵒᵖ) :
    IsPullback (S.projectionAt' i) g' (S.horizontal.app i) (S.projectionAt i) :=
  S.isPullback_projection sq i

end IntegralSquareLimitData

/-! ### Existence of the datum -/

/-- **The geometric setup of [Stacks, Tag 0EYP] for a square with affine corners.** A cartesian
square whose vertical morphism `f` is integral and whose base `Y` and base change `Y'` are affine
is the limit of a directed inverse system of cartesian squares in which the vertical morphisms are
finite.

[Stacks, Tag 09YZ] over the affine base `Y`, in the form
`AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine`, writes `f` as the limit of
finite morphisms `X_i ⟶ Y`; base changing that system along `g` gives the primed system, whose
limit property is `Stacks.EtaleCohomology.isLimit_of_isPullback_stages`. The affineness of `X` and
`X'` is not assumed: `X` is affine because `f` is integral, hence affine, over the affine `Y`, and
`f'` is integral by base change along the given square. -/
theorem nonempty_integralSquareLimitData {X X' Y Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) [IsIntegralHom f]
    [IsAffine Y] [IsAffine Y'] : Nonempty (IntegralSquareLimitData g' f' f g) := by
  obtain ⟨P⟩ := AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine f
  let := P.indexPreorder
  let := P.indexNonempty
  let := P.indexDirected
  have : IsConnected (P.indexTypeᵒᵖ) := IsCofiltered.isConnected _
  have hfin : ∀ i, IsFinite (P.structureMap.app i) := P.stageFinite
  have haff : ∀ i, IsAffineHom (P.structureMap.app i) := fun i => (P.stageFinite i).toIsAffineHom
  have hcomp : ∀ i, P.limitCone.app i ≫ P.structureMap.app i = f := fun i => (P.compatible i).symm
  have hw : ∀ i, (g' ≫ P.limitCone.app i) ≫ P.structureMap.app i = f' ≫ g := by
    intro i
    rw [Category.assoc, hcomp i, sq.w]
  have hst := baseChangeProjection_comp_structureMap P.diagram P.structureMap g P.limitCone g' f' hw
  have hhor := baseChangeProjection_comp_horizontal P.diagram P.structureMap g P.limitCone g' f' hw
  exact ⟨{ indexType := P.indexType
           diagram := P.diagram
           structureMap := P.structureMap
           projection := P.limitCone
           compatible := hcomp
           isLimit := P.isLimit
           stageFinite := P.stageFinite
           stageAffine := isAffine_obj_of_structureMap P.diagram P.structureMap
           transitionAffine := isAffineHom_map_of_structureMap P.diagram P.structureMap
           diagram' := baseChangeDiagram P.diagram P.structureMap g
           structureMap' := baseChangeStructureMap P.diagram P.structureMap g
           horizontal := baseChangeHorizontal P.diagram P.structureMap g
           projection' := baseChangeProjection P.diagram P.structureMap g P.limitCone g' f' hw
           compatible' := hst
           horizontalCompatible := hhor
           isLimit' :=
             isLimit_of_isPullback_stages
               (isPullback_baseChangeStage P.diagram P.structureMap g) sq hcomp hst hhor P.isLimit
           stageFinite' := isFinite_baseChangeStructureMap P.diagram P.structureMap g
           stageAffine' := isAffine_baseChangeDiagram_obj P.diagram P.structureMap g
           transitionAffine' := isAffineHom_map_of_structureMap _
             (baseChangeStructureMap P.diagram P.structureMap g)
           isPullbackStage := isPullback_baseChangeStage P.diagram P.structureMap g }⟩

end Stacks.EtaleCohomology

end
