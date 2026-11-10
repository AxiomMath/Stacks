module

public import Mathlib.Algebra.Free
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Tactic.CategoryTheory.CategoryStar
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemComparison
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.Comparison
public import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.FlatModel
import StacksFrontier.AlgebraicGeometry.FlatGoodDiagram.ImageBaseChange

/-!
# Flat morphisms of the image systems of good diagrams

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `X ⟶ S` and `Y ⟶ S` be quasi-separated and of finite type, and let
`f : X ⟶ Y` be a morphism over `S` which is flat and of finite presentation. Given good diagrams
for `X ⟶ S` and `Y ⟶ S` (Tag 0CNN) and a morphism `F` of the associated systems of
scheme-theoretic images inducing `f` (Tag 0CNR), this file proves that on a sufficiently late
tail the stage morphisms are flat, the transition squares are cartesian, and the square comparing
`f` with each late stage morphism is cartesian.  This is Stacks Tag 0CNT.

## Main definitions

* `AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`: Stacks Tag 01ZM part (1) -- the
  essential-surjectivity half of Tag 0EY1 -- as an explicit hypothesis.  See *The missing input*
  below.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStage`: the good diagram obtained from
  a good diagram by using its scheme-theoretic image at one stage as a new model, for a finally
  small index.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStageSmallnessFree`: the same
  construction with no smallness hypothesis on the index; this is the one the results below use.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofModel`: the good diagram for `X`
  obtained from a model of `f` over the model of a good diagram for `Y`.
* `AlgebraicGeometry.LimitNoetherianSituation.MorphismAt.ofModel`: the morphism of image systems
  attached to such a model, whose stage morphisms are base changes of the model morphism.

## Main results

The three assertions of Tag 0CNT, in the namespace
`AlgebraicGeometry.LimitNoetherianSituation`:

* `eventually_flat_morphismAt_of_hasFinitePresentationModels`: eventual flatness of the stage
  morphisms.
* `eventually_isPullback_morphismAt_of_hasFinitePresentationModels`: the transition squares are
  cartesian on a late tail.
* `eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels`: the square comparing
  `f` with each late stage morphism is cartesian.

The reduction to a `u`-small index that keeps the index universe of Tag 0CNT free is
`AlgebraicGeometry.exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant`, in
`StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex`: an inverse limit of schemes affine and
scheme-theoretically dominant over a base stays a limit after restriction along a monotone map
from a `u`-small directed preorder, with no smallness hypothesis on the original index.

## The method

This is the proof of the source.  By Tag 01ZM part (1) the morphism `f`, being of finite
presentation, is the base change of a morphism `U ⟶ Y_i` of finite presentation over some stage
of the system of images of `Y`; after increasing `i` that morphism is flat as well, by Tag 04AI.
Replacing the good diagram used for `X` by the one coming from `X ⟶ U ⟶ S_i`
(`GoodDiagram.ofModel`), the stage schemes of `X` become the scheme-theoretic images of `X` in
`Y_{i'} ×_{Y_i} U`; since `U ⟶ Y_i` is flat and the image of `Y ⟶ Y_i` is all of `Y_i`, Tag 081I
identifies that image with `Y_{i'} ×_{Y_i} U` itself.  So for the replaced good diagram the three
assertions hold on the nose, and Tag 0CNS transports them to the given one, the comparison being
an isomorphism of systems at every late stage.

## The input from Tag 01ZM part (1)

The three main results of this file no longer carry Stacks Tag 01ZM part (1),
`AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`, as a hypothesis: their proofs do
not use it.  They are not themselves tagged with `0CNT`.  That hypothesis is **now proved**, as
`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation` in
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing`, and discharged as
`AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`; the unconditional, tagged forms of
the three results are
`StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystemModels`.

## Implementation notes

The reduction to a `u`-small index is the one point where this file does not follow the source.
Tag 01ZM is only available for an index essentially small in the universe of the schemes, while
Tag 0CNT is stated for an index type unrelated to it; so the system of images of `Y` has to be
replaced by a cofinal-enough `u`-small subsystem before Tag 01ZM can be applied.  That is
possible here without any smallness hypothesis, and for a reason specific to this situation: the
projections from `X` to its images are scheme-theoretically dominant, so on an affine open of the
base every stage injects into the limit, the limit of rings is the *union* of the images of the
stages, and a `u`-small family of stages already exhausts it.  Threading that through, the
cofinality condition that the Tag 0CNM family otherwise needs is not needed here, and the index
universe stays free.  No smallness hypothesis is carried by the main results either: the stage
replacement is taken in its smallness-free form
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStageSmallnessFree`, the two
inputs from Tag 0CNR, through Tag 0CNS, are taken in their smallness-free forms
`AlgebraicGeometry.LimitNoetherianSituation.exists_eventual_iso_imageSystem'` and
`AlgebraicGeometry.LimitNoetherianSituation.eventually_natural_imageSystem_comparison'`, and the
projections out of the limit are affine by
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`, which is universe polymorphic in the
index.

## References

* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Flatness as a morphism property -/

section FlatProperty

/-- Flatness transfers across an isomorphism of squares. -/
private lemma flat_of_isomorphic_square
    {A B A' B' : Scheme.{u}} (f : A ⟶ B) (g : A' ⟶ B')
    (α : A ⟶ A') (β : B ⟶ B') [IsIso α] [IsIso β]
    (h : f ≫ β = α ≫ g) [Flat g] : Flat f := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hg : Flat (α ≫ g) := MorphismProperty.RespectsIso.precomp
    (@Flat : MorphismProperty Scheme.{u}) α g inferInstance
  have hf : Flat (f ≫ β) := h ▸ hg
  exact (MorphismProperty.cancel_right_of_respectsIso
    (P := (@Flat : MorphismProperty Scheme.{u})) f β).mp hf

end FlatProperty

/-! ### Limits of schemes affine over a base -/

section AffineOverBase

end AffineOverBase

/-! ### Flat models over a stage -/

namespace LimitDescent

/-- **Stacks Project, Tag 01ZM part (1)**, at an index type in the universe of the schemes: every
scheme of finite presentation over a cofiltered limit of quasi-compact, quasi-separated schemes
with affine transition morphisms is the base change of one of finite presentation over a stage.

This is the essential-surjectivity half of Tag 0EY1 and is not proved in this library; only its
affine case is, as
`AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation_of_isAffine`.  It is
stated here as a predicate so that the results depending on it carry it as a hypothesis rather
than an open goal.  It is an instance of the statement of Tag 01ZM part (1), so proving that
tag discharges it. -/
def HasFinitePresentationModels : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : J, CompactSpace (D.obj i)] [∀ i : J, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D), IsLimit c → ∀ (X : Over c.pt), FinitePresentation X.hom →
      ∃ (i : J) (Xᵢ : Over (D.obj i)), FinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ)

end LimitDescent

section FlatModel

variable (hmod : LimitDescent.HasFinitePresentationModels.{u})

include hmod

end FlatModel

section FlatModelNoetherian

variable (hmod : LimitDescent.HasFinitePresentationModels.{u})

include hmod

end FlatModelNoetherian

/-! ### Scheme-theoretic images under flat base change -/

section ImageFlat

/-- A square of base changes induced by a cartesian square is cartesian. -/
lemma isPullback_induced_baseChange
    {S B W Z Y X : Scheme.{u}} (s : S ⟶ B) (m : W ⟶ B)
    (p : Y ⟶ S) (y : Y ⟶ W) (q : Z ⟶ W)
    (a : X ⟶ Z) (f : X ⟶ Y)
    (hy : p ≫ s = y ≫ m) (hx : a ≫ q = f ≫ y)
    (h : IsPullback a f q y) :
    IsPullback
      (pullback.lift (f ≫ p) a (by
        calc
          (f ≫ p) ≫ s = f ≫ (p ≫ s) := Category.assoc _ _ _
          _ = f ≫ (y ≫ m) := by rw [hy]
          _ = (f ≫ y) ≫ m := (Category.assoc _ _ _).symm
          _ = (a ≫ q) ≫ m := by rw [hx]
          _ = a ≫ q ≫ m := Category.assoc _ _ _))
      f
      (pullback.lift (pullback.fst s (q ≫ m))
        (pullback.snd s (q ≫ m) ≫ q) (by
          rw [Category.assoc, ← pullback.condition]))
      (pullback.lift p y hy) := by
  apply IsPullback.mk' (by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
      exact hx)
  · intro T l l' hl hl'
    refine h.hom_ext ?_ hl'
    have := congrArg (· ≫ pullback.snd s (q ≫ m)) hl
    simpa only [Category.assoc, pullback.lift_snd] using this
  · intro T c b hbc
    have hc : (c ≫ pullback.snd s (q ≫ m)) ≫ q = b ≫ y := by
      have := congrArg (· ≫ pullback.snd s m) hbc
      simpa only [Category.assoc, pullback.lift_snd] using this
    refine ⟨h.lift (c ≫ pullback.snd s (q ≫ m)) b hc, ?_, h.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · have hb : b ≫ p = c ≫ pullback.fst s (q ≫ m) := by
        have := congrArg (· ≫ pullback.fst s m) hbc
        simpa only [Category.assoc, pullback.lift_fst] using this.symm
      simp only [Category.assoc, pullback.lift_fst, h.lift_snd_assoc, hb]
    · simp only [Category.assoc, pullback.lift_snd, h.lift_fst]

end ImageFlat

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-! ### Replacing a good diagram by one of its stages -/

/-- The good diagram obtained from `G` by taking its scheme-theoretic image at the stage `j` as
the new model.  This is the replacement of the initial diagram described in Remark 0CNS: the
image system of `ofStage G j` is the restriction of that of `G` to the tail above `j`. -/
noncomputable def GoodDiagram.ofStage {D : LimitNoetherianSituation.{v, u} I}
    [FinallySmall.{u} I] {X : Scheme.{u}} {p : X ⟶ D.limitScheme} [QuasiCompact p]
    (G : GoodDiagram D p) (j : Over (op G.index)) : GoodDiagram D p := by
  let q := GoodDiagram.stageMap G j
  let b := q.imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap
  have hb : p ≫ D.limitCone.π.app j.left = q.toImage ≫ b := by
    simp only [b, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact (pullback.lift_fst _ _ _).symm
  let l := pullback.lift p q.toImage hb
  let a : pullback (D.limitCone.π.app j.left) b ⟶
      pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
    pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ q.imageι ≫ pullback.snd _ _) (by
        rw [Category.assoc, Category.assoc, ← pullback.condition]
        change pullback.fst _ _ ≫ D.limitCone.π.app (op G.index) =
          pullback.snd _ _ ≫ b ≫ D.system.map j.hom
        rw [← pullback.condition_assoc, D.limitCone.w j.hom])
  let _ : IsAffineHom (D.limitCone.π.app j.left) := isAffineHom_π_of_finallySmall D j.left
  let _ : IsAffineHom (D.limitCone.π.app (op G.index)) :=
    isAffineHom_π_of_finallySmall D (op G.index)
  let _ : IsAffineHom (pullback.snd (D.limitCone.π.app j.left) b) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (D.limitCone.π.app j.left) b)
      (isAffineHom_π_of_finallySmall D j.left)
  let _ : IsAffineHom q.imageι := inferInstance
  let _ : IsAffineHom (pullback.snd (D.system.map j.hom) G.modelMap) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap)
      (D.transition_affine j.hom)
  have : IsAffineHom (a ≫ pullback.snd _ _) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsAffineHom a := IsAffineHom.of_comp a (pullback.snd _ _)
  have hla : l ≫ a = G.induced := by
    apply pullback.hom_ext
    · simp only [l, a, Category.assoc, pullback.lift_fst]
    · simp only [l, a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, ← Category.assoc,
        Scheme.Hom.toImage_imageι]
      exact pullback.lift_snd _ _ _
  have : IsClosedImmersion (l ≫ a) := hla ▸ G.isClosedImmersion
  let _ : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  let _ : QuasiCompact G.modelMap := G.quasiCompact
  exact {
    index := unop j.left
    W := q.image
    modelMap := b
    toModel := q.toImage
    commutes := hb
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    isClosedImmersion := IsClosedImmersion.of_comp l a }

/-- `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofStage` for an index carrying no
smallness hypothesis: the same replacement of the initial diagram, with the affineness of the
projections out of the limit taken from
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`, which is universe polymorphic in the index,
instead of from `AlgebraicGeometry.isAffineHom_π_of_finallySmall`. -/
noncomputable def GoodDiagram.ofStageSmallnessFree {D : LimitNoetherianSituation.{v, u} I}
    {X : Scheme.{u}} {p : X ⟶ D.limitScheme} [QuasiCompact p]
    (G : GoodDiagram D p) (j : Over (op G.index)) : GoodDiagram D p := by
  let q := GoodDiagram.stageMap G j
  let b := q.imageι ≫ pullback.fst (D.system.map j.hom) G.modelMap
  have hb : p ≫ D.limitCone.π.app j.left = q.toImage ≫ b := by
    simp only [b, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact (pullback.lift_fst _ _ _).symm
  let l := pullback.lift p q.toImage hb
  let a : pullback (D.limitCone.π.app j.left) b ⟶
      pullback (D.limitCone.π.app (op G.index)) G.modelMap :=
    pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ q.imageι ≫ pullback.snd _ _) (by
        rw [Category.assoc, Category.assoc, ← pullback.condition]
        change pullback.fst _ _ ≫ D.limitCone.π.app (op G.index) =
          pullback.snd _ _ ≫ b ≫ D.system.map j.hom
        rw [← pullback.condition_assoc, D.limitCone.w j.hom])
  have hπ : ∀ i : Iᵒᵖ, IsAffineHom (D.limitCone.π.app i) := fun i =>
    EventualLimit.isAffineHom_π_app D.system D.limitCone D.isLimit i
  let _ : IsAffineHom (D.limitCone.π.app j.left) := hπ j.left
  let _ : IsAffineHom (D.limitCone.π.app (op G.index)) := hπ (op G.index)
  let _ : IsAffineHom (pullback.snd (D.limitCone.π.app j.left) b) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (D.limitCone.π.app j.left) b)
      (hπ j.left)
  let _ : IsAffineHom q.imageι := inferInstance
  let _ : IsAffineHom (pullback.snd (D.system.map j.hom) G.modelMap) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap)
      (D.transition_affine j.hom)
  have : IsAffineHom (a ≫ pullback.snd _ _) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsAffineHom a := IsAffineHom.of_comp a (pullback.snd _ _)
  have hla : l ≫ a = G.induced := by
    apply pullback.hom_ext
    · simp only [l, a, Category.assoc, pullback.lift_fst]
    · simp only [l, a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, ← Category.assoc,
        Scheme.Hom.toImage_imageι]
      exact pullback.lift_snd _ _ _
  have : IsClosedImmersion (l ≫ a) := hla ▸ G.isClosedImmersion
  let _ : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  let _ : QuasiCompact G.modelMap := G.quasiCompact
  exact {
    index := unop j.left
    W := q.image
    modelMap := b
    toModel := q.toImage
    commutes := hb
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    isClosedImmersion := IsClosedImmersion.of_comp l a }

end LimitNoetherianSituation

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-! ### The good diagram and the morphism of systems attached to a model -/

section Model

variable {D : LimitNoetherianSituation.{v, u} I}
  {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}

/-- The good diagram for `X` obtained from a model `Z ⟶ H.W` of `f : X ⟶ Y` over the model of a
good diagram `H` for `Y`: its model is `Z ⟶ H.W ⟶ S_i`. -/
noncomputable def GoodDiagram.ofModel
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (H : GoodDiagram D pY)
    (Z : Over H.W) (hZ : FinitePresentation Z.hom)
    (e : Over.mk f ≅ (Over.pullback H.toModel).obj Z) : GoodDiagram D pX := by
  let a : X ⟶ Z.left := e.hom.left ≫ pullback.fst Z.hom H.toModel
  have ha : a ≫ Z.hom = f ≫ H.toModel := by
    have he : e.hom.left ≫ pullback.snd Z.hom H.toModel = f := e.hom.w
    dsimp [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hm : pX ≫ D.limitCone.π.app (op H.index) =
      a ≫ (Z.hom ≫ H.modelMap) := by
    rw [← hf, Category.assoc, H.commutes, reassoc_of% ha]
  have hp : IsPullback a f Z.hom H.toModel :=
    IsPullback.of_iso_pullback (CommSq.mk ha) ((Over.forget Y).mapIso e) rfl e.hom.w
  have hpb := isPullback_induced_baseChange
    (D.limitCone.π.app (op H.index)) H.modelMap pY H.toModel Z.hom
    a f H.commutes ha hp
  have hclosed : IsClosedImmersion (pullback.lift pX a hm) := by
    have hs := MorphismProperty.of_isPullback hpb.flip H.isClosedImmersion
    simpa only [hf] using hs
  let _ : LocallyOfFinitePresentation Z.hom := hZ.1
  let _ : QuasiCompact Z.hom := hZ.2.1
  let _ : LocallyOfFiniteType H.modelMap := H.locallyOfFiniteType
  let _ : QuasiCompact H.modelMap := H.quasiCompact
  exact {
    index := H.index
    W := Z.left
    modelMap := Z.hom ≫ H.modelMap
    toModel := a
    commutes := hm
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    isClosedImmersion := hclosed }

/-- The transition morphism between the base changes of a model and of the model it lives over. -/
noncomputable def modelStageMap (H : GoodDiagram D pY) (Z : Over H.W)
    (j : Over (op H.index)) :
    pullback (D.system.map j.hom) (Z.hom ≫ H.modelMap) ⟶
      pullback (D.system.map j.hom) H.modelMap :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Z.hom)
    (by rw [Category.assoc, ← pullback.condition])

/-- The stage transition attached to a model is a base change of the model morphism. -/
private lemma isPullback_modelStageMap (H : GoodDiagram D pY) (Z : Over H.W)
    (j : Over (op H.index)) :
    IsPullback (modelStageMap H Z j)
      (pullback.snd (D.system.map j.hom) (Z.hom ≫ H.modelMap))
      (pullback.snd (D.system.map j.hom) H.modelMap) Z.hom := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [modelStageMap, pullback.lift_fst]
  exact IsPullback.of_hasPullback _ _

/-- The stage maps of the replaced good diagram are base changes of `f`. -/
lemma isPullback_stageMap_model
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (H : GoodDiagram D pY)
    (Z : Over H.W) (hZ : FinitePresentation Z.hom)
    (e : Over.mk f ≅ (Over.pullback H.toModel).obj Z)
    (j : Over (op H.index)) :
    IsPullback (GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j)
      f (modelStageMap H Z j) (GoodDiagram.stageMap H j) := by
  let a : X ⟶ Z.left := e.hom.left ≫ pullback.fst Z.hom H.toModel
  have he : e.hom.left ≫ pullback.snd Z.hom H.toModel = f := e.hom.w
  have ha : a ≫ Z.hom = f ≫ H.toModel := by
    dsimp [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hp : IsPullback a f Z.hom H.toModel :=
    IsPullback.of_iso_pullback (CommSq.mk ha) ((Over.forget Y).mapIso e) rfl he
  have hy : (pY ≫ D.limitCone.π.app j.left) ≫ D.system.map j.hom =
      H.toModel ≫ H.modelMap := by
    rw [Category.assoc, D.limitCone.w j.hom, H.commutes]
  have h := isPullback_induced_baseChange (D.system.map j.hom) H.modelMap
    (pY ≫ D.limitCone.π.app j.left) H.toModel Z.hom a f hy ha hp
  simpa only [GoodDiagram.stageMap, GoodDiagram.ofModel, modelStageMap,
    ← Category.assoc, hf] using h

/-- The stage transition attached to a flat model is flat. -/
private lemma flat_modelStageMap (H : GoodDiagram D pY) (Z : Over H.W) [Flat Z.hom]
    (j : Over (op H.index)) : Flat (modelStageMap H Z j) :=
  MorphismProperty.of_isPullback (isPullback_modelStageMap H Z j).flip inferInstance

end Model

end LimitNoetherianSituation

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}
  {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}

/-! ### The morphism of image systems attached to a model -/

section ModelMorphism

variable (f : X ⟶ Y) (hf : f ≫ pY = pX) (H : GoodDiagram D pY)
  (Z : Over H.W) (hZ : FinitePresentation Z.hom)
  (e : Over.mk f ≅ (Over.pullback H.toModel).obj Z)

/-- The morphism of scheme-theoretic images at a stage induced by the model: the functoriality
`AlgebraicGeometry.Scheme.Hom.imageMap` applied to the square of stage maps. -/
noncomputable def modelImageMap (j : Over (op H.index)) :
    (GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j).image ⟶
      (GoodDiagram.stageMap H j).image :=
  Scheme.Hom.imageMap _ _ f (modelStageMap H Z j)
    (isPullback_stageMap_model f hf H Z hZ e j).w

/-- The induced map of images commutes with the image inclusions and the stage map of the model. -/
@[reassoc (attr := simp)]
lemma modelImageMap_imageι (j : Over (op H.index)) :
    modelImageMap f hf H Z hZ e j ≫ (GoodDiagram.stageMap H j).imageι =
      (GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j).imageι ≫
        modelStageMap H Z j :=
  Scheme.Hom.imageMap_imageι _ _ _ _ _

/-- The stage transitions attached to a model are natural. -/
private lemma modelStageMap_natural {j k : Over (op H.index)} (a : j ⟶ k) :
    GoodDiagram.stageTargetMap (GoodDiagram.ofModel f hf H Z hZ e) a ≫
        modelStageMap H Z k =
      modelStageMap H Z j ≫ GoodDiagram.stageTargetMap H a := by
  apply pullback.hom_ext
  · simp only [modelStageMap, GoodDiagram.ofModel, GoodDiagram.stageTargetMap,
      Category.assoc, pullback.lift_fst]
    simp only [← Category.assoc, pullback.lift_fst]
    exact pullback.lift_fst _ _ _
  · simp only [modelStageMap, GoodDiagram.ofModel, GoodDiagram.stageTargetMap,
      Category.assoc, pullback.lift_snd]
    simp only [← Category.assoc]
    exact congrArg (fun t => t ≫ Z.hom) (pullback.lift_snd _ _ _)

/-- The square of stage transitions attached to a model is cartesian. -/
private lemma isPullback_modelStageMap_transition {j k : Over (op H.index)} (a : j ⟶ k) :
    IsPullback
      (GoodDiagram.stageTargetMap (GoodDiagram.ofModel f hf H Z hZ e) a)
      (modelStageMap H Z j)
      (modelStageMap H Z k)
      (GoodDiagram.stageTargetMap H a) := by
  let aj := GoodDiagram.stageTargetMap (GoodDiagram.ofModel f hf H Z hZ e) a
  let bj := GoodDiagram.stageTargetMap H a
  have hj := (isPullback_modelStageMap H Z j).flip
  have hk := (isPullback_modelStageMap H Z k).flip
  have hx : aj ≫ pullback.snd (D.system.map k.hom) (Z.hom ≫ H.modelMap) =
      pullback.snd (D.system.map j.hom) (Z.hom ≫ H.modelMap) :=
    pullback.lift_snd _ _ _
  have hy : bj ≫ pullback.snd (D.system.map k.hom) H.modelMap =
      pullback.snd (D.system.map j.hom) H.modelMap :=
    pullback.lift_snd _ _ _
  have hout : IsPullback
      (aj ≫ pullback.snd (D.system.map k.hom) (Z.hom ≫ H.modelMap))
      (modelStageMap H Z j) Z.hom
      (bj ≫ pullback.snd (D.system.map k.hom) H.modelMap) := by
    rw [hx, hy]
    exact hj
  exact IsPullback.of_right hout (modelStageMap_natural f hf H Z hZ e a) hk

/-- The morphisms of images attached to a model are natural. -/
lemma modelImageMap_natural {j k : Over (op H.index)} (a : j ⟶ k) :
    GoodDiagram.imageTransition (GoodDiagram.ofModel f hf H Z hZ e) a ≫
        modelImageMap f hf H Z hZ e k =
      modelImageMap f hf H Z hZ e j ≫ GoodDiagram.imageTransition H a := by
  let GX := GoodDiagram.ofModel f hf H Z hZ e
  let aj := GoodDiagram.stageMap GX j
  let ak := GoodDiagram.stageMap GX k
  let bj := GoodDiagram.stageMap H j
  let bk := GoodDiagram.stageMap H k
  let gj := modelImageMap f hf H Z hZ e j
  let gk := modelImageMap f hf H Z hZ e k
  let tj := modelStageMap H Z j
  let tk := modelStageMap H Z k
  apply (cancel_mono bk.imageι).mp
  calc
    (GoodDiagram.imageTransition GX a ≫ gk) ≫ bk.imageι =
        GoodDiagram.imageTransition GX a ≫ (gk ≫ bk.imageι) := Category.assoc _ _ _
    _ = GoodDiagram.imageTransition GX a ≫ (ak.imageι ≫ tk) := by
      rw [modelImageMap_imageι]
    _ = (GoodDiagram.imageTransition GX a ≫ ak.imageι) ≫ tk := (Category.assoc _ _ _).symm
    _ = (aj.imageι ≫ GoodDiagram.stageTargetMap GX a) ≫ tk :=
      congrArg (fun q => q ≫ tk) (GoodDiagram.imageTransition_imageι GX a)
    _ = aj.imageι ≫ (GoodDiagram.stageTargetMap GX a ≫ tk) := Category.assoc _ _ _
    _ = aj.imageι ≫ (tj ≫ GoodDiagram.stageTargetMap H a) :=
      congrArg (fun q => aj.imageι ≫ q) (modelStageMap_natural f hf H Z hZ e a)
    _ = (aj.imageι ≫ tj) ≫ GoodDiagram.stageTargetMap H a := (Category.assoc _ _ _).symm
    _ = (gj ≫ bj.imageι) ≫ GoodDiagram.stageTargetMap H a := by
      rw [modelImageMap_imageι]
    _ = gj ≫ (bj.imageι ≫ GoodDiagram.stageTargetMap H a) := Category.assoc _ _ _
    _ = gj ≫ (GoodDiagram.imageTransition H a ≫ bk.imageι) := by
      rw [GoodDiagram.imageTransition_imageι]
    _ = (gj ≫ GoodDiagram.imageTransition H a) ≫ bk.imageι := (Category.assoc _ _ _).symm

/-- The inclusion of the image at a stage is a base change of the stage map of a flat model. -/
private lemma isPullback_modelImageMap_imageι [QuasiCompact pY] [Flat Z.hom]
    (j : Over (op H.index)) :
    IsPullback (GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j).imageι
      (modelImageMap f hf H Z hZ e j) (modelStageMap H Z j)
      (GoodDiagram.stageMap H j).imageι :=
  have : Flat (modelStageMap H Z j) := flat_modelStageMap H Z j
  have : QuasiCompact (GoodDiagram.stageMap H j) := GoodDiagram.quasiCompact_stageMap H j
  isPullback_image_of_flat (p := modelStageMap H Z j) (q := GoodDiagram.stageMap H j)
    ((isPullback_stageMap_model f hf H Z hZ e j).flip)
    (modelImageMap f hf H Z hZ e j)
    (modelImageMap_imageι f hf H Z hZ e j).symm

/-- The stage morphisms attached to a flat model are flat, for an index carrying no smallness
hypothesis; this is the flat base change of the scheme-theoretic image. -/
private lemma flat_modelImageMap_smallnessFree [QuasiCompact pY]
    (hflat : Flat Z.hom) (j : Over (op H.index)) :
    Flat (modelImageMap f hf H Z hZ e j) :=
  have : Flat Z.hom := hflat
  MorphismProperty.of_isPullback (isPullback_modelImageMap_imageι f hf H Z hZ e j)
    (flat_modelStageMap H Z j)

/-- The squares attached to a flat model are cartesian, for an index carrying no smallness
hypothesis; the argument pastes two flat base-change squares. -/
private lemma isPullback_modelImageMap_transition_smallnessFree [QuasiCompact pY]
    (hflat : Flat Z.hom) {j k : Over (op H.index)} (a : j ⟶ k) :
    IsPullback
      (GoodDiagram.imageTransition (GoodDiagram.ofModel f hf H Z hZ e) a)
      (modelImageMap f hf H Z hZ e j)
      (modelImageMap f hf H Z hZ e k)
      (GoodDiagram.imageTransition H a) := by
  have : Flat Z.hom := hflat
  have hj := isPullback_modelImageMap_imageι f hf H Z hZ e j
  have hk := isPullback_modelImageMap_imageι f hf H Z hZ e k
  have houter := hj.paste_horiz (isPullback_modelStageMap_transition f hf H Z hZ e a)
  rw [← GoodDiagram.imageTransition_imageι (GoodDiagram.ofModel f hf H Z hZ e) a,
    ← GoodDiagram.imageTransition_imageι H a] at houter
  exact IsPullback.of_right houter (modelImageMap_natural f hf H Z hZ e a) hk

/-- The morphism of image systems, starting at the index of `H`, determined by a model. -/
noncomputable def MorphismAt.ofModel :
    MorphismAt D f (GoodDiagram.ofModel f hf H Z hZ e) H H.index le_rfl le_rfl where
  maps := {
    app := modelImageMap f hf H Z hZ e
    naturality := fun _ _ a => modelImageMap_natural f hf H Z hZ e a }
  over_base := by
    intro j
    let a := GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j
    let b := GoodDiagram.stageMap H j
    let t := modelStageMap H Z j
    let g := modelImageMap f hf H Z hZ e j
    change g ≫ b.imageι ≫ pullback.fst _ _ = a.imageι ≫ pullback.fst _ _
    calc
      g ≫ b.imageι ≫ pullback.fst _ _ = (a.imageι ≫ t) ≫ pullback.fst _ _ := by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ pullback.fst _ _)
          (modelImageMap_imageι f hf H Z hZ e j)
      _ = a.imageι ≫ pullback.fst _ _ := by
        have ht : t ≫ pullback.fst (D.system.map j.hom) H.modelMap =
            pullback.fst (D.system.map j.hom) (Z.hom ≫ H.modelMap) :=
          pullback.lift_fst _ _ _
        calc
          (a.imageι ≫ t) ≫ pullback.fst _ _ =
              a.imageι ≫ (t ≫ pullback.fst _ _) := Category.assoc _ _ _
          _ = a.imageι ≫ pullback.fst _ _ := congrArg (fun q => a.imageι ≫ q) ht
  induces := by
    intro j
    change (GoodDiagram.stageMap (GoodDiagram.ofModel f hf H Z hZ e) j).toImage ≫
        modelImageMap f hf H Z hZ e j =
      f ≫ (GoodDiagram.stageMap H j).toImage
    exact Scheme.Hom.toImage_imageMap _ _ _ _ _

end ModelMorphism

end LimitNoetherianSituation

/-! ### Transporting a cartesian transition square to the limit -/

section LimitSquare

/-- If a morphism of cofiltered diagrams is cartesian on every transition square into `k`, then
the square comparing the induced morphism of limits with the component at `k` is cartesian. -/
private lemma isPullback_limit_of_isPullback_transition
    {J : Type*} [Category* J] [IsCofiltered J]
    {C : Type*} [Category* C] {A B : J ⥤ C}
    (cA : Cone A) (cB : Cone B) (hA : IsLimit cA) (hB : IsLimit cB)
    (φ : A ⟶ B) (f : cA.pt ⟶ cB.pt)
    (hf : ∀ j, cA.π.app j ≫ φ.app j = f ≫ cB.π.app j)
    (k : J)
    (hp : ∀ {j : J} (a : j ⟶ k),
      IsPullback (φ.app j) (A.map a) (B.map a) (φ.app k)) :
    IsPullback f (cA.π.app k) (cB.π.app k) (φ.app k) := by
  let hA' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) cA).symm hA
  let hB' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) cB).symm hB
  apply IsPullback.mk' (hf k).symm
  · intro T l l' hl hl'
    apply hA'.hom_ext
    intro j
    change l ≫ cA.π.app j.left = l' ≫ cA.π.app j.left
    apply (hp j.hom).hom_ext
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, hl]
    · simpa only [Category.assoc, cA.w] using hl'
  · intro T a b hab
    let l (j : Over k) : T ⟶ A.obj j.left :=
      (hp j.hom).lift (a ≫ cB.π.app j.left) b (by
        simpa only [Category.assoc, cB.w] using hab)
    have hl₁ (j : Over k) : l j ≫ φ.app j.left = a ≫ cB.π.app j.left :=
      (hp j.hom).lift_fst _ _ _
    have hl₂ (j : Over k) : l j ≫ A.map j.hom = b :=
      (hp j.hom).lift_snd _ _ _
    let d : Cone ((Over.forget k) ⋙ A) := {
      pt := T
      π := {
        app := l
        naturality := by
          intro j j' t
          change 𝟙 T ≫ l j' = l j ≫ A.map t.left
          rw [Category.id_comp]
          apply (hp j'.hom).hom_ext
          · rw [Category.assoc, φ.naturality, ← Category.assoc, hl₁, hl₁,
              Category.assoc, cB.w]
          · rw [Category.assoc, ← A.map_comp, Over.w t, hl₂, hl₂] } }
    refine ⟨hA'.lift d, ?_, ?_⟩
    · apply hB'.hom_ext
      intro j
      change (hA'.lift d ≫ f) ≫ cB.π.app j.left = a ≫ cB.π.app j.left
      rw [Category.assoc, ← hf, ← Category.assoc]
      have h := hA'.fac d j
      change hA'.lift d ≫ cA.π.app j.left = d.π.app j at h
      rw [h]
      exact hl₁ j
    · have h := hA'.fac d (Over.mk (𝟙 k))
      change hA'.lift d ≫ cA.π.app k = _ at h
      rw [h]
      have h' := hl₂ (Over.mk (𝟙 k))
      change l (Over.mk (𝟙 k)) ≫ A.map (𝟙 k) = b at h'
      calc
        d.π.app (Over.mk (𝟙 k)) = l (Over.mk (𝟙 k)) ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = l (Over.mk (𝟙 k)) ≫ A.map (𝟙 k) :=
          congrArg (fun t => l (Over.mk (𝟙 k)) ≫ t) (A.map_id k).symm
        _ = b := h'

end LimitSquare

/-! ### Slices above a later stage -/

section Slice

/-- A stage above `i₀` which is also above `i₁`, read in the slice over `op i₁`. -/
private def overAt {I : Type v} [Preorder I] {i₀ i₁ : I}
    (j : Over (op i₀)) (hj : i₁ ≤ unop j.left) : Over (op i₁) :=
  Over.mk ((homOfLE hj).op)

private lemma overMap_overAt {I : Type v} [Preorder I] {i₀ i₁ : I}
    (h : i₀ ≤ i₁) (j : Over (op i₀)) (hj : i₁ ≤ unop j.left) :
    (Over.map ((homOfLE h).op)).obj (overAt j hj) = j := by
  apply CostructuredArrow.obj_ext
  · rfl
  · rfl

private def overAtHom {I : Type v} [Preorder I] {i₀ i₁ : I}
    {j k : Over (op i₀)} (a : j ⟶ k)
    (hj : i₁ ≤ unop j.left) (hk : i₁ ≤ unop k.left) :
    overAt j hj ⟶ overAt k hk :=
  Over.homMk a.left (Subsingleton.elim _ _)

private lemma overMap_overAtHom {I : Type v} [Preorder I] {i₀ i₁ : I}
    (h : i₀ ≤ i₁) {j k : Over (op i₀)} (a : j ⟶ k)
    (hj : i₁ ≤ unop j.left) (hk : i₁ ≤ unop k.left) :
    (Over.map ((homOfLE h).op)).map (overAtHom a hj hk) = a := by
  apply CostructuredArrow.hom_ext
  rfl

end Slice

namespace LimitNoetherianSituation

/-! ### Tag 0CNT -/

section MainSmallnessFree

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-! The statements of this section carry no smallness hypothesis on the index; those of the
section `Main` below are their specialisations to a finally small index. -/

/-- Two good diagrams for `X` and two for `Y`, together with morphisms of systems inducing `f`
for each pair, are compared on a late tail by isomorphisms of systems commuting with the two
morphisms. -/
private lemma exists_eventual_model_comparison
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (f : X ⟶ Y) (GX GM : GoodDiagram D pX) (GY H : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (hM : GM.index ≤ H.index)
    (M : MorphismAt D f GM H H.index hM le_rfl) :
    ∃ (i₁ : I) (k₀ : i₀ ≤ i₁)
      (kX : GX.index ≤ i₁) (kM : GM.index ≤ i₁)
      (kY : GY.index ≤ i₁) (kH : H.index ≤ i₁)
      (FX : MorphismAt D (𝟙 X) GX GM i₁ kX kM)
      (FY : MorphismAt D (𝟙 Y) GY H i₁ kY kH)
      (i₂ : I) (_ : i₁ ≤ i₂),
      ∀ (j : Over (op i₁)), i₂ ≤ unop j.left →
        IsIso (FX.maps.app j) ∧ IsIso (FY.maps.app j) ∧
        (MorphismAt.restrict D f GX GY k₀ F).maps.app j ≫ FY.maps.app j =
          FX.maps.app j ≫ (MorphismAt.restrict D f GM H kH M).maps.app j := by
  obtain ⟨iX, hGX, hGM, FX₀, GX₀, hIsoX⟩ :=
    exists_eventual_iso_imageSystem' D pX GX GM
  obtain ⟨iY, hGY, hH, FY₀, GY₀, hIsoY⟩ :=
    exists_eventual_iso_imageSystem' D pY GY H
  obtain ⟨iA, h₀A, hXA⟩ := exists_ge_ge i₀ iX
  obtain ⟨iB, hAB, hYB⟩ := exists_ge_ge iA iY
  obtain ⟨i₁, hB₁, hH₁⟩ := exists_ge_ge iB H.index
  let k₀ := h₀A.trans (hAB.trans hB₁)
  let kIX := hXA.trans (hAB.trans hB₁)
  let kIY := hYB.trans hB₁
  let kX := hX.trans k₀
  let kM := hGM.trans kIX
  let kY := hY.trans k₀
  let kH := hH₁
  let FX := MorphismAt.restrict D (𝟙 X) GX GM kIX FX₀
  let FY := MorphismAt.restrict D (𝟙 Y) GY H kIY FY₀
  let FR := MorphismAt.restrict D f GX GY k₀ F
  let MR := MorphismAt.restrict D f GM H kH M
  obtain ⟨i₂, h₁₂, hnat⟩ :=
    eventually_natural_imageSystem_comparison' D f FX FY FR MR
  refine ⟨i₁, k₀, kX, kM, kY, kH, FX, FY, i₂, h₁₂, ?_⟩
  intro j hj
  have hFX : IsIso (FX.maps.app j) := by
    let q : Over (op iX) := (Over.map ((homOfLE kIX).op)).obj j
    have hq := hIsoX q
    change IsIso (FX₀.maps.app q)
    exact ⟨GX₀.maps.app q, hq.1, hq.2⟩
  have hFY : IsIso (FY.maps.app j) := by
    let q : Over (op iY) := (Over.map ((homOfLE kIY).op)).obj j
    have hq := hIsoY q
    change IsIso (FY₀.maps.app q)
    exact ⟨GY₀.maps.app q, hq.1, hq.2⟩
  exact ⟨hFX, hFY, hnat j hj⟩

/-- **Stacks Project, Tag 0CNT, eventual flatness**.

The morphisms of the image systems of a flat morphism of finite presentation are flat at every
sufficiently late stage. -/
theorem eventually_flat_morphismAt_of_hasFinitePresentationModels'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → Flat (F.maps.app j) := by
  obtain ⟨jY, Z, hZ, hflat, e⟩ := exists_flat_model_imageSystem D f hfp GY
  obtain ⟨e⟩ := e
  let H := GoodDiagram.ofStageSmallnessFree GY jY
  let GM := GoodDiagram.ofModel f hf H Z hZ e
  let M := MorphismAt.ofModel f hf H Z hZ e
  obtain ⟨i₁, k₀, kX, kM, kY, kH, FX, FY, i₂, h₁₂, hcmp⟩ :=
    exists_eventual_model_comparison D f GX GM GY H i₀ hX hY F le_rfl M
  refine ⟨i₂, k₀.trans h₁₂, fun j hj => ?_⟩
  let j₁ := overAt j (h₁₂.trans hj)
  let jH := (Over.map ((homOfLE kH).op)).obj j₁
  have hc := hcmp j₁ hj
  let _ : IsIso (FX.maps.app j₁) := hc.1
  let _ : IsIso (FY.maps.app j₁) := hc.2.1
  have hg : Flat ((MorphismAt.restrict D f GM H kH M).maps.app j₁) := by
    change Flat (M.maps.app jH)
    exact flat_modelImageMap_smallnessFree f hf H Z hZ e hflat jH
  let _ : Flat ((MorphismAt.restrict D f GM H kH M).maps.app j₁) := hg
  have hh : Flat ((MorphismAt.restrict D f GX GY k₀ F).maps.app j₁) :=
    flat_of_isomorphic_square _ _ (FX.maps.app j₁) (FY.maps.app j₁) hc.2.2
  change Flat (F.maps.app ((Over.map ((homOfLE k₀).op)).obj j₁)) at hh
  rwa [overMap_overAt k₀ j (h₁₂.trans hj)] at hh

/-- **Stacks Project, Tag 0CNT, cartesian transition squares**.

On a sufficiently late tail every transition square of the morphism of image systems of a flat
morphism of finite presentation is cartesian. -/
theorem eventually_isPullback_morphismAt_of_hasFinitePresentationModels'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ {j k : Over (op i₀)} (a : j ⟶ k),
        i₃ ≤ unop j.left → i₃ ≤ unop k.left →
          IsPullback (F.maps.app j)
            ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map a)
            ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).map a)
            (F.maps.app k) := by
  obtain ⟨jY, Z, hZ, hflat, e⟩ := exists_flat_model_imageSystem D f hfp GY
  obtain ⟨e⟩ := e
  let H := GoodDiagram.ofStageSmallnessFree GY jY
  let GM := GoodDiagram.ofModel f hf H Z hZ e
  let M := MorphismAt.ofModel f hf H Z hZ e
  obtain ⟨i₁, k₀, kX, kM, kY, kH, FX, FY, i₂, h₁₂, hcmp⟩ :=
    exists_eventual_model_comparison D f GX GM GY H i₀ hX hY F le_rfl M
  refine ⟨i₂, k₀.trans h₁₂, fun {j k} a hj hk => ?_⟩
  let j₁ := overAt j (h₁₂.trans hj)
  let k₁ := overAt k (h₁₂.trans hk)
  let a₁ := overAtHom a (h₁₂.trans hj) (h₁₂.trans hk)
  let b := (Over.map ((homOfLE kH).op)).map a₁
  let FR := MorphismAt.restrict D f GX GY k₀ F
  let MR := MorphismAt.restrict D f GM H kH M
  have hcj := hcmp j₁ hj
  have hck := hcmp k₁ hk
  let _ : IsIso (FX.maps.app j₁) := hcj.1
  let _ : IsIso (FY.maps.app j₁) := hcj.2.1
  let _ : IsIso (FX.maps.app k₁) := hck.1
  let _ : IsIso (FY.maps.app k₁) := hck.2.1
  have hmodel : IsPullback (MR.maps.app j₁)
      ((Over.map ((homOfLE kM).op) ⋙ GoodDiagram.imageSystem GM).map a₁)
      ((Over.map ((homOfLE kH).op) ⋙ GoodDiagram.imageSystem H).map a₁)
      (MR.maps.app k₁) := by
    change IsPullback (M.maps.app ((Over.map ((homOfLE kH).op)).obj j₁))
      ((GoodDiagram.imageSystem GM).map ((Over.map ((homOfLE kM).op)).map a₁))
      ((GoodDiagram.imageSystem H).map b)
      (M.maps.app ((Over.map ((homOfLE kH).op)).obj k₁))
    have hb : (Over.map ((homOfLE kM).op)).map a₁ = b := by
      apply CostructuredArrow.hom_ext
      rfl
    rw [hb]
    change IsPullback
      (modelImageMap f hf H Z hZ e ((Over.map ((homOfLE kH).op)).obj j₁))
      (GoodDiagram.imageTransition GM b)
      (GoodDiagram.imageTransition H b)
      (modelImageMap f hf H Z hZ e ((Over.map ((homOfLE kH).op)).obj k₁))
    simpa only [GM, j₁, k₁] using
      (isPullback_modelImageMap_transition_smallnessFree f hf H Z hZ e hflat b).flip
  have hp : IsPullback (FR.maps.app j₁)
      ((Over.map ((homOfLE kX).op) ⋙ GoodDiagram.imageSystem GX).map a₁)
      ((Over.map ((homOfLE kY).op) ⋙ GoodDiagram.imageSystem GY).map a₁)
      (FR.maps.app k₁) :=
    hmodel.of_iso' (asIso (FX.maps.app j₁)) (asIso (FY.maps.app j₁))
      (asIso (FX.maps.app k₁)) (asIso (FY.maps.app k₁)) hcj.2.2.symm
      (FX.maps.naturality a₁).symm (FY.maps.naturality a₁).symm hck.2.2.symm
  change IsPullback
      (F.maps.app ((Over.map ((homOfLE k₀).op)).obj j₁))
      ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map
        ((Over.map ((homOfLE k₀).op)).map a₁))
      ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).map
        ((Over.map ((homOfLE k₀).op)).map a₁))
      (F.maps.app ((Over.map ((homOfLE k₀).op)).obj k₁)) at hp
  have haEq : (Over.map ((homOfLE k₀).op)).map a₁ = a :=
    overMap_overAtHom k₀ a (h₁₂.trans hj) (h₁₂.trans hk)
  simp only [haEq] at hp
  exact hp

/-- **Stacks Project, Tag 0CNT, cartesian limit square**.

The square relating a flat morphism of finite presentation to each sufficiently late morphism of
the image systems is cartesian. -/
theorem eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left →
        IsPullback f
          ((GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j))
          ((GoodDiagram.imageCone GY).π.app ((Over.map ((homOfLE hY).op)).obj j))
          (F.maps.app j) := by
  obtain ⟨i₃, hi₃, hp⟩ :=
    eventually_isPullback_morphismAt_of_hasFinitePresentationModels' D f hf hfp
      GX GY i₀ hX hY F
  let cX := (GoodDiagram.imageCone GX).whisker (Over.map ((homOfLE hX).op))
  let cY := (GoodDiagram.imageCone GY).whisker (Over.map ((homOfLE hY).op))
  let hcX : IsLimit cX := (Functor.Initial.isLimitWhiskerEquiv _ _).symm
    (GoodDiagram.isLimit_imageCone D pX GX)
  let hcY : IsLimit cY := (Functor.Initial.isLimitWhiskerEquiv _ _).symm
    (GoodDiagram.isLimit_imageCone D pY GY)
  refine ⟨i₃, hi₃, fun j hj => ?_⟩
  exact isPullback_limit_of_isPullback_transition cX cY hcX hcY F.maps f
    F.induces j (fun a => hp a (hj.trans (leOfHom a.left.unop)) hj)

end MainSmallnessFree

section Main

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]

omit [FinallySmall.{u} I] in
/-- **Stacks Project, Tag 0CNT, eventual flatness**.

The morphisms of the image systems of a flat morphism of finite presentation are flat at every
sufficiently late stage. -/
theorem eventually_flat_morphismAt_of_hasFinitePresentationModels
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → Flat (F.maps.app j) :=
  eventually_flat_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

omit [FinallySmall.{u} I] in
/-- **Stacks Project, Tag 0CNT, cartesian transition squares**.

On a sufficiently late tail every transition square of the morphism of image systems of a flat
morphism of finite presentation is cartesian. -/
theorem eventually_isPullback_morphismAt_of_hasFinitePresentationModels
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ {j k : Over (op i₀)} (a : j ⟶ k),
        i₃ ≤ unop j.left → i₃ ≤ unop k.left →
          IsPullback (F.maps.app j)
            ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map a)
            ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).map a)
            (F.maps.app k) :=
  eventually_isPullback_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

omit [FinallySmall.{u} I] in
/-- **Stacks Project, Tag 0CNT, cartesian limit square**.

The square relating a flat morphism of finite presentation to each sufficiently late morphism of
the image systems is cartesian. -/
theorem eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left →
        IsPullback f
          ((GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j))
          ((GoodDiagram.imageCone GY).π.app ((Over.map ((homOfLE hY).op)).obj j))
          (F.maps.app j) :=
  eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

end Main

end LimitNoetherianSituation

end AlgebraicGeometry
