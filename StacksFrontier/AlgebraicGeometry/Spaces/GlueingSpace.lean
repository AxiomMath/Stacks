module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructGlueingFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CartesianSquareDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# The glueing construction of Stacks 0EDM over an algebraic space

Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S` and let
`y : Spec k ⟶ Y` be a closed immersion representing a point of `|Y|`.  Over each object `V` of
the big fppf site mapping to `Y` the construction of
`StacksFrontier.AlgebraicGeometry.Spaces.ConstructGlueing` gives a scheme `P_V` over `V`, and by
`StacksFrontier.AlgebraicGeometry.Spaces.ConstructGlueingFunctorial` the assignment is functorial in
the chart and cartesian over an étale separated chart morphism.

This file descends that construction along a separated étale chart `U` of `Y` with kernel pair
`R`.  The two projections of the kernel pair are chart morphisms over `Y`, so they induce two
morphisms `P_R ⇉ P_U`; the diagonal, the flip and the composition of the kernel pair induce the
reflexivity, symmetry and transitivity witnesses; and the cartesian squares make `P_R ⇉ P_U` an
*étale equivalence relation*.  Its quotient sheaf is an algebraic space by
[Stacks Project, Tag 02WW].

## Main definitions

* `AlgebraicGeometry.Space.glueingChartSitePushout` is the chart-level pushout as an object of
  the site, with `AlgebraicGeometry.Space.glueingChartSiteToBase` its structure morphism to the
  chart and `AlgebraicGeometry.Space.glueingChartSitePushoutMap` the induced morphisms.
* `AlgebraicGeometry.Space.glueingRelationTarget` and
  `AlgebraicGeometry.Space.glueingRelationSource` are the two legs `P_R ⇉ P_U`.

## Main results

* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_glueingRelation`: the two legs form an
  étale equivalence relation.
* `AlgebraicGeometry.Space.isAlgebraicSpace_glueingSpaceSheaf`: its quotient sheaf is an
  algebraic space over `S`.

## Implementation notes

The compatibility of a morphism of the site with the structure morphisms to `S` is
`AlgebraicGeometry.toScheme_map_comp_inclusion_hom`.

That the chart-level pushout belongs to the site is not an extra hypothesis: its size is bounded
by those of the two schemes being glued, both of which are objects of the site
(`AlgebraicGeometry.Space.pushoutScheme_size_le`).

The equivalence-relation structure is `Stacks.Descent.isEquivalenceRelation_of_isPullback`: given
the kernel pair as an internal equivalence relation downstairs and the two cartesian squares,
each of reflexivity, symmetry and transitivity reduces to a single equation, and each of those
three equations is an instance of functoriality of the chart-level pushout.  Joint monicity is
free.

## References

* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme
  pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site is a deep instance search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_GlueingSpace :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_GlueingSpace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The functor from the big fppf category over `S` to schemes reflects cospan limits.**  It
preserves them, the category has them, and it reflects isomorphisms, being the composite of the
forgetful functor of a slice with a full subcategory inclusion. -/
theorem reflectsPullbacks_bigFppfOverToScheme :
    ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
  {Ky : BigFppfOver B S hS} {y : yoneda.obj Ky ⟶ Y.1} (hy : IsClosedImmersion B S hS y)
  {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y.1)

/-! ### The chart-level pushout as an object of the site -/

/-- **The chart-level pushout belongs to the site.**  Its size is bounded by the sizes of the
two schemes being glued, and both are objects of the site. -/
theorem contains_glueingChartPushout :
    B.Contains (glueingChartPushout B S hS f hf hy v) := by
  refine (pushoutScheme_size_le (glueingChartSituation B S hS f hf hy v)).trans_lt
    (max_lt ?_ ?_)
  · exact (glueingChartSource B S hS f hf v).left.property
  · exact (glueingChartFibre B S hS hy v).left.property

/-- The chart-level pushout as an object of the big fppf site over `S`. -/
def glueingChartSitePushout : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_glueingChartPushout B S hS f hf hy v)
    (glueingChartPushoutToBase B S hS f hf hy v ≫ B.inclusion.map V.hom)

/-- The underlying scheme of `glueingChartSitePushout` is the chart-level pushout. -/
@[simp] theorem toScheme_obj_glueingChartSitePushout :
    (BigFppfOver.toScheme B S hS).obj (glueingChartSitePushout B S hS f hf hy v) =
      glueingChartPushout B S hS f hf hy v := rfl

/-- The structure morphism of the chart-level pushout to the chart, as a morphism of the site. -/
def glueingChartSiteToBase : glueingChartSitePushout B S hS f hf hy v ⟶ V :=
  BigFppfOver.homMk B S hS V.left.property (B.inclusion.map V.hom)
    (glueingChartPushoutToBase B S hS f hf hy v) rfl

/-- The underlying morphism of schemes of `glueingChartSiteToBase` is
`glueingChartPushoutToBase`. -/
@[simp] theorem toScheme_map_glueingChartSiteToBase :
    (BigFppfOver.toScheme B S hS).map (glueingChartSiteToBase B S hS f hf hy v) =
      glueingChartPushoutToBase B S hS f hf hy v := rfl

/-- The canonical morphism from the chart-level source `X ×_Y V` into the chart-level pushout,
as a morphism of the site. -/
def glueingChartSiteInl :
    glueingChartSource B S hS f hf v ⟶ glueingChartSitePushout B S hS f hf hy v :=
  BigFppfOver.homMk B S hS (contains_glueingChartPushout B S hS f hf hy v)
    (glueingChartPushoutToBase B S hS f hf hy v ≫ B.inclusion.map V.hom)
    (pushoutInl (glueingChartSituation B S hS f hf hy v)) (by
      rw [← Category.assoc, pushoutToBase_inl]
      exact toScheme_map_comp_inclusion_hom B S hS (glueingChartSourceHom B S hS f hf v))

/-- The underlying morphism of schemes of `glueingChartSiteInl` is `pushoutInl`. -/
@[simp] theorem toScheme_map_glueingChartSiteInl :
    (BigFppfOver.toScheme B S hS).map (glueingChartSiteInl B S hS f hf hy v) =
      pushoutInl (glueingChartSituation B S hS f hf hy v) := rfl

/-- The canonical morphism from the chart-level fibre `Spec k ×_Y V` into the chart-level
pushout, as a morphism of the site.  Its image is the distinguished closed subscheme. -/
def glueingChartSiteInr :
    glueingChartFibre B S hS hy v ⟶ glueingChartSitePushout B S hS f hf hy v :=
  BigFppfOver.homMk B S hS (contains_glueingChartPushout B S hS f hf hy v)
    (glueingChartPushoutToBase B S hS f hf hy v ≫ B.inclusion.map V.hom)
    (pushoutInr (glueingChartSituation B S hS f hf hy v)) (by
      rw [← Category.assoc, pushoutToBase_inr]
      exact toScheme_map_comp_inclusion_hom B S hS (glueingChartFibreHom B S hS hy v))

/-- The underlying morphism of schemes of `glueingChartSiteInr` is `pushoutInr`. -/
@[simp] theorem toScheme_map_glueingChartSiteInr :
    (BigFppfOver.toScheme B S hS).map (glueingChartSiteInr B S hS f hf hy v) =
      pushoutInr (glueingChartSituation B S hS f hf hy v) := rfl

/-- The canonical morphism from the chart-level fibre into the chart-level pushout lies over the
structure morphism of the fibre. -/
theorem glueingChartSiteInr_comp_toBase :
    glueingChartSiteInr B S hS f hf hy v ≫ glueingChartSiteToBase B S hS f hf hy v =
      glueingChartFibreHom B S hS hy v := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [CategoryTheory.Functor.map_comp, toScheme_map_glueingChartSiteInr,
    toScheme_map_glueingChartSiteToBase]
  exact pushoutToBase_inr (glueingChartSituation B S hS f hf hy v)

/-- The canonical morphism into the chart-level pushout lies over the structure morphism of the
chart-level source. -/
theorem glueingChartSiteInl_comp_toBase :
    glueingChartSiteInl B S hS f hf hy v ≫ glueingChartSiteToBase B S hS f hf hy v =
      glueingChartSourceHom B S hS f hf v := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [CategoryTheory.Functor.map_comp, toScheme_map_glueingChartSiteInl,
    toScheme_map_glueingChartSiteToBase]
  exact pushoutToBase_inl (glueingChartSituation B S hS f hf hy v)

section ChartMap

variable {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1} {v' : yoneda.obj V' ⟶ Y.1}
  (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v)

include ha in
/-- The morphism of chart-level pushouts induced by a morphism of charts over `Y`, as a morphism
of the site. -/
def glueingChartSitePushoutMap :
    glueingChartSitePushout B S hS f hf hy v ⟶ glueingChartSitePushout B S hS f hf hy v' :=
  BigFppfOver.homMk B S hS (contains_glueingChartPushout B S hS f hf hy v')
    (glueingChartPushoutToBase B S hS f hf hy v' ≫ B.inclusion.map V'.hom)
    (glueingChartPushoutMap B S hS f hf hy a ha) (by
      change glueingChartPushoutMap B S hS f hf hy a ha ≫
          (glueingChartPushoutToBase B S hS f hf hy v' ≫ B.inclusion.map V'.hom) =
        glueingChartPushoutToBase B S hS f hf hy v ≫ B.inclusion.map V.hom
      rw [← Category.assoc, glueingChartPushoutMap_comp_toBase, Category.assoc,
        toScheme_map_comp_inclusion_hom])

/-- The underlying morphism of schemes of `glueingChartSitePushoutMap` is
`glueingChartPushoutMap`. -/
@[simp] theorem toScheme_map_glueingChartSitePushoutMap :
    (BigFppfOver.toScheme B S hS).map (glueingChartSitePushoutMap B S hS f hf hy a ha) =
      glueingChartPushoutMap B S hS f hf hy a ha := rfl

include ha in
/-- The induced morphism of chart-level pushouts lies over `a`, as a morphism of the site. -/
theorem glueingChartSitePushoutMap_comp_toBase :
    glueingChartSitePushoutMap B S hS f hf hy a ha ≫
        glueingChartSiteToBase B S hS f hf hy v' =
      glueingChartSiteToBase B S hS f hf hy v ≫ a := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    toScheme_map_glueingChartSitePushoutMap, toScheme_map_glueingChartSiteToBase,
    toScheme_map_glueingChartSiteToBase]
  exact glueingChartPushoutMap_comp_toBase B S hS f hf hy a ha

include ha in
/-- **The chart-level pushout over a chart is the base change of the one over a larger chart**,
as a cartesian square of the site. -/
theorem isPullback_glueingChartSitePushoutMap
    (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    IsPullback (glueingChartSitePushoutMap B S hS f hf hy a ha)
      (glueingChartSiteToBase B S hS f hf hy v)
      (glueingChartSiteToBase B S hS f hf hy v') a := by
  have := reflectsPullbacks_bigFppfOverToScheme B S hS
  refine IsPullback.of_map (BigFppfOver.toScheme B S hS)
    (glueingChartSitePushoutMap_comp_toBase B S hS f hf hy a ha) ?_
  rw [toScheme_map_glueingChartSitePushoutMap, toScheme_map_glueingChartSiteToBase,
    toScheme_map_glueingChartSiteToBase]
  exact isPullback_glueingChartPushoutMap B S hS f hf hy a ha het hsep

/-- The induced morphism of chart-level pushouts is étale, as a morphism of the site. -/
theorem etale_glueingChartSitePushoutMap
    (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (glueingChartSitePushoutMap B S hS f hf hy a ha)) := by
  rw [toScheme_map_glueingChartSitePushoutMap]
  exact etale_glueingChartPushoutMap B S hS f hf hy a ha het hsep

/-! ### Functoriality of the chart-level pushout in the site -/

/-- Equal chart morphisms induce the same morphism of chart-level pushouts. -/
theorem glueingChartSitePushoutMap_congr (a' : V ⟶ V')
    (ha' : yoneda.map a' ≫ v' = v) (h : a = a') :
    glueingChartSitePushoutMap B S hS f hf hy a ha =
      glueingChartSitePushoutMap B S hS f hf hy a' ha' := by
  subst h
  rfl

/-- The identity of a chart induces the identity of the chart-level pushout, as a morphism of
the site. -/
theorem glueingChartSitePushoutMap_id (hv : yoneda.map (𝟙 V) ≫ v = v) :
    glueingChartSitePushoutMap B S hS f hf hy (𝟙 V) hv = 𝟙 _ := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [toScheme_map_glueingChartSitePushoutMap, CategoryTheory.Functor.map_id,
    glueingChartPushoutMap_id]
  rfl

include ha in
/-- The canonical morphisms into the chart-level pushouts are natural in the chart. -/
theorem glueingChartSiteInl_naturality :
    glueingChartSiteInl B S hS f hf hy v ≫ glueingChartSitePushoutMap B S hS f hf hy a ha =
      glueingChartSourceMap B S hS f hf a ha ≫ glueingChartSiteInl B S hS f hf hy v' := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    toScheme_map_glueingChartSiteInl, toScheme_map_glueingChartSitePushoutMap,
    toScheme_map_glueingChartSiteInl]
  exact pushoutInl_comp_glueingChartPushoutMap B S hS f hf hy a ha

include ha in
/-- The canonical morphisms from the chart-level fibres into the chart-level pushouts are
natural in the chart. -/
theorem glueingChartSiteInr_naturality :
    glueingChartSiteInr B S hS f hf hy v ≫ glueingChartSitePushoutMap B S hS f hf hy a ha =
      glueingChartFibreMap B S hS hy a ha ≫ glueingChartSiteInr B S hS f hf hy v' := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    toScheme_map_glueingChartSiteInr, toScheme_map_glueingChartSitePushoutMap,
    toScheme_map_glueingChartSiteInr]
  exact pushoutInr_comp_glueingChartPushoutMap B S hS f hf hy a ha

end ChartMap

section ChartComp

variable {V V' V'' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1} {v' : yoneda.obj V' ⟶ Y.1}
  {v'' : yoneda.obj V'' ⟶ Y.1}
  (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) (b : V' ⟶ V'') (hb : yoneda.map b ≫ v'' = v')

/-- **Functoriality of the chart-level pushout in the site.** -/
theorem glueingChartSitePushoutMap_comp (hab : yoneda.map (a ≫ b) ≫ v'' = v) :
    glueingChartSitePushoutMap B S hS f hf hy (a ≫ b) hab =
      glueingChartSitePushoutMap B S hS f hf hy a ha ≫
        glueingChartSitePushoutMap B S hS f hf hy b hb := by
  apply BigFppfOver.map_toScheme_injective B S hS
  beta_reduce
  rw [toScheme_map_glueingChartSitePushoutMap, CategoryTheory.Functor.map_comp,
    toScheme_map_glueingChartSitePushoutMap, toScheme_map_glueingChartSitePushoutMap]
  exact glueingChartPushoutMap_comp B S hS f hf hy a ha b hb

/-- Functoriality, in the form in which the relation identities use it: a composite of chart
morphisms known to equal a third one. -/
theorem glueingChartSitePushoutMap_comp_eq (d : V ⟶ V'') (hd : yoneda.map d ≫ v'' = v)
    (h : a ≫ b = d) :
    glueingChartSitePushoutMap B S hS f hf hy a ha ≫
        glueingChartSitePushoutMap B S hS f hf hy b hb =
      glueingChartSitePushoutMap B S hS f hf hy d hd := by
  rw [← glueingChartSitePushoutMap_comp B S hS f hf hy a ha b hb
    (by rw [CategoryTheory.Functor.map_comp, Category.assoc, hb, ha])]
  exact glueingChartSitePushoutMap_congr B S hS f hf hy (a ≫ b)
    (by rw [CategoryTheory.Functor.map_comp, Category.assoc, hb, ha]) d hd h

end ChartComp

/-- Two factorizations of the same chart morphism give the same composite of induced morphisms of
chart-level pushouts. -/
private theorem glueingChartSitePushoutMap_comp_congr {W₁ W₂ W₃ W₄ : BigFppfOver B S hS}
    {w₁ : yoneda.obj W₁ ⟶ Y.1} {w₂ : yoneda.obj W₂ ⟶ Y.1} {w₃ : yoneda.obj W₃ ⟶ Y.1}
    {w₄ : yoneda.obj W₄ ⟶ Y.1} (a : W₁ ⟶ W₂)
    (ha : yoneda.map a ≫ w₂ = w₁) (b : W₂ ⟶ W₄) (hb : yoneda.map b ≫ w₄ = w₂) (a' : W₁ ⟶ W₃)
    (ha' : yoneda.map a' ≫ w₃ = w₁) (b' : W₃ ⟶ W₄) (hb' : yoneda.map b' ≫ w₄ = w₃)
    (h : a ≫ b = a' ≫ b') :
    glueingChartSitePushoutMap B S hS f hf hy a ha ≫
        glueingChartSitePushoutMap B S hS f hf hy b hb =
      glueingChartSitePushoutMap B S hS f hf hy a' ha' ≫
        glueingChartSitePushoutMap B S hS f hf hy b' hb' := by
  have hd : yoneda.map (a ≫ b) ≫ w₄ = w₁ := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hb, ha]
  exact (glueingChartSitePushoutMap_comp_eq B S hS f hf hy a ha b hb _ hd rfl).trans
    (glueingChartSitePushoutMap_comp_eq B S hS f hf hy a' ha' b' hb' _ hd h.symm).symm

/-! ### The relation on the chart-level pushouts -/

section Relation

variable (c : EtaleChartRelation B S hS Y.1)

/-- The chart-level pushout over the chart of a separated étale chart relation. -/
abbrev glueingRelationBase : BigFppfOver B S hS :=
  glueingChartSitePushout B S hS f hf hy c.u

/-- The chart-level pushout over the relation object. -/
abbrev glueingRelationObj : BigFppfOver B S hS :=
  glueingChartSitePushout B S hS f hf hy c.chartR

/-- The chart-level pushout over the object of composable pairs. -/
abbrev glueingRelationTwo : BigFppfOver B S hS :=
  glueingChartSitePushout B S hS f hf hy c.chartTwo

/-- The target leg of the relation on the chart-level pushouts. -/
def glueingRelationTarget :
    glueingRelationObj B S hS f hf hy c ⟶ glueingRelationBase B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.t c.t_chart

/-- The source leg of the relation on the chart-level pushouts. -/
def glueingRelationSource :
    glueingRelationObj B S hS f hf hy c ⟶ glueingRelationBase B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.s c.s_chart

/-- The reflexivity witness. -/
def glueingRelationRefl :
    glueingRelationBase B S hS f hf hy c ⟶ glueingRelationObj B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.diag c.diag_chart

/-- The symmetry witness. -/
def glueingRelationFlip :
    glueingRelationObj B S hS f hf hy c ⟶ glueingRelationObj B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.flip c.flip_chart

/-- The first projection from the composable pairs. -/
def glueingRelationFirst :
    glueingRelationTwo B S hS f hf hy c ⟶ glueingRelationObj B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.first c.first_chart

/-- The second projection from the composable pairs. -/
def glueingRelationSecond :
    glueingRelationTwo B S hS f hf hy c ⟶ glueingRelationObj B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.second c.second_chart

/-- The transitivity witness. -/
def glueingRelationComp :
    glueingRelationTwo B S hS f hf hy c ⟶ glueingRelationObj B S hS f hf hy c :=
  glueingChartSitePushoutMap B S hS f hf hy c.comp c.comp_chart

/-! #### The relation identities, each an instance of functoriality -/

/-- The reflexivity witness followed by the target leg is the identity. -/
theorem glueingRelationRefl_comp_target :
    glueingRelationRefl B S hS f hf hy c ≫ glueingRelationTarget B S hS f hf hy c = 𝟙 _ := by
  rw [glueingRelationRefl, glueingRelationTarget,
    glueingChartSitePushoutMap_comp_eq B S hS f hf hy c.diag c.diag_chart c.t c.t_chart
      (𝟙 c.U) (by simp) c.diag_comp_t]
  exact glueingChartSitePushoutMap_id B S hS f hf hy (by simp)

/-- The reflexivity witness followed by the source leg is the identity. -/
theorem glueingRelationRefl_comp_source :
    glueingRelationRefl B S hS f hf hy c ≫ glueingRelationSource B S hS f hf hy c = 𝟙 _ := by
  rw [glueingRelationRefl, glueingRelationSource,
    glueingChartSitePushoutMap_comp_eq B S hS f hf hy c.diag c.diag_chart c.s c.s_chart
      (𝟙 c.U) (by simp) c.diag_comp_s]
  exact glueingChartSitePushoutMap_id B S hS f hf hy (by simp)

/-- The symmetry witness followed by the target leg is the source leg. -/
theorem glueingRelationFlip_comp_target :
    glueingRelationFlip B S hS f hf hy c ≫ glueingRelationTarget B S hS f hf hy c =
      glueingRelationSource B S hS f hf hy c :=
  glueingChartSitePushoutMap_comp_eq B S hS f hf hy c.flip c.flip_chart c.t c.t_chart
    c.s c.s_chart c.flip_comp_t

/-- The symmetry witness followed by the source leg is the target leg. -/
theorem glueingRelationFlip_comp_source :
    glueingRelationFlip B S hS f hf hy c ≫ glueingRelationSource B S hS f hf hy c =
      glueingRelationTarget B S hS f hf hy c :=
  glueingChartSitePushoutMap_comp_eq B S hS f hf hy c.flip c.flip_chart c.s c.s_chart
    c.t c.t_chart c.flip_comp_s

/-- The source of the first projection of a composable pair is the target of the second. -/
theorem glueingRelationFirst_comp_source :
    glueingRelationFirst B S hS f hf hy c ≫ glueingRelationSource B S hS f hf hy c =
      glueingRelationSecond B S hS f hf hy c ≫ glueingRelationTarget B S hS f hf hy c := by
  exact glueingChartSitePushoutMap_comp_congr B S hS f hf hy c.first c.first_chart c.s c.s_chart
    c.second c.second_chart c.t c.t_chart c.first_comp_s

/-- The target of the composite of a composable pair is the target of its first projection. -/
theorem glueingRelationComp_comp_target :
    glueingRelationComp B S hS f hf hy c ≫ glueingRelationTarget B S hS f hf hy c =
      glueingRelationFirst B S hS f hf hy c ≫ glueingRelationTarget B S hS f hf hy c := by
  exact glueingChartSitePushoutMap_comp_congr B S hS f hf hy c.comp c.comp_chart c.t c.t_chart
    c.first c.first_chart c.t c.t_chart c.comp_comp_t

/-- The source of the composite of a composable pair is the source of its second projection. -/
theorem glueingRelationComp_comp_source :
    glueingRelationComp B S hS f hf hy c ≫ glueingRelationSource B S hS f hf hy c =
      glueingRelationSecond B S hS f hf hy c ≫ glueingRelationSource B S hS f hf hy c := by
  exact glueingChartSitePushoutMap_comp_congr B S hS f hf hy c.comp c.comp_chart c.s c.s_chart
    c.second c.second_chart c.s c.s_chart c.comp_comp_s

/-! #### The two legs are étale, and cartesian over the two projections -/

/-- The target leg of the relation on the chart-level pushouts is étale. -/
theorem etale_glueingRelationTarget :
    Etale ((BigFppfOver.toScheme B S hS).map (glueingRelationTarget B S hS f hf hy c)) :=
  etale_glueingChartSitePushoutMap B S hS f hf hy c.t c.t_chart c.etale_t c.isSeparated_t

/-- The source leg of the relation on the chart-level pushouts is étale. -/
theorem etale_glueingRelationSource :
    Etale ((BigFppfOver.toScheme B S hS).map (glueingRelationSource B S hS f hf hy c)) :=
  etale_glueingChartSitePushoutMap B S hS f hf hy c.s c.s_chart c.etale_s c.isSeparated_s

/-- The target leg is the base change of `P_U ⟶ U` along the target projection `R ⟶ U`. -/
theorem isPullback_glueingRelationTarget :
    IsPullback (glueingRelationTarget B S hS f hf hy c)
      (glueingChartSiteToBase B S hS f hf hy c.chartR)
      (glueingChartSiteToBase B S hS f hf hy c.u) c.t :=
  isPullback_glueingChartSitePushoutMap B S hS f hf hy c.t c.t_chart c.etale_t c.isSeparated_t

/-- The source leg is the base change of `P_U ⟶ U` along the source projection `R ⟶ U`. -/
theorem isPullback_glueingRelationSource :
    IsPullback (glueingRelationSource B S hS f hf hy c)
      (glueingChartSiteToBase B S hS f hf hy c.chartR)
      (glueingChartSiteToBase B S hS f hf hy c.u) c.s :=
  isPullback_glueingChartSitePushoutMap B S hS f hf hy c.s c.s_chart c.etale_s c.isSeparated_s

/-- The first projection from the composable pairs of the chart-level pushouts is the base change
of `P_R ⟶ R` along the first projection of the composable pairs of `R`. -/
theorem isPullback_glueingRelationFirst :
    IsPullback (glueingRelationFirst B S hS f hf hy c)
      (glueingChartSiteToBase B S hS f hf hy c.chartTwo)
      (glueingChartSiteToBase B S hS f hf hy c.chartR) c.first :=
  isPullback_glueingChartSitePushoutMap B S hS f hf hy c.first c.first_chart c.etale_first
    c.isSeparated_first

/-- The second projection from the composable pairs of the chart-level pushouts is the base
change of `P_R ⟶ R` along the second projection of the composable pairs of `R`. -/
theorem isPullback_glueingRelationSecond :
    IsPullback (glueingRelationSecond B S hS f hf hy c)
      (glueingChartSiteToBase B S hS f hf hy c.chartTwo)
      (glueingChartSiteToBase B S hS f hf hy c.chartR) c.second :=
  isPullback_glueingChartSitePushoutMap B S hS f hf hy c.second c.second_chart c.etale_second
    c.isSeparated_second

/-- **The composable pairs of the relation on the pushouts are the fibre product of the two
legs.**  Pasting the cartesian square of the first projection with the one of the composable
pairs of the base relation, and cancelling the cartesian square of the second leg. -/
theorem isPullback_glueingRelationFirst_second :
    IsPullback (glueingRelationFirst B S hS f hf hy c) (glueingRelationSecond B S hS f hf hy c)
      (glueingRelationSource B S hS f hf hy c) (glueingRelationTarget B S hS f hf hy c) := by
  refine (IsPullback.of_right ?_ ?_ (isPullback_glueingRelationTarget B S hS f hf hy c).flip).flip
  · have h := IsPullback.paste_horiz (isPullback_glueingRelationFirst B S hS f hf hy c).flip
      c.isPullback_two.flip
    rw [← (isPullback_glueingRelationSecond B S hS f hf hy c).w,
      ← (isPullback_glueingRelationSource B S hS f hf hy c).w] at h
    exact h
  · exact (glueingRelationFirst_comp_source B S hS f hf hy c).symm

/-! #### The étale equivalence relation and its quotient -/

/-- The kernel pair of the chart is an internal equivalence relation of presheaves. -/
def baseEquivalenceRelation : EquivalenceRelation (yoneda.map c.t) (yoneda.map c.s) :=
  IsKernelPair.equivalenceRelation c.u (yoneda.map c.t) (yoneda.map c.s)
    (IsPullback.of_hasPullback (yoneda.map c.s) (yoneda.map c.t)).isLimit c.isPullback

/-- **The two legs of the relation on the chart-level pushouts form an internal equivalence
relation of presheaves.**  The two cartesian squares reduce each of reflexivity, symmetry and
transitivity to one equation, and each of those three is an instance of functoriality of the
chart-level pushout. -/
theorem isEquivalenceRelation_yoneda_glueingRelation :
    IsEquivalenceRelation (yoneda.map (glueingRelationTarget B S hS f hf hy c))
      (yoneda.map (glueingRelationSource B S hS f hf hy c)) := by
  refine Stacks.Descent.isEquivalenceRelation_of_isPullback (baseEquivalenceRelation B S hS c)
    ((isPullback_glueingRelationTarget B S hS f hf hy c).map yoneda)
    ((isPullback_glueingRelationSource B S hS f hf hy c).map yoneda)
    (PullbackCone.mk (yoneda.map (glueingRelationFirst B S hS f hf hy c))
      (yoneda.map (glueingRelationSecond B S hS f hf hy c))
      ((isPullback_glueingRelationFirst_second B S hS f hf hy c).map yoneda).w)
    ((isPullback_glueingRelationFirst_second B S hS f hf hy c).map yoneda).isLimit
    ⟨yoneda.map (glueingRelationRefl B S hS f hf hy c), ?_, ?_⟩
    ⟨yoneda.map (glueingRelationFlip B S hS f hf hy c), ?_, ?_⟩
    ⟨yoneda.map (glueingRelationComp B S hS f hf hy c), ?_, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, glueingRelationRefl_comp_target,
      CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, glueingRelationRefl_comp_source,
      CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, glueingRelationFlip_comp_target]
  · rw [← CategoryTheory.Functor.map_comp, glueingRelationFlip_comp_source]
  · change yoneda.map (glueingRelationComp B S hS f hf hy c) ≫
        yoneda.map (glueingRelationTarget B S hS f hf hy c) =
      yoneda.map (glueingRelationFirst B S hS f hf hy c) ≫
        yoneda.map (glueingRelationTarget B S hS f hf hy c)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      glueingRelationComp_comp_target]
  · change yoneda.map (glueingRelationComp B S hS f hf hy c) ≫
        yoneda.map (glueingRelationSource B S hS f hf hy c) =
      yoneda.map (glueingRelationSecond B S hS f hf hy c) ≫
        yoneda.map (glueingRelationSource B S hS f hf hy c)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      glueingRelationComp_comp_source]

/-- A property of presheaf morphisms that holds after every representable base change is stable
under base change. -/
private theorem presheaf_inverseImage_of_isPullback (P : MorphismProperty Scheme.{u})
    {W X Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : W ⟶ X} {snd : W ⟶ Z} {f : X ⟶ T}
    {g : Z ⟶ T} (h : IsPullback fst snd f g)
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf snd :=
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
    (F := yoneda (C := BigFppfOver B S hS))
  MorphismProperty.IsStableUnderBaseChange.of_isPullback h hf

/-- The base change of a kernel pair along a morphism `X ⟶ Y` is the kernel pair of the base
change of the chart. -/
private theorem isPullback_kernel_pair_of_isPullback {C : Type*} [Category C]
    {AR AU R U X Y : C} {ks kt : AR ⟶ AU} {hR : AR ⟶ R} {hU : AU ⟶ U} {p : AU ⟶ X} {f : X ⟶ Y}
    {s t : R ⟶ U} {u : U ⟶ Y} (hKt : IsPullback kt hR hU t) (hKs : IsPullback ks hR hU s)
    (hCu : IsPullback p hU f u) (hP : IsPullback s t u u) (h : ks ≫ p = kt ≫ p) :
    IsPullback ks kt p p := by
  have hrect := IsPullback.paste_horiz hKt.flip hP
  rw [← hKs.w, ← hCu.w] at hrect
  exact IsPullback.of_right hrect h hCu.flip

/-- If the squares `iR ≫ src = sA ≫ iU` and `iR ≫ tgt = tA ≫ iU` commute, and `q` coequalizes
`src` and `tgt`, then `iU ≫ q` coequalizes `sA` and `tA`. -/
private theorem map_comp_eq_map_comp_of_squares {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A A' P P' : C} {Q : D} {iR : A ⟶ P} {iU : A' ⟶ P'} {src tgt : P ⟶ P'}
    {sA tA : A ⟶ A'} {q : F.obj P' ⟶ Q} (h1 : iR ≫ src = sA ≫ iU) (h2 : iR ≫ tgt = tA ≫ iU)
    (hq : F.map src ≫ q = F.map tgt ≫ q) : F.map sA ≫ F.map iU ≫ q = F.map tA ≫ F.map iU ≫ q := by
  rw [← Category.assoc, ← F.map_comp, ← h1, F.map_comp, Category.assoc, hq, ← Category.assoc,
    ← F.map_comp, h2, F.map_comp, Category.assoc]

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The relation on the chart-level pushouts is an étale equivalence relation.**  This is the
hypothesis of [Stacks Project, Tag 02WW]. -/
theorem isEtaleEquivalenceRelation_glueingRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B S hS (glueingRelationSource B S hS f hf hy c)
        (glueingRelationTarget B S hS f hf hy c)) := by
  refine isEtaleEquivalenceRelation_of_yoneda B S hS _ _ (Iso.refl _) ?_
    (etale_glueingRelationTarget B S hS f hf hy c)
    (etale_glueingRelationSource B S hS f hf hy c)
  simpa only [Iso.refl_hom, Category.id_comp] using
    isEquivalenceRelation_yoneda_glueingRelation B S hS f hf hy c

/-- **The algebraic space `X'` of [Stacks Project, Tag 0EDM].**  It is the quotient of the
chart-level pushout `P_U` by the étale equivalence relation `P_R ⇉ P_U`. -/
def glueingSpaceSheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (glueingRelationSource B S hS f hf hy c)
      (glueingRelationTarget B S hS f hf hy c))

/-- **The quotient is an algebraic space over `S`**, by [Stacks Project, Tag 02WW]. -/
theorem isAlgebraicSpace_glueingSpaceSheaf :
    IsAlgebraicSpace B S hS (glueingSpaceSheaf B S hS f hf hy c).obj :=
  have := isEtaleEquivalenceRelation_glueingRelation B S hS f hf hy c
  isAlgebraicSpace_quotient_unconditional B S hS _ _

/-- The chart-level pushout `P_U` as a chart of the quotient. -/
def glueingSpaceChart :
    yoneda.obj (glueingRelationBase B S hS f hf hy c) ⟶ (glueingSpaceSheaf B S hS f hf hy c).obj :=
  quotientMap B S hS (glueingRelationSource B S hS f hf hy c)
    (glueingRelationTarget B S hS f hf hy c)

/-- **The relation is the kernel pair of the chart of the quotient**, by
[Stacks Project, Tag 02WV]. -/
theorem isPullback_glueingSpaceChart :
    IsPullback (yoneda.map (glueingRelationTarget B S hS f hf hy c))
      (yoneda.map (glueingRelationSource B S hS f hf hy c))
      (glueingSpaceChart B S hS f hf hy c) (glueingSpaceChart B S hS f hf hy c) :=
  have := isEtaleEquivalenceRelation_glueingRelation B S hS f hf hy c
  quotientMap_isPullback B S hS _ _

/-- The chart of the quotient is surjective after every representable base change. -/
theorem surjective_glueingSpaceChart :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingSpaceChart B S hS f hf hy c) :=
  have := isEtaleEquivalenceRelation_glueingRelation B S hS f hf hy c
  quotientMap_surjective_unconditional B S hS _ _

/-- The chart of the quotient is étale after every representable base change. -/
theorem etale_glueingSpaceChart :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingSpaceChart B S hS f hf hy c) :=
  have := isEtaleEquivalenceRelation_glueingRelation B S hS f hf hy c
  quotientMap_etale_unconditional B S hS _ _

/-! #### The factorization `X ⟶ X' ⟶ Y` -/

/-- The chart of `X` obtained by base change of the chart of `Y` along `f`. -/
abbrev glueingSourceChart : yoneda.obj (glueingChartSource B S hS f hf c.u) ⟶ X.1 :=
  (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst c.u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The base change of the kernel pair is the kernel pair of the base-changed chart.**
`X ×_Y R` is the fibre product of two copies of `X ×_Y U` over `X`. -/
theorem isPullback_glueingSourceChart :
    IsPullback (yoneda.map (glueingChartSourceMap B S hS f hf c.s c.s_chart))
      (yoneda.map (glueingChartSourceMap B S hS f hf c.t c.t_chart))
      (glueingSourceChart B S hS f hf c) (glueingSourceChart B S hS f hf c) := by
  refine isPullback_kernel_pair_of_isPullback
    (isPullback_yoneda_glueingChartSourceMap B S hS f hf c.t c.t_chart)
    (isPullback_yoneda_glueingChartSourceMap B S hS f hf c.s c.s_chart)
    (glueingChartSource_isPullback B S hS f hf c.u) c.isPullback.flip ?_
  rw [glueingChartSourceMap_comp_fst, glueingChartSourceMap_comp_fst]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The base-changed chart is surjective after every representable base change. -/
theorem surjective_glueingSourceChart :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingSourceChart B S hS f hf c) :=
  presheaf_inverseImage_of_isPullback B S hS _ (glueingChartSource_isPullback B S hS f hf c.u).flip
    c.surjective_u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The base-changed chart is étale after every representable base change. -/
theorem etale_glueingSourceChart :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingSourceChart B S hS f hf c) :=
  presheaf_inverseImage_of_isPullback B S hS _ (glueingChartSource_isPullback B S hS f hf c.u).flip
    c.etale_u

/-- The structure morphism of `P_U` to `Y`, which the relation leaves invariant. -/
abbrev glueingBaseInvariant :
    yoneda.obj (glueingRelationBase B S hS f hf hy c) ⟶ Y.1 :=
  yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) ≫ c.u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The structure morphism `P_U ⟶ Y` equalizes the two legs of the relation. -/
theorem glueingBaseInvariant_invariant :
    yoneda.map (glueingRelationTarget B S hS f hf hy c) ≫
        glueingBaseInvariant B S hS f hf hy c =
      yoneda.map (glueingRelationSource B S hS f hf hy c) ≫
        glueingBaseInvariant B S hS f hf hy c := by
  exact map_comp_eq_map_comp_of_squares yoneda
    (glueingChartSitePushoutMap_comp_toBase B S hS f hf hy c.t c.t_chart).symm
    (glueingChartSitePushoutMap_comp_toBase B S hS f hf hy c.s c.s_chart).symm c.isPullback.w

/-- **The morphism `X' ⟶ Y` of [Stacks Project, Tag 0EDM].**  The structure morphism of `P_U`
to `Y` is invariant under the relation, so it descends to the quotient. -/
def glueingSpaceToBase : (glueingSpaceSheaf B S hS f hf hy c).obj ⟶ Y.1 :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS
    (glueingSpaceSheaf B S hS f hf hy c).property (glueingSpaceChart B S hS f hf hy c)
    (isPullback_glueingSpaceChart B S hS f hf hy c)
    (surjective_glueingSpaceChart B S hS f hf hy c)
    (etale_glueingSpaceChart B S hS f hf hy c) Y.property.isSheaf
    (glueingBaseInvariant B S hS f hf hy c)
    (glueingBaseInvariant_invariant B S hS f hf hy c)).choose

/-- The chart `P_U ⟶ X'` followed by `X' ⟶ Y` is the structure morphism `P_U ⟶ Y`. -/
theorem glueingSpaceChart_comp_toBase :
    glueingSpaceChart B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c =
      glueingBaseInvariant B S hS f hf hy c :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS
    (glueingSpaceSheaf B S hS f hf hy c).property (glueingSpaceChart B S hS f hf hy c)
    (isPullback_glueingSpaceChart B S hS f hf hy c)
    (surjective_glueingSpaceChart B S hS f hf hy c)
    (etale_glueingSpaceChart B S hS f hf hy c) Y.property.isSheaf
    (glueingBaseInvariant B S hS f hf hy c)
    (glueingBaseInvariant_invariant B S hS f hf hy c)).choose_spec.1

/-- The composite `X ×_Y U ⟶ P_U ⟶ X'`, which the relation on `X ×_Y U` leaves invariant. -/
abbrev glueingSourceInvariant :
    yoneda.obj (glueingChartSource B S hS f hf c.u) ⟶ (glueingSpaceSheaf B S hS f hf hy c).obj :=
  yoneda.map (glueingChartSiteInl B S hS f hf hy c.u) ≫ glueingSpaceChart B S hS f hf hy c

/-- The composite `X ×_Y U ⟶ P_U ⟶ X'` equalizes the two projections `X ×_Y R ⇉ X ×_Y U`. -/
theorem glueingSourceInvariant_invariant :
    yoneda.map (glueingChartSourceMap B S hS f hf c.s c.s_chart) ≫
        glueingSourceInvariant B S hS f hf hy c =
      yoneda.map (glueingChartSourceMap B S hS f hf c.t c.t_chart) ≫
        glueingSourceInvariant B S hS f hf hy c := by
  exact map_comp_eq_map_comp_of_squares yoneda
    (glueingChartSiteInl_naturality B S hS f hf hy c.s c.s_chart)
    (glueingChartSiteInl_naturality B S hS f hf hy c.t c.t_chart)
    (isPullback_glueingSpaceChart B S hS f hf hy c).w.symm

/-- **The morphism `X ⟶ X'` of [Stacks Project, Tag 0EDM].**  The composite
`X ×_Y U ⟶ P_U ⟶ X'` is invariant under the relation on the chart `X ×_Y U` of `X`, so it
descends to `X`. -/
def glueingSpaceFromSource : X.1 ⟶ (glueingSpaceSheaf B S hS f hf hy c).obj :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS X.property.isSheaf
    (glueingSourceChart B S hS f hf c) (isPullback_glueingSourceChart B S hS f hf c)
    (surjective_glueingSourceChart B S hS f hf c) (etale_glueingSourceChart B S hS f hf c)
    (glueingSpaceSheaf B S hS f hf hy c).property (glueingSourceInvariant B S hS f hf hy c)
    (glueingSourceInvariant_invariant B S hS f hf hy c)).choose

/-- The chart `X ×_Y U ⟶ X` followed by `X ⟶ X'` is the composite `X ×_Y U ⟶ P_U ⟶ X'`. -/
theorem glueingSourceChart_comp_fromSource :
    glueingSourceChart B S hS f hf c ≫ glueingSpaceFromSource B S hS f hf hy c =
      glueingSourceInvariant B S hS f hf hy c :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS X.property.isSheaf
    (glueingSourceChart B S hS f hf c) (isPullback_glueingSourceChart B S hS f hf c)
    (surjective_glueingSourceChart B S hS f hf c) (etale_glueingSourceChart B S hS f hf c)
    (glueingSpaceSheaf B S hS f hf hy c).property (glueingSourceInvariant B S hS f hf hy c)
    (glueingSourceInvariant_invariant B S hS f hf hy c)).choose_spec.1

/-- **The factorization of `f`.**  The two descended morphisms compose to `f`. -/
theorem glueingSpaceFromSource_comp_toBase :
    glueingSpaceFromSource B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c = f.hom := by
  obtain ⟨d, -, huniq⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS X.property.isSheaf
    (glueingSourceChart B S hS f hf c) (isPullback_glueingSourceChart B S hS f hf c)
    (surjective_glueingSourceChart B S hS f hf c) (etale_glueingSourceChart B S hS f hf c)
    Y.property.isSheaf (glueingSourceChart B S hS f hf c ≫ f.hom)
    (by
      rw [← Category.assoc, ← Category.assoc, glueingChartSourceMap_comp_fst,
        glueingChartSourceMap_comp_fst])
  refine (huniq _ ?_).trans (huniq f.hom rfl).symm
  change glueingSourceChart B S hS f hf c ≫
      (glueingSpaceFromSource B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c) =
    glueingSourceChart B S hS f hf c ≫ f.hom
  rw [← Category.assoc, glueingSourceChart_comp_fromSource, Category.assoc,
    glueingSpaceChart_comp_toBase]
  change yoneda.map (glueingChartSiteInl B S hS f hf hy c.u) ≫
      (yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) ≫ c.u) =
    glueingSourceChart B S hS f hf c ≫ f.hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, glueingChartSiteInl_comp_toBase]
  exact (glueingChartSource_isPullback B S hS f hf c.u).w.symm

/-! #### Clause (1): `X' ⟶ Y` is integral -/

/-- The chart of the quotient is surjective as a morphism of algebraic spaces. -/
theorem isSurjective_glueingSpaceChart :
    IsSurjective B S hS (glueingSpaceChart B S hS f hf hy c) :=
  (presheafSurjective_iff_isSurjective_yoneda B S hS _
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) _ _).1
    (surjective_glueingSpaceChart B S hS f hf hy c)

/-- The chart of the quotient is étale as a morphism of algebraic spaces. -/
theorem isEtale_glueingSpaceChart :
    IsEtale B S hS (glueingSpaceChart B S hS f hf hy c) :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).2 (etale_glueingSpaceChart B S hS f hf hy c)

/-- **`P_R` is the fibre product of `P_U` and `U` over `Y`.**  Pasting the cartesian square of
the source leg of the relation with the cartesian square presenting `R` as `U ×_Y U`. -/
theorem isPullback_glueingRelationObj_over_base :
    IsPullback (yoneda.map (glueingRelationTarget B S hS f hf hy c) ≫
        yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u))
      (yoneda.map (glueingRelationSource B S hS f hf hy c)) c.u
      (glueingSpaceChart B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c) := by
  have hbase : glueingSpaceChart B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c =
      yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) ≫ c.u :=
    glueingSpaceChart_comp_toBase B S hS f hf hy c
  have h1 : glueingRelationTarget B S hS f hf hy c ≫
      glueingChartSiteToBase B S hS f hf hy c.u =
      glueingChartSiteToBase B S hS f hf hy c.chartR ≫ c.t :=
    glueingChartSitePushoutMap_comp_toBase B S hS f hf hy c.t c.t_chart
  have hTt : yoneda.map (glueingChartSiteToBase B S hS f hf hy c.chartR) ≫ yoneda.map c.t =
      yoneda.map (glueingRelationTarget B S hS f hf hy c) ≫
        yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg yoneda.map h1.symm
  have hpaste := (IsPullback.paste_vert
    ((isPullback_glueingRelationSource B S hS f hf hy c).map yoneda) c.isPullback.flip).flip
  rwa [hTt, ← hbase] at hpaste

/-- **The chart-level pushout is the base change of `X'` along the chart of `Y`.**  This is
[Stacks Project, Tag 07VZ] applied to the chart `P_U ⟶ X'`: the left cartesian square is the
kernel pair of that chart, and the outer rectangle is
`AlgebraicGeometry.Space.isPullback_glueingRelationObj_over_base`. -/
theorem isPullback_glueingSpaceChart_toBase :
    IsPullback (glueingSpaceChart B S hS f hf hy c)
      (yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u))
      (glueingSpaceToBase B S hS f hf hy c) c.u :=
  (isPullback_right_of_isPullback_of_surjective_etale B S hS
    (isAlgebraicSpace_yoneda B S hS (glueingRelationObj B S hS f hf hy c))
    (isAlgebraicSpace_yoneda B S hS (glueingRelationBase B S hS f hf hy c))
    (isAlgebraicSpace_yoneda B S hS (glueingRelationBase B S hS f hf hy c))
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c)
    (isAlgebraicSpace_yoneda B S hS c.U) Y.property
    (glueingSpaceChart_comp_toBase B S hS f hf hy c).symm
    (isPullback_glueingSpaceChart B S hS f hf hy c)
    (isPullback_glueingRelationObj_over_base B S hS f hf hy c)
    (isSurjective_glueingSpaceChart B S hS f hf hy c)
    (isEtale_glueingSpaceChart B S hS f hf hy c)).flip

/-- The base change of `X' ⟶ Y` along the chart of `Y` is integral: it is the structure morphism
of the chart-level pushout, which is integral by the local form of clause (1). -/
theorem presheaf_isIntegralHom_pullback_snd_glueingSpaceToBase :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd (glueingSpaceToBase B S hS f hf hy c) c.u) :=
  presheaf_pullback_snd_of_isPullback
    (isPullback_glueingSpaceChart_toBase B S hS f hf hy c)
    (isIntegralHom_glueingChartPushoutToBase B S hS f hf hy c.u)

/-- **Clause (1) of [Stacks Project, Tag 0EDM].**  The morphism `X' ⟶ Y` is integral.

Integrality descends along the surjective étale chart `U ⟶ Y`
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom`, Stacks 03I2 at
the class of integral morphisms), and over the chart the morphism is the structure morphism of
the pushout, integral by `AlgebraicGeometry.isIntegralHom_glueingToBase`. -/
theorem isIntegralHom_glueingSpaceToBase :
    IsIntegralHom B S hS (glueingSpaceToBase B S hS f hf hy c) := by
  have := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have hpre := presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom B S hS)
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c).isSheaf Y.property.isSheaf
    c.surjective_u c.etale_u
    (presheaf_isIntegralHom_pullback_snd_glueingSpaceToBase B S hS f hf hy c)
  rw [isIntegralHom_iff_representable B S hS _
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) Y.property]
  exact ⟨hpre.rep, hpre⟩

/-! #### The final assertion: `X' ⟶ Y` is finite -/

/-- The base change of `X' ⟶ Y` along the chart of `Y` is finite when `f` is finite and the
chart is locally Noetherian. -/
theorem presheaf_isFinite_pullback_snd_glueingSpaceToBase (hfin : IsFinite B S hS f.hom)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj c.U)] :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd (glueingSpaceToBase B S hS f hf hy c) c.u) :=
  presheaf_pullback_snd_of_isPullback
    (isPullback_glueingSpaceChart_toBase B S hS f hf hy c)
    (isFinite_glueingChartPushoutToBase B S hS f hf hy c.u hfin)

/-- **The final assertion of [Stacks Project, Tag 0EDM].**  If `f` is finite and the chart of
`Y` is locally Noetherian, then `X' ⟶ Y` is finite.

Finiteness descends along the surjective étale chart
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom`,
Stacks 03I2 at the class of finite morphisms), and over the chart the morphism is finite by
`AlgebraicGeometry.isFinite_glueingToBase`, which is clause (1) together with Tag 0E27. -/
theorem isFinite_glueingSpaceToBase (hfin : IsFinite B S hS f.hom)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj c.U)] :
    IsFinite B S hS (glueingSpaceToBase B S hS f hf hy c) := by
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hpre := presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom
      (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS))
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c).isSheaf Y.property.isSheaf
    c.surjective_u c.etale_u
    (presheaf_isFinite_pullback_snd_glueingSpaceToBase B S hS f hf hy c hfin)
  rw [isFinite_iff_representable B S hS _
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) Y.property]
  exact ⟨hpre.rep, hpre⟩

/-! #### Clause (3), first half: the distinguished closed immersion `Spec k ⟶ X'` -/

/-- The chart of `Spec k` obtained by base change of the chart of `Y` along `y`. -/
abbrev glueingFibreChart : yoneda.obj (glueingChartFibre B S hS hy c.u) ⟶ yoneda.obj Ky :=
  hy.rep.fst c.u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The base change of the kernel pair is the kernel pair of the base-changed chart**, for the
closed immersion `y` in place of `f`. -/
theorem isPullback_glueingFibreChart :
    IsPullback (yoneda.map (glueingChartFibreMap B S hS hy c.s c.s_chart))
      (yoneda.map (glueingChartFibreMap B S hS hy c.t c.t_chart))
      (glueingFibreChart B S hS hy c) (glueingFibreChart B S hS hy c) := by
  refine isPullback_kernel_pair_of_isPullback
    (isPullback_yoneda_glueingChartFibreMap B S hS hy c.t c.t_chart)
    (isPullback_yoneda_glueingChartFibreMap B S hS hy c.s c.s_chart)
    (glueingChartFibre_isPullback B S hS hy c.u) c.isPullback.flip ?_
  rw [glueingChartFibreMap_comp_fst, glueingChartFibreMap_comp_fst]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The base-changed chart of `Spec k` is surjective after every representable base change. -/
theorem surjective_glueingFibreChart :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingFibreChart B S hS hy c) :=
  presheaf_inverseImage_of_isPullback B S hS _ (glueingChartFibre_isPullback B S hS hy c.u).flip
    c.surjective_u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The base-changed chart of `Spec k` is étale after every representable base change. -/
theorem etale_glueingFibreChart :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingFibreChart B S hS hy c) :=
  presheaf_inverseImage_of_isPullback B S hS _ (glueingChartFibre_isPullback B S hS hy c.u).flip
    c.etale_u

/-- The composite `Spec k ×_Y U ⟶ P_U ⟶ X'`, which the relation on `Spec k ×_Y U` leaves
invariant. -/
abbrev glueingFibreInvariant :
    yoneda.obj (glueingChartFibre B S hS hy c.u) ⟶ (glueingSpaceSheaf B S hS f hf hy c).obj :=
  yoneda.map (glueingChartSiteInr B S hS f hf hy c.u) ≫ glueingSpaceChart B S hS f hf hy c

/-- The composite `Spec k ×_Y U ⟶ P_U ⟶ X'` equalizes the two projections
`Spec k ×_Y R ⇉ Spec k ×_Y U`. -/
theorem glueingFibreInvariant_invariant :
    yoneda.map (glueingChartFibreMap B S hS hy c.s c.s_chart) ≫
        glueingFibreInvariant B S hS f hf hy c =
      yoneda.map (glueingChartFibreMap B S hS hy c.t c.t_chart) ≫
        glueingFibreInvariant B S hS f hf hy c := by
  exact map_comp_eq_map_comp_of_squares yoneda
    (glueingChartSiteInr_naturality B S hS f hf hy c.s c.s_chart)
    (glueingChartSiteInr_naturality B S hS f hf hy c.t c.t_chart)
    (isPullback_glueingSpaceChart B S hS f hf hy c).w.symm

/-- **The distinguished point `x' : Spec k ⟶ X'` of [Stacks Project, Tag 0EDM].**  The composite
`Spec k ×_Y U ⟶ P_U ⟶ X'` is invariant under the relation on the chart `Spec k ×_Y U` of
`Spec k`, so it descends. -/
def glueingSpacePoint : yoneda.obj Ky ⟶ (glueingSpaceSheaf B S hS f hf hy c).obj :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_yoneda B S hS Ky).isSheaf (glueingFibreChart B S hS hy c)
    (isPullback_glueingFibreChart B S hS hy c) (surjective_glueingFibreChart B S hS hy c)
    (etale_glueingFibreChart B S hS hy c) (glueingSpaceSheaf B S hS f hf hy c).property
    (glueingFibreInvariant B S hS f hf hy c)
    (glueingFibreInvariant_invariant B S hS f hf hy c)).choose

/-- The chart `Spec k ×_Y U ⟶ Spec k` followed by the distinguished point `Spec k ⟶ X'` is the
composite `Spec k ×_Y U ⟶ P_U ⟶ X'`. -/
theorem glueingFibreChart_comp_point :
    glueingFibreChart B S hS hy c ≫ glueingSpacePoint B S hS f hf hy c =
      glueingFibreInvariant B S hS f hf hy c :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_yoneda B S hS Ky).isSheaf (glueingFibreChart B S hS hy c)
    (isPullback_glueingFibreChart B S hS hy c) (surjective_glueingFibreChart B S hS hy c)
    (etale_glueingFibreChart B S hS hy c) (glueingSpaceSheaf B S hS f hf hy c).property
    (glueingFibreInvariant B S hS f hf hy c)
    (glueingFibreInvariant_invariant B S hS f hf hy c)).choose_spec.1

/-- **The distinguished point lies over `y`.** -/
theorem glueingSpacePoint_comp_toBase :
    glueingSpacePoint B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c = y := by
  obtain ⟨d, -, huniq⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    (isAlgebraicSpace_yoneda B S hS Ky).isSheaf (glueingFibreChart B S hS hy c)
    (isPullback_glueingFibreChart B S hS hy c) (surjective_glueingFibreChart B S hS hy c)
    (etale_glueingFibreChart B S hS hy c) Y.property.isSheaf
    (glueingFibreChart B S hS hy c ≫ y)
    (by
      rw [← Category.assoc, ← Category.assoc, glueingChartFibreMap_comp_fst,
        glueingChartFibreMap_comp_fst])
  refine (huniq _ ?_).trans (huniq y rfl).symm
  change glueingFibreChart B S hS hy c ≫
      (glueingSpacePoint B S hS f hf hy c ≫ glueingSpaceToBase B S hS f hf hy c) =
    glueingFibreChart B S hS hy c ≫ y
  rw [← Category.assoc, glueingFibreChart_comp_point, Category.assoc,
    glueingSpaceChart_comp_toBase]
  change yoneda.map (glueingChartSiteInr B S hS f hf hy c.u) ≫
      (yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) ≫ c.u) =
    glueingFibreChart B S hS hy c ≫ y
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, glueingChartSiteInr_comp_toBase]
  exact (glueingChartFibre_isPullback B S hS hy c.u).w.symm

/-- **The chart-level fibre is the base change of the distinguished point along the chart of
`X'`.**  Pasting the identification `P_U = X' ×_Y U` with the identification
`Spec k ×_Y U = Spec k ×_Y U`. -/
theorem isPullback_glueingSpacePoint :
    IsPullback (yoneda.map (glueingChartSiteInr B S hS f hf hy c.u))
      (glueingFibreChart B S hS hy c) (glueingSpaceChart B S hS f hf hy c)
      (glueingSpacePoint B S hS f hf hy c) := by
  refine IsPullback.of_right ?_ ?_
    (isPullback_glueingSpaceChart_toBase B S hS f hf hy c).flip
  · have hinr : yoneda.map (glueingChartSiteInr B S hS f hf hy c.u) ≫
        yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) =
        yoneda.map (glueingChartFibreHom B S hS hy c.u) := by
      rw [← CategoryTheory.Functor.map_comp, glueingChartSiteInr_comp_toBase]
    rw [hinr, glueingSpacePoint_comp_toBase]
    exact (glueingChartFibre_isPullback B S hS hy c.u).flip
  · exact (glueingFibreChart_comp_point B S hS f hf hy c).symm

/-- **Clause (3) of [Stacks Project, Tag 0EDM], the residue field.**  The distinguished point
`Spec k ⟶ X'` is a closed immersion.

Over the chart it is `AlgebraicGeometry.pushoutInr`, a closed immersion by
[Stacks Project, Tag 0E25], and closed immersions descend effectively along the surjective étale
chart `P_U ⟶ X'`. -/
theorem isClosedImmersion_glueingSpacePoint :
    IsClosedImmersion B S hS (glueingSpacePoint B S hS f hf hy c) := by
  have hres := presheaf_pullback_snd_of_isPullback
    (P := (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}))
    (isPullback_glueingSpacePoint B S hS f hf hy c).flip
    (inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion
      (pushoutInr (glueingChartSituation B S hS f hf hy c.u))))
  exact presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
    (isAlgebraicSpace_yoneda B S hS Ky).isSheaf
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c).isSheaf
    (surjective_glueingSpaceChart B S hS f hf hy c)
    (etale_glueingSpaceChart B S hS f hf hy c) hres

/-- **The chart-level source is the base change of `X` along the chart of `X'`.**  Pasting the
identification `P_U = X' ×_Y U` with the square presenting `X ×_Y U`. -/
theorem isPullback_glueingSourceChart_chart :
    IsPullback (yoneda.map (glueingChartSiteInl B S hS f hf hy c.u))
      (glueingSourceChart B S hS f hf c) (glueingSpaceChart B S hS f hf hy c)
      (glueingSpaceFromSource B S hS f hf hy c) := by
  refine IsPullback.of_right ?_ ?_
    (isPullback_glueingSpaceChart_toBase B S hS f hf hy c).flip
  · have hinl : yoneda.map (glueingChartSiteInl B S hS f hf hy c.u) ≫
        yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) =
        yoneda.map (glueingChartSourceHom B S hS f hf c.u) := by
      rw [← CategoryTheory.Functor.map_comp, glueingChartSiteInl_comp_toBase]
    rw [hinl, glueingSpaceFromSource_comp_toBase]
    exact (glueingChartSource_isPullback B S hS f hf c.u).flip
  · exact (glueingSourceChart_comp_fromSource B S hS f hf hy c).symm

/-! #### Clause (3), second half: the fibre is exactly the distinguished point -/

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- A point of a represented presheaf lies in the image of a morphism of representables exactly
when the corresponding scheme point lies in the image of the morphism of schemes. -/
theorem mem_range_pointsMap_yoneda_iff {W₁ W₂ : BigFppfOver B S hS} (g : W₁ ⟶ W₂)
    (p : points B S hS (yoneda.obj W₂)) :
    p ∈ Set.range (pointsMap B S hS (yoneda.obj W₁) (yoneda.map g)) ↔
      pointsToScheme B S hS W₂ p ∈ Set.range ((BigFppfOver.toScheme B S hS).map g) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨pointsToScheme B S hS W₁ x, (pointsToScheme_pointsMap B S hS g x).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨(schemePointsHomeomorph B S hS W₁).symm z, ?_⟩
    apply (schemePointsHomeomorph B S hS W₂).injective
    rwa [schemePointsHomeomorph_apply, pointsToScheme_pointsMap, ← schemePointsHomeomorph_apply,
      Homeomorph.apply_symm_apply]

/-- **Clause (3) of [Stacks Project, Tag 0EDM], the fibre.**  The fibre of `X' ⟶ Y` over the
point represented by `y` is exactly the image of the distinguished closed immersion
`Spec k ⟶ X'`.

The chart `P_U ⟶ X'` is surjective on points, so the statement may be checked after pulling
back along it; there both sides become subsets of the chart-level pushout, and the equality is
`AlgebraicGeometry.range_glueingPoint`, the scheme-level clause (3). -/
theorem preimage_range_pointsMap_glueingSpaceToBase :
    pointsMap B S hS (glueingSpaceSheaf B S hS f hf hy c).obj
          (glueingSpaceToBase B S hS f hf hy c) ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj Ky) y) =
      Set.range (pointsMap B S hS (yoneda.obj Ky) (glueingSpacePoint B S hS f hf hy c)) := by
  have hR : pointsMap B S hS (yoneda.obj (glueingRelationBase B S hS f hf hy c))
        (glueingSpaceChart B S hS f hf hy c) ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj Ky) (glueingSpacePoint B S hS f hf hy c)) =
      Set.range (pointsMap B S hS (yoneda.obj (glueingChartFibre B S hS hy c.u))
        (yoneda.map (glueingChartSiteInr B S hS f hf hy c.u))) := by
    simpa only [Set.image_univ, Set.preimage_univ] using
      preimage_image_pointsMap_of_isPullback B S hS
        (isPullback_glueingSpacePoint B S hS f hf hy c).flip Set.univ
  have hL : pointsMap B S hS (yoneda.obj c.U) c.u ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj Ky) y) =
      Set.range (pointsMap B S hS (yoneda.obj (glueingChartFibre B S hS hy c.u))
        (yoneda.map (glueingChartFibreHom B S hS hy c.u))) := by
    simpa only [Set.image_univ, Set.preimage_univ] using
      preimage_image_pointsMap_of_isPullback B S hS
        (glueingChartFibre_isPullback B S hS hy c.u) Set.univ
  refine (Set.preimage_eq_preimage (isSurjective_glueingSpaceChart B S hS f hf hy c)).mp ?_
  rw [hR, ← Set.preimage_comp, ← pointsMap_comp, glueingSpaceChart_comp_toBase]
  change pointsMap B S hS (yoneda.obj (glueingRelationBase B S hS f hf hy c))
        (yoneda.map (glueingChartSiteToBase B S hS f hf hy c.u) ≫ c.u) ⁻¹'
      Set.range (pointsMap B S hS (yoneda.obj Ky) y) = _
  rw [pointsMap_comp, Set.preimage_comp, hL]
  let := isIntegralHom_glueingChartSourceHom B S hS f hf c.u
  let := isClosedImmersion_glueingChartFibreHom B S hS hy c.u
  ext π
  rw [Set.mem_preimage, mem_range_pointsMap_yoneda_iff, mem_range_pointsMap_yoneda_iff,
    pointsToScheme_pointsMap]
  exact (Set.ext_iff.mp (range_glueingPoint
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf c.u))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy c.u)))
    (pointsToScheme B S hS (glueingChartSitePushout B S hS f hf hy c.u) π)).symm

/-- **Clause (3) of [Stacks Project, Tag 0EDM], the single point.**  When the source of `y` has
at most one point -- in particular when it is the spectrum of a field, which is the case of the
source -- the fibre of `X' ⟶ Y` over the point represented by `y` has at most one point. -/
theorem subsingleton_fibre_glueingSpaceToBase
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj Ky)] :
    (pointsMap B S hS (glueingSpaceSheaf B S hS f hf hy c).obj
      (glueingSpaceToBase B S hS f hf hy c) ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj Ky) y)).Subsingleton := by
  rw [preimage_range_pointsMap_glueingSpaceToBase]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have hab : a = b :=
    (schemePointsHomeomorph B S hS Ky).injective (Subsingleton.elim _ _)
  rw [hab]

end Relation


end Chart


end AlgebraicGeometry.Space

end
