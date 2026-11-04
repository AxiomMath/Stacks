module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantClosedSubschemeGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Charts of the base changes of an algebraic space over a scheme

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`T₀` be a scheme of the site over `Y`, and let `φ : U ⟶ X_{T₀}` be a surjective étale chart of the
base change `X_{T₀} = X ×_Y T₀` by an object `U` of the site, with structure morphism
`u : U ⟶ T₀`. For every scheme `T'` over `T₀` the fibre product `T' ×_{T₀} U` is a surjective
étale chart of `X_{T'}`, and if `t, s : R ⟶ U` present `U ×_{X_{T₀}} U`, their base changes
present the relation of that chart. This file constructs these charts *with underlying scheme
literally the fibre product of the underlying schemes*, so that the systems they form over an
inverse system of schemes `T'` are, on the nose, the base changed systems of
`AlgebraicGeometry.pullbackDiagram`.

## Main definitions

* `AlgebraicGeometry.Space.stageObj`: the object of the site whose underlying scheme is the
  fibre product `T' ×_{T₀} V` of two morphisms `T' ⟶ T₀` and `V ⟶ T₀` of the site, with its
  projections `AlgebraicGeometry.Space.stageFst` and `AlgebraicGeometry.Space.stageSnd`.
* `AlgebraicGeometry.Space.stageMap` and `AlgebraicGeometry.Space.stageMapRight`: the
  morphisms between such fibre products induced by a morphism of the first, respectively of the
  second, factor.
* `AlgebraicGeometry.Space.fibreProductChart`: the chart `T' ×_{T₀} U ⟶ X_{T'}` of a base change.

## Main results

* `AlgebraicGeometry.Space.isPullback_stage`: the fibre product of the site is a fibre product.
* `AlgebraicGeometry.Space.isPullback_fibreProductChart`: the chart of the base change is the base
  change of the chart, so it is again surjective and étale
  (`AlgebraicGeometry.Space.fibreProductChart_surjective`,
  `AlgebraicGeometry.Space.fibreProductChart_etale`).
* `AlgebraicGeometry.Space.isPullback_stageRelation`: the base changes of a presentation of the
  relation `U ×_{X_{T₀}} U` present the relation of the base changed chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

section Stage

variable {T' T₀ V : BigFppfOver B S hS} (t : T' ⟶ T₀) (v : V ⟶ T₀)

/-- The object of the site whose underlying scheme is the fibre product of the underlying
schemes of `t : T' ⟶ T₀` and `v : V ⟶ T₀`, over `S` through `T'`. -/
def stageObj : BigFppfOver B S hS :=
  siteObject B S hS
    (Scheme.size_pullback_lt ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map v) T'.left.property V.left.property)
    (pullback.fst ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map v) ≫
      T'.hom.hom)

/-- The underlying scheme of `stageObj` is the fibre product of the underlying schemes. -/
@[simp]
theorem toScheme_obj_stageObj :
    (BigFppfOver.toScheme B S hS).obj (stageObj B S hS t v) =
      pullback ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map v) :=
  rfl

/-- The first projection `T' ×_{T₀} V ⟶ T'`. -/
def stageFst : stageObj B S hS t v ⟶ T' :=
  Over.homMk (ObjectProperty.homMk (pullback.fst _ _)) rfl

/-- The second projection `T' ×_{T₀} V ⟶ V`. -/
def stageSnd : stageObj B S hS t v ⟶ V :=
  Over.homMk (ObjectProperty.homMk (pullback.snd _ _)) (by
    apply ObjectProperty.hom_ext
    change pullback.snd ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map v) ≫ V.hom.hom =
      pullback.fst ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map v) ≫ T'.hom.hom
    have ht : (BigFppfOver.toScheme B S hS).map t ≫ T₀.hom.hom = T'.hom.hom :=
      congrArg (fun k => k.hom) (Over.w t)
    have hv : (BigFppfOver.toScheme B S hS).map v ≫ T₀.hom.hom = V.hom.hom :=
      congrArg (fun k => k.hom) (Over.w v)
    rw [← ht, ← hv, ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The underlying morphism of `stageFst` is the first projection of the fibre product. -/
@[simp]
theorem toScheme_map_stageFst :
    (BigFppfOver.toScheme B S hS).map (stageFst B S hS t v) = pullback.fst _ _ := rfl

/-- The underlying morphism of `stageSnd` is the second projection of the fibre product. -/
@[simp]
theorem toScheme_map_stageSnd :
    (BigFppfOver.toScheme B S hS).map (stageSnd B S hS t v) = pullback.snd _ _ := rfl

/-- The square formed by `stageFst`, `stageSnd`, `t` and `v` commutes. -/
theorem stage_condition : stageFst B S hS t v ≫ t = stageSnd B S hS t v ≫ v := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  simp only [Functor.map_comp, toScheme_map_stageFst, toScheme_map_stageSnd]
  exact pullback.condition

/-- **The fibre product of the site is a fibre product.** -/
theorem isPullback_stage : IsPullback (stageFst B S hS t v) (stageSnd B S hS t v) t v := by
  have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact IsPullback.of_map (BigFppfOver.toScheme B S hS) (stage_condition B S hS t v)
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map v))

/-- The fibre product of the site, read in presheaves through Yoneda. -/
theorem isPullback_yoneda_stage :
    IsPullback (yoneda.map (stageFst B S hS t v)) (yoneda.map (stageSnd B S hS t v))
      (yoneda.map t) (yoneda.map v) :=
  (isPullback_stage B S hS t v).map yoneda

variable {T'' : BigFppfOver B S hS} {t' : T'' ⟶ T₀} (h : T'' ⟶ T') (ht : h ≫ t = t')

include ht in
/-- The morphisms `T'' ×_{T₀} V ⟶ T'` and `T'' ×_{T₀} V ⟶ V` given by the first projection
followed by `h` and by the second projection agree after composing to `T₀`. -/
theorem stageMap_condition :
    (pullback.fst ((BigFppfOver.toScheme B S hS).map t') ((BigFppfOver.toScheme B S hS).map v) ≫
        (BigFppfOver.toScheme B S hS).map h) ≫ (BigFppfOver.toScheme B S hS).map t =
      pullback.snd ((BigFppfOver.toScheme B S hS).map t')
        ((BigFppfOver.toScheme B S hS).map v) ≫ (BigFppfOver.toScheme B S hS).map v := by
  rw [Category.assoc, ← Functor.map_comp, ht]
  exact pullback.condition

/-- The morphism `T'' ×_{T₀} V ⟶ T' ×_{T₀} V` induced by a morphism `h : T'' ⟶ T'` over `T₀`. -/
def stageMap : stageObj B S hS t' v ⟶ stageObj B S hS t v :=
  Over.homMk (ObjectProperty.homMk (pullback.lift
    (pullback.fst _ _ ≫ (BigFppfOver.toScheme B S hS).map h) (pullback.snd _ _)
    (stageMap_condition B S hS t v h ht))) (by
      apply ObjectProperty.hom_ext
      change pullback.lift _ _ (stageMap_condition B S hS t v h ht) ≫
          pullback.fst ((BigFppfOver.toScheme B S hS).map t)
            ((BigFppfOver.toScheme B S hS).map v) ≫ T'.hom.hom =
        pullback.fst ((BigFppfOver.toScheme B S hS).map t')
          ((BigFppfOver.toScheme B S hS).map v) ≫ T''.hom.hom
      rw [pullback.lift_fst_assoc, Category.assoc]
      congr 1
      exact congrArg (fun k => k.hom) (Over.w h))

/-- The underlying morphism of `stageMap` is the morphism of fibre products induced by `h`. -/
@[simp]
theorem toScheme_map_stageMap :
    (BigFppfOver.toScheme B S hS).map (stageMap B S hS t v h ht) =
      pullback.lift (pullback.fst _ _ ≫ (BigFppfOver.toScheme B S hS).map h) (pullback.snd _ _)
        (stageMap_condition B S hS t v h ht) := rfl

/-- `stageMap` followed by the first projection is the first projection followed by `h`. -/
@[reassoc (attr := simp)]
theorem stageMap_fst :
    stageMap B S hS t v h ht ≫ stageFst B S hS t v = stageFst B S hS t' v ≫ h := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_stageMap, toScheme_map_stageFst,
    toScheme_map_stageFst]
  exact pullback.lift_fst _ _ _

/-- `stageMap` commutes with the second projections to `V`. -/
@[reassoc (attr := simp)]
theorem stageMap_snd :
    stageMap B S hS t v h ht ≫ stageSnd B S hS t v = stageSnd B S hS t' v := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_stageMap, toScheme_map_stageSnd, toScheme_map_stageSnd]
  exact pullback.lift_snd _ _ _

end Stage

section StageRight

variable {T' T₀ V W : BigFppfOver B S hS} (t : T' ⟶ T₀) (v : V ⟶ T₀) {w : W ⟶ T₀} (k : W ⟶ V)
  (hk : k ≫ v = w)

include hk in
/-- The morphisms `T' ×_{T₀} W ⟶ T'` and `T' ×_{T₀} W ⟶ V` given by the first projection and
by the second projection followed by `k` agree after composing to `T₀`. -/
theorem stageMapRight_condition :
    pullback.fst ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map w) ≫
        (BigFppfOver.toScheme B S hS).map t =
      (pullback.snd ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map w) ≫
        (BigFppfOver.toScheme B S hS).map k) ≫ (BigFppfOver.toScheme B S hS).map v := by
  rw [Category.assoc, ← Functor.map_comp, hk]
  exact pullback.condition

/-- The morphism `T' ×_{T₀} W ⟶ T' ×_{T₀} V` induced by a morphism `k : W ⟶ V` over `T₀`. -/
def stageMapRight : stageObj B S hS t w ⟶ stageObj B S hS t v :=
  Over.homMk (ObjectProperty.homMk (pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (BigFppfOver.toScheme B S hS).map k)
    (stageMapRight_condition B S hS t v k hk))) (by
      apply ObjectProperty.hom_ext
      change pullback.lift _ _ (stageMapRight_condition B S hS t v k hk) ≫
          pullback.fst ((BigFppfOver.toScheme B S hS).map t)
            ((BigFppfOver.toScheme B S hS).map v) ≫ T'.hom.hom =
        pullback.fst ((BigFppfOver.toScheme B S hS).map t)
          ((BigFppfOver.toScheme B S hS).map w) ≫ T'.hom.hom
      rw [pullback.lift_fst_assoc])

/-- The underlying morphism of `stageMapRight` is the morphism of fibre products induced by
`k`. -/
@[simp]
theorem toScheme_map_stageMapRight :
    (BigFppfOver.toScheme B S hS).map (stageMapRight B S hS t v k hk) =
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (BigFppfOver.toScheme B S hS).map k)
        (stageMapRight_condition B S hS t v k hk) := rfl

/-- `stageMapRight` commutes with the first projections to `T'`. -/
@[reassoc (attr := simp)]
theorem stageMapRight_fst :
    stageMapRight B S hS t v k hk ≫ stageFst B S hS t v = stageFst B S hS t w := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_stageMapRight, toScheme_map_stageFst, toScheme_map_stageFst]
  exact pullback.lift_fst _ _ _

/-- `stageMapRight` followed by the second projection is the second projection followed by
`k`. -/
@[reassoc (attr := simp)]
theorem stageMapRight_snd :
    stageMapRight B S hS t v k hk ≫ stageSnd B S hS t v = stageSnd B S hS t w ≫ k := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_stageMapRight, toScheme_map_stageSnd,
    toScheme_map_stageSnd]
  exact pullback.lift_snd _ _ _

/-- The base change of a morphism over `T₀` along the first projection is a fibre product. -/
theorem isPullback_stageMapRight :
    IsPullback (stageSnd B S hS t w) (stageMapRight B S hS t v k hk) k (stageSnd B S hS t v) := by
  refine IsPullback.of_bot ?_ (stageMapRight_snd B S hS t v k hk).symm
    (isPullback_stage B S hS t v).flip
  rw [stageMapRight_fst, hk]
  exact (isPullback_stage B S hS t w).flip

end StageRight

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T₀ : SchemesOverPresheaf B S hS Y}
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ schemeBaseChange f T₀) (u : U ⟶ T₀.left)
    (hu : yoneda.map u = φ ≫ pullback.snd f.hom T₀.hom)
    {T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T₀)

include hu in
/-- The morphism `T' ×_{T₀} U ⟶ X` given by the second projection, `φ` and the projection to
`X`, and the first projection `T' ×_{T₀} U ⟶ T'`, agree after composing to `Y`. -/
theorem fibreProductChart_condition :
    (yoneda.map (stageSnd B S hS g.left u) ≫ φ ≫ pullback.fst f.hom T₀.hom) ≫ f.hom =
      yoneda.map (stageFst B S hS g.left u) ≫ T'.hom := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc φ, ← hu,
    ← Category.assoc, ← Functor.map_comp, ← stage_condition, Functor.map_comp, Category.assoc,
    CostructuredArrow.w g]

/-- **The chart of a base change.** The morphism `T' ×_{T₀} U ⟶ X_{T'}` induced by the chart
`φ : U ⟶ X_{T₀}` and a morphism `g : T' ⟶ T₀` of schemes over `Y`. -/
def fibreProductChart : yoneda.obj (stageObj B S hS g.left u) ⟶ schemeBaseChange f T' :=
  pullback.lift (yoneda.map (stageSnd B S hS g.left u) ≫ φ ≫ pullback.fst f.hom T₀.hom)
    (yoneda.map (stageFst B S hS g.left u)) (fibreProductChart_condition B S hS f φ u hu g)

/-- `fibreProductChart` followed by the projection to `X` is the second projection followed by
`φ` and the projection to `X`. -/
@[reassoc (attr := simp)]
theorem fibreProductChart_fst :
    fibreProductChart B S hS f φ u hu g ≫ pullback.fst f.hom T'.hom =
      yoneda.map (stageSnd B S hS g.left u) ≫ φ ≫ pullback.fst f.hom T₀.hom :=
  pullback.lift_fst _ _ _

/-- `fibreProductChart` followed by the projection to `T'` is the first projection. -/
@[reassoc (attr := simp)]
theorem fibreProductChart_snd :
    fibreProductChart B S hS f φ u hu g ≫ pullback.snd f.hom T'.hom =
      yoneda.map (stageFst B S hS g.left u) :=
  pullback.lift_snd _ _ _

/-- The chart of a base change is compatible with the chart at `T₀`. -/
@[reassoc]
theorem fibreProductChart_comp_schemeBaseChangeMap :
    fibreProductChart B S hS f φ u hu g ≫ schemeBaseChangeMap f g =
      yoneda.map (stageSnd B S hS g.left u) ≫ φ := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, schemeBaseChangeMap_snd, fibreProductChart_snd_assoc, Category.assoc, ← hu,
      ← Functor.map_comp, ← Functor.map_comp, stage_condition]

/-- **The chart of a base change is the base change of the chart.** -/
theorem isPullback_fibreProductChart :
    IsPullback (yoneda.map (stageSnd B S hS g.left u)) (fibreProductChart B S hS f φ u hu g) φ
      (schemeBaseChangeMap f g) := by
  refine IsPullback.of_bot ?_ (fibreProductChart_comp_schemeBaseChangeMap B S hS f φ u hu g).symm
    (isPullback_schemeBaseChangeMap f g)
  rw [fibreProductChart_snd, ← hu]
  exact (isPullback_yoneda_stage B S hS g.left u).flip

/-- The charts of two base changes are compatible with the morphism between the base changes
induced by a morphism `h : T'' ⟶ T'` of schemes over `T₀`. -/
@[reassoc]
theorem stageMap_fibreProductChart {T'' : SchemesOverPresheaf B S hS Y} {g' : T'' ⟶ T₀}
    (h : T'' ⟶ T')
    (hg : h ≫ g = g') :
    yoneda.map (stageMap B S hS g.left u h.left (by rw [← hg]; rfl)) ≫
        fibreProductChart B S hS f φ u hu g =
      fibreProductChart B S hS f φ u hu g' ≫ schemeBaseChangeMap f h := by
  subst hg
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreProductChart_fst, schemeBaseChangeMap_fst]
    rw [← Functor.map_comp_assoc, stageMap_snd]
  · simp only [Category.assoc, fibreProductChart_snd, schemeBaseChangeMap_snd,
      fibreProductChart_snd_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, stageMap_fst]

variable {φ}

/-- A relative property of morphisms of presheaves holds for the chart of a base change as soon as
it holds for the chart `φ`. -/
private theorem fibreProductChart_presheaf (P : MorphismProperty Scheme.{u})
    (hP : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) φ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)))
      (fibreProductChart B S hS f φ u hu g) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _
  exact MorphismProperty.of_isPullback (isPullback_fibreProductChart B S hS f φ u hu g) hP

/-- The chart of a base change is surjective after every representable base change. -/
theorem fibreProductChart_surjective
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (fibreProductChart B S hS f φ u hu g) :=
  fibreProductChart_presheaf B S hS f u hu g _ hs

/-- The chart of a base change is étale after every representable base change. -/
theorem fibreProductChart_etale
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (fibreProductChart B S hS f φ u hu g) :=
  fibreProductChart_presheaf B S hS f u hu g _ he

variable (φ) {R : BigFppfOver B S hS} (rt rs : R ⟶ U)
    (hR : IsPullback (yoneda.map rt) (yoneda.map rs) φ φ)

include hR hu in
/-- The two legs of a presentation of the relation of the chart have the same composite to
`T₀`. -/
theorem relation_comp_eq : rt ≫ u = rs ≫ u := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, hu, ← Category.assoc, ← Category.assoc, hR.w]

/-- **The relation of the base changed chart is the base change of the relation.** If `rt, rs`
present `U ×_{X_{T₀}} U`, their base changes present `(T' ×_{T₀} U) ×_{X_{T'}} (T' ×_{T₀} U)`. -/
theorem isPullback_stageRelation :
    IsPullback (yoneda.map (stageMapRight B S hS g.left u rt
        (relation_comp_eq B S hS f φ u hu rt rs hR)))
      (yoneda.map (stageMapRight B S hS g.left u rs rfl))
      (fibreProductChart B S hS f φ u hu g) (fibreProductChart B S hS f φ u hu g) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_fibreProductChart B S hS f φ u hu g)
  · rw [← Functor.map_comp, stageMapRight_snd, Functor.map_comp,
      fibreProductChart_comp_schemeBaseChangeMap]
    exact ((isPullback_stageMapRight B S hS g.left u rs rfl).map yoneda).paste_horiz hR
  · apply pullback.hom_ext
    · simp only [Category.assoc, fibreProductChart_fst]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, stageMapRight_snd,
        stageMapRight_snd, Functor.map_comp_assoc, Functor.map_comp_assoc, reassoc_of% hR.w]
    · simp only [Category.assoc, fibreProductChart_snd, ← Functor.map_comp, stageMapRight_fst]

end Chart

/-- The legs of the relations of the base changed charts are compatible with the morphisms
between the base changes induced by a morphism `h : T'' ⟶ T'` over `T₀`. -/
theorem stageMap_comp_stageMapRight {T'' T₀' T₁ V W : BigFppfOver B S hS} {t : T₁ ⟶ T₀'}
    {t' : T'' ⟶ T₀'} (h : T'' ⟶ T₁) (ht : h ≫ t = t') {v : V ⟶ T₀'} {w : W ⟶ T₀'} (k : W ⟶ V)
    (hk : k ≫ v = w) :
    stageMap B S hS t w h ht ≫ stageMapRight B S hS t v k hk =
      stageMapRight B S hS t' v k hk ≫ stageMap B S hS t v h ht := by
  apply (isPullback_stage B S hS t v).hom_ext
  · simp only [Category.assoc, stageMapRight_fst, stageMap_fst, stageMapRight_fst_assoc]
  · simp only [Category.assoc, stageMapRight_snd, stageMap_snd, stageMap_snd_assoc]

end AlgebraicGeometry.Space

end
