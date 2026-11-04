module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.BaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.Schemes

/-!
# Functoriality of the glueing construction of Stacks 0EDM in the chart

Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S` and let
`y : Spec k ⟶ Y` be a closed immersion representing a point of `|Y|`.  Over an object `V` of
the big fppf site mapping to `Y` the pushout `AlgebraicGeometry.Space.glueingChartPushout` is
a scheme `P_V` over `V`.

This file makes `V ↦ (P_V, P_V ⟶ V)` *functorial* in the chart: a morphism `a : V ⟶ V'` over `Y`
induces `P_V ⟶ P_{V'}` over `a`, compatibly with identities and composition; and when `a` is
étale and separated, the resulting square

```
P_V -----> P_{V'}
 |           |
 v           v
 V ---a---> V'
```

is cartesian and `P_V ⟶ P_{V'}` is étale.

## Main definitions

* `AlgebraicGeometry.Space.glueingChartSourceMap` and
  `AlgebraicGeometry.Space.glueingChartFibreMap`: the induced morphisms of the two chart-level
  fibre products.
* `AlgebraicGeometry.Space.glueingChartMiddleMap`: the induced morphism of the intersections.
* `AlgebraicGeometry.Space.glueingChartPushoutMap`: the induced morphism of pushouts.

## Main results

* `AlgebraicGeometry.Space.glueingChartPushoutMap_id` and
  `AlgebraicGeometry.Space.glueingChartPushoutMap_comp`: functoriality.
* `AlgebraicGeometry.Space.isPullback_glueingChartPushoutMap`: the displayed square is cartesian
  for an étale separated chart morphism.
* `AlgebraicGeometry.Space.etale_glueingChartPushoutMap`: the induced morphism is étale.

## References

* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Two cartesian squares attached to a morphism of cospans -/

section PullbackMap

variable {C : Type*} [Category* C] [HasPullbacks C] {C₁ K₁ V₁ C₂ K₂ V₂ : C}
  (p₁ : C₁ ⟶ V₁) (q₁ : K₁ ⟶ V₁) (p₂ : C₂ ⟶ V₂) (q₂ : K₂ ⟶ V₂)
  (uu : C₁ ⟶ C₂) (ww : K₁ ⟶ K₂) (b : V₁ ⟶ V₂)
  (e₁ : p₁ ≫ b = uu ≫ p₂) (e₂ : q₁ ≫ b = ww ≫ q₂)

/-- If `K₁` is the base change of `K₂` along `b`, then `C₁ ×_{V₁} K₁` is the base change of
`C₂ ×_{V₂} K₂` along `uu : C₁ ⟶ C₂`. -/
theorem isPullback_fst_pullbackMap (hK : IsPullback ww q₁ q₂ b) :
    IsPullback (pullback.fst p₁ q₁) (pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂) uu
      (pullback.fst p₂ q₂) := by
  have he : pullback.fst p₁ q₁ ≫ uu =
      pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂ ≫ pullback.fst p₂ q₂ := by
    simp
  rw [← IsPullback.paste_vert_iff (IsPullback.of_hasPullback p₂ q₂) he]
  have hmap : pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂ ≫ pullback.snd p₂ q₂ =
      pullback.snd p₁ q₁ ≫ ww := by simp
  rw [hmap, ← e₁]
  exact (IsPullback.paste_horiz (IsPullback.of_hasPullback p₁ q₁).flip hK).flip

/-- If `C₁` is the base change of `C₂` along `b`, then `C₁ ×_{V₁} K₁` is the base change of
`C₂ ×_{V₂} K₂` along `ww : K₁ ⟶ K₂`. -/
theorem isPullback_snd_pullbackMap (hC : IsPullback uu p₁ p₂ b) :
    IsPullback (pullback.snd p₁ q₁) (pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂) ww
      (pullback.snd p₂ q₂) := by
  have he : pullback.snd p₁ q₁ ≫ ww =
      pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂ ≫ pullback.snd p₂ q₂ := by
    simp
  rw [← IsPullback.paste_vert_iff (IsPullback.of_hasPullback p₂ q₂).flip he]
  have hmap : pullback.map p₁ q₁ p₂ q₂ uu ww b e₁ e₂ ≫ pullback.fst p₂ q₂ =
      pullback.fst p₁ q₁ ≫ uu := by simp
  rw [hmap, ← e₂]
  exact (IsPullback.paste_horiz (IsPullback.of_hasPullback p₁ q₁) hC).flip

end PullbackMap

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
  {Ky : BigFppfOver B S hS} {y : yoneda.obj Ky ⟶ Y.1} (hy : IsClosedImmersion B S hS y)
  {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1} {v' : yoneda.obj V' ⟶ Y.1}
  (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v)

/-! ### The two chart-level morphisms -/

include ha in
/-- The morphism `X ×_Y V ⟶ X ×_Y V'` induced by a morphism `a : V ⟶ V'` of charts over `Y`. -/
def glueingChartSourceMap :
    glueingChartSource B S hS f hf v ⟶ glueingChartSource B S hS f hf v' :=
  (exists_glueingChartSourceMap B S hS f hf a ha).choose

/-- The induced morphism of chart-level sources lies over `a`. -/
theorem glueingChartSourceMap_comp_hom :
    glueingChartSourceMap B S hS f hf a ha ≫ glueingChartSourceHom B S hS f hf v' =
      glueingChartSourceHom B S hS f hf v ≫ a :=
  (exists_glueingChartSourceMap B S hS f hf a ha).choose_spec.1

/-- The induced morphism of chart-level sources is compatible with the projections to `X`. -/
theorem glueingChartSourceMap_comp_fst :
    yoneda.map (glueingChartSourceMap B S hS f hf a ha) ≫
        (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v' =
      (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v :=
  (exists_glueingChartSourceMap B S hS f hf a ha).choose_spec.2

/-- The two characterising equations determine the induced morphism of chart-level sources. -/
theorem glueingChartSourceMap_unique
    (m : glueingChartSource B S hS f hf v ⟶ glueingChartSource B S hS f hf v')
    (h₁ : m ≫ glueingChartSourceHom B S hS f hf v' =
      glueingChartSourceHom B S hS f hf v ≫ a)
    (h₂ : yoneda.map m ≫ (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v' =
      (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v) :
    m = glueingChartSourceMap B S hS f hf a ha := by
  apply yoneda.map_injective
  refine (glueingChartSource_isPullback B S hS f hf v').hom_ext ?_ ?_
  · exact h₂.trans (glueingChartSourceMap_comp_fst B S hS f hf a ha).symm
  · rw [← Functor.map_comp, ← Functor.map_comp, h₁, glueingChartSourceMap_comp_hom]

include ha in
/-- The morphism `Spec k ×_Y V ⟶ Spec k ×_Y V'` induced by a morphism `a : V ⟶ V'` of charts
over `Y`. -/
def glueingChartFibreMap :
    glueingChartFibre B S hS hy v ⟶ glueingChartFibre B S hS hy v' :=
  (exists_glueingChartFibreMap B S hS hy a ha).choose

/-- The induced morphism of chart-level fibres lies over `a`. -/
theorem glueingChartFibreMap_comp_hom :
    glueingChartFibreMap B S hS hy a ha ≫ glueingChartFibreHom B S hS hy v' =
      glueingChartFibreHom B S hS hy v ≫ a :=
  (exists_glueingChartFibreMap B S hS hy a ha).choose_spec.1

/-- The induced morphism of chart-level fibres is compatible with the projections to `Spec k`. -/
theorem glueingChartFibreMap_comp_fst :
    yoneda.map (glueingChartFibreMap B S hS hy a ha) ≫ hy.rep.fst v' = hy.rep.fst v :=
  (exists_glueingChartFibreMap B S hS hy a ha).choose_spec.2

/-- The two characterising equations determine the induced morphism of chart-level fibres. -/
theorem glueingChartFibreMap_unique
    (m : glueingChartFibre B S hS hy v ⟶ glueingChartFibre B S hS hy v')
    (h₁ : m ≫ glueingChartFibreHom B S hS hy v' = glueingChartFibreHom B S hS hy v ≫ a)
    (h₂ : yoneda.map m ≫ hy.rep.fst v' = hy.rep.fst v) :
    m = glueingChartFibreMap B S hS hy a ha := by
  apply yoneda.map_injective
  refine (glueingChartFibre_isPullback B S hS hy v').hom_ext ?_ ?_
  · exact h₂.trans (glueingChartFibreMap_comp_fst B S hS hy a ha).symm
  · rw [← Functor.map_comp, ← Functor.map_comp, h₁, glueingChartFibreMap_comp_hom]

/-! ### Functoriality -/

/-- The identity of a chart induces the identity of the chart-level source. -/
theorem glueingChartSourceMap_id (hv : yoneda.map (𝟙 V) ≫ v = v) :
    glueingChartSourceMap B S hS f hf (𝟙 V) hv = 𝟙 _ :=
  (glueingChartSourceMap_unique B S hS f hf (𝟙 V) hv (𝟙 _) (by simp) (by simp)).symm

/-- The identity of a chart induces the identity of the chart-level fibre. -/
theorem glueingChartFibreMap_id (hv : yoneda.map (𝟙 V) ≫ v = v) :
    glueingChartFibreMap B S hS hy (𝟙 V) hv = 𝟙 _ :=
  (glueingChartFibreMap_unique B S hS hy (𝟙 V) hv (𝟙 _) (by simp) (by simp)).symm

/-! ### The two chart-level squares are cartesian -/

include ha in
/-- The induced morphism of chart-level sources lies over `a`, as a square of schemes. -/
theorem glueingChartSourceMap_w :
    (BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v) ≫
        (BigFppfOver.toScheme B S hS).map a =
      (BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha) ≫
        (BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v') := by
  rw [← Functor.map_comp, ← Functor.map_comp, glueingChartSourceMap_comp_hom]

include ha in
/-- The induced morphism of chart-level fibres lies over `a`, as a square of schemes. -/
theorem glueingChartFibreMap_w :
    (BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v) ≫
        (BigFppfOver.toScheme B S hS).map a =
      (BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha) ≫
        (BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v') := by
  rw [← Functor.map_comp, ← Functor.map_comp, glueingChartFibreMap_comp_hom]

include ha in
/-- `X ×_Y V` is the base change of `X ×_Y V'` along `a`, as a square of presheaves. -/
theorem isPullback_yoneda_glueingChartSourceMap :
    IsPullback (yoneda.map (glueingChartSourceMap B S hS f hf a ha))
      (yoneda.map (glueingChartSourceHom B S hS f hf v))
      (yoneda.map (glueingChartSourceHom B S hS f hf v')) (yoneda.map a) := by
  refine IsPullback.of_right ?_ ?_ (glueingChartSource_isPullback B S hS f hf v')
  · rw [glueingChartSourceMap_comp_fst, ha]
    exact glueingChartSource_isPullback B S hS f hf v
  · rw [← Functor.map_comp, ← Functor.map_comp, glueingChartSourceMap_comp_hom]

include ha in
/-- `Spec k ×_Y V` is the base change of `Spec k ×_Y V'` along `a`, as a square of
presheaves. -/
theorem isPullback_yoneda_glueingChartFibreMap :
    IsPullback (yoneda.map (glueingChartFibreMap B S hS hy a ha))
      (yoneda.map (glueingChartFibreHom B S hS hy v))
      (yoneda.map (glueingChartFibreHom B S hS hy v')) (yoneda.map a) := by
  refine IsPullback.of_right ?_ ?_ (glueingChartFibre_isPullback B S hS hy v')
  · rw [glueingChartFibreMap_comp_fst, ha]
    exact glueingChartFibre_isPullback B S hS hy v
  · rw [← Functor.map_comp, ← Functor.map_comp, glueingChartFibreMap_comp_hom]

include ha in
/-- `X ×_Y V` is the base change of `X ×_Y V'` along `a`, as a square of schemes. -/
theorem isPullback_glueingChartSourceMap :
    IsPullback ((BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha))
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v))
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v'))
      ((BigFppfOver.toScheme B S hS).map a) :=
  let := preservesPullbacks_bigFppfOverToScheme B S hS
  (IsPullback.of_map yoneda (glueingChartSourceMap_comp_hom B S hS f hf a ha)
      (isPullback_yoneda_glueingChartSourceMap B S hS f hf a ha)).map
    (BigFppfOver.toScheme B S hS)

include ha in
/-- `Spec k ×_Y V` is the base change of `Spec k ×_Y V'` along `a`, as a square of
schemes. -/
theorem isPullback_glueingChartFibreMap :
    IsPullback ((BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha))
      ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v))
      ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v'))
      ((BigFppfOver.toScheme B S hS).map a) :=
  let := preservesPullbacks_bigFppfOverToScheme B S hS
  (IsPullback.of_map yoneda (glueingChartFibreMap_comp_hom B S hS hy a ha)
      (isPullback_yoneda_glueingChartFibreMap B S hS hy a ha)).map
    (BigFppfOver.toScheme B S hS)

/-! ### The morphism of intersections -/

include ha in
/-- The morphism of the two chart-level intersections `(X ×_Y V) ×_V (Spec k ×_Y V)` induced by a
morphism of charts over `Y`. -/
abbrev glueingChartMiddleMap :
    (glueingChartSituation B S hS f hf hy v).Z ⟶ (glueingChartSituation B S hS f hf hy v').Z :=
  pullback.map _ _ _ _
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha))
    ((BigFppfOver.toScheme B S hS).map a)
    (glueingChartSourceMap_w B S hS f hf a ha) (glueingChartFibreMap_w B S hS hy a ha)

include ha in
/-- The square relating the intersections to the sources is cartesian. -/
theorem isPullback_glueingChartMiddleMap_fst :
    IsPullback (glueingChartSituation B S hS f hf hy v).i
      (glueingChartMiddleMap B S hS f hf hy a ha)
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha))
      (glueingChartSituation B S hS f hf hy v').i :=
  isPullback_fst_pullbackMap _ _ _ _ _ _ _ (glueingChartSourceMap_w B S hS f hf a ha)
    (glueingChartFibreMap_w B S hS hy a ha) (isPullback_glueingChartFibreMap B S hS hy a ha)

include ha in
/-- The square relating the intersections to the fibres is cartesian. -/
theorem isPullback_glueingChartMiddleMap_snd :
    IsPullback (glueingChartSituation B S hS f hf hy v).j
      (glueingChartMiddleMap B S hS f hf hy a ha)
      ((BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha))
      (glueingChartSituation B S hS f hf hy v').j :=
  isPullback_snd_pullbackMap _ _ _ _ _ _ _ (glueingChartSourceMap_w B S hS f hf a ha)
    (glueingChartFibreMap_w B S hS hy a ha) (isPullback_glueingChartSourceMap B S hS f hf a ha)

/-! ### The morphism of pushouts -/

include ha in
/-- The morphism of pushouts `P_V ⟶ P_{V'}` induced by a morphism of charts over `Y`, given by
the universal property of `P_V` out of the two chart-level morphisms. -/
def glueingChartPushoutMap :
    glueingChartPushout B S hS f hf hy v ⟶ glueingChartPushout B S hS f hf hy v' :=
  (pushoutAlongClosedImmersionAndIntegral
      (glueingChartSituation B S hS f hf hy v)).isPushout.desc
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha) ≫
      pushoutInl (glueingChartSituation B S hS f hf hy v'))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha) ≫
      pushoutInr (glueingChartSituation B S hS f hf hy v')) (by
      rw [← Category.assoc, ← Category.assoc,
        (isPullback_glueingChartMiddleMap_fst B S hS f hf hy a ha).w,
        (isPullback_glueingChartMiddleMap_snd B S hS f hf hy a ha).w, Category.assoc,
        Category.assoc]
      exact congrArg (fun k ↦ glueingChartMiddleMap B S hS f hf hy a ha ≫ k)
        (pushoutAlongClosedImmersionAndIntegral
          (glueingChartSituation B S hS f hf hy v')).isPushout.w)

/-- The induced morphism of pushouts restricts to the induced morphism of sources. -/
theorem pushoutInl_comp_glueingChartPushoutMap :
    pushoutInl (glueingChartSituation B S hS f hf hy v) ≫
        glueingChartPushoutMap B S hS f hf hy a ha =
      (BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha) ≫
        pushoutInl (glueingChartSituation B S hS f hf hy v') :=
  (pushoutAlongClosedImmersionAndIntegral
    (glueingChartSituation B S hS f hf hy v)).isPushout.inl_desc _ _ _

/-- The induced morphism of pushouts restricts to the induced morphism of fibres. -/
theorem pushoutInr_comp_glueingChartPushoutMap :
    pushoutInr (glueingChartSituation B S hS f hf hy v) ≫
        glueingChartPushoutMap B S hS f hf hy a ha =
      (BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha) ≫
        pushoutInr (glueingChartSituation B S hS f hf hy v') :=
  (pushoutAlongClosedImmersionAndIntegral
    (glueingChartSituation B S hS f hf hy v)).isPushout.inr_desc _ _ _

/-- The two restrictions determine the induced morphism of pushouts. -/
theorem glueingChartPushoutMap_unique
    (k : glueingChartPushout B S hS f hf hy v ⟶ glueingChartPushout B S hS f hf hy v')
    (h₁ : pushoutInl (glueingChartSituation B S hS f hf hy v) ≫ k =
      (BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha) ≫
        pushoutInl (glueingChartSituation B S hS f hf hy v'))
    (h₂ : pushoutInr (glueingChartSituation B S hS f hf hy v) ≫ k =
      (BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha) ≫
        pushoutInr (glueingChartSituation B S hS f hf hy v')) :
    k = glueingChartPushoutMap B S hS f hf hy a ha :=
  (pushoutAlongClosedImmersionAndIntegral
      (glueingChartSituation B S hS f hf hy v)).isPushout.hom_ext
    (h₁.trans (pushoutInl_comp_glueingChartPushoutMap B S hS f hf hy a ha).symm)
    (h₂.trans (pushoutInr_comp_glueingChartPushoutMap B S hS f hf hy a ha).symm)

include ha in
/-- The induced morphism of pushouts lies over `a`. -/
theorem glueingChartPushoutMap_comp_toBase :
    glueingChartPushoutMap B S hS f hf hy a ha ≫
        glueingChartPushoutToBase B S hS f hf hy v' =
      glueingChartPushoutToBase B S hS f hf hy v ≫ (BigFppfOver.toScheme B S hS).map a := by
  refine (pushoutAlongClosedImmersionAndIntegral
    (glueingChartSituation B S hS f hf hy v)).isPushout.hom_ext ?_ ?_
  · rw [← Category.assoc, pushoutInl_comp_glueingChartPushoutMap, Category.assoc,
      pushoutToBase_inl, ← Category.assoc, pushoutToBase_inl]
    exact (glueingChartSourceMap_w B S hS f hf a ha).symm
  · rw [← Category.assoc, pushoutInr_comp_glueingChartPushoutMap, Category.assoc,
      pushoutToBase_inr, ← Category.assoc, pushoutToBase_inr]
    exact (glueingChartFibreMap_w B S hS hy a ha).symm

/-- The identity of a chart induces the identity of the pushout. -/
theorem glueingChartPushoutMap_id (hv : yoneda.map (𝟙 V) ≫ v = v) :
    glueingChartPushoutMap B S hS f hf hy (𝟙 V) hv = 𝟙 _ :=
  (glueingChartPushoutMap_unique B S hS f hf hy (𝟙 V) hv (𝟙 _)
    (by simp [glueingChartSourceMap_id]) (by simp [glueingChartFibreMap_id])).symm

/-! ### The cartesian square over an étale separated morphism of charts -/

include ha in
/-- The cartesian diagram over the chart situation of `V'` attached to an étale separated
morphism of charts, whose span is the chart-level span over `V`. -/
def glueingChartDiagram (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    CartesianDiagram (glueingChartSituation B S hS f hf hy v') := by
  haveI hetf : Etale
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_glueingChartSourceMap B S hS f hf a ha).flip het
  haveI hetg : Etale
      ((BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_glueingChartFibreMap B S hS hy a ha).flip het
  haveI heth : Etale (glueingChartMiddleMap B S hS f hf hy a ha) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_glueingChartMiddleMap_fst B S hS f hf hy a ha) hetf
  exact
    { X' := (BigFppfOver.toScheme B S hS).obj (glueingChartSource B S hS f hf v)
      Y' := (BigFppfOver.toScheme B S hS).obj (glueingChartFibre B S hS hy v)
      Z' := (glueingChartSituation B S hS f hf hy v).Z
      i' := (glueingChartSituation B S hS f hf hy v).i
      j' := (glueingChartSituation B S hS f hf hy v).j
      f := (BigFppfOver.toScheme B S hS).map (glueingChartSourceMap B S hS f hf a ha)
      g := (BigFppfOver.toScheme B S hS).map (glueingChartFibreMap B S hS hy a ha)
      h := glueingChartMiddleMap B S hS f hf hy a ha
      left_isPullback := isPullback_glueingChartMiddleMap_fst B S hS f hf hy a ha
      right_isPullback := isPullback_glueingChartMiddleMap_snd B S hS f hf hy a ha
      f_isSeparated := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_glueingChartSourceMap B S hS f hf a ha).flip hsep
      g_isSeparated := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_glueingChartFibreMap B S hS hy a ha).flip hsep
      h_isSeparated := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_glueingChartMiddleMap_fst B S hS f hf hy a ha)
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (isPullback_glueingChartSourceMap B S hS f hf a ha).flip hsep)
      f_locallyOfFiniteType := (locallyQuasiFinite_of_etale _).1
      g_locallyOfFiniteType := (locallyQuasiFinite_of_etale _).1
      h_locallyOfFiniteType := (locallyQuasiFinite_of_etale _).1
      f_locallyQuasiFinite := (locallyQuasiFinite_of_etale _).2
      g_locallyQuasiFinite := (locallyQuasiFinite_of_etale _).2
      h_locallyQuasiFinite := (locallyQuasiFinite_of_etale _).2 }

include ha in
/-- The induced morphism of pushouts is the morphism of [Stacks Project, Tag 0ECK] attached to
the induced cartesian diagram. -/
theorem glueingChartPushoutMap_eq_pushoutMap
    (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    glueingChartPushoutMap B S hS f hf hy a ha =
      pushoutMap (glueingChartSituation B S hS f hf hy v')
        (glueingChartDiagram B S hS f hf hy a ha het hsep) :=
  (glueingChartPushoutMap_unique B S hS f hf hy a ha _
    (pushoutMap_left_isPullback (glueingChartSituation B S hS f hf hy v')
      (glueingChartDiagram B S hS f hf hy a ha het hsep)).w
    (pushoutMap_right_isPullback (glueingChartSituation B S hS f hf hy v')
      (glueingChartDiagram B S hS f hf hy a ha het hsep)).w).symm

include ha in
/-- For an étale separated morphism of charts over `Y`, the square relating the two pushouts to
the two charts is cartesian: the pushout over `V` is the base change of the pushout over `V'`. -/
theorem isPullback_glueingChartPushoutMap
    (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    IsPullback (glueingChartPushoutMap B S hS f hf hy a ha)
      (glueingChartPushoutToBase B S hS f hf hy v)
      (glueingChartPushoutToBase B S hS f hf hy v') ((BigFppfOver.toScheme B S hS).map a) := by
  have : Flat ((BigFppfOver.toScheme B S hS).map a) :=
    (Etale.iff_flat_and_formallyUnramified.mp het).1
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map a) :=
    (locallyQuasiFinite_of_etale _).1
  have : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map a) :=
    (locallyQuasiFinite_of_etale _).2
  rw [glueingChartPushoutMap_eq_pushoutMap B S hS f hf hy a ha het hsep]
  exact isPullback_pushoutMap_of_isPullback (glueingChartSituation B S hS f hf hy v')
    ((BigFppfOver.toScheme B S hS).map a)
    (glueingChartDiagram B S hS f hf hy a ha het hsep)
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v))
    (isPullback_glueingChartSourceMap B S hS f hf a ha)
    (isPullback_glueingChartFibreMap B S hS hy a ha)
    (glueingChartPushoutToBase B S hS f hf hy v) (pushoutToBase_inl _) (pushoutToBase_inr _)

include ha in
/-- The induced morphism of pushouts is étale over an étale separated morphism of charts. -/
theorem etale_glueingChartPushoutMap
    (het : Etale ((BigFppfOver.toScheme B S hS).map a))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a)) :
    Etale (glueingChartPushoutMap B S hS f hf hy a ha) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_glueingChartPushoutMap B S hS f hf hy a ha het hsep).flip het

variable {V'' : BigFppfOver B S hS} {v'' : yoneda.obj V'' ⟶ Y.1}
  (b : V' ⟶ V'') (hb : yoneda.map b ≫ v'' = v')

include ha hb in
/-- The induced morphisms of chart-level sources compose. -/
theorem glueingChartSourceMap_comp :
    glueingChartSourceMap B S hS f hf (a ≫ b)
        (by rw [Functor.map_comp, Category.assoc, hb, ha]) =
      glueingChartSourceMap B S hS f hf a ha ≫ glueingChartSourceMap B S hS f hf b hb :=
  (glueingChartSourceMap_unique B S hS f hf (a ≫ b)
    (by rw [Functor.map_comp, Category.assoc, hb, ha]) _
    (by rw [Category.assoc, glueingChartSourceMap_comp_hom, ← Category.assoc,
      glueingChartSourceMap_comp_hom, Category.assoc])
    (by simp only [Functor.map_comp, Category.assoc, glueingChartSourceMap_comp_fst])).symm

include ha hb in
/-- The induced morphisms of chart-level fibres compose. -/
theorem glueingChartFibreMap_comp :
    glueingChartFibreMap B S hS hy (a ≫ b)
        (by rw [Functor.map_comp, Category.assoc, hb, ha]) =
      glueingChartFibreMap B S hS hy a ha ≫ glueingChartFibreMap B S hS hy b hb :=
  (glueingChartFibreMap_unique B S hS hy (a ≫ b)
    (by rw [Functor.map_comp, Category.assoc, hb, ha]) _
    (by rw [Category.assoc, glueingChartFibreMap_comp_hom, ← Category.assoc,
      glueingChartFibreMap_comp_hom, Category.assoc])
    (by simp only [Functor.map_comp, Category.assoc, glueingChartFibreMap_comp_fst])).symm

include ha hb in
/-- The morphism of pushouts induced by a composite of chart morphisms is the composite of the
induced morphisms. -/
theorem glueingChartPushoutMap_comp :
    glueingChartPushoutMap B S hS f hf hy (a ≫ b)
        (by rw [Functor.map_comp, Category.assoc, hb, ha]) =
      glueingChartPushoutMap B S hS f hf hy a ha ≫
        glueingChartPushoutMap B S hS f hf hy b hb :=
  (glueingChartPushoutMap_unique B S hS f hf hy (a ≫ b)
    (by rw [Functor.map_comp, Category.assoc, hb, ha]) _
    (by
      rw [← Category.assoc, pushoutInl_comp_glueingChartPushoutMap, Category.assoc,
        pushoutInl_comp_glueingChartPushoutMap, ← Category.assoc, ← Functor.map_comp,
        ← glueingChartSourceMap_comp B S hS f hf a ha b hb])
    (by
      rw [← Category.assoc, pushoutInr_comp_glueingChartPushoutMap, Category.assoc,
        pushoutInr_comp_glueingChartPushoutMap, ← Category.assoc, ← Functor.map_comp,
        ← glueingChartFibreMap_comp B S hS hy a ha b hb])).symm

end Chart

end Space

end AlgebraicGeometry

end
