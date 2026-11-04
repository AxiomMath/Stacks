module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Characterization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientChartLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientEtaleModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart

/-!
# A scheme stage of a system of étale quotients and its chart system

Let `D` be an inverse system of presheaves on the big fppf site whose transition morphisms are
relatively representable, and let `q₀ : Y₀ ⟶ D_{i₀}` be a morphism from an object of the site.
The base changes `Y₀ ×_{D_{i₀}} D_j` for the stages `j` over `i₀` are again objects of the site,
and they form an inverse system over `Y₀`, the *chart system* of `q₀`.

In the proof of Stacks 07SU the étale neighbourhood `W ⟶ U` of the open part has been descended
to an étale morphism `W_k ⟶ U_k` from a scheme at a stage `k` of the system `U_i` approximating
`U`, and one needs `W = lim_{i ≥ k} W_i` in schemes, where `W_i = W_k ×_{U_k} U_i`. That is the
chart system of `W_k ⟶ U_k`, and when `U_i = V_i/R_i` is a system of étale quotients its limit
is computed in schemes (`AlgebraicGeometry.Space.EtaleRelationSystem.chartLimitsInSchemes`).

## Main definitions

* `AlgebraicGeometry.Space.stageChartOverDiagram`: the chart system `j ↦ Y₀ ×_{D_{i₀}} D_j` of a
  morphism `q₀ : Y₀ ⟶ D_{i₀}`, as a functor to objects over `Y₀`.
* `AlgebraicGeometry.Space.stageChartOverCone`: the cone over it from the base change of the limit.
* `AlgebraicGeometry.Space.tailToOver`: the tail `{i | k ≤ i}` of a directed set, as an initial
  functor into the stages over `k` of the opposite category.

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.isLimit_stageChartCone`: the chart system of a
  morphism into a stage of a system of étale quotients has the base change of the limit as its
  limit in schemes.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {J : Type u} [Category.{u} J] (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hrep : ∀ {i j : J} (g : i ⟶ j), yoneda.relativelyRepresentable (D.map g))
  (i₀ : J) {Y₀ : BigFppfOver B S hS} (q₀ : yoneda.obj Y₀ ⟶ D.obj i₀)

/-- The chart `Y₀ ×_{D_{i₀}} D_j` of a morphism `q₀ : Y₀ ⟶ D_{i₀}` at a stage `j` over `i₀`. -/
noncomputable def quotientStageChart (j : Over i₀) : BigFppfOver B S hS :=
  (hrep j.hom).pullback q₀

/-- The projection of a chart to its stage. -/
noncomputable def stageChartToStage (j : Over i₀) :
    yoneda.obj (quotientStageChart D hrep i₀ q₀ j) ⟶ D.obj j.left :=
  (hrep j.hom).fst q₀

/-- The projection of a chart to the base object `Y₀`. -/
noncomputable def stageChartToBase (j : Over i₀) : quotientStageChart D hrep i₀ q₀ j ⟶ Y₀ :=
  (hrep j.hom).snd q₀

/-- The chart `Y₀ ×_{D_{i₀}} D_j` is the pullback of `D_j ⟶ D_{i₀}` along `q₀`. -/
lemma isPullback_stageChartToStage (j : Over i₀) :
    IsPullback (stageChartToStage D hrep i₀ q₀ j) (yoneda.map (stageChartToBase D hrep i₀ q₀ j))
      (D.map j.hom) q₀ :=
  (hrep j.hom).isPullback q₀

/-- The transition morphism of the chart system. -/
noncomputable def stageChartMap {j k : Over i₀} (e : j ⟶ k) :
    quotientStageChart D hrep i₀ q₀ j ⟶ quotientStageChart D hrep i₀ q₀ k :=
  (hrep k.hom).lift (stageChartToStage D hrep i₀ q₀ j ≫ D.map e.left)
    (stageChartToBase D hrep i₀ q₀ j) (by
      rw [Category.assoc, ← D.map_comp, Over.w e]
      exact (isPullback_stageChartToStage D hrep i₀ q₀ j).w)

/-- The transition morphisms of the chart system commute with the projections to the stages. -/
@[reassoc (attr := simp)]
lemma stageChartMap_toStage {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (stageChartMap D hrep i₀ q₀ e) ≫ stageChartToStage D hrep i₀ q₀ k =
      stageChartToStage D hrep i₀ q₀ j ≫ D.map e.left :=
  (hrep k.hom).lift_fst _ _ _

/-- The transition morphisms of the chart system commute with the projections to `Y₀`. -/
@[reassoc (attr := simp)]
lemma stageChartMap_toBase {j k : Over i₀} (e : j ⟶ k) :
    stageChartMap D hrep i₀ q₀ e ≫ stageChartToBase D hrep i₀ q₀ k =
      stageChartToBase D hrep i₀ q₀ j :=
  (hrep k.hom).lift_snd _ _ _

/-- Two morphisms into a chart agree when they agree after the projections to the stage and
to `Y₀`. -/
lemma stageChart_hom_ext {j : Over i₀} {T : BigFppfOver B S hS}
    {a b : T ⟶ quotientStageChart D hrep i₀ q₀ j}
    (h₁ : yoneda.map a ≫ stageChartToStage D hrep i₀ q₀ j =
      yoneda.map b ≫ stageChartToStage D hrep i₀ q₀ j)
    (h₂ : a ≫ stageChartToBase D hrep i₀ q₀ j = b ≫ stageChartToBase D hrep i₀ q₀ j) : a = b :=
  (hrep j.hom).hom_ext h₁ h₂

/-- **The chart system** `j ↦ Y₀ ×_{D_{i₀}} D_j` of a morphism `q₀ : Y₀ ⟶ D_{i₀}`, as a
system of objects over `Y₀` indexed by the stages over `i₀`. -/
@[simps]
noncomputable def stageChartOverDiagram : Over i₀ ⥤ Over Y₀ where
  obj j := Over.mk (stageChartToBase D hrep i₀ q₀ j)
  map e := Over.homMk (stageChartMap D hrep i₀ q₀ e) (stageChartMap_toBase D hrep i₀ q₀ e)
  map_id j := by
    ext1
    refine stageChart_hom_ext D hrep i₀ q₀ ?_ ?_
    · simp
    · simp
  map_comp {j k l} e f := by
    ext1
    refine stageChart_hom_ext D hrep i₀ q₀ ?_ ?_
    · simp
    · simp

variable [HasLimit D] {YL : BigFppfOver B S hS} (pL : yoneda.obj YL ⟶ limit D) (qL : YL ⟶ Y₀)
  (hL : IsPullback pL (yoneda.map qL) (limit.π D i₀) q₀)

/-- The leg of the chart cone at a stage `j`: the map `Y₀ ×_{D_{i₀}} lim D ⟶ Y₀ ×_{D_{i₀}} D_j`. -/
noncomputable def stageChartLeg (j : Over i₀) : YL ⟶ quotientStageChart D hrep i₀ q₀ j :=
  (hrep j.hom).lift (pL ≫ limit.π D j.left) qL (by rw [Category.assoc, limit.w]; exact hL.w)

/-- The leg of the chart cone at `j`, followed by the projection to the stage `j`, is the
projection of the base change `Y₀ ×_{D_{i₀}} lim D` to `D_j`. -/
@[reassoc (attr := simp)]
lemma stageChartLeg_toStage (j : Over i₀) :
    yoneda.map (stageChartLeg D hrep i₀ q₀ pL qL hL j) ≫ stageChartToStage D hrep i₀ q₀ j =
      pL ≫ limit.π D j.left :=
  (hrep j.hom).lift_fst _ _ _

/-- The legs of the chart cone commute with the projections to `Y₀`. -/
@[reassoc (attr := simp)]
lemma stageChartLeg_toBase (j : Over i₀) :
    stageChartLeg D hrep i₀ q₀ pL qL hL j ≫ stageChartToBase D hrep i₀ q₀ j = qL :=
  (hrep j.hom).lift_snd _ _ _

/-- The legs of the chart cone are compatible with the transition morphisms of the chart
system. -/
@[reassoc (attr := simp)]
lemma stageChartLeg_chartMap {j k : Over i₀} (e : j ⟶ k) :
    stageChartLeg D hrep i₀ q₀ pL qL hL j ≫ stageChartMap D hrep i₀ q₀ e =
      stageChartLeg D hrep i₀ q₀ pL qL hL k := by
  refine stageChart_hom_ext D hrep i₀ q₀ ?_ ?_
  · simp only [Functor.map_comp, Category.assoc, stageChartMap_toStage, stageChartLeg_toStage_assoc,
      stageChartLeg_toStage, limit.w]
  · simp

/-- **The base change of the limit is the base change of every stage**:
`Y₀ ×_{D_{i₀}} lim D = lim D ×_{D_j} (Y₀ ×_{D_{i₀}} D_j)`. -/
lemma isPullback_stageChartLeg (j : Over i₀) :
    IsPullback pL (yoneda.map (stageChartLeg D hrep i₀ q₀ pL qL hL j)) (limit.π D j.left)
      (stageChartToStage D hrep i₀ q₀ j) := by
  refine IsPullback.of_bot ?_ (stageChartLeg_toStage D hrep i₀ q₀ pL qL hL j).symm
    (isPullback_stageChartToStage D hrep i₀ q₀ j)
  rw [← yoneda.map_comp, stageChartLeg_toBase, limit.w]
  exact hL

/-- **The chart cone**, from the base change `Y₀ ×_{D_{i₀}} lim D` to the chart system. -/
@[simps]
noncomputable def stageChartOverCone : Cone (stageChartOverDiagram D hrep i₀ q₀) where
  pt := Over.mk qL
  π :=
    { app j := Over.homMk (stageChartLeg D hrep i₀ q₀ pL qL hL j)
        (stageChartLeg_toBase D hrep i₀ q₀ pL qL hL j)
      naturality j k e := by
        ext1
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Over.comp_left]
        exact (stageChartLeg_chartMap D hrep i₀ q₀ pL qL hL e).symm }

end Chart

namespace EtaleRelationSystem

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {J : Type u} [Category.{u} J] [IsCofiltered J] (E : EtaleRelationSystem B S hS J)

omit [IsCofiltered J] in
/-- The transition morphisms of a system of étale quotients with affine transition morphisms on
the objects are relatively representable. -/
lemma relativelyRepresentable_quotient_map
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    {i j : J} (g : i ⟶ j) : yoneda.relativelyRepresentable (E.quotient.map g) := by
  have h := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (E.quotient.map g)
    (E.isAlgebraicSpace_quotient_obj _) (E.isAlgebraicSpace_quotient_obj _)).out 2 1).mp
      (E.isAffineHom_quotient_map hobj g)
  exact h.1

/-- **The chart system of a morphism into a stage of a system of étale quotients is computed in
schemes.** Let `E` be an inverse system of étale equivalence relations with affine transition
morphisms on the objects, whose objects have a limit in schemes, and let `q₀ : Y₀ ⟶ V_{i₀}/R_{i₀}`
be a morphism from a quasi-compact quasi-separated object of the site. Then the base change
`Y₀ ×_{V_{i₀}/R_{i₀}} lim_j V_j/R_j` is the limit in schemes of the chart system
`Y₀ ×_{V_{i₀}/R_{i₀}} V_j/R_j`. -/
theorem isLimit_stageChartCone
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (i₀ : J) {Y₀ : BigFppfOver B S hS}
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj Y₀)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Y₀)]
    (q₀ : yoneda.obj Y₀ ⟶ E.quotient.obj i₀) {YL : BigFppfOver B S hS}
    (pL : yoneda.obj YL ⟶ limit E.quotient) (qL : YL ⟶ Y₀)
    (hL : IsPullback pL (yoneda.map qL) (limit.π E.quotient i₀) q₀) :
    Nonempty (IsLimit ((Over.forget Y₀ ⋙ BigFppfOver.toScheme B S hS).mapCone
      (stageChartOverCone E.quotient (E.relativelyRepresentable_quotient_map hobj) i₀ q₀ pL qL
        hL))) := by
  have hrep : ∀ {i j : J} (g : i ⟶ j), _ := E.relativelyRepresentable_quotient_map hobj
  exact E.chartLimitsInSchemes hobj cV hV i₀ Y₀ q₀ (stageChartOverDiagram E.quotient hrep i₀ q₀)
    (stageChartToStage E.quotient hrep i₀ q₀)
    (stageChartMap_toStage E.quotient hrep i₀ q₀)
    (isPullback_stageChartToStage E.quotient hrep i₀ q₀)
    (stageChartOverCone E.quotient hrep i₀ q₀ pL qL hL) pL hL
    (stageChartLeg_toStage E.quotient hrep i₀ q₀ pL qL hL)

omit [IsCofiltered J] in
/-- **An object étale over a stage of a system of étale quotients is locally of finite type** over
`Spec ℤ` when the object of the relation at that stage is: it has a surjective étale chart, the
base change of the quotient map, which is étale over that object. -/
lemma locallyOfFiniteType_of_presheaf_etale (j : J)
    (hlft : LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj (E.obj.obj j))))
    {Z : BigFppfOver B S hS} (z : yoneda.obj Z ⟶ E.quotient.obj j)
    (hz : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf z) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj Z)) := by
  let T := BigFppfOver.toScheme B S hS
  have hrep : yoneda.relativelyRepresentable (E.toQuotient.app j) :=
    (E.isAlgebraicSpace_quotient_obj j).diagonal_representable.of_diag _
  let a : hrep.pullback z ⟶ Z := hrep.snd z
  obtain ⟨b, hb⟩ := yoneda.map_surjective (hrep.fst z)
  have hsq : IsPullback (yoneda.map b) (yoneda.map a) (E.toQuotient.app j) z := by
    rw [hb]; exact hrep.isPullback z
  have hsurj : Surjective (T.map a) :=
    (quotientMap_surjective_unconditional B S hS (E.s.app j) (E.t.app j)).property z _ a hsq
  have haet : Etale (T.map a) :=
    (quotientMap_etale_unconditional B S hS (E.s.app j) (E.t.app j)).property z _ a hsq
  have hbet : Etale (T.map b) := hz.property (E.toQuotient.app j) (yoneda.map a) b hsq.flip
  have hP : LocallyOfFiniteType (terminal.from (T.obj (hrep.pullback z))) := by
    rw [← terminal.comp_from (T.map b)]
    infer_instance
  refine (IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram
    (terminal.from (T.obj Z)) isEtaleLocalOnSourceAndTarget_locallyOfFiniteType).mpr
    ⟨T.obj (hrep.pullback z), ⊤_ Scheme.{u}, T.map a, 𝟙 _, terminal.from _, haet,
      inferInstance, hsurj.surj, by simp, hP⟩

end EtaleRelationSystem

namespace EtaleRelationSystem

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **An étale neighbourhood of the limit of a system of étale quotients descends to a scheme
stage (proof of Stacks 07SU).** Let `E` be an inverse system of étale equivalence relations over
a directed set, with affine transition morphisms on the objects and a limit of the objects in
schemes, whose system of quotients `U_i` has bounded charts and quasi-compact quasi-separated
stages, with algebraic limit `U`. Let `w : W ⟶ U` be an étale morphism of finite presentation
from an object `W` of the site.

Then there are a stage `k`, an object `W_k` of the site with quasi-compact underlying scheme,
an étale morphism `w_k : W_k ⟶ U_k` and a morphism `W ⟶ W_k` exhibiting `W` as the base change
`U ×_{U_k} W_k`. This combines Stacks 07SK, 07SL and 07SR
(`AlgebraicGeometry.Space.EtaleRelationSystem.exists_morphismDescentSystem_of_isEtale`). -/
theorem exists_schemeStage_of_isEtale {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (E : EtaleRelationSystem B S hS Iᵒᵖ)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (hb : ChartsBounded B S hS E.quotient)
    (hqc : ∀ j, IsQuasiCompactSpace B S hS (E.quotient.obj j))
    (hqs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ (E.quotient.obj j))
    (hL : IsAlgebraicSpace B S hS (limit E.quotient))
    {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ limit E.quotient)
    (hFp : IsFinitePresentation B S hS w) (hEt : IsEtale B S hS w) :
    ∃ (k : I) (Wk : BigFppfOver B S hS) (wk : yoneda.obj Wk ⟶ E.quotient.obj (op k))
      (g : W ⟶ Wk),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf wk ∧
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Wk) ∧
      IsPullback w (yoneda.map g) (limit.π E.quotient (op k)) wk := by
  classical
  let U := E.quotient
  have hD : ∀ j, IsAlgebraicSpace B S hS (U.obj j) := E.isAlgebraicSpace_quotient_obj
  obtain ⟨i₀, Y₀, y, hY₀, hyfp, ⟨e, he⟩, ⟨i, hi, het⟩, hrep⟩ :=
    E.exists_morphismDescentSystem_of_isEtale (hZ := hZ) hobj cV hV hb hqc hqs hL (Over.mk w)
      (isAlgebraicSpace_yoneda B S hS W) hFp hEt
  obtain ⟨k, hk, hkrep⟩ := hrep (inferInstanceAs (yoneda.obj W).IsRepresentable)
  obtain ⟨m, him, hkm⟩ := directed_of (· ≤ ·) i k
  have hρ : ∀ {a b c : I} (hab : a ≤ b) (hbc : b ≤ c),
      U.map (homOfLE hbc).op ≫ U.map (homOfLE hab).op = U.map (homOfLE (hab.trans hbc)).op :=
    fun hab hbc => by rw [← U.map_comp]; rfl
  -- the representable stage `k` and its base change `W_m` to the stage `m`
  let Pk := pullback (U.map (homOfLE hk).op) y
  let ε : yoneda.obj Pk.reprX ≅ Pk := Pk.reprW
  have sqPk : IsPullback (ε.hom ≫ pullback.fst _ _) (ε.hom ≫ pullback.snd _ _)
      (U.map (homOfLE hk).op) y :=
    IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ ε rfl rfl
  have hrepmk := E.relativelyRepresentable_quotient_map hobj (homOfLE hkm).op
  let Wm := hrepmk.pullback (ε.hom ≫ pullback.fst _ _)
  let wm : yoneda.obj Wm ⟶ U.obj (op m) := hrepmk.fst _
  let L : yoneda.obj Wm ⟶ Y₀ := yoneda.map (hrepmk.snd _) ≫ ε.hom ≫ pullback.snd _ _
  have big : IsPullback wm L (U.map (homOfLE (hk.trans hkm)).op) y := by
    have := (hrepmk.isPullback (ε.hom ≫ pullback.fst _ _)).paste_vert sqPk
    rwa [hρ hk hkm] at this
  -- `W_m ⟶ U_m` is étale, being the base change of the étale stage `i`
  let toPi : yoneda.obj Wm ⟶ pullback (U.map (homOfLE hi).op) y :=
    pullback.lift (wm ≫ U.map (homOfLE him).op) L (by
      rw [Category.assoc, hρ hi him]
      have : hi.trans him = hk.trans hkm := rfl
      rw [this]; exact big.w)
  have sqi : IsPullback wm toPi (U.map (homOfLE him).op)
      (pullback.fst (U.map (homOfLE hi).op) y) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_snd, hρ hi him]
    exact big
  have hwmEt : IsEtale B S hS wm :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqi (isAlgebraicSpace_yoneda B S hS Wm)
      (hD _) (isAlgebraicSpace_pullback B S hS _ _ (hD _) hY₀ (hD _)) (hD _) het
  -- the limit square
  have sqL : IsPullback w (e.hom ≫ pullback.snd _ _) (limit.π U (op i₀)) y := by
    have h' : e.hom ≫ pullback.fst _ _ = w := he
    exact IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, ← pullback.condition, ← Category.assoc, h']⟩ e h' rfl
  let gY : yoneda.obj W ⟶ yoneda.obj Wm :=
    big.lift (w ≫ limit.π U (op m)) (e.hom ≫ pullback.snd _ _) (by
      rw [Category.assoc, limit.w]; exact sqL.w)
  obtain ⟨g, hg⟩ := yoneda.map_surjective gY
  refine ⟨m, Wm, wm, g, (isEtale_iff_presheaf_of_yoneda B S hS wm).1 hwmEt, ?_, ?_⟩
  · have hY₀qc : IsQuasiCompactSpace B S hS Y₀ :=
      isQuasiCompactSpace_source_of_isQuasiCompact B S hS (hD _) (hqc _) hyfp.2.1
    have hPqc : IsQuasiCompactSpace B S hS (pullback (U.map (homOfLE (hk.trans hkm)).op) y) :=
      isQuasiCompactSpace_pullback B S hS hZ _ _ (hD _) (hD _) (hqc _) hY₀qc (hqs _)
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS big.isoPullback.symm hPqc)
  · refine IsPullback.of_bot ?_ (by rw [hg]; exact (big.lift_fst _ _ _).symm) big
    rw [hg, big.lift_snd, limit.w]
    exact sqL

end EtaleRelationSystem

section Tail

variable {I : Type u} [Preorder I] (k : I)

/-- The tail `{i | k ≤ i}` of a preorder. -/
abbrev Tail : Type u := {i : I // k ≤ i}

/-- The tail `{i | k ≤ i}` is nonempty: it contains `k`. -/
instance Tail.nonempty : Nonempty (Tail k) := ⟨⟨k, le_rfl⟩⟩

/-- The tail of a directed preorder is directed. -/
instance Tail.isDirected [IsDirected I (· ≤ ·)] : IsDirected (Tail k) (· ≤ ·) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- The tail `{i | k ≤ i}`, as a system of stages over `k` in the opposite category. -/
@[simps]
def tailToOver : (Tail k)ᵒᵈ ⥤ Over (op k) where
  obj i := Over.mk (homOfLE (OrderDual.ofDual i).2).op
  map {i j} f := Over.homMk
    (homOfLE (show (OrderDual.ofDual j).1 ≤ (OrderDual.ofDual i).1 from leOfHom f)).op
    (by apply Quiver.Hom.unop_inj; exact Subsingleton.elim _ _)

/-- The functor `tailToOver k` is full. -/
instance : (tailToOver k).Full where
  map_surjective {i j} f :=
    ⟨homOfLE (show (OrderDual.ofDual j).1 ≤ (OrderDual.ofDual i).1 from leOfHom f.left.unop),
      by ext1; apply Quiver.Hom.unop_inj; exact Subsingleton.elim _ _⟩

/-- The functor `tailToOver k` is faithful. -/
instance : (tailToOver k).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- For a directed set `I`, the tail `{i | k ≤ i}` is initial among the stages over `k` of
`Iᵒᵖ`. -/
instance [IsDirected I (· ≤ ·)] : (tailToOver k).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun d =>
    ⟨OrderDual.toDual ⟨d.left.unop, leOfHom d.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (by apply Quiver.Hom.unop_inj; exact Subsingleton.elim _ _)⟩⟩

end Tail

end AlgebraicGeometry.Space

end
