module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentedGroupoidRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureAffineChart
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureRealization
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# The étale chart `[U/R] ⟶ 𝒳` of a quasi-DM stack with separated diagonal

The second step of the proofs of **Stacks 0DU3** and **Stacks 0DU4**. Let `U ⟶ 𝒳` be a chart of
an algebraic stack by an affine scheme which is surjective, flat, locally of finite presentation
and locally quasi-finite, and let `𝒳` be quasi-DM with separated diagonal. Then
`R = U ×_𝒳 U` is a scheme (**Stacks 03XX**), `(U, R, s, t, c)` is a groupoid scheme with flat,
locally finitely presented, separated source and target, the source locally quasi-finite, and
`[U/R] ⟶ 𝒳` is an equivalence (**Stacks 04WY**). This file records the result as a
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`: the groupoid scheme, given by
objects and morphisms of the site, together with a 1-morphism from the small model of its
quotient stack which is representable by algebraic spaces, étale and fully faithful.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.exists_representedRealizationHom`: the groupoid of
  Stacks 04T4 (4) of a chart, whose source and target are Yoneda images, is the realization of a
  groupoid scheme of the site, through a morphism which is the identity on object and arrow
  spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The groupoid of Stacks 04T4 (4) is a realized groupoid scheme.** A groupoid in algebraic
spaces built by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.ofComposable` on the representable
algebraic spaces of two objects `U`, `R` of the site receives a morphism from the realization of
a groupoid scheme of the site with source and target morphisms `s, t : R ⟶ U` whose Yoneda images
are the given source and target; the morphism is the identity on object and arrow spaces, and its
evaluated functors are full and faithful. -/
theorem exists_representedRealizationHom {U R : BigFppfOver B S hS}
    (σ τ : yoneda.obj R ⟶ yoneda.obj U)
    (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R) σ τ ⟶ yoneda.obj R)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (σ.app T) (τ.app T)
      fun p => c.app T p)) :
    ∃ (s t : R ⟶ U) (c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
        (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
      (hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
        ((yoneda.map t).app T) fun p => c'.app T p)),
      yoneda.map s = σ ∧ yoneda.map t = τ ∧
        ∃ φ : GroupoidInAlgebraicSpaces.Hom (Space.representedRealization s t c' hG')
            (GroupoidInAlgebraicSpaces.ofComposable
              (schemeSpace U)
              (schemeSpace R)
              (ObjectProperty.homMk σ) (ObjectProperty.homMk τ) c hG),
          φ.toGroupoidHom.mapObjects = 𝟙 (yoneda.obj U) ∧
            (∀ T, (φ.toGroupoidHom.evaluation T).Full) ∧
              ∀ T, (φ.toGroupoidHom.evaluation T).Faithful := by
  obtain ⟨s, rfl⟩ := yoneda.map_surjective σ
  obtain ⟨t, rfl⟩ := yoneda.map_surjective τ
  exact ⟨s, t, c, hG, rfl, rfl, Space.representedRealizationHom s t c hG, rfl,
    Space.representedRealizationHom_evaluation_full s t c hG,
    Space.representedRealizationHom_evaluation_faithful s t c hG⟩

/-! ### Separatedness of the source and the target -/

section Separated

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

/-- The structure morphism to the base of the representable algebraic space of an affine object of
the site is separated. -/
theorem isSeparated_objectsToBase_pointGroupoid
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    Space.IsSeparated B S hS
      (SelfIntersection.pointGroupoid B S hS U f Rsp eR).objectsToBase.hom := by
  obtain ⟨a, ha⟩ := yoneda.map_surjective
    (SelfIntersection.pointGroupoid B S hS U f Rsp eR).objectsToBase.hom
  rw [← ha]
  refine (Space.isSeparated_yoneda_map_iff B S hS a).2 ?_
  have : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map a ≫
      terminal.from ((BigFppfOver.toScheme B S hS).obj (Space.baseTerminal B S hS))) := by
    rw [show (BigFppfOver.toScheme B S hS).map a ≫
        terminal.from ((BigFppfOver.toScheme B S hS).obj (Space.baseTerminal B S hS)) =
        terminal.from ((BigFppfOver.toScheme B S hS).obj U) from terminal.hom_ext _ _]
    infer_instance
  exact _root_.AlgebraicGeometry.IsSeparated.of_comp _
    (terminal.from ((BigFppfOver.toScheme B S hS).obj (Space.baseTerminal B S hS)))

/-- **The source of the groupoid of a chart by an affine scheme is separated** when the diagonal
of the stack over `S` is: it is the pair `(t, s)`, a base change of the diagonal, followed by the
second projection `U ×_S U ⟶ U`, a base change of the separated `U ⟶ S`. -/
theorem isSeparated_source_pointGroupoid (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    Space.IsSeparated B S hS (SelfIntersection.pointGroupoid B S hS U f Rsp eR).source.hom := by
  let G := SelfIntersection.pointGroupoid B S hS U f Rsp eR
  rw [show G.source.hom = (GroupoidInAlgebraicSpaces.sourceTarget G).hom ≫
      pullback.snd G.objectsToBase.hom G.objectsToBase.hom from (pullback.lift_snd _ _ _).symm]
  exact Space.isSeparated_comp B S hS _ _
    (SelfIntersection.isSeparated_sourceTarget_pointGroupoid B S hS U f Rsp eR hΔ)
    (Space.isSeparated_pullback B S hS _ _ (isSeparated_objectsToBase_pointGroupoid f Rsp eR hU))

/-- **The target of the groupoid of a chart by an affine scheme is separated** when the diagonal
of the stack over `S` is. -/
theorem isSeparated_target_pointGroupoid (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    Space.IsSeparated B S hS (SelfIntersection.pointGroupoid B S hS U f Rsp eR).target.hom := by
  let G := SelfIntersection.pointGroupoid B S hS U f Rsp eR
  have hfst : Space.IsSeparated B S hS (pullback.fst G.objectsToBase.hom G.objectsToBase.hom) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    exact Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isIso B S hS _)
      (Space.isSeparated_pullback B S hS _ _ (isSeparated_objectsToBase_pointGroupoid f Rsp eR hU))
  rw [show G.target.hom = (GroupoidInAlgebraicSpaces.sourceTarget G).hom ≫
      pullback.fst G.objectsToBase.hom G.objectsToBase.hom from (pullback.lift_fst _ _ _).symm]
  exact Space.isSeparated_comp B S hS _ _
    (SelfIntersection.isSeparated_sourceTarget_pointGroupoid B S hS U f Rsp eR hΔ) hfst

end Separated

/-! ### The chart groupoid -/

/-- **A quotient chart of an algebraic stack**: a groupoid scheme `(U, R, s, t, c)` of the site —
`U` affine, `s` and `t` flat, locally of finite presentation, separated and locally of finite
type, `s` locally quasi-finite — together with a 1-morphism `[U/R] ⟶ 𝒳` from the small model of
the quotient stack of its realization which is representable by algebraic spaces, étale in the
sense of Stacks 04XB, and fully faithful. -/
structure ChartGroupoid (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The object scheme. -/
  U : BigFppfOver B S hS
  /-- The arrow scheme. -/
  V : BigFppfOver B S hS
  /-- The source. -/
  s : V ⟶ U
  /-- The target. -/
  t : V ⟶ U
  /-- The composition law. -/
  c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s) (yoneda.map t) ⟶
    yoneda.obj V
  /-- The groupoid axioms, pointwise. -/
  hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p)
  /-- The object scheme is affine. -/
  isAffine_U : IsAffine ((BigFppfOver.toScheme B S hS).obj U)
  /-- The source is flat. -/
  flat_s : Flat ((BigFppfOver.toScheme B S hS).map s)
  /-- The source is locally of finite presentation. -/
  lfp_s : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map s)
  /-- The target is flat. -/
  flat_t : Flat ((BigFppfOver.toScheme B S hS).map t)
  /-- The target is locally of finite presentation. -/
  lfp_t : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t)
  /-- The source is separated. -/
  separated_s : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map s)
  /-- The target is separated. -/
  separated_t : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map t)
  /-- The source is locally of finite type. -/
  lft_s : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map s)
  /-- The target is locally of finite type. -/
  lft_t : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t)
  /-- The source is locally quasi-finite. -/
  lqf_s : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map s)
  /-- The quotient stack of the realization is algebraic. -/
  alg : IsAlgebraicStack.{u, w} B S hS (quotientStack (Space.representedRealization s t c hG))
  /-- The 1-morphism to the stack. -/
  map : smallAlgebraicQuotientStack.{u, w} (Space.representedRealization s t c hG) alg ⟶ 𝒳
  /-- The 1-morphism is étale. -/
  etale : IsRelativelyEtale B S hS map.hom
  /-- The 1-morphism is full. -/
  full : (CatFiberedInGroupoids.homFunctor map.hom).Full
  /-- The 1-morphism is faithful. -/
  faithful : (CatFiberedInGroupoids.homFunctor map.hom).Faithful

namespace ChartGroupoid

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : ChartGroupoid B S hS 𝒳)

/-- The groupoid scheme of a quotient chart. -/
noncomputable abbrev groupoid : Stacks.Groupoids.GroupoidScheme S :=
  Space.representedGroupoidScheme K.s K.t K.c K.hG

/-- The realization of the groupoid scheme of a quotient chart. -/
noncomputable abbrev realization :
    GroupoidInAlgebraicSpaces B S hS (Stacks.Groupoids.GroupoidScheme.realizationBase B hS) :=
  Space.representedRealization K.s K.t K.c K.hG

/-- The small model of the quotient stack of a quotient chart, as an algebraic stack. -/
noncomputable abbrev quotient : AlgebraicStacks.{u, w} B S hS :=
  smallAlgebraicQuotientStack.{u, w} K.realization K.alg

/-- The point of the quotient stack of a quotient chart attached to a point of its object
space. -/
noncomputable def point (z : Space.points B S hS (yoneda.obj K.U)) :
    AlgebraicStacks.points B S hS K.quotient :=
  smallQuotientStackPoint K.realization K.alg z

end ChartGroupoid

/-- **Stacks 046S, the direction used here.** A morphism of groupoids in algebraic spaces whose
evaluated functors are full and faithful induces a fully faithful 1-morphism of quotient
stacks. -/
theorem nonempty_fullyFaithful_quotientStackMap {A : AlgebraicSpaces B S hS}
    {G H : GroupoidInAlgebraicSpaces B S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful) :
    Nonempty (quotientStackMap φ).toFunctor.FullyFaithful :=
  (fullyFaithful_quotientStackMap_iff_isPullback φ).2
    (isPullback_mapArrows_of_evaluation_fullyFaithful φ.toGroupoidHom fun T =>
      have := hfull T
      have := hfaith T
      Functor.FullyFaithful.ofFullyFaithful _)

variable {B S hS} in
/-- **The points of the chart and of the quotient chart.** Every point of `|U|` is sent by the
chart to the image of the corresponding point of the quotient stack. -/
theorem pointsMap_chart_point {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : BigFppfOver B S hS}
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories ((schemeSpace U :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom).val.p
      (presheafOfCategories ((schemeSpace V :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    {s t : V ⟶ U}
    {c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s) (yoneda.map t) ⟶
      yoneda.obj V}
    {hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
      ((yoneda.map t).app T) fun p => c'.app T p)}
    (φP : GroupoidInAlgebraicSpaces.Hom (Space.representedRealization s t c' hG')
      (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).groupoid)
    (hφobj : φP.toGroupoidHom.mapObjects = 𝟙 (yoneda.obj U))
    (alg : IsAlgebraicStack.{u, w} B S hS (quotientStack (Space.representedRealization s t c' hG')))
    (algP : IsAlgebraicStack.{u, w} B S hS
      (quotientStack (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).groupoid))
    (p : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :
    ∃ z, AlgebraicStacks.pointsMap B S hS
        (smallQuotientStackMap.{u, w} φP alg algP ≫ smallQuotientStackLift.{u, w}
          (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).groupoid algP
          (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).canonicalMap)
        (smallQuotientStackPoint _ alg z) = AlgebraicStacks.pointsMap B S hS f p := by
  let P := SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property
  let can := smallQuotientStackLift.{u, w} P.groupoid algP P.canonicalMap
  let eUb : (schemeStack.{u, w} B S hS U).val.val ⥤ᵇ
      (fibredCategory B S hS (yoneda.obj U)).val :=
    ⟨P.sourcePresentation.hom.functor, P.sourcePresentation.hom.w⟩
  let y := pointsMap B S hS _ (schemeStack.{u, w} B S hS U).val.property
    (fibredCategory B S hS (yoneda.obj U)).property eUb p
  obtain ⟨z, hz⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U)).2 y
  refine ⟨z, ?_⟩
  let X : (quotientStack P.groupoid) ⥤ᵇ 𝒳.val.val := P.canonicalMap
  let η : BasedNatTrans (eUb.comp (BasedFunctor.comp (quotientStackProjection P.groupoid) X))
      f.hom.hom :=
    { toNatTrans := P.extends_f.1.hom
      isHomLift' := fun a => P.extends_f.2 a }
  have hR : AlgebraicStacks.pointsMap B S hS f p =
      pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
        (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property
        (BasedFunctor.comp (quotientStackProjection P.groupoid) X) y := by
    change pointsMap B S hS _ _ _ f.hom.hom p = _
    rw [← pointsMap_eq_of_basedNatTrans B S hS _ _ _ η, ← pointsMap_comp]
  have hid : Space.pointsMap B S hS
      (Space.representedRealization s t c' hG').toGroupoidInFunctors.objects
      φP.toGroupoidHom.mapObjects z = z := by
    rw [hφobj]
    exact congrFun (Space.pointsMap_id B S hS (F := yoneda.obj U)) z
  refine (congrFun (AlgebraicStacks.pointsMap_comp B S hS
    (smallQuotientStackMap.{u, w} φP alg algP) can) _).trans ?_
  rw [Function.comp_apply, pointsMap_smallQuotientStackMap_point.{u, w} φP alg algP z, hR, ← hz]
  exact (pointsMap_smallQuotientStackLift_point.{u, w} P.groupoid algP P.canonicalMap
    (Space.pointsMap B S hS _ φP.toGroupoidHom.mapObjects z)).trans
    (congrArg (fun w => pointsMap B S hS _ _ _
      (BasedFunctor.comp (quotientStackProjection P.groupoid) X)
      (spacePointMap B S hS _ _ (BasedFunctor.id _) w)) hid)

variable {B S hS} in
/-- **A comparison of groupoids followed by an equivalence is étale.** A morphism of groupoids in
algebraic spaces with full and faithful evaluated functors and flat, locally finitely presented
object map, into a groupoid with flat, locally finitely presented source, followed by the lift of
an equivalence from the quotient stack of the target, is étale. -/
theorem isRelativelyEtale_smallQuotientStackMap_comp_lift {A : AlgebraicSpaces B S hS}
    {G H : GroupoidInAlgebraicSpaces B S hS A} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful)
    (hflat : Space.IsFlat B S hS φ.toGroupoidHom.mapObjects)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS φ.toGroupoidHom.mapObjects)
    (hsflat : Space.IsFlat B S hS H.source.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation B S hS H.source.hom)
    (hG : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hH : IsAlgebraicStack.{u, w} B S hS (quotientStack H))
    (X : quotientStack H ⥤ᵇ 𝒳.val.val) (hX : X.toFunctor.IsEquivalence) :
    IsRelativelyEtale B S hS
      (smallQuotientStackMap.{u, w} φ hG hH ≫ smallQuotientStackLift.{u, w} H hH X).hom := by
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful.{u, w} φ hG hH
    (faithful_quotientStackMap_of_evaluation_faithful φ hfaith)
  exact isRelativelyEtale_comp_of_isEquivalence B S hS _ _
    (isEquivalence_smallQuotientStackLift.{u, w} H hH X)
    (isRelativelyEtale_smallQuotientStackMap.{u, w} φ hG hH hrep
      (hasRelativeProperty_etale_quotientStackMap_of_full_of_faithful φ hfull hfaith hflat hlfp
        hsflat hslfp hrep))

variable {B S hS} in
/-- **A comparison of groupoids followed by an equivalence is fully faithful** when the evaluated
functors of the comparison are full and faithful. -/
theorem nonempty_fullyFaithful_smallQuotientStackMap_comp_lift {A : AlgebraicSpaces B S hS}
    {G H : GroupoidInAlgebraicSpaces B S hS A} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful)
    (hG : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hH : IsAlgebraicStack.{u, w} B S hS (quotientStack H))
    (X : quotientStack H ⥤ᵇ 𝒳.val.val) (hX : X.toFunctor.IsEquivalence) :
    Nonempty (CatFiberedInGroupoids.homFunctor
      (smallQuotientStackMap.{u, w} φ hG hH ≫
        smallQuotientStackLift.{u, w} H hH X).hom).FullyFaithful := by
  have := isEquivalence_smallQuotientStackLift.{u, w} H hH X
  obtain ⟨hFF⟩ := nonempty_fullyFaithful_smallQuotientStackMap.{u, w} φ hG hH
    (nonempty_fullyFaithful_quotientStackMap B S hS φ hfull hfaith)
  exact ⟨hFF.comp (Functor.FullyFaithful.ofFullyFaithful
    (CatFiberedInGroupoids.homFunctor (smallQuotientStackLift.{u, w} H hH X).hom))⟩

variable {B S hS} in
/-- **The quotient chart of a groupoid scheme realizing the self-intersection.** Let `(U, V, s, t)`
be a groupoid scheme of the site whose realization maps to the groupoid `U ×_𝒳 U` of a chart
`f : U ⟶ 𝒳` by a morphism which is the identity on objects with full and faithful evaluated
functors, the source and target of `U ×_𝒳 U` being flat, locally of finite presentation and
separated and the source locally quasi-finite, and let `[U/R] ⟶ 𝒳` be an equivalence. Then this
gives a quotient chart of `𝒳` through which every point of the image of `f` factors. -/
theorem exists_chartGroupoid_of_representedRealizationHom {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U V : BigFppfOver B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories ((schemeSpace U :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom).val.p
      (presheafOfCategories ((schemeSpace V :
        AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {s t : V ⟶ U}
    {c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s) (yoneda.map t) ⟶
      yoneda.obj V}
    {hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
      ((yoneda.map t).app T) fun p => c'.app T p)}
    (hs : yoneda.map s = SelfIntersection.relationSourceMap eU eR)
    (ht : yoneda.map t = SelfIntersection.relationTargetMap eU eR)
    (φ : GroupoidInAlgebraicSpaces.Hom (Space.representedRealization s t c' hG')
      (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).groupoid)
    (hφobj : φ.toGroupoidHom.mapObjects = 𝟙 (yoneda.obj U))
    (hφfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hφfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful)
    (hsFl : Space.IsFlat B S hS (SelfIntersection.relationSourceMap eU eR))
    (htFl : Space.IsFlat B S hS (SelfIntersection.relationTargetMap eU eR))
    (hsL : Space.IsLocallyOfFinitePresentation B S hS (SelfIntersection.relationSourceMap eU eR))
    (htL : Space.IsLocallyOfFinitePresentation B S hS (SelfIntersection.relationTargetMap eU eR))
    (hsQ : Space.IsLocallyQuasiFinite B S hS (SelfIntersection.relationSourceMap eU eR))
    (hsSep : Space.IsSeparated B S hS (SelfIntersection.relationSourceMap eU eR))
    (htSep : Space.IsSeparated B S hS (SelfIntersection.relationTargetMap eU eR))
    (hcan : (SelfIntersection.selfIntersectionPresentation eU eR
      𝒳.property).canonicalMap.toFunctor.IsEquivalence) :
    ∃ K : ChartGroupoid B S hS 𝒳, ∀ p : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U),
      ∃ z, AlgebraicStacks.pointsMap B S hS K.map (K.point z) =
        AlgebraicStacks.pointsMap B S hS f p := by
  let P := SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property
  have key {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocalOnSourceAndTarget P) {k : V ⟶ U}
      {r : yoneda.obj V ⟶ yoneda.obj U} (hk : yoneda.map k = r)
      (h : Space.HoldsOnEveryEtaleChart B S hS P r) : P ((BigFppfOver.toScheme B S hS).map k) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP k).1 (hk ▸ h)
  have flat_s := key Flat.isEtaleLocalOnSourceAndTarget hs hsFl
  have flat_t := key Flat.isEtaleLocalOnSourceAndTarget ht htFl
  have lfp_s := key LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hs hsL
  have lfp_t := key LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ht htL
  obtain ⟨lft_s, lqf_s⟩ :=
    key isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite hs hsQ
  have lft_t : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t) := inferInstance
  have separated_s := (Space.isSeparated_yoneda_map_iff B S hS s).1 (by rwa [hs])
  have separated_t := (Space.isSeparated_yoneda_map_iff B S hS t).1 (by rwa [ht])
  -- algebraicity of the two quotient stacks
  have : Flat (Space.representedGroupoidScheme s t c' hG').source.left := flat_s
  have : Flat (Space.representedGroupoidScheme s t c' hG').target.left := flat_t
  have : LocallyOfFinitePresentation (Space.representedGroupoidScheme s t c' hG').source.left :=
    lfp_s
  have : LocallyOfFinitePresentation (Space.representedGroupoidScheme s t c' hG').target.left :=
    lfp_t
  have alg :
      IsAlgebraicStack.{u, w} B S hS (quotientStack (Space.representedRealization s t c' hG')) :=
    Stacks.Groupoids.GroupoidScheme.isAlgebraicStack_quotientStack_realization.{u, w} B hS _ _ _
  have algP : IsAlgebraicStack.{u, w} B S hS (quotientStack P.groupoid) :=
    isAlgebraicStack_quotientStack_of_flat P.groupoid hsFl htFl hsL htL
  -- the comparison 1-morphism `[U/R] ⟶ [U/R]` and the canonical 1-morphism `[U/R] ⟶ 𝒳`
  have hobj (Q : MorphismProperty Scheme.{u})
      (hQ : (@Etale.{u} : MorphismProperty Scheme.{u}) ≤ Q) :
      Space.HoldsOnEveryEtaleChart B S hS Q φ.toGroupoidHom.mapObjects := by
    rw [hφobj]
    exact Space.holdsOnEveryEtaleChart_id_presheaf B S hS Q hQ _
  obtain ⟨hFF⟩ := nonempty_fullyFaithful_smallQuotientStackMap_comp_lift φ hφfull hφfaith alg algP
    P.canonicalMap hcan
  exact ⟨{
      U := U, V := V, s := s, t := t, c := c', hG := hG', isAffine_U := hU,
      flat_s := flat_s, lfp_s := lfp_s, flat_t := flat_t, lfp_t := lfp_t,
      separated_s := separated_s, separated_t := separated_t, lft_s := lft_s, lft_t := lft_t,
      lqf_s := lqf_s, alg := alg,
      map := smallQuotientStackMap.{u, w} φ alg algP ≫
        smallQuotientStackLift.{u, w} P.groupoid algP P.canonicalMap,
      etale := isRelativelyEtale_smallQuotientStackMap_comp_lift φ hφfull hφfaith
        (hobj _ fun _ _ _ hg => have := hg; inferInstance)
        (hobj _ fun _ _ _ hg => have := hg; inferInstance) hsFl hsL alg algP P.canonicalMap
        hcan,
      full := hFF.full, faithful := hFF.faithful }, pointsMap_chart_point f eU eR φ hφobj alg algP⟩

variable {B S hS} in
/-- **The quotient chart of a surjective chart.** Let `f : U ⟶ 𝒳` be a 1-morphism from an affine
object of the site to an algebraic stack which is quasi-DM over `S` with separated diagonal, and
let `f` be surjective, flat, locally of finite presentation and locally quasi-finite. Then the
groupoid `R = U ×_𝒳 U` is a groupoid scheme of the site (Stacks 03XX) and `[U/R] ⟶ 𝒳` is an
equivalence (Stacks 04WY), which gives a quotient chart of `𝒳` through which every point of the
image of `f` factors. -/
theorem exists_chartGroupoid_of_isSurjective {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hlqf : IsLocallyQuasiFinite B S hS f.hom) (hQ : IsQuasiDMOver B S hS 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    ∃ K : ChartGroupoid B S hS 𝒳, ∀ p : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U),
      ∃ z, AlgebraicStacks.pointsMap B S hS K.map (K.point z) =
        AlgebraicStacks.pointsMap B S hS f p := by
  classical
  obtain ⟨V, ⟨eR₀⟩⟩ := exists_representation_relation f hQ hΔ
  let Uₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let Rₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (Uₛ.obj ⋙ typeToCat)).p := representedChart B S hS U
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p := eR₀
  have hrep := isRepresentableByAlgebraicSpaces_schemeStack_hom B S hS f
  have hflatP := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS U).property
    𝒳.property f.hom hrep).1 hflat
  have hlfpP := (hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (schemeStack.{u, w} B S hS U).property 𝒳.property f.hom hrep).1 hlfp
  have hsurjP := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).1 hsurj
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR 𝒳.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  obtain ⟨s, t, c', hG', hs, ht, φ, hφobj, hφfull, hφfaith⟩ :=
    exists_representedRealizationHom B S hS (SelfIntersection.relationSourceMap eU eR)
      (SelfIntersection.relationTargetMap eU eR)
      (SelfIntersection.compositionLaw eU eR (SelfIntersection.isFiberedInSetoids_source eU))
      (SelfIntersection.nonempty_pointwiseGroupoid eU eR
        (SelfIntersection.isFiberedInSetoids_source eU))
  -- the source and the target of the groupoid
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget B S hS
    (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom Uₛ Rₛ eU eR hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget B S hS
      (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom Uₛ Rₛ eU eR hrep hlfpP
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact exists_chartGroupoid_of_representedRealizationHom f eU eR hU hs ht φ hφobj hφfull hφfaith
    hsFl htFl hsL htL
    (SelfIntersection.prop_relationSource B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom Uₛ
      Rₛ eU eR (Space.locallyQuasiFiniteProperty B S hS) hrep hlqf)
    (isSeparated_source_pointGroupoid f Rₛ eR hU hΔ)
    (isSeparated_target_pointGroupoid f Rₛ eR hU hΔ)
    (CategoryTheory.Equivalence.mk _ E.inv E.unitIso.symm E.counitIso).isEquivalence_functor

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
