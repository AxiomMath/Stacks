module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperDescent
public import StacksFrontier.CategoryTheory.Filtered.CofilteredDirectedInitial

/-!
# Flatness and proper support descend along the system `X ×_Y T_k`, and Stacks 08KD

In Situation 08KB let `T = lim T_j` be a cofiltered limit of affine schemes of the big fppf site,
taken in schemes, and let `g : T_i ⟶ Y` be a morphism from a stage. A finitely presented module
`Q` on `X_{T_k} = X ×_Y T_k` whose inverse image to `X_T` is flat over `T` with support proper
over `T` is already flat over `T_j` with support proper over `T_j` after inverse image to some
later stage `X_{T_j}`. This is
`AlgebraicGeometry.Space.CoherentSituation.FlatProperSupportDescends`, the one hypothesis of
`CoherentSituation.isLimitPreserving_coherent_of_flatProperSupportDescends`, and it is Stacks 08K0
and Stacks 08K2 for the system of base changes `X_{T_j} ⟶ T_j`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.stageSituation`: the system of base changes above a
  stage, reindexed by a directed set along an initial functor, as a situation of Stacks 084W
  (`AlgebraicGeometry.Space.MorphismDescentSituation`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.flatProperSupportDescends`: the descent of flatness
  and of proper support along the system of base changes, for every cofiltered system of affine
  schemes of the site whose limit lies in the site.
* `AlgebraicGeometry.Space.CoherentSituation.isLimitPreserving_coherent`: **Stacks 08KD**,
  `Coh_{X/Y}` is limit preserving when `Y` is locally of finite presentation over `S`, at index
  categories in the scheme universe.

## Implementation notes

The descent results of Stacks 08K0 and Stacks 08K2, in the namespace
`AlgebraicGeometry.Space.MorphismDescentSituation` the declarations
`C1573.exists_isFlatOver_mapAt_of_siteContainsBaseChangeLimits` and
`exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits`, are stated for a
directed inverse system with its limit taken in presheaves, under the chapter's convention of
Section 70.2 (tag 07SD). The cofiltered system of stages above `i` is reindexed by a directed set
along an initial functor (Stacks 0032, `CategoryTheory.IsCofiltered.exists_directed_initial`); the
reindexed system of test schemes has the limit `T` in presheaves and satisfies the convention, both
by `StacksFrontier/AlgebraicGeometry/Quot/CoherentStackLimitSystem.lean`.

The situation of Stacks 084W has base `B_a = T_a`, distinguished source `X₀ = X_{T_{a₀}}` and
target `Y₀ = T_{a₀}`, so its base changes `T_a ×_{T_{a₀}} X_{T_{a₀}}` and
`T ×_{T_{a₀}} X_{T_{a₀}}` are only isomorphic to `X_{T_a}` and `X_T`. The two sides are compared
through cartesian squares whose horizontal morphisms are these isomorphisms, along which flatness
(Stacks 05VW) and properness of the support (Stacks 0CZJ) are carried by
`AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation`. The comparison
isomorphisms are kept opaque: they enter only through their two projections.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison)

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-! ### Flatness and proper support carried along a cartesian square -/

section Transport

variable {X Y X' Y' Z : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {gg : Y' ⟶ Y}

/-- The proper support over the target of a module on `X`, the second condition beyond finite
presentation on an object of `Coh_{X/Y}`, read for an arbitrary morphism `f : X ⟶ Y`. -/
abbrev HasProperSupportOver (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (hp : IsLocallyOfFiniteType B S hS f.hom)
    (hU : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M))),
    IsProperOver B S hS X.2 Y.2 f.hom hp
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) hU

/-- Proper support over the target is unchanged by an isomorphism of modules. -/
theorem HasProperSupportOver.of_iso {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N)
    (h : HasProperSupportOver f M) : HasProperSupportOver f N := by
  obtain ⟨hp, hU, hpr⟩ := h
  have heq := supportOfSheaf_eq_of_iso B S hS X e
  have key : ∀ (T T' : Set (points B S hS X.1)) (_ : T = T') (hT : IsClosed T)
      (hT' : IsClosed T'), IsProperOver B S hS X.2 Y.2 f.hom hp T hT →
      IsProperOver B S hS X.2 Y.2 f.hom hp T' hT' := by
    rintro T _ rfl hT hT' h
    exact h
  exact ⟨hp, heq ▸ hU, key _ _ heq hU _ hpr⟩

/-- **Stacks 0CZJ**, for a module of finite presentation: proper support over the target is
carried along a cartesian square to the inverse image along its top morphism. -/
theorem HasProperSupportOver.of_isPullback (sq : IsPullback g' f' f gg)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsFinitePresentationOnSite)
    (h : HasProperSupportOver f M) :
    HasProperSupportOver f' ((modulePullback B S hS g').obj M) := by
  obtain ⟨hp, hU, hpr⟩ := h
  have := hM
  obtain ⟨hU', hpr'⟩ := (modulePullbackStabilityOfFinitePresentation B S hS).properSupport sq hp
    M inferInstance inferInstance hU hpr
  exact ⟨_, hU', hpr'⟩

/-- Flatness over the target, carried along a cartesian square to the inverse image of a module
read through a factorization `g' ≫ p = q`. -/
theorem isFlatOver_of_isPullback_of_comp (sq : IsPullback g' f' f gg)
    (Q : Modules.{u, u} B S hS Z.1 Z.2) (hQ : Q.IsFinitePresentationOnSite) (p : X ⟶ Z)
    (q : X' ⟶ Z) (hq : g' ≫ p = q)
    (h : IsFlatOver B S hS X.2 f.hom ((modulePullback B S hS p).obj Q)) :
    IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS q).obj Q) :=
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  IsFlatOver.of_iso B S hS X'.2 (pullbackComparison B S hS g' p q hq Q).symm
    (hst.flat sq _ (hst.finitePresentation p Q hQ) h)

/-- Proper support over the target, carried along a cartesian square to the inverse image of a
module read through a factorization `g' ≫ p = q`. -/
theorem HasProperSupportOver.of_isPullback_of_comp (sq : IsPullback g' f' f gg)
    (Q : Modules.{u, u} B S hS Z.1 Z.2) (hQ : Q.IsFinitePresentationOnSite) (p : X ⟶ Z)
    (q : X' ⟶ Z) (hq : g' ≫ p = q)
    (h : HasProperSupportOver f ((modulePullback B S hS p).obj Q)) :
    HasProperSupportOver f' ((modulePullback B S hS q).obj Q) :=
  (h.of_isPullback sq ((modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation
    p Q hQ)).of_iso (pullbackComparison B S hS g' p q hq Q).symm

end Transport

/-! ### The system of base changes above a stage, as a situation of Stacks 084W -/

section Stage

variable {I : Type u} [Category.{u} I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E) {i : I}
  (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
  {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] (F : αᵒᵖ ⥤ Over i)

/-- The cone of representable presheaves of the test schemes `T_a` with vertex the limit `T`,
reindexed along `F`. -/
abbrev stageLimitCone :
    Cone ((F ⋙ D.stageTestSystem E g) ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda) :=
  (CostructuredArrow.proj _ D.Y ⋙ yoneda).mapCone ((D.stageTestCone E c g).whisker F)

/-- The limit `T` is the limit of the reindexed test schemes, as presheaves. -/
noncomputable def isLimit_stageLimitCone [IsCofiltered I] [F.Initial]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    IsLimit (D.stageLimitCone E c g F) :=
  IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv F _).symm
    (D.isLimit_stageTestCone E c g hc)) (Functor.mapConeWhisker _).symm

/-- The limit of the reindexed test schemes, in presheaves, is the limit `T`. -/
noncomputable def stageLimitIso [IsCofiltered I] [F.Initial]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    limit ((F ⋙ D.stageTestSystem E g) ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda) ≅
      (D.stageLimitCone E c g F).pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (D.isLimit_stageLimitCone E c g F hc)

omit [IsDirected α fun x1 x2 ↦ x1 ≤ x2] in
/-- The limit isomorphism lies over the projections to the stages. -/
@[reassoc (attr := simp)]
theorem stageLimitIso_hom_comp [IsCofiltered I] [F.Initial]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (a : αᵒᵖ) :
    (D.stageLimitIso E c g F hc).hom ≫ (D.stageLimitCone E c g F).π.app a =
      limit.π ((F ⋙ D.stageTestSystem E g) ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda) a :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ a

/-- **The system of base changes above a stage as a situation of Stacks 084W**: the base is the
system of test schemes `T_a`, reindexed along `F`, the distinguished stage is `a₀`, and the
morphism is the projection `X_{T_{a₀}} ⟶ T_{a₀}` over `T_{a₀}`. -/
def stageSituation [IsCofiltered I] [F.Initial]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hZ : B.Contains (⊤_ Scheme.{u})) (a₀ : α) : MorphismDescentSituation B S hS hZ α where
  base := (F ⋙ D.stageTestSystem E g) ⋙ CostructuredArrow.proj _ D.Y ⋙ yoneda
  base_isAlgebraicSpace _ := isAlgebraicSpace_yoneda B S hS _
  transition_affine {a b} m := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj
          ((F ⋙ D.stageTestSystem E g).obj a))) := (E.obj _).property
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj
          ((F ⋙ D.stageTestSystem E g).obj b))) := (E.obj _).property
    exact isAffineHom_yoneda_map B S hS _
  limit_isAlgebraicSpace :=
    (isAlgebraicSpace_yoneda B S hS _).of_iso (D.stageLimitIso E c g F hc).symm
  initial := a₀
  source₀ := (D.space ((D.stageTestSystem E g).obj (F.obj (op a₀)))).1
  target₀ := yoneda.obj ((D.stageTestSystem E g).obj (F.obj (op a₀))).left
  sourceToBase := (D.projection ((D.stageTestSystem E g).obj (F.obj (op a₀)))).hom
  targetToBase := 𝟙 _
  map₀ := (D.projection ((D.stageTestSystem E g).obj (F.obj (op a₀)))).hom
  map₀_over := Category.comp_id _
  source₀_isAlgebraicSpace := (D.space _).2
  target₀_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  base₀_quasiCompact := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (E.obj _).property
  base₀_quasiSeparated := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj
          ((F ⋙ D.stageTestSystem E g).obj (op a₀)))) := (E.obj _).property
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((D.stageTestSystem E g).obj (F.obj (op a₀))).left) := (E.obj _).property
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩
  source₀_quasiCompact := D.isQuasiCompactSpace_space _ (E.obj _).property
  source₀_quasiSeparated := D.isAbsolutelyQuasiSeparated_space hZ _ (E.obj _).property
  target₀_quasiCompact := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (E.obj _).property
  target₀_quasiSeparated := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj
          ((F ⋙ D.stageTestSystem E g).obj (op a₀)))) := (E.obj _).property
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((D.stageTestSystem E g).obj (F.obj (op a₀))).left) := (E.obj _).property
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
      ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩

variable [IsCofiltered I] [F.Initial] (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
  (hZ : B.Contains (⊤_ Scheme.{u})) (a₀ : α)

/-- **The system of test schemes of the situation satisfies the chapter's convention (Stacks
07SD).** -/
theorem siteContainsBaseChangeLimits_stageSituation [Nonempty α] :
    SiteContainsBaseChangeLimits B S hS (D.stageSituation E c g F hc hZ a₀).base :=
  siteContainsBaseChangeLimits_affineYoneda ((F ⋙ Over.forget i) ⋙ E)
    (c.whisker (F ⋙ Over.forget i))
    ((Functor.Initial.isLimitWhiskerEquiv (F ⋙ Over.forget i) _).symm hc)

/-- The morphism of the situation over the distinguished stage is locally of finite
presentation, being a base change of `f`. -/
theorem isLocallyOfFinitePresentation_stageSituation_map₀ :
    IsLocallyOfFinitePresentation B S hS (D.stageSituation E c g F hc hZ a₀).map₀ :=
  (D.isFinitePresentation_projection _).1

/-- The base change of the target of the situation along a morphism to the distinguished stage
is the source of that morphism: the target is the distinguished stage itself. -/
noncomputable def stageTargetIso {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : W ⟶ (D.stageSituation E c g F hc hZ a₀).base.obj
      (op (D.stageSituation E c g F hc hZ a₀).initial)) :
    pullback t (D.stageSituation E c g F hc hZ a₀).targetToBase ≅ W :=
  (IsPullback.of_hasPullback t (D.stageSituation E c g F hc hZ a₀).targetToBase).isoIsPullback
    _ _ (IsPullback.of_id_fst :
      IsPullback (𝟙 _) t t (D.stageSituation E c g F hc hZ a₀).targetToBase)

/-- The comparison of the base change of the target with the source of the morphism is the
first projection. -/
theorem stageTargetIso_hom {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : W ⟶ (D.stageSituation E c g F hc hZ a₀).base.obj
      (op (D.stageSituation E c g F hc hZ a₀).initial)) :
    (D.stageTargetIso E c g F hc hZ a₀ t).hom =
      pullback.fst t (D.stageSituation E c g F hc hZ a₀).targetToBase :=
  (Category.comp_id _).symm.trans (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- **The base change at a stage of the situation is `X_{T_a}`.** The stage `X_{T_a}` of the
system of base changes, with its projection to `T_a`, maps by an isomorphism to the base change
`T_a ×_{T_{a₀}} X_{T_{a₀}}` of the situation, over an isomorphism of `T_a` with the target of
that base change; the square is cartesian, and the isomorphism lies over the morphism
`X_{T_a} ⟶ X_{T_{a₀}}` of base changes. -/
theorem exists_isPullback_stageSituation_mapAt (a : α)
    (ha : (D.stageSituation E c g F hc hZ a₀).initial ≤ a) :
    ∃ (φ : D.space ((D.stageTestSystem E g).obj (F.obj (op a))) ⟶
        ⟨(D.stageSituation E c g F hc hZ a₀).sourceAt a ha,
          (D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha⟩)
      (ψ : (schemeSpaceFunctor B S hS).obj ((D.stageTestSystem E g).obj (F.obj (op a))).left ⟶
        ⟨(D.stageSituation E c g F hc hZ a₀).targetAt a ha,
          (D.stageSituation E c g F hc hZ a₀).targetAt_isAlgebraicSpace a ha⟩),
      IsPullback φ (D.projection ((D.stageTestSystem E g).obj (F.obj (op a))))
        (ObjectProperty.homMk ((D.stageSituation E c g F hc hZ a₀).mapAt a ha)) ψ ∧
      φ.hom ≫ pullback.snd ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)
          (D.stageSituation E c g F hc hZ a₀).sourceToBase =
        (D.relativeMap ((D.stageTestSystem E g).map (F.map (homOfLE ha).op))).hom := by
  have P : IsPullback (D.projection ((D.stageTestSystem E g).obj (F.obj (op a)))).hom
      (D.relativeMap ((D.stageTestSystem E g).map (F.map (homOfLE ha).op))).hom
      ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)
      (D.stageSituation E c g F hc hZ a₀).sourceToBase :=
    ((isPullback_baseChangeMap D.f
      ((D.stageTestSystem E g).map (F.map (homOfLE ha).op))).map (ObjectProperty.ι _)).flip
  have hsq : IsPullback P.isoPullback.hom
      (D.projection ((D.stageTestSystem E g).obj (F.obj (op a)))).hom
      ((D.stageSituation E c g F hc hZ a₀).mapAt a ha)
      (D.stageTargetIso E c g F hc hZ a₀
        ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)).inv := by
    have : @IsIso ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) _
        ((schemeSpaceFunctor B S hS).obj ((D.stageTestSystem E g).obj (F.obj (op a))).left).1
        ((D.stageSituation E c g F hc hZ a₀).targetAt a ha)
        (D.stageTargetIso E c g F hc hZ a₀
          ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)).inv :=
      Iso.isIso_inv _
    refine IsPullback.of_horiz_isIso ⟨(Iso.eq_comp_inv _).2 ?_⟩
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (P.isoPullback.hom ≫ ·) ((congrArg
      ((D.stageSituation E c g F hc hZ a₀).mapAt a ha ≫ ·)
      (D.stageTargetIso_hom E c g F hc hZ a₀ _)).trans
      ((D.stageSituation E c g F hc hZ a₀).mapAt_fst a ha))).trans ?_
    exact IsPullback.isoPullback_hom_fst P
  refine ⟨ObjectProperty.homMk P.isoPullback.hom,
    ObjectProperty.homMk (D.stageTargetIso E c g F hc hZ a₀
      ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)).inv,
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) hsq, ?_⟩
  exact IsPullback.isoPullback_hom_snd P

/-- **The base change at the limit of the situation is `X_T`.** For a test scheme `T₀` over `Y`
whose representable presheaf is the limit of the system of test schemes, compatibly with a
morphism `γ : T₀ ⟶ T_{a₀}`, the base change `T ×_{T_{a₀}} X_{T_{a₀}}` of the situation maps by
an isomorphism to `X_{T₀}`, over an isomorphism of its target with `T₀`; the square is
cartesian, and the isomorphism lies over the morphism `X_{T₀} ⟶ X_{T_{a₀}}` of base changes. -/
theorem exists_isPullback_stageSituation_mapLimit (T₀ : SchemesOver D.Y)
    (γ : T₀ ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)))
    (ι : limit (D.stageSituation E c g F hc hZ a₀).base ≅ yoneda.obj T₀.left)
    (hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial)) :
    ∃ (φ : (⟨(D.stageSituation E c g F hc hZ a₀).sourceLimit,
          (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ D.space T₀)
      (ψ : (⟨(D.stageSituation E c g F hc hZ a₀).targetLimit,
          (D.stageSituation E c g F hc hZ a₀).targetLimit_isAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ (schemeSpaceFunctor B S hS).obj T₀.left),
      IsPullback φ (ObjectProperty.homMk (D.stageSituation E c g F hc hZ a₀).mapLimit)
        (D.projection T₀) ψ ∧
      φ.hom ≫ (D.relativeMap γ).hom =
        pullback.snd (limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
          (D.stageSituation E c g F hc hZ a₀).sourceToBase := by
  have P₂ : IsPullback (D.relativeMap γ).hom (D.projection T₀).hom
      (D.projection ((D.stageTestSystem E g).obj (F.obj (op a₀)))).hom (yoneda.map γ.left) :=
    (isPullback_baseChangeMap D.f γ).map (ObjectProperty.ι _)
  have P₁ : IsPullback (pullback.snd (limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
      (D.stageSituation E c g F hc hZ a₀).sourceToBase)
      (pullback.fst (limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
      (D.stageSituation E c g F hc hZ a₀).sourceToBase ≫ ι.hom)
      (D.projection ((D.stageTestSystem E g).obj (F.obj (op a₀)))).hom (yoneda.map γ.left) :=
    (IsPullback.of_hasPullback (limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
      (D.stageSituation E c g F hc hZ a₀).sourceToBase).flip.of_iso
      (Iso.refl _) (Iso.refl _) ι (Iso.refl _) (by simp) (by simp)
      (by simp only [Iso.refl_hom]; rfl)
      (by simp only [Iso.refl_hom]; exact (Category.comp_id _).trans hι.symm)
  have hsq : IsPullback (P₁.isoIsPullback _ _ P₂).hom (D.stageSituation E c g F hc hZ a₀).mapLimit
      (D.projection T₀).hom ((D.stageTargetIso E c g F hc hZ a₀
        (limit.π (D.stageSituation E c g F hc hZ a₀).base
          (op (D.stageSituation E c g F hc hZ a₀).initial))).hom ≫ ι.hom) := by
    have : @IsIso ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) _
        (D.stageSituation E c g F hc hZ a₀).targetLimit
        ((schemeSpaceFunctor B S hS).obj T₀.left).1
        ((D.stageTargetIso E c g F hc hZ a₀
          (limit.π (D.stageSituation E c g F hc hZ a₀).base
            (op (D.stageSituation E c g F hc hZ a₀).initial))).hom ≫ ι.hom) :=
      (inferInstance : IsIso ((D.stageTargetIso E c g F hc hZ a₀
          (limit.π (D.stageSituation E c g F hc hZ a₀).base
            (op (D.stageSituation E c g F hc hZ a₀).initial))).hom ≫ ι.hom))
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    exact (IsPullback.isoIsPullback_hom_snd _ _ P₁ P₂).trans
      (((congrArg (· ≫ ι.hom) (D.stageSituation E c g F hc hZ a₀).mapLimit_fst).symm.trans
        (Category.assoc _ _ _)).trans
        (congrArg (fun x => (D.stageSituation E c g F hc hZ a₀).mapLimit ≫ x ≫ ι.hom)
          (D.stageTargetIso_hom E c g F hc hZ a₀ _).symm))
  refine ⟨ObjectProperty.homMk (P₁.isoIsPullback _ _ P₂).hom,
    ObjectProperty.homMk ((D.stageTargetIso E c g F hc hZ a₀
        (limit.π (D.stageSituation E c g F hc hZ a₀).base
          (op (D.stageSituation E c g F hc hZ a₀).initial))).hom ≫ ι.hom),
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) hsq, ?_⟩
  exact IsPullback.isoIsPullback_hom_fst _ _ P₁ P₂

variable {k : Over i} (e₀ : F.obj (op a₀) ⟶ k)
  (Q : Modules.{u, u} B S hS (D.space ((D.stageTestSystem E g).obj k)).1
    (D.space ((D.stageTestSystem E g).obj k)).2) (hQ : Q.IsFinitePresentationOnSite)

/-- The module `F₀` of the situation on `X₀ = X_{T_{a₀}}`: the inverse image of `Q` along the
morphism `X_{T_{a₀}} ⟶ X_{T_k}` of base changes. -/
abbrev stageModule₀ : Modules.{u, u} B S hS (D.stageSituation E c g F hc hZ a₀).source₀
    (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace :=
  (modulePullback B S hS
    (ObjectProperty.homMk (D.relativeMap ((D.stageTestSystem E g).map e₀)).hom :
    (⟨(D.stageSituation E c g F hc hZ a₀).source₀,
      (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      D.space ((D.stageTestSystem E g).obj k))).obj Q

/-- A cartesian square over `X_U ⟶ U` for the stage `a`, whose top morphism is compatible with the
morphisms of base changes to `X_{T_{a₀}}` and `X_{T_k}`. -/
private theorem exists_isPullback_stageSituation_comp (a : α)
    (ha : (D.stageSituation E c g F hc hZ a₀).initial ≤ a)
    {U : SchemesOver D.Y} (w : U ⟶ (D.stageTestSystem E g).obj (F.obj (op a)))
    (ε : U ⟶ (D.stageTestSystem E g).obj k)
    (hε : w ≫ (D.stageTestSystem E g).map (F.map (homOfLE ha).op ≫ e₀) = ε) :
    ∃ (φ : D.space U ⟶ ⟨(D.stageSituation E c g F hc hZ a₀).sourceAt a ha,
          (D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha⟩)
      (ψ : (schemeSpaceFunctor B S hS).obj U.left ⟶
        ⟨(D.stageSituation E c g F hc hZ a₀).targetAt a ha,
          (D.stageSituation E c g F hc hZ a₀).targetAt_isAlgebraicSpace a ha⟩),
      IsPullback φ (D.projection U)
        (ObjectProperty.homMk ((D.stageSituation E c g F hc hZ a₀).mapAt a ha)) ψ ∧
      φ ≫ ObjectProperty.homMk (pullback.snd
          ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) ≫
        ObjectProperty.homMk (D.relativeMap ((D.stageTestSystem E g).map e₀)).hom =
          D.relativeMap ε := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_mapAt E c g F hc hZ a₀ a ha
  have h₁ : D.relativeMap w ≫ D.relativeMap ((D.stageTestSystem E g).map (F.map (homOfLE ha).op)) ≫
      D.relativeMap ((D.stageTestSystem E g).map e₀) = D.relativeMap ε :=
    (congrArg (D.relativeMap w ≫ ·) (baseChangeMap_comp D.f _ _).symm).trans
      ((baseChangeMap_comp D.f _ _).symm.trans (congrArg (fun x => D.relativeMap x)
        ((congrArg (w ≫ ·) ((D.stageTestSystem E g).map_comp _ _).symm).trans hε)))
  refine ⟨_, _, (isPullback_baseChangeMap D.f w).paste_horiz sq, ObjectProperty.hom_ext _ ?_⟩
  exact (congrArg ((D.relativeMap w).hom ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (D.relativeMap ((D.stageTestSystem E g).map e₀)).hom) hφ))).trans
    (congrArg (fun x => x.hom) h₁)

include hQ in
/-- **Flatness at a stage of the situation is flatness of the stage module.** If the module `F₀`
of the situation is flat over the target after inverse image to the stage `a`, then the inverse
image of `Q` to any test scheme `U` over `T_a` is flat over `U`. -/
theorem isFlatOver_of_stageSituation (a : α) (ha : (D.stageSituation E c g F hc hZ a₀).initial ≤ a)
    {U : SchemesOver D.Y} (w : U ⟶ (D.stageTestSystem E g).obj (F.obj (op a)))
    (ε : U ⟶ (D.stageTestSystem E g).obj k)
    (hε : w ≫ (D.stageTestSystem E g).map (F.map (homOfLE ha).op ≫ e₀) = ε)
    (h : IsFlatOver B S hS ((D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha)
      ((D.stageSituation E c g F hc hZ a₀).mapAt a ha)
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) :
          (⟨(D.stageSituation E c g F hc hZ a₀).sourceAt a ha,
            (D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨(D.stageSituation E c g F hc hZ a₀).source₀,
              (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace⟩)).obj
        (D.stageModule₀ E c g F hc hZ a₀ e₀ Q))) :
    IsFlatOver B S hS (D.space U).2 (D.projection U).hom
      ((modulePullback B S hS (D.relativeMap ε)).obj Q) := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_comp E c g F hc hZ a₀ e₀ a ha w ε hε
  exact isFlatOver_of_isPullback_of_comp sq Q hQ _ (D.relativeMap ε) hφ
    (IsFlatOver.of_iso B S hS _ (pullbackComparison B S hS _ _ _ rfl Q).symm h)

include hQ in
/-- **Proper support at a stage of the situation is proper support of the stage module.** If
the module `F₀` of the situation has support proper over the target after inverse image to the
stage `a`, then the inverse image of `Q` to any test scheme `U` over `T_a` has support proper
over `U`. -/
theorem hasProperSupportOver_of_stageSituation (a : α)
    (ha : (D.stageSituation E c g F hc hZ a₀).initial ≤ a)
    {U : SchemesOver D.Y} (w : U ⟶ (D.stageTestSystem E g).obj (F.obj (op a)))
    (ε : U ⟶ (D.stageTestSystem E g).obj k)
    (hε : w ≫ (D.stageTestSystem E g).map (F.map (homOfLE ha).op ≫ e₀) = ε)
    (h : HasProperSupportOver (ObjectProperty.homMk
        ((D.stageSituation E c g F hc hZ a₀).mapAt a ha) :
          (⟨(D.stageSituation E c g F hc hZ a₀).sourceAt a ha,
            (D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨(D.stageSituation E c g F hc hZ a₀).targetAt a ha,
              (D.stageSituation E c g F hc hZ a₀).targetAt_isAlgebraicSpace a ha⟩)
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd ((D.stageSituation E c g F hc hZ a₀).baseAtToInitial a ha)
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) :
          (⟨(D.stageSituation E c g F hc hZ a₀).sourceAt a ha,
            (D.stageSituation E c g F hc hZ a₀).sourceAt_isAlgebraicSpace a ha⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨(D.stageSituation E c g F hc hZ a₀).source₀,
              (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace⟩)).obj
        (D.stageModule₀ E c g F hc hZ a₀ e₀ Q))) :
    HasProperSupportOver (D.projection U) ((modulePullback B S hS (D.relativeMap ε)).obj Q) := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_comp E c g F hc hZ a₀ e₀ a ha w ε hε
  exact HasProperSupportOver.of_isPullback_of_comp sq Q hQ _ (D.relativeMap ε) hφ
    (h.of_iso (pullbackComparison B S hS _ _ _ rfl Q).symm)

/-- A cartesian square over the limit `X_{T₀} ⟶ T₀`, whose top morphism is compatible with the
morphisms of base changes to `X_{T_{a₀}}` and `X_{T_k}`. -/
private theorem exists_isPullback_stageSituation_comp_mapLimit (T₀ : SchemesOver D.Y)
    (γ : T₀ ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)))
    (ι : limit (D.stageSituation E c g F hc hZ a₀).base ≅ yoneda.obj T₀.left)
    (hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
    (β : T₀ ⟶ (D.stageTestSystem E g).obj k) (hβ : γ ≫ (D.stageTestSystem E g).map e₀ = β) :
    ∃ (φ : (⟨(D.stageSituation E c g F hc hZ a₀).sourceLimit,
          (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ D.space T₀)
      (ψ : (⟨(D.stageSituation E c g F hc hZ a₀).targetLimit,
          (D.stageSituation E c g F hc hZ a₀).targetLimit_isAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ (schemeSpaceFunctor B S hS).obj T₀.left),
      IsPullback φ (ObjectProperty.homMk (D.stageSituation E c g F hc hZ a₀).mapLimit)
        (D.projection T₀) ψ ∧
      φ ≫ D.relativeMap β = ObjectProperty.homMk (pullback.snd
          (limit.π (D.stageSituation E c g F hc hZ a₀).base
            (op (D.stageSituation E c g F hc hZ a₀).initial))
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) ≫
        ObjectProperty.homMk (D.relativeMap ((D.stageTestSystem E g).map e₀)).hom := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_mapLimit E c g F hc hZ a₀ T₀ γ ι hι
  have h₁ : D.relativeMap γ ≫ D.relativeMap ((D.stageTestSystem E g).map e₀) =
      D.relativeMap β :=
    (baseChangeMap_comp D.f _ _).symm.trans (congrArg (fun x => D.relativeMap x) hβ)
  refine ⟨φ, ψ, sq, ObjectProperty.hom_ext _ ?_⟩
  exact (congrArg (φ.hom ≫ ·) (congrArg (fun x => x.hom) h₁).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (D.relativeMap ((D.stageTestSystem E g).map e₀)).hom) hφ))

include hQ in
/-- **Flatness of the module of an object over the limit is flatness of `F` in the situation.**
Let `T₀` be a test scheme over `Y` whose representable presheaf is the limit of the system,
`β : T₀ ⟶ T_k` a morphism through `γ : T₀ ⟶ T_{a₀}`, and `M` a module on `X_{T₀}` flat over `T₀`
and isomorphic to the inverse image of `Q`. Then the inverse image of `F₀` to the base change
of the situation at the limit is flat over its target. -/
theorem isFlatOver_stageSituation_mapLimit (T₀ : SchemesOver D.Y)
    (γ : T₀ ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)))
    (ι : limit (D.stageSituation E c g F hc hZ a₀).base ≅ yoneda.obj T₀.left)
    (hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
    (β : T₀ ⟶ (D.stageTestSystem E g).obj k) (hβ : γ ≫ (D.stageTestSystem E g).map e₀ = β)
    {M : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (eM : (modulePullback B S hS (D.relativeMap β)).obj Q ≅ M)
    (h : IsFlatOver B S hS (D.space T₀).2 (D.projection T₀).hom M) :
    IsFlatOver B S hS (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace
      (D.stageSituation E c g F hc hZ a₀).mapLimit
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (limit.π (D.stageSituation E c g F hc hZ a₀).base
          (op (D.stageSituation E c g F hc hZ a₀).initial))
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) :
          (⟨(D.stageSituation E c g F hc hZ a₀).sourceLimit,
            (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨(D.stageSituation E c g F hc hZ a₀).source₀,
              (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace⟩)).obj
        (D.stageModule₀ E c g F hc hZ a₀ e₀ Q)) := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_comp_mapLimit E c g F hc hZ a₀ e₀
    T₀ γ ι hι β hβ
  refine IsFlatOver.of_iso B S hS _ ?_ (isFlatOver_of_isPullback_of_comp sq Q hQ
    (D.relativeMap β) _ hφ (IsFlatOver.of_iso B S hS _ eM.symm h))
  exact pullbackComparison B S hS _ _ _ rfl Q

include hQ in
/-- **Proper support of the module of an object over the limit is proper support of `F` in the
situation.** The counterpart of
`AlgebraicGeometry.Space.CoherentSituation.isFlatOver_stageSituation_mapLimit` for the
properness of the support. -/
theorem hasProperSupportOver_stageSituation_mapLimit (T₀ : SchemesOver D.Y)
    (γ : T₀ ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)))
    (ι : limit (D.stageSituation E c g F hc hZ a₀).base ≅ yoneda.obj T₀.left)
    (hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
    (β : T₀ ⟶ (D.stageTestSystem E g).obj k) (hβ : γ ≫ (D.stageTestSystem E g).map e₀ = β)
    {M : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (eM : (modulePullback B S hS (D.relativeMap β)).obj Q ≅ M)
    (h : HasProperSupportOver (D.projection T₀) M) :
    HasProperSupportOver (ObjectProperty.homMk (D.stageSituation E c g F hc hZ a₀).mapLimit :
        (⟨(D.stageSituation E c g F hc hZ a₀).sourceLimit,
          (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨(D.stageSituation E c g F hc hZ a₀).targetLimit,
            (D.stageSituation E c g F hc hZ a₀).targetLimit_isAlgebraicSpace⟩)
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (limit.π (D.stageSituation E c g F hc hZ a₀).base
          (op (D.stageSituation E c g F hc hZ a₀).initial))
          (D.stageSituation E c g F hc hZ a₀).sourceToBase) :
          (⟨(D.stageSituation E c g F hc hZ a₀).sourceLimit,
            (D.stageSituation E c g F hc hZ a₀).sourceLimit_isAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            ⟨(D.stageSituation E c g F hc hZ a₀).source₀,
              (D.stageSituation E c g F hc hZ a₀).source₀_isAlgebraicSpace⟩)).obj
        (D.stageModule₀ E c g F hc hZ a₀ e₀ Q)) := by
  obtain ⟨φ, ψ, sq, hφ⟩ := D.exists_isPullback_stageSituation_comp_mapLimit E c g F hc hZ a₀ e₀
    T₀ γ ι hι β hβ
  refine HasProperSupportOver.of_iso ?_ (HasProperSupportOver.of_isPullback_of_comp sq Q hQ
    (D.relativeMap β) _ hφ (h.of_iso eM.symm))
  exact pullbackComparison B S hS _ _ _ rfl Q

include hQ in
/-- **Flatness and proper support descend to a stage of the situation**, by Stacks 08K0 and
Stacks 08K2 for the situation of Stacks 084W under the convention of Section 70.2 (tag 07SD):
a module `M` on `X_{T₀}`, flat over `T₀` with support proper over `T₀` and isomorphic to the
inverse image of `Q`, is the inverse image of a module on some stage `X_{T_b}` that is flat
over `T_b` with support proper over `T_b`. -/
theorem exists_isFlatWithProperSupport_of_stageSituation [Nonempty α] (T₀ : SchemesOver D.Y)
    (γ : T₀ ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)))
    (ι : limit (D.stageSituation E c g F hc hZ a₀).base ≅ yoneda.obj T₀.left)
    (hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial))
    (β : T₀ ⟶ (D.stageTestSystem E g).obj k) (hβ : γ ≫ (D.stageTestSystem E g).map e₀ = β)
    {M : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (eM : (modulePullback B S hS (D.relativeMap β)).obj Q ≅ M)
    (hM : D.IsFlatWithProperSupport T₀ M) :
    ∃ (b : α) (hb : (D.stageSituation E c g F hc hZ a₀).initial ≤ b),
      D.IsFlatWithProperSupport ((D.stageTestSystem E g).obj (F.obj (op b)))
        ((modulePullback B S hS
          (D.relativeMap ((D.stageTestSystem E g).map (F.map (homOfLE hb).op ≫ e₀)))).obj Q) := by
  have : (D.stageModule₀ E c g F hc hZ a₀ e₀ Q).IsFinitePresentationOnSite :=
    (modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation _ Q hQ
  have hqc : (D.stageModule₀ E c g F hc hZ a₀ e₀ Q).IsQuasicoherentOnSite := inferInstance
  have hftm : SheafOfModules.IsFiniteTypeOnSite (D.stageModule₀ E c g F hc hZ a₀ e₀ Q) :=
    inferInstance
  have hfp := D.isLocallyOfFinitePresentation_stageSituation_map₀ E c g F hc hZ a₀
  have hft : IsLocallyOfFiniteType B S hS (D.stageSituation E c g F hc hZ a₀).map₀ :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp
  have hconv := D.siteContainsBaseChangeLimits_stageSituation E c g F hc hZ a₀
  obtain ⟨a, ha, hfa⟩ :=
    MorphismDescentSituation.C1573.exists_isFlatOver_mapAt_of_siteContainsBaseChangeLimits
      (D.stageSituation E c g F hc hZ a₀) hconv (D.stageModule₀ E c g F hc hZ a₀ e₀ Q)
      (D.isFlatOver_stageSituation_mapLimit E c g F hc hZ a₀ e₀ Q hQ T₀ γ ι hι β hβ eM hM.1) hfp
  obtain ⟨_, _, hpl⟩ :=
    D.hasProperSupportOver_stageSituation_mapLimit E c g F hc hZ a₀ e₀ Q hQ T₀ γ ι hι β hβ eM hM.2
  obtain ⟨a', ha', hpa'⟩ := (D.stageSituation E c g F hc hZ a₀)
    |>.exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits
    (D.stageModule₀ E c g F hc hZ a₀ e₀ Q) hconv hqc hft hftm hpl
  obtain ⟨b, hab, ha'b⟩ := directed_of (· ≤ ·) a a'
  have hop : ∀ {x y : α} (hxy : x ≤ y) (hx : (D.stageSituation E c g F hc hZ a₀).initial ≤ x),
      (D.stageTestSystem E g).map (F.map (homOfLE hxy).op) ≫
        (D.stageTestSystem E g).map (F.map (homOfLE hx).op ≫ e₀) =
      (D.stageTestSystem E g).map (F.map (homOfLE (hx.trans hxy)).op ≫ e₀) := by
    intro x y hxy hx
    have h : (homOfLE hxy).op ≫ (homOfLE hx).op = (homOfLE (hx.trans hxy)).op := by
      rw [← op_comp, homOfLE_comp]
    exact ((D.stageTestSystem E g).map_comp _ _).symm.trans (congrArg (D.stageTestSystem E g).map
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e₀)
        ((F.map_comp _ _).symm.trans (congrArg F.map h)))))
  refine ⟨b, ha.trans hab, ?_, ?_⟩
  · exact D.isFlatOver_of_stageSituation E c g F hc hZ a₀ e₀ Q hQ a ha
      ((D.stageTestSystem E g).map (F.map (homOfLE hab).op)) _ (hop hab ha) hfa
  · exact D.hasProperSupportOver_of_stageSituation E c g F hc hZ a₀ e₀ Q hQ a' ha'
      ((D.stageTestSystem E g).map (F.map (homOfLE ha'b).op)) _ (hop ha'b ha') ⟨_, _, hpa'⟩

end Stage

/-! ### The descent of flatness and of proper support, and Stacks 08KD -/

section Descent

variable {I : Type u} [Category.{u} I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)

/-- **Stacks 08K0 and 08K2 for the system of base changes `X_{T_k} = X ×_Y T_k`.** For a
cofiltered system of affine schemes of the site whose limit `T` in schemes lies in the site, the
flatness and the properness of the support of a finitely presented module on `X_T` descend
along the system of base changes above any stage: this is
`AlgebraicGeometry.Space.CoherentSituation.FlatProperSupportDescends`.

The stages above `i` are reindexed by a directed set along an initial functor (Stacks 0032),
which makes the system of base changes a situation of Stacks 084W
(`AlgebraicGeometry.Space.CoherentSituation.stageSituation`) satisfying the chapter's
convention; Stacks 08K0 and Stacks 08K2 for that situation give the stage. -/
theorem flatProperSupportDescends [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    D.FlatProperSupportDescends E c := by
  intro A₀ hA₀ i g k β hβ Q hQ eQ
  obtain ⟨A, _, _, _, F, _⟩ := IsCofiltered.exists_directed_initial (Over i)
  obtain ⟨a₀, ⟨e₀⟩⟩ : ∃ a₀ : A, Nonempty (F.obj (op a₀) ⟶ k) :=
    have x := (Functor.Initial.out (F := F) k).is_nonempty.some
    ⟨x.left.unop, ⟨x.hom⟩⟩
  have hZ := B.contains_terminal
  let incl := BigAffineFppf.inclusion B S hS
  have hw : (schemeSpaceFunctor B S hS).map
      (eqToHom hA₀ ≫ incl.map (c.π.app (F.obj (op a₀)).left)) ≫
        ((D.stageTestSystem E g).obj (F.obj (op a₀))).hom = A₀.T.hom := by
    refine Eq.trans ?_ (CostructuredArrow.w β)
    rw [hβ]
    change (schemeSpaceFunctor B S hS).map
        (eqToHom hA₀ ≫ incl.map (c.π.app (F.obj (op a₀)).left)) ≫
          (schemeSpaceFunctor B S hS).map (incl.map (E.map (F.obj (op a₀)).hom)) ≫ g =
      (schemeSpaceFunctor B S hS).map (eqToHom hA₀ ≫ incl.map (c.π.app k.left)) ≫
          (schemeSpaceFunctor B S hS).map (incl.map (E.map k.hom)) ≫ g
    simp only [← Functor.map_comp_assoc, Category.assoc, ← Functor.map_comp, Cone.w]
  let γ : A₀.T ⟶ (D.stageTestSystem E g).obj (F.obj (op a₀)) := CostructuredArrow.homMk _ hw
  have hγβ : γ ≫ (D.stageTestSystem E g).map e₀ = β := by
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, hβ]
    change (eqToHom hA₀ ≫ incl.map (c.π.app (F.obj (op a₀)).left)) ≫ incl.map (E.map e₀.left) =
      eqToHom hA₀ ≫ incl.map (c.π.app k.left)
    rw [Category.assoc, ← Functor.map_comp, Cone.w]
  let ι := D.stageLimitIso E c g F hc ≪≫ yoneda.mapIso (eqToIso hA₀.symm)
  have h₁ : yoneda.map (eqToHom hA₀.symm) ≫ yoneda.map γ.left =
      (D.stageLimitCone E c g F).π.app (op a₀) := by
    rw [← Functor.map_comp]
    change yoneda.map (eqToHom hA₀.symm ≫ eqToHom hA₀ ≫ incl.map (c.π.app (F.obj (op a₀)).left)) =
      yoneda.map (incl.map (c.π.app (F.obj (op a₀)).left))
    rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hι : ι.hom ≫ yoneda.map γ.left = limit.π (D.stageSituation E c g F hc hZ a₀).base
      (op (D.stageSituation E c g F hc hZ a₀).initial) :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans
      (D.stageLimitIso_hom_comp E c g F hc (op a₀)))
  obtain ⟨b, hb, h⟩ := D.exists_isFlatWithProperSupport_of_stageSituation E c g F hc hZ a₀ e₀ Q hQ
    A₀.T γ ι hι β hγβ eQ ⟨A₀.flat, A₀.properSupport⟩
  exact ⟨F.obj (op b), F.map (homOfLE hb).op ≫ e₀, h⟩

end Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- **Stacks 08KD.** In Situation 08KB, let `f : X ⟶ Y` be a morphism of finite presentation of
algebraic spaces over `S` and assume `Y` locally of finite presentation over `S`. Then
`Coh_{X/Y}` is limit preserving in the sense of Artin's Axioms, Definition 07XL: for every
cofiltered inverse system of affine schemes `T_j` of the big fppf site, indexed by a category in
the scheme universe, whose limit `T` in schemes lies in the site, the comparison functor
`colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` is an equivalence.

The index category is taken in the scheme universe, which is the smallness the source's
directed sets have, as in `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`. -/
@[stacks 08KD "at a small index category"]
theorem isLimitPreserving_coherent
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u} B S hS D.coherentCFG :=
  D.isLimitPreserving_coherent_of_flatProperSupportDescends hY
    (fun _ _ _ E c hc => D.flatProperSupportDescends E c hc)

end AlgebraicGeometry.Space.CoherentSituation

end
