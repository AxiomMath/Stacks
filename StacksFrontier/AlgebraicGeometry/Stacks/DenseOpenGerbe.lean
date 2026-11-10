module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfFlatInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyCancel
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.InvariantStabilizerLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquareAlgebraicStacks
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence

/-!
# A reduced algebraic stack with quasi-compact inertia is generically a gerbe (Stacks 06RC)

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site, reduced in the sense of
Stacks 04YG, whose inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact. **Stacks 06RC** says that there
is a dense open substack `𝒰 ⊆ 𝒳` which is a gerbe.

## Main results

* `AlgebraicGeometry.Stack.exists_openSubstack_dense_isGerbe`: **Stacks 06RC**.

The proof follows the source and produces the following intermediate results, each stated in
general:

* `AlgebraicGeometry.Stack.exists_groupoidPresentation_isSmooth_isSurjective`: an algebraic
  stack has a presentation (Stacks 04T3) whose chart `𝒮_U ⟶ 𝒳` is smooth and surjective.
* `AlgebraicGeometry.Stack.isFiniteType_presentationStabilizer`: the stabilizer `G ⟶ U` of a
  presentation is of finite type when the inertia projection is quasi-compact (Stacks 06PR,
  050Q, 050T).
* `AlgebraicGeometry.Stack.exists_isDenseOpenSubspace_isFlat_presentationStabilizer`: generic
  flatness (Stacks 06QS) of the stabilizer over the reduced object space.
* `AlgebraicGeometry.Stack.pointsWithinOpenSubstackLift` and
  `AlgebraicGeometry.Stack.isSmooth_isSurjective_pointsWithinOpenSubstackLift`: a smooth
  1-morphism from an algebraic space factors through the open substack of its image (Stacks
  06FJ) by a smooth surjective 1-morphism.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaFullyFaithfulSquareAlgebraicStacks`:
  **Stacks 06R5** in the 2-category of algebraic stacks, for a fully faithful 1-morphism.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_algebraicSpaceStackPullbackSquare`: a fibre product
  of algebraic spaces is a 2-fibre product of the attached algebraic stacks.

## Implementation notes

The open set `W ⊆ U` over which the stabilizer is flat and locally of finite presentation is the
dense open subspace of Stacks 06QS itself rather than the largest such open: its image in `|𝒳|`
is open because `𝒮_W ⟶ 𝒳` is smooth (Stacks 06R7), so no invariance statement (Stacks 06R4) is
needed to obtain the open substack, which is the open substack of that image
(`AlgebraicGeometry.Stack.pointsWithinOpenSubstack`). The flatness of the inertia of `𝒰` is read
on the smooth surjective 1-morphism `𝒮_{G ×_U W} ⟶ I_𝒰`, the composite of the comparison of two
2-fibre products of one cospan with the base change of `𝒮_W ⟶ 𝒰`: the two 2-fibre products are
the pastings of Stacks 06R5 for `𝒰 ⊆ 𝒳` with the canonical square of `I_𝒰 ⟶ 𝒰` along `𝒮_W ⟶ 𝒰`,
and of Stacks 06PR with the fibre product `G ×_U W`. The gerbe is then given by the implication
(2) ⟹ (1) of Stacks 06QJ.

## References

* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
* [Stacks Project, Tag 06QS](https://stacks.math.columbia.edu/tag/06QS)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u w

/-- Changing the base of a groupoid in algebraic spaces leaves the projection of Stacks 044R
unchanged. -/
theorem toFunctor_quotientStackProjection_changeBase {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (G : GroupoidInAlgebraicSpaces B S hS Z) :
    (quotientStackProjection (GroupoidInAlgebraicSpaces.changeBase i G)).toFunctor =
      (quotientStackProjection G).toFunctor :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presentation of Stacks 04T3 built from a self-intersection presentation datum has
smooth and surjective chart.** Let `f : 𝒮_W ⟶ 𝒳` be a 1-morphism which is smooth and surjective,
and let `sp` be a presentation datum of Stacks 04T4 (4), (5) for it whose canonical 1-morphism is
the forward 1-morphism of an equivalence `e` over the site. Then the chart `𝒮_U ⟶ 𝒳` of the
resulting presentation is smooth and surjective: it is `f` read through the vertical
2-isomorphism of Stacks 04T4 (5) and the chosen identification of `𝒮_W` with `𝒮_U`. -/
theorem isSmooth_isSurjective_presentationObjectMorphism_of_selfIntersection
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (W : BigFppfOver B S hS)
    (F : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hFsm : AlgebraicStacks.IsSmooth B S hS F) (hFsurj : IsSurjective B S hS F)
    {U R : AlgebraicSpaces B S hS}
    {eU : StacksRepresentableCFG.EquivalenceOver
      (schemeFibredCategory B S hS W).val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p}
    {eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS W) 𝒳.val F.hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p}
    (sp : SelfIntersection.SelfIntersectionPresentation eU eR)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS sp.groupoid)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack sp.groupoid).p 𝒳.val.val.p)
    (he : e.hom.functor = sp.canonicalMap.toFunctor) :
    ∃ P : GroupoidPresentation B S hS 𝒳.val.val,
      AlgebraicStacks.IsSmooth B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) ∧
        IsSurjective B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) := by
  let P : GroupoidPresentation B S hS 𝒳.val.val :=
    { groupoid := GroupoidInAlgebraicSpaces.changeBase
        ((isTerminal_baseSpace B S hS).from sp.base) sp.groupoid
      smooth := hG
      equivalence := e }
  let p := presentationObjectMorphismAlgebraicStacks B S hS P
  let k : schemeStack.{u, w} B S hS W ⟶ presentationObjectAlgebraicStack B S hS P :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      ⟨sp.sourcePresentation.hom.functor, sp.sourcePresentation.hom.w⟩)
  have hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom) :=
    sp.sourcePresentation.toEquivalence.isEquivalence_functor
  let α : F.hom.hom.toFunctor ≅ sp.sourcePresentation.hom.functor ⋙
      ((quotientStackProjection P.groupoid).toFunctor ⋙ e.hom.functor) :=
    sp.extends_f.1.symm ≪≫ Functor.isoWhiskerLeft sp.sourcePresentation.hom.functor
      (Functor.isoWhiskerLeft (quotientStackProjection sp.groupoid).toFunctor
        (eqToIso he.symm))
  have hα : ∀ x, 𝒳.val.val.p.IsHomLift
      (𝟙 ((schemeFibredCategory B S hS W).val.p.obj x)) (α.hom.app x) := by
    intro x
    have : 𝒳.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS W).val.p.obj x))
        (sp.extends_f.1.app x).hom := sp.extends_f.2 x
    have : 𝒳.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS W).val.p.obj x))
        (sp.extends_f.1.app x).inv :=
      IsHomLift.lift_id_inv _ _ (sp.extends_f.1.app x)
    change 𝒳.val.val.p.IsHomLift _ ((sp.extends_f.1.app x).inv ≫
      (eqToHom he.symm).app ((quotientStackProjection sp.groupoid).toFunctor.obj
        (sp.sourcePresentation.hom.functor.obj x)))
    rw [eqToHom_app]
    infer_instance
  let θ : F ≅ k ≫ p := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (F := F.hom.hom) (G := BasedFunctor.comp
      ⟨sp.sourcePresentation.hom.functor, sp.sourcePresentation.hom.w⟩ p.hom.hom) α hα))
  refine ⟨P, hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS _ p.hom F.hom k.hom hk
    (Bicategory.InducedBicategory.isoHom θ) hFsm, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hFsurj x
  rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS θ.hom, AlgebraicStacks.pointsMap_comp] at hy
  exact ⟨_, hy⟩

/-- **A presentation whose chart is smooth and surjective.** Every algebraic stack `𝒳` over `S`
has a presentation `[U/R] ⟶ 𝒳` (Stacks 04T3) for which the 1-morphism `𝒮_U ⟶ 𝒳` of
`AlgebraicGeometry.Stack.presentationObjectMorphismAlgebraicStacks` is smooth and surjective. -/
theorem exists_groupoidPresentation_isSmooth_isSurjective (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ P : GroupoidPresentation B S hS 𝒳.val.val,
      AlgebraicStacks.IsSmooth B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) ∧
        IsSurjective B S hS (presentationObjectMorphismAlgebraicStacks B S hS P) := by
  have h𝒳 := 𝒳.property
  obtain ⟨_hfib, ⟨⟨-, -⟩, -, W, f, hf, hfprop⟩⟩ := id h𝒳
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS W
  let F : schemeStack.{u, w} B S hS W ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f)
  let U : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p :=
    sliceElementsEquivalenceOver W
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳.val F.hom.hom h𝒳
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let R : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p := eR₀
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F.hom hf :=
    fun V y hy G hG he => (hfprop V y hy G hG he).2
  have hsrc := SelfIntersection.isSmooth_selfIntersectionPresentation_source
    (𝒰 := 𝒰) (𝒳 := 𝒳.val) (F := F.hom) (U := U) (R := R) eU eR hf hsmooth h𝒳
  have htgt := SelfIntersection.isSmooth_selfIntersectionPresentation_target
    (𝒰 := 𝒰) (𝒳 := 𝒳.val) (F := F.hom) (U := U) (R := R) eU eR hf hsmooth h𝒳
  obtain ⟨e, he⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    (𝒰 := 𝒰) (𝒳 := 𝒳.val) (f := F.hom) (U := U) (R := R) eU eR h𝒳
    (fun V y hy G hG he => (hfprop V y hy G hG he).2)
    (fun V y hy G hG he => (hfprop V y hy G hG he).1)
  exact isSmooth_isSurjective_presentationObjectMorphism_of_selfIntersection B S hS 𝒳 W F
    (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) h𝒳 F.hom hf hsmooth)
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS F hf).mpr
      (fun V y hy G hG he => (hfprop V y hy G hG he).1))
    (SelfIntersection.selfIntersectionPresentation eU eR h𝒳) ⟨hsrc, htgt⟩ e he

/-- **The stabilizer of a presentation inherits a property of the inertia, in the form of
Stacks 04XB.** Let `[U/R] ⟶ 𝒳` be a presentation of an algebraic stack over `S`, with
stabilizer `G ⟶ U`, and let `Q` be a property of morphisms of algebraic spaces over `S` stable
under base change and fppf local on the target. If every algebraic space representing a base
change of the inertia projection `I_𝒳 ⟶ 𝒳` along a scheme-valued point has structural morphism
with `Q`, then `G ⟶ U` has `Q`.

By **Stacks 06PR** the square `𝒮_G ⟶ 𝒮_U`, `I_𝒳 ⟶ 𝒳` is 2-cartesian, so `𝒮_G ⟶ 𝒮_U` is a base
change of the inertia projection (Stacks 045C), and the 1-morphism attached to a morphism of
algebraic spaces has a relative property exactly when the morphism has it (Stacks 04XB). -/
theorem prop_presentationStabilizer_of_inertiaProjection
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)
    (Q : MorphismProperty (AlgebraicSpaces B S hS)) [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hQ : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (inertiaAlgebraicStack B S hS 𝒳).val.val.p 𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Q (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    Q (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid) := by
  let sq := (inertiaPresentationSquareAlgebraicStacks B S hS P).swap
  have hsq : Bicategory.IsTwoFibreProduct sq :=
    Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks
      B S hS P)
  have hsqU : Bicategory.IsTwoFibreProduct sq.underlying :=
    Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS
        (presentationObjectMorphismAlgebraicStacks B S hS P)
        (inertiaProjectionAlgebraicStacks B S hS 𝒳)) hsq
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
  have hbase := relativeProperty_baseChange.{u, u, u} B S hS Q _ _ _
    (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
    (presentationObjectMorphismAlgebraicStacks B S hS P).hom sq.underlying hsqU hQ
  let a := (presentationStabilizerProjectionAlgebraicStacks B S hS P).hom
  have ha : IsRepresentableByAlgebraicSpaces B S hS a.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (presentationObjectAlgebraicStack B S hS P).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS _
        (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property) a
  have key := (hasRelativeProperty_iff_prop_representingMap B S hS Q a ha _ _
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property
    P.groupoid.objects.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).mp hbase
  have hrm := representingMap_associatedMap B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).obj P.groupoid.objects.obj
    (GroupoidInAlgebraicSpaces.inertiaForgetful P.groupoid).objectsMap.hom
  exact (congrArg (fun h => Q (ObjectProperty.homMk h :
    GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid ⟶ P.groupoid.objects)) hrm).mp key

/-- **Stacks 06RC, the finiteness of the stabilizer.** If the inertia projection of an algebraic
stack `𝒳` over `S` is quasi-compact, then for every presentation `[U/R] ⟶ 𝒳` the stabilizer
`G ⟶ U` is of finite type: quasi-compact as a base change of the inertia projection (Stacks 06PR,
050T) and locally of finite type because the inertia projection always is (Stacks 050Q). -/
theorem isFiniteType_presentationStabilizer
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    Space.IsFiniteType B S hS (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid).hom := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom.hom :=
    isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u, w} B S hS
      𝒳.val 𝒳.property
  exact ⟨prop_presentationStabilizer_of_inertiaProjection B S hS P
      (Space.locallyOfFiniteTypeProperty B S hS)
      (isLocallyOfFiniteType_inertiaProjection B S hS 𝒳),
    prop_presentationStabilizer_of_inertiaProjection B S hS P (Space.quasiCompactProperty B S hS)
      ((isQuasiCompact_iff_baseChange_quasiCompact B S hS _ hrep).mpr hqc)⟩

/-- **The object space of a smooth presentation of a reduced algebraic stack is reduced.** The
chart `𝒮_U ⟶ 𝒳` of the presentation is smooth, and a reduced algebraic stack has reduced source on
every smooth chart by an algebraic space (Stacks 04YF). -/
theorem hasEtaleLocalProperty_isReduced_presentationObjects
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (hred : IsReducedStack B S hS 𝒳)
    (P : GroupoidPresentation B S hS 𝒳.val.val)
    (hp : AlgebraicStacks.IsSmooth B S hS (presentationObjectMorphismAlgebraicStacks B S hS P)) :
    Space.HasEtaleLocalProperty B S hS P.groupoid.objects.obj (fun T : Scheme.{u} => IsReduced T) :=
  (exists_space_atlas_iff_forall_space B S hS (fun T : Scheme.{u} => IsReduced T) 𝒳).1
    ((exists_scheme_atlas_iff_exists_space_atlas B S hS (fun T : Scheme.{u} => IsReduced T)
      𝒳).1 hred) P.groupoid.objects.obj P.groupoid.objects.property
    (presentationObjectMorphismAlgebraicStacks B S hS P) hp

/-- **Stacks 06RC, generic flatness of the stabilizer.** For a smooth presentation `[U/R] ⟶ 𝒳` of
a reduced algebraic stack with quasi-compact inertia, there is a dense open subspace `W ⊆ U` over
which the stabilizer `G ⟶ U` is flat and locally of finite presentation: `G ⟶ U` is of finite
type and `U` is reduced, so Stacks 06QS applies. -/
theorem exists_isDenseOpenSubspace_isFlat_presentationStabilizer
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (hred : IsReducedStack B S hS 𝒳)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (P : GroupoidPresentation B S hS 𝒳.val.val)
    (hp : AlgebraicStacks.IsSmooth B S hS (presentationObjectMorphismAlgebraicStacks B S hS P)) :
    ∃ W : Subfunctor P.groupoid.objects.obj,
      Space.IsDenseOpenSubspace B S hS P.groupoid.objects.property W ∧
      Space.IsFlat B S hS
        (pullback.snd (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid).hom W.ι) ∧
      Space.IsLocallyOfFinitePresentation B S hS
        (pullback.snd (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid).hom W.ι) := by
  have hG := (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property
  obtain ⟨W, hW, hflat, hlfp, -, -⟩ := Space.exists_dense_open_genericFlatness B S hS hG
    P.groupoid.objects.property (hasEtaleLocalProperty_isReduced_presentationObjects B S hS hred
      P hp) _ (isFiniteType_presentationStabilizer B S hS P hqc) (Space.unitModule B S hS hG)
    (Space.isQuasicoherentOnCharts_unitModule B S hS hG)
    (Space.isFiniteTypeOnCharts_unitModule B S hS hG)
  exact ⟨W, hW, hflat, hlfp⟩

/-- **A dense open subspace has dense image in the space of points of the ambient stack.** For a
dense open subspace `W` of an algebraic space `U` over `S`, the map `|𝒮_W| ⟶ |𝒮_U|` on the points
of Stacks 04XG of the attached algebraic stacks has dense image: the points of `𝒮_U` are those of
`U`, with the same topology (Stacks 04XL), compatibly with the map induced by `W ⟶ U`. -/
theorem dense_range_pointsMap_algebraicSpaceStackMap_of_isDenseOpenSubspace
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U) {W : Subfunctor U}
    (hW : Space.IsDenseOpenSubspace B S hS hU W) :
    @Dense _ (pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hW.1.1 hU W.ι))) := by
  let _ := Space.pointTopology B S hS U
  let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val
  have hσ := isHomeomorph_spacePointMap_representing B S hS U hU (fibredCategory B S hS U)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have hdense : Dense ((spacePointMap B S hS U (fibredCategory B S hS U)
      (representingEquivalence B S hS U (fibredCategory B S hS U)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).functor) ''
        Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :=
    hσ.surjective.denseRange.dense_image hσ.continuous hW.2
  refine hdense.mono ?_
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨spacePointMap B S hS W.toFunctor (fibredCategory B S hS W.toFunctor)
    (representingEquivalence B S hS W.toFunctor (fibredCategory B S hS W.toFunctor)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).functor x, ?_⟩
  have hnat := spacePointMap_representing_naturality B S hS W.toFunctor U
    (fibredCategory B S hS W.toFunctor) (fibredCategory B S hS U)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS W.ι).1 x
  rw [representingMap_associatedMap] at hnat
  exact hnat.symm

/-- A smooth 1-morphism of algebraic stacks with source represented by an algebraic space is
relatively smooth. -/
private theorem isRelativelySmooth_of_isSmooth_of_isRepresentableByAlgebraicSpace
    {𝒱 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒴)
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val)
    (hg : AlgebraicStacks.IsSmooth B S hS g) : IsRelativelySmooth B S hS g.hom :=
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property
    h𝒱 g.hom
  ⟨hrep, (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    𝒱.property 𝒴.property g.hom hrep).1 hg⟩

/-- **Smoothness descends through an open immersion.** Let `g : 𝒱 ⟶ 𝒴` and `j : 𝒴 ⟶ 𝒳` be
1-morphisms of algebraic stacks over `S` with `𝒱` represented by an algebraic space and `j` an
open immersion. If `g ≫ j` is smooth, so is `g`: on representing algebraic spaces this is the
cancellation of smoothness against an étale morphism (an open immersion is étale). -/
theorem AlgebraicStacks.isSmooth_of_comp_isOpenImmersion
    {𝒱 𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒴) (j : 𝒴 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (hgj : AlgebraicStacks.IsSmooth B S hS (g ≫ j))
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) :
    AlgebraicStacks.IsSmooth B S hS g := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  obtain ⟨hgjrep, hgjrel⟩ :=
    isRelativelySmooth_of_isSmooth_of_isRepresentableByAlgebraicSpace B S hS (g ≫ j) h𝒱 hgj
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property h𝒱 g.hom
  have hgrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) g.hom hgrep := by
    refine prop_of_comp_of_spaceCancel B S hS (Space.smoothMorphismProperty B S hS)
      (Space.openImmersionProperty B S hS) ?_ g.hom j.hom hj.1 hgjrep hgjrel hj.2
    intro X' Y' Z' a b hab hb
    exact Space.isSmooth_of_comp_isEtale B S hS a.hom b.hom
      (Space.isEtale_of_isOpenImmersion B S hS hb) hab
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) 𝒴.property g.hom hgrep hgrel

/-- **An object seen by a 1-morphism with image in `Ω` lies in the locus of `Ω`.** Let
`q : 𝒮_V ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space whose image on
points lies in a set `Ω` of points of `|𝒳|`. Then every object of `𝒳` in the image of `q` lies in
`AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`. -/
theorem pointsWithin_obj_of_range_pointsMap_subset {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (q : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (hq : Set.range (AlgebraicStacks.pointsMap B S hS q) ⊆ Ω)
    (x : (fibredCategory B S hS V).val.obj) :
    pointsWithin 𝒳 Ω (q.hom.hom.toFunctor.obj x) := by
  refine pointsWithin_of_range_spacePointMap_subset B S hS V Ω q.hom.hom x.fiber.as ?_
  rintro _ ⟨y, rfl⟩
  have hcomp := spacePointMap_comp B S hS V (fibredCategory B S hS V) 𝒳.val
    (BasedFunctor.id _) q.hom.hom
  have h := congrFun hcomp (Space.pointsMap B S hS (yoneda.obj x.base)
    (yonedaEquiv.symm x.fiber.as) y)
  exact hq ⟨_, h.symm⟩

/-- **The factorization of a 1-morphism with image in an open set of points through the open
substack of that set.** Let `Ω` be an open set of points of `|𝒳|` and let `q : 𝒮_V ⟶ 𝒳` have image
in `Ω`. Then `q` factors, strictly, through the inclusion of the open substack
`AlgebraicGeometry.Stack.pointsWithinOpenSubstack` of `Ω`. -/
def pointsWithinOpenSubstackLift {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (q : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (hq : Set.range (AlgebraicStacks.pointsMap B S hS q) ⊆ Ω) :
    algebraicSpaceStack.{u, w} B S hS V hV ⟶
      fullSubcategoryAlgebraicStack 𝒳 (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ).property
        (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ).isAlgebraic :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift _ q.hom.hom.toFunctor
        (pointsWithin_obj_of_range_pointsMap_subset B S hS Ω hV q hq)
      w := q.hom.hom.w })

/-- The factorization `AlgebraicGeometry.Stack.pointsWithinOpenSubstackLift` composed with the
inclusion of the open substack is the 1-morphism it factors, on the nose. -/
theorem pointsWithinOpenSubstackLift_comp {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (q : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (hq : Set.range (AlgebraicStacks.pointsMap B S hS q) ⊆ Ω) :
    pointsWithinOpenSubstackLift B S hS Ω hΩ hV q hq ≫
      (pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ).inclusion = q :=
  rfl

/-- **The factorization through the open substack of `Ω` is smooth and surjective** as soon as
`q` is smooth with image exactly `Ω`: smoothness descends through the open immersion of the
open substack, and the points of the open substack are those of `Ω` (Stacks 06FJ), on which the
inclusion is injective. -/
theorem isSmooth_isSurjective_pointsWithinOpenSubstackLift {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (q : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
    (hqΩ : Set.range (AlgebraicStacks.pointsMap B S hS q) = Ω)
    (hqsm : AlgebraicStacks.IsSmooth B S hS q) :
    AlgebraicStacks.IsSmooth B S hS (pointsWithinOpenSubstackLift B S hS Ω hΩ hV q hqΩ.subset) ∧
      IsSurjective B S hS (pointsWithinOpenSubstackLift B S hS Ω hΩ hV q hqΩ.subset) := by
  let W := pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ
  let g := pointsWithinOpenSubstackLift B S hS Ω hΩ hV q hqΩ.subset
  refine ⟨AlgebraicStacks.isSmooth_of_comp_isOpenImmersion B S hS g W.inclusion
    W.isOpenImmersion hqsm (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV), ?_⟩
  have : (CatFiberedInGroupoids.homFunctor W.inclusion.hom).Full :=
    inferInstanceAs W.property.ι.Full
  have : (CatFiberedInGroupoids.homFunctor W.inclusion.hom).Faithful :=
    inferInstanceAs W.property.ι.Faithful
  intro y
  have hy : AlgebraicStacks.pointsMap B S hS W.inclusion y ∈ W.pointSet B S hS := ⟨y, rfl⟩
  rw [pointSet_pointsWithinOpenSubstack, ← hqΩ] at hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, pointsMap_injective_of_fullyFaithful B S hS W.inclusion ?_⟩
  exact (congrFun (AlgebraicStacks.pointsMap_comp B S hS g W.inclusion) x).symm.trans hx

section InertiaFullyFaithful

variable {𝒬 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒬 ⟶ 𝒳)
  (hf : (CatFiberedInGroupoids.homFunctor f.hom).FullyFaithful)

/-- The comparison `I_𝒬 ⟶ I_𝒳 ×_𝒳 𝒬` of Stacks 06R5 for a 1-morphism of algebraic stacks, as a
1-morphism of categories fibred in groupoids into the canonical 2-fibre product of Stacks 003Q. -/
noncomputable def inertiaFullyFaithfulComparisonAlgebraicStacks :
    (inertiaAlgebraicStack B S hS 𝒬).val ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom f.hom).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := inertiaPullbackComparison 𝒬.val.val.p 𝒳.val.val.p f.hom.hom.toFunctor
        f.hom.hom.w
      w := (inertiaPullbackComparison_isEquivalenceOver 𝒬.val.val.p 𝒳.val.val.p
        f.hom.hom.toFunctor f.hom.hom.w hf).elim (fun e => e.functor_over) }

/-- The inertia square of Stacks 06R5 of a fully faithful 1-morphism `f : 𝒬 ⟶ 𝒳`, as a square of
categories fibred in groupoids: the canonical 2-fibre product square of the cospan
`I_𝒳 ⟶ 𝒳 ⟵ 𝒬` reindexed along the comparison of Stacks 06R5. -/
noncomputable def inertiaFullyFaithfulCatSquare :
    Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom f.hom :=
  (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom f.hom).precompose
    (inertiaFullyFaithfulComparisonAlgebraicStacks B S hS f hf)

/-- **The inertia square of Stacks 06R5 in the 2-category of algebraic stacks.** For a
1-morphism `f : 𝒬 ⟶ 𝒳` of algebraic stacks over `S` whose underlying functor is fully faithful,
the square

```
I_𝒬 ----> I_𝒳
 |         |
 v         v
 𝒬 --f---> 𝒳
```

with apex the inertia of `𝒬`. -/
noncomputable def inertiaFullyFaithfulSquareAlgebraicStacks :
    Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳) f where
  pt := inertiaAlgebraicStack B S hS 𝒬
  fst := Bicategory.InducedBicategory.mkHom (inertiaFullyFaithfulCatSquare B S hS f hf).fst
  snd := Bicategory.InducedBicategory.mkHom (inertiaFullyFaithfulCatSquare B S hS f hf).snd
  iso := Bicategory.InducedBicategory.isoMk (inertiaFullyFaithfulCatSquare B S hS f hf).iso

/-- The second leg of the inertia square of Stacks 06R5 is the inertia projection of `𝒬`. -/
theorem inertiaFullyFaithfulSquareAlgebraicStacks_snd :
    (inertiaFullyFaithfulSquareAlgebraicStacks B S hS f hf).snd =
      inertiaProjectionAlgebraicStacks B S hS 𝒬 :=
  rfl

/-- **Stacks 06R5 in the 2-category of algebraic stacks.** If the underlying functor of the
1-morphism `f : 𝒬 ⟶ 𝒳` of algebraic stacks is fully faithful — as it is for a monomorphism, in
particular for the inclusion of an open substack — then the inertia of `𝒬` is the base change of
the inertia of `𝒳` along `f`: the square
`AlgebraicGeometry.Stack.inertiaFullyFaithfulSquareAlgebraicStacks` is a 2-fibre product.

The comparison of Stacks 06R5, `CategoryTheory.inertiaPullbackComparison_isEquivalenceOver`, is an
equivalence onto the canonical 2-fibre product, and the 2-category of algebraic stacks is a full
sub-2-category of categories fibred in groupoids. -/
noncomputable def isTwoFibreProduct_inertiaFullyFaithfulSquareAlgebraicStacks :
    Bicategory.IsTwoFibreProduct (inertiaFullyFaithfulSquareAlgebraicStacks B S hS f hf) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (Bicategory.TwoCommSq.PreHom.ofPrecompose _ _)
      ((inertiaPullbackComparison_isEquivalenceOver 𝒬.val.val.p 𝒳.val.val.p
        f.hom.hom.toFunctor f.hom.hom.w hf).elim (fun e => e.isEquivalence)))

end InertiaFullyFaithful

/-- **The square of algebraic stacks attached to a fibre product of algebraic spaces.** For
morphisms `a : X ⟶ Z` and `b : Y ⟶ Z` of algebraic spaces over `S`, the square of the attached
algebraic stacks with apex the algebraic stack of `X ×_Z Y`; its filler is an identity. -/
noncomputable def algebraicSpaceStackPullbackSquare
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (a : X ⟶ Z) (b : Y ⟶ Z) :
    Bicategory.TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hX hZ a)
      (algebraicSpaceStackMap.{u, w} B S hS hY hZ b) where
  pt := algebraicSpaceStack.{u, w} B S hS (pullback a b)
    (isAlgebraicSpace_pullback B S hS a b hX hY hZ)
  fst := Bicategory.InducedBicategory.mkHom (associatedMap B S hS (pullback.fst a b)).1
  snd := Bicategory.InducedBicategory.mkHom (associatedMap B S hS (pullback.snd a b)).1
  iso := Bicategory.InducedBicategory.isoMk (fibredCategorySquare (pullback.condition)).iso

/-- **A fibre product of algebraic spaces is a 2-fibre product of the attached algebraic
stacks** (Stacks 04T2 read through Stacks 0458): the square
`AlgebraicGeometry.Stack.algebraicSpaceStackPullbackSquare` is a 2-fibre product in the
2-category of algebraic stacks over `S`. -/
noncomputable def isTwoFibreProduct_algebraicSpaceStackPullbackSquare
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (a : X ⟶ Z) (b : Y ⟶ Z) :
    Bicategory.IsTwoFibreProduct
      (algebraicSpaceStackPullbackSquare.{u, w} B S hS hX hY hZ a b) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (isTwoFibreProduct_fibredCategorySquare (IsPullback.of_hasPullback a b))

/-- **Flatness and local finite presentation from one smooth diagram.** Let `c : 𝒵 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, and suppose given algebraic spaces `U`, `V`, a smooth
surjective `a : 𝒮_U ⟶ 𝒵`, a smooth `b : 𝒮_V ⟶ 𝒴` and a flat, locally finitely presented
`h : U ⟶ V` with `𝒮_h ≫ b ≅ a ≫ c`. Then `c` is flat and locally of finite presentation: this is
the definition of flatness (Stacks 06PW) and Stacks 06FM for local finite presentation. -/
theorem AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_smoothDiagram
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (c : 𝒵 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : (fibredCategory B S hS U) ⟶ 𝒵.val) (b : (fibredCategory B S hS V) ⟶ 𝒴.val)
    (h : U ⟶ V) (e : (associatedMap B S hS h).1 ≫ b ≅ a ≫ c.hom)
    (ha : IsRelativelySmooth B S hS a)
    (hasurj : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor a))
    (hb : IsRelativelySmooth B S hS b)
    (hflat : Space.IsFlat B S hS h) (hlfp : Space.IsLocallyOfFinitePresentation B S hS h) :
    AlgebraicStacks.IsFlat B S hS c ∧ AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c :=
  ⟨⟨U, V, hU, hV, a, b, h, ⟨e⟩, ha, hasurj, hb, hflat⟩,
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ f => Space.IsLocallyOfFinitePresentation B S hS f)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒵.property 𝒴.property c.hom).mpr ⟨U, V, hU, hV, a, b, h, ⟨e⟩, ha, hasurj, hb, hlfp⟩⟩

/-- **Stacks 06RC.** Let `𝒳` be a reduced algebraic stack over `S` whose inertia projection
`I_𝒳 ⟶ 𝒳` is quasi-compact. Then there is a dense open substack `𝒰 ⊆ 𝒳` which is a gerbe.

The proof is the source's. Choose a presentation `[U/R] ⟶ 𝒳` whose chart `U ⟶ 𝒳` is smooth and
surjective (Stacks 04T3); `U` is reduced (Stacks 04YF) and the stabilizer `G ⟶ U` is the base
change of `I_𝒳 ⟶ 𝒳` (Stacks 06PR), hence of finite type (Stacks 050Q). Generic flatness
(Stacks 06QS) gives a dense open `W ⊆ U` over which `G` is flat and locally of finite
presentation. The image `Ω` of `|W|` in `|𝒳|` is open, `W ⟶ 𝒳` being smooth, and dense; `𝒰` is the
open substack with `|𝒰| = Ω` (Stacks 06FJ), through which `W ⟶ 𝒳` factors by a smooth surjective
1-morphism. By Stacks 06R5 and Stacks 06PR the base change of `I_𝒰 ⟶ 𝒰` along `W ⟶ 𝒰` is
`G ×_U W ⟶ W`, so `I_𝒰 ⟶ 𝒰` is flat and locally of finite presentation, and `𝒰` is a gerbe by
Stacks 06QJ. -/
@[stacks 06RC]
theorem exists_openSubstack_dense_isGerbe (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hred : IsReducedStack B S hS 𝒳)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    ∃ W : OpenSubstack 𝒳, @Dense _ (pointTopology B S hS 𝒳.val) (W.pointSet B S hS) ∧
      AlgebraicStacks.IsGerbe B S hS
        (fullSubcategoryAlgebraicStack 𝒳 W.property W.isAlgebraic) := by
  obtain ⟨P, hp, hpsurj⟩ := exists_groupoidPresentation_isSmooth_isSurjective B S hS 𝒳
  obtain ⟨W, hW, hflat, hlfp⟩ :=
    exists_isDenseOpenSubspace_isFlat_presentationStabilizer B S hS hred hqc P hp
  let p := presentationObjectMorphismAlgebraicStacks B S hS P
  have hU := P.groupoid.objects.property
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor := hW.1.1
  let j := algebraicSpaceStackMap.{u, w} B S hS hWalg hU W.ι
  let q := j ≫ p
  have hq : AlgebraicStacks.IsSmooth B S hS q :=
    AlgebraicStacks.isSmooth_comp B S hS j p
      (isSmooth_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hWalg hU hW.1.2) hp
  let Ω := Set.range (AlgebraicStacks.pointsMap B S hS q)
  have hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω :=
    isOpen_range_pointsMap_of_isSmooth B S hS q hq
  let 𝒰' := pointsWithinOpenSubstack B S hS 𝒳 Ω hΩ
  refine ⟨𝒰', ?_, ?_⟩
  · -- density
    rw [pointSet_pointsWithinOpenSubstack]
    let _ := pointTopology B S hS 𝒳.val
    let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS _ hU).val
    have hj := dense_range_pointsMap_algebraicSpaceStackMap_of_isDenseOpenSubspace.{u, w}
      B S hS hU hW
    have hpc : Continuous (AlgebraicStacks.pointsMap B S hS p) :=
      continuous_pointsMap B S hS _ 𝒳.val p.hom.hom
    have hd := hpsurj.denseRange.dense_image hpc hj
    change Dense (Set.range (AlgebraicStacks.pointsMap B S hS (j ≫ p)))
    rw [AlgebraicStacks.pointsMap_comp, Set.range_comp]
    exact hd
  · -- the open substack is a gerbe
    let 𝒰 := fullSubcategoryAlgebraicStack 𝒳 𝒰'.property 𝒰'.isAlgebraic
    let ι := 𝒰'.inclusion
    let g := pointsWithinOpenSubstackLift B S hS Ω hΩ hWalg q le_rfl
    obtain ⟨hgsm, hgsurj⟩ :=
      isSmooth_isSurjective_pointsWithinOpenSubstackLift B S hS Ω hΩ hWalg q rfl hq
    have hff : (CatFiberedInGroupoids.homFunctor ι.hom).FullyFaithful :=
      ObjectProperty.fullyFaithfulι _
    let A := inertiaFullyFaithfulSquareAlgebraicStacks B S hS ι hff
    have hA := isTwoFibreProduct_inertiaFullyFaithfulSquareAlgebraicStacks B S hS ι hff
    let K : Bicategory.TwoCommSq A.snd g :=
      twoFibreProductSquareAlgebraicStacks B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒰) g
    have hK : Bicategory.IsTwoFibreProduct K :=
      isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ g
    have hAK := Bicategory.isTwoFibreProduct_paste hA hK
    let Bsq := inertiaPresentationSquareAlgebraicStacks B S hS P
    have hB := isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks B S hS P
    let Csq : Bicategory.TwoCommSq Bsq.snd j :=
      algebraicSpaceStackPullbackSquare.{u, w} B S hS
        (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property hWalg hU
        (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid).hom W.ι
    have hC : Bicategory.IsTwoFibreProduct Csq :=
      isTwoFibreProduct_algebraicSpaceStackPullbackSquare.{u, w} B S hS _ hWalg hU _ W.ι
    have hO := Bicategory.isTwoFibreProduct_paste hB hC
    let O : Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳) (g ≫ ι) :=
      Bsq.paste Csq
    let m : Bicategory.TwoCommSq.PreHom O (A.paste K) := _root_.Quotient.out (hAK.from O)
    have hm : (CatFiberedInGroupoids.homFunctor m.hom.hom).IsEquivalence :=
      isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hO hAK m
    -- the smooth 1-morphism `𝒮_{G ×_U W} ⟶ I_𝒰`
    have hgrel : IsRelativelySmooth B S hS g.hom :=
      isRelativelySmooth_of_isSmooth_of_isRepresentableByAlgebraicSpace B S hS g
        (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ hWalg) hgsm
    have hKfst : IsRelativelySmooth B S hS K.fst.hom :=
      isRelativelySmooth_baseChange.{u, u, u} B S hS _ _ _ g.hom
        (inertiaProjectionAlgebraicStacks B S hS 𝒰).hom K.underlying
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
        hgrel
    have ha : IsRelativelySmooth B S hS (m.hom ≫ K.fst).hom :=
      isRelativelySmooth_of_isEquivalence_comp B S hS m.hom.hom K.fst.hom hm hKfst
    have hasurj : IsSurjective B S hS (m.hom ≫ K.fst) :=
      isSurjective_comp B S hS m.hom K.fst (surjective_pointsMap_of_isEquivalence B S hS m.hom hm)
        (isSurjective_of_isTwoFibreProduct B S hS K.swap (Bicategory.isTwoFibreProduct_swap hK)
          hgsurj)
    let e : (associatedMap B S hS
        (pullback.snd (GroupoidInAlgebraicSpaces.stabilizerToObjects P.groupoid).hom W.ι)).1 ≫
          g.hom ≅ (m.hom ≫ K.fst).hom ≫ (inertiaProjectionAlgebraicStacks B S hS 𝒰).hom :=
      Bicategory.InducedBicategory.isoHom
        (Bicategory.whiskerRightIso m.isoSnd g ≪≫ Bicategory.associator _ _ _ ≪≫
          Bicategory.whiskerLeftIso m.hom K.iso.symm ≪≫ (Bicategory.associator _ _ _).symm)
    obtain ⟨hIflat, hIlfp⟩ :=
      AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_smoothDiagram B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒰)
        (isAlgebraicSpace_pullback B S hS _ W.ι
          (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property hWalg hU)
        hWalg (m.hom ≫ K.fst).hom g.hom _ e ha
        (isSurjectiveOnObjects_of_pointsMap_surjective B S hS (m.hom ≫ K.fst) hasurj)
        hgrel hflat hlfp
    exact AlgebraicStacks.isGerbe_of_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection
      B S hS 𝒰 hIflat hIlfp

end AlgebraicGeometry.Stack

end
