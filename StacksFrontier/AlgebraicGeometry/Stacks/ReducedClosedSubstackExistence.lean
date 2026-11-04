module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceSmoothPreimage
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackFromChart
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Reduction
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionCanonicalMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction

/-!
# Existence of the reduced closed substack on a closed set of points

Let `𝒳` be an algebraic stack over `S` and let `T ⊆ |𝒳|` be closed. There is a unique closed
substack `𝒵 ⊆ 𝒳` with `|𝒵| = T` and `𝒵` reduced. This file proves existence, and combines it with
uniqueness, `AlgebraicGeometry.Stack.eq_of_isReducedStack_of_range_pointsMap_eq`.

## Main definitions

* `AlgebraicGeometry.Stack.chartPointMap`: the map `|W₀| ⟶ |𝒳|` of a chart by a scheme.
* `AlgebraicGeometry.Stack.chartReducedSubspace`: the reduced closed subspace of the chart on the
  inverse image of `T`.
* `AlgebraicGeometry.Stack.subspaceToSlice`: the category of elements of a subspace of `W₀`, read
  in the slice of the site over `W₀`.

## Main results

* `AlgebraicGeometry.Stack.isChartInvariant_chartReducedSubspace`: the reduced closed subspace of
  a smooth chart is invariant under the self-intersection of the chart.
* `AlgebraicGeometry.Stack.range_pointsMap_chartLocus_chartReducedSubspace`: the closed substack it
  cuts out has `T` as its set of points.
* `AlgebraicGeometry.Stack.isReducedStack_chartLocus`: that closed substack is reduced.
* `AlgebraicGeometry.Stack.exists_isClosedSubstack_isReducedStack_range_pointsMap_eq`: there is a
  reduced closed substack whose set of points is `T`.
* `AlgebraicGeometry.Stack.exists_isReducedInducedStackStructure`: the same, in the vocabulary of
  the reduced induced algebraic stack structure.
* `AlgebraicGeometry.Stack.exists_isClosedImmersion_range_pointsMap_eq`: the same, read as a
  closed immersion of algebraic stacks whose image on points is the given closed set.
* `AlgebraicGeometry.Stack.existsUnique_reducedClosedSubstack`: there is a unique reduced closed
  substack whose set of points is `T`.
* `AlgebraicGeometry.Stack.exists_reduction`: every algebraic stack has a reduction.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {W₀ : BigFppfOver B S hS}
  (f : (schemeFibredCategory B S hS W₀).val ⥤ᵇ 𝒳.val.val)

/-- A chart by the category represented by a scheme `W₀`, read as a 1-morphism out of the
category of elements of the algebraic space `W₀` represents. -/
noncomputable def chartSpaceMap : (fibredCategory B S hS (yoneda.obj W₀)).val ⥤ᵇ 𝒳.val.val :=
  (schemeFibredCategoryEquivalence B S hS W₀).inverse.comp f

/-- The map `|W₀| ⟶ |𝒳|` on points induced by a chart by a scheme `W₀`. -/
noncomputable def chartPointMap :
    Space.points B S hS (yoneda.obj W₀) → AlgebraicStacks.points B S hS 𝒳 :=
  spacePointMap B S hS (yoneda.obj W₀) 𝒳.val (chartSpaceMap f)

/-- The map on points induced by a chart is continuous. -/
theorem continuous_chartPointMap :
    @Continuous _ _ (Space.pointTopology B S hS (yoneda.obj W₀)) (pointTopology B S hS 𝒳.val)
      (chartPointMap f) :=
  continuous_spacePointMap B S hS (yoneda.obj W₀) (isAlgebraicSpace_yoneda B S hS W₀) 𝒳.val
    (chartSpaceMap f)

variable (T : Set (AlgebraicStacks.points B S hS 𝒳))
  (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T)

/-- The reduced closed subspace of `W₀` on the inverse image of `T` along the map on points of
the chart. -/
noncomputable def chartReducedSubspace :
    Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Space.reducedClosedSubspace B S hS (yoneda.obj W₀) (isAlgebraicSpace_yoneda B S hS W₀)
    (chartPointMap f ⁻¹' T)
    (@IsClosed.preimage _ _ (Space.pointTopology B S hS (yoneda.obj W₀))
      (pointTopology B S hS 𝒳.val) (chartPointMap f) (continuous_chartPointMap f) T hT)

/-- The algebraic space represented by `W₀`. -/
abbrev chartSpace (W₀ : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩

/-- For the self-intersection `ℛ = 𝒮_{W₀} ×_𝒳 𝒮_{W₀}` of a chart, represented by an algebraic
space `R`, the source and target maps `R ⟶ W₀` followed by the map on points of the chart agree on
points. -/
theorem chartPointMap_relationSourceMap_eq {R : AlgebraicSpaces B S hS}
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS W₀) 𝒳.val f).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p)
    (x : Space.points B S hS R.obj) :
    chartPointMap f (Space.pointsMap B S hS R.obj (SelfIntersection.relationSourceMap
        (U := chartSpace W₀) (PresheafOfCategories.sliceElementsEquivalenceOver W₀) eR) x) =
      chartPointMap f (Space.pointsMap B S hS R.obj (SelfIntersection.relationTargetMap
        (U := chartSpace W₀) (PresheafOfCategories.sliceElementsEquivalenceOver W₀) eR) x) := by
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver W₀
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  show spacePointMap B S hS (yoneda.obj W₀) 𝒳.val (chartSpaceMap f)
      ((Space.FieldValuedPoint.map B S hS R.obj
        (SelfIntersection.relationSourceMap (U := chartSpace W₀) eU eR) p).class B S hS _) =
    spacePointMap B S hS (yoneda.obj W₀) 𝒳.val (chartSpaceMap f)
      ((Space.FieldValuedPoint.map B S hS R.obj
        (SelfIntersection.relationTargetMap (U := chartSpace W₀) eU eR) p).class B S hS _)
  rw [spacePointMap_class, spacePointMap_class]
  apply (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property _ _).2
  refine ⟨_, ⟨𝟙 _⟩, ⟨?_⟩⟩
  let Wp := p.siteObject
  let ρ := eR.inv.functor.obj (⟨Wp, Discrete.mk p.value⟩ :
    (presheafOfCategories (R.obj ⋙ typeToCat)).obj)
  have hρ : (SelfIntersection.relation B S hS (schemeFibredCategory B S hS W₀) 𝒳.val f).val.p.obj
      ρ = Wp := Functor.congr_obj eR.inv.w _
  have hval : PresheafOfCategories.sectionOfObj eR ρ hρ = p.value :=
    PresheafOfCategories.sectionOfObj_inv_obj eR _
  have hs := SelfIntersection.relationSourceMap_sectionOfObj (U := chartSpace W₀) eU eR ρ hρ
  rw [hval] at hs
  have ht := SelfIntersection.relationTargetMap_sectionOfObj (U := chartSpace W₀) eU eR ρ hρ
  rw [hval] at ht
  let iy := SelfIntersection.representingObjIsoOfSection (U := chartSpace W₀)
    (𝒰 := schemeFibredCategory B S hS W₀) eU ρ.y (SelfIntersection.relation_obj_y hρ)
  let ix := SelfIntersection.representingObjIsoOfSection (U := chartSpace W₀)
    (𝒰 := schemeFibredCategory B S hS W₀) eU ρ.x (SelfIntersection.relation_obj_x hρ)
  show f.obj (Over.mk ((SelfIntersection.relationSourceMap (U := chartSpace W₀) eU eR).app
      (op Wp) p.value)) ⟶
    f.obj (Over.mk ((SelfIntersection.relationTargetMap (U := chartSpace W₀) eU eR).app
      (op Wp) p.value))
  rw [hs, ht]
  exact f.map (Functor.Fiber.fiberInclusion.map iy.hom) ≫ ρ.iso.inv ≫
    f.map (Functor.Fiber.fiberInclusion.map ix.inv)

omit hT in
/-- Two reduced closed subspaces on equal closed sets of points are equal. -/
theorem reducedClosedSubspace_congr {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T₁ T₂ : Set (Space.points B S hS X)}
    (h₁ : @IsClosed _ (Space.pointTopology B S hS X) T₁)
    (h₂ : @IsClosed _ (Space.pointTopology B S hS X) T₂) (h : T₁ = T₂) :
    Space.reducedClosedSubspace B S hS X hX T₁ h₁ =
      Space.reducedClosedSubspace B S hS X hX T₂ h₂ := by
  subst h
  rfl

/-- For a chart `f` representable by algebraic spaces and smooth, the reduced closed subspace
`chartReducedSubspace f T hT` is invariant in the sense of
`AlgebraicGeometry.Stack.IsChartInvariant`. -/
theorem isChartInvariant_chartReducedSubspace
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f : schemeFibredCategory B S hS W₀ ⟶ 𝒳.val) hrep) :
    IsChartInvariant f (chartReducedSubspace f T hT) := by
  intro a b φ g hφ hb
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS W₀).val.p
      (presheafOfCategories ((chartSpace W₀).obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver W₀
  obtain ⟨Rsp, hRsp, ⟨eR⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (schemeFibredCategory B S hS W₀) 𝒳.val f 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W₀)
  let R : AlgebraicSpaces B S hS := ⟨Rsp, hRsp⟩
  let sR := SelfIntersection.relationSourceMap (U := chartSpace W₀) (R := R) eU eR
  let tR := SelfIntersection.relationTargetMap (U := chartSpace W₀) (R := R) eU eR
  have hsm_s : Space.IsSmooth B S hS sR :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_source (𝒳 := 𝒳.val)
      (F := Bicategory.InducedBicategory.mkHom f) (U := chartSpace W₀) (R := R) eU eR hrep
      hsmooth 𝒳.property
  have hsm_t : Space.IsSmooth B S hS tR :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_target (𝒳 := 𝒳.val)
      (F := Bicategory.InducedBicategory.mkHom f) (U := chartSpace W₀) (R := R) eU eR hrep
      hsmooth 𝒳.property
  have hW := isAlgebraicSpace_yoneda B S hS W₀
  have hpts : Space.pointsMap B S hS R.obj sR ⁻¹' (chartPointMap f ⁻¹' T) =
      Space.pointsMap B S hS R.obj tR ⁻¹' (chartPointMap f ⁻¹' T) := by
    ext x
    simp only [Set.mem_preimage]
    rw [chartPointMap_relationSourceMap_eq f eR x]
  have hinv : (chartReducedSubspace f T hT).preimage sR =
      (chartReducedSubspace f T hT).preimage tR := by
    rw [chartReducedSubspace,
      Space.preimage_reducedClosedSubspace_of_isSmooth B S hS hW R.property sR hsm_s,
      Space.preimage_reducedClosedSubspace_of_isSmooth B S hS hW R.property tR hsm_t]
    exact reducedClosedSubspace_congr R.property _ _ hpts
  let a' : Over W₀ := Over.mk (g ≫ b.hom)
  have hfib : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  have hm := isHomLift_overHomMk b g
  have hψ : 𝒳.val.val.p.IsHomLift g (f.map (Over.homMk g rfl : a' ⟶ b)) :=
    BasedFunctor.preserves_isHomLift f g _
  have hcart : 𝒳.val.val.p.IsStronglyCartesian g (f.map (Over.homMk g rfl : a' ⟶ b)) :=
    hfib.isStronglyCartesian_homLift g _
  let χ : f.obj a ⟶ f.obj a' :=
    Functor.IsStronglyCartesian.map 𝒳.val.val.p g (f.map (Over.homMk g rfl : a' ⟶ b))
      (f' := g) (g := 𝟙 a.left) (by simp) φ
  have hχ : 𝒳.val.val.p.IsHomLift (𝟙 a.left) χ := inferInstance
  let αF : (Functor.Fiber.mk (SelfIntersection.fObj_over (U := chartSpace W₀) (f := f) eU a.hom) :
      𝒳.val.val.p.Fiber a.left) ⟶
      Functor.Fiber.mk (SelfIntersection.fObj_over (U := chartSpace W₀) (f := f) eU a'.hom) :=
    ⟨χ, hχ⟩
  let r := SelfIntersection.arrowOfFiberHom (U := chartSpace W₀) (R := R) eU eR a'.hom a.hom αF
  have hr_s : sR.app (op a.left) r = a'.hom :=
    SelfIntersection.relationSourceMap_arrowOfFiberHom (U := chartSpace W₀) (R := R) eU eR
      a'.hom a.hom αF
  have hr_t : tR.app (op a.left) r = a.hom :=
    SelfIntersection.relationTargetMap_arrowOfFiberHom (U := chartSpace W₀) (R := R) eU eR
      a'.hom a.hom αF
  have hrs : r ∈ ((chartReducedSubspace f T hT).preimage sR).obj (op a.left) := by
    show sR.app (op a.left) r ∈ (chartReducedSubspace f T hT).obj (op a.left)
    rwa [hr_s]
  rw [hinv] at hrs
  change tR.app (op a.left) r ∈ (chartReducedSubspace f T hT).obj (op a.left) at hrs
  rwa [hr_t] at hrs

omit T hT in
/-- For a locally essentially surjective chart, every field-valued point of `𝒳` receives a
morphism from the image of a field-valued point of `W₀`. -/
theorem exists_spaceFieldValuedPoint_hom (hloc : IsChartLocallyEssSurj f)
    (q : FieldValuedPoint B S hS 𝒳.val.val) :
    ∃ p₀ : Space.FieldValuedPoint B S hS (yoneda.obj W₀),
      Nonempty (f.obj (Over.mk p₀.value) ⟶ q.obj) := by
  have hqField : IsFieldObject B S hS q.base := ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩
  obtain ⟨R, hR, hlift⟩ := hloc q.base ⟨q.obj, q.over⟩
  obtain ⟨V, g, hV, hg⟩ := exists_isFieldObject_arrow_of_mem_topology B S hS hqField hR
  obtain ⟨z, φ, hφ⟩ := hlift hg
  obtain ⟨k, hk, ⟨eV⟩⟩ := hV
  have hzV : z.left = V :=
    (Functor.congr_obj f.w z).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p g φ)
  subst hzV
  let : Field k := hk
  let Q : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := k, field := hk, base := z.left, isSpec := eV, obj := f.obj z,
      «over» := Functor.congr_obj f.w z }
  refine ⟨Space.FieldValuedPoint.map B S hS (yoneda.obj z.left) (yoneda.map z.hom)
    (baseSpacePoint B S hS Q), ⟨?_⟩⟩
  exact f.map (Over.homMk (spectrumSiteObjectIso B S hS Q).hom rfl) ≫ φ

omit T hT in
/-- The point of `|𝒳|` the chart assigns to a field-valued point of `W₀` is the point of any
field-valued point of `𝒳` receiving a morphism from its image. -/
theorem chartPointMap_class_eq (p₀ : Space.FieldValuedPoint B S hS (yoneda.obj W₀))
    (q : FieldValuedPoint B S hS 𝒳.val.val) (φ : f.obj (Over.mk p₀.value) ⟶ q.obj) :
    chartPointMap f (p₀.class B S hS _) = pointClass B S hS 𝒳.val.val 𝒳.val.property q := by
  rw [chartPointMap, spacePointMap_class]
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property _ _).2
    ⟨_, ⟨𝟙 _⟩, ⟨φ⟩⟩

/-- For an invariant reduced closed subspace and a locally essentially surjective chart, the set
of points of the locus of `chartReducedSubspace f T hT` is `T`. -/
theorem range_pointsMap_chartLocus_chartReducedSubspace
    (hZ : IsChartInvariant f (chartReducedSubspace f T hT)) (hloc : IsChartLocallyEssSurj f)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (chartLocus f (chartReducedSubspace f T hT)))) :
    Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (chartLocus f (chartReducedSubspace f T hT)) hP)) = T := by
  set Z := chartReducedSubspace f T hT with hZdef
  have hrange : Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) = chartPointMap f ⁻¹' T :=
    Space.range_pointsMap_ι_reducedClosedSubspace B S hS (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B S hS W₀) _ _
  ext t
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    obtain ⟨p₀, ⟨φ⟩⟩ := exists_spaceFieldValuedPoint_hom f hloc
      (fieldValuedPointMap B S hS _ (fullSubcategoryInclusion 𝒳 _ hP).hom.hom q)
    have hmem : p₀.value ∈ Z.obj (op p₀.siteObject) := q.obj.property (Over.mk p₀.value) φ
    let pZ : Space.FieldValuedPoint B S hS Z.toFunctor :=
      { carrier := p₀.carrier, field := p₀.field, contained := p₀.contained,
        toBase := p₀.toBase, value := ⟨p₀.value, hmem⟩ }
    have hp : p₀.class B S hS _ = Space.pointsMap B S hS Z.toFunctor Z.ι (pZ.class B S hS _) :=
      rfl
    have ht : chartPointMap f (p₀.class B S hS _) ∈ T := by
      rw [← Set.mem_preimage, ← hrange, hp]
      exact Set.mem_range_self _
    show pointClass B S hS 𝒳.val.val 𝒳.val.property
      (fieldValuedPointMap B S hS _ (fullSubcategoryInclusion 𝒳 _ hP).hom.hom q) ∈ T
    rwa [← chartPointMap_class_eq f p₀ _ φ]
  · intro ht
    obtain ⟨q, rfl⟩ := Quotient.exists_rep t
    obtain ⟨p₀, ⟨φ⟩⟩ := exists_spaceFieldValuedPoint_hom f hloc q
    have hq : pointClass B S hS 𝒳.val.val 𝒳.val.property q ∈ T := ht
    rw [← chartPointMap_class_eq f p₀ q φ, ← Set.mem_preimage, ← hrange] at hq
    obtain ⟨w, hw⟩ := hq
    obtain ⟨pZ, rfl⟩ := Quot.exists_rep w
    let r := Space.FieldValuedPoint.map B S hS Z.toFunctor Z.ι pZ
    have hr : r.class B S hS _ = p₀.class B S hS _ := hw
    have hrZ : chartLocus f Z (f.obj (Over.mk r.value)) :=
      (chartLocus_obj_iff hZ (Over.mk r.value)).2 pZ.value.2
    let qZ : FieldValuedPoint B S hS (fullSubcategoryBased 𝒳 (chartLocus f Z)) :=
      { carrier := r.carrier, field := r.field, base := r.siteObject, isSpec := Iso.refl _,
        obj := ⟨f.obj (Over.mk r.value), hrZ⟩, «over» := Functor.congr_obj f.w _ }
    refine ⟨pointClass B S hS _ (Classical.choose hP) qZ, ?_⟩
    show pointClass B S hS 𝒳.val.val 𝒳.val.property
      (fieldValuedPointMap B S hS _ (fullSubcategoryInclusion 𝒳 _ hP).hom.hom qZ) = _
    rw [← chartPointMap_class_eq f r _ (𝟙 _), hr]
    exact chartPointMap_class_eq f p₀ q φ

section Reduced

variable (W₀) in
/-- The category of elements of a subspace `Z` of the algebraic space represented by `W₀`, read in
the slice of the site over `W₀`: a section of `Z` over `T` is a morphism `T ⟶ W₀`. -/
def subspaceToSlice (Z : Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    (fibredCategory B S hS Z.toFunctor).val ⥤ᵇ (schemeFibredCategory B S hS W₀).val where
  toFunctor :=
    { obj X := Over.mk X.fiber.as.1
      map {_ _} u := Over.homMk u.base (congrArg Subtype.val (Discrete.eq_of_hom u.fiber)).symm
      map_id _ := by apply Over.OverMorphism.ext; rfl
      map_comp _ _ := by apply Over.OverMorphism.ext; rfl }
  w := rfl

/-- The functor underlying `subspaceToSlice W₀ Z` is faithful. -/
instance (Z : Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    (subspaceToSlice W₀ Z).toFunctor.Faithful where
  map_injective {_ _} u v h :=
    PresheafOfCategories.elements_hom_ext (G := Z.toFunctor) u v (congrArg CommaMorphism.left h)

/-- The functor underlying `subspaceToSlice W₀ Z` is full. -/
instance (Z : Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    (subspaceToSlice W₀ Z).toFunctor.Full where
  map_surjective {X Y} g := by
    refine ⟨(PresheafOfCategories.homEquiv (Z.toFunctor ⋙ typeToCat) X Y).symm
      ⟨g.left, Discrete.eqToHom (Subtype.ext (Over.w g).symm)⟩, ?_⟩
    apply Over.OverMorphism.ext
    rfl

/-- The locus of a reduced invariant closed subspace of a smooth surjective chart is a reduced
algebraic stack. -/
theorem isReducedStack_chartLocus {Z : Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hZ : IsChartInvariant f Z) (hZc : Space.IsClosedSubspace B S hS Z)
    (hZr : Space.HasEtaleLocalProperty B S hS Z.toFunctor (fun X : Scheme.{u} => IsReduced X))
    (hfS : AlgebraicStacks.IsSmooth B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f) :
        schemeStack.{u, w} B S hS W₀ ⟶ 𝒳))
    (hfSs : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f) :
        schemeStack.{u, w} B S hS W₀ ⟶ 𝒳))
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (chartLocus f Z))) :
    IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 (chartLocus f Z) hP) := by
  let P := chartLocus f Z
  let fS : schemeStack.{u, w} B S hS W₀ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f)
  let incl := fullSubcategoryInclusion 𝒳 P hP
  let Q := twoFibreProductSquareAlgebraicStacks B S hS incl fS
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS incl fS
  have hsm : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS fS incl Q hQ hfS
  have hsu : IsSurjective B S hS Q.fst :=
    isSurjective_of_isTwoFibreProduct B S hS Q.swap (Bicategory.isTwoFibreProduct_swap hQ) hfSs
  let K := subspaceToSlice W₀ Z
  have hmem : ∀ w, P (f.obj (K.obj w)) := fun w => (chartLocus_obj_iff hZ _).2 w.fiber.as.2
  let H : (fibredCategory B S hS Z.toFunctor).val.obj ⥤ P.FullSubcategory :=
    P.lift (K.toFunctor ⋙ f.toFunctor) hmem
  have hH : H ⋙ (fullSubcategoryBased 𝒳 P).p = (fibredCategory B S hS Z.toFunctor).val.p := by
    show (K.toFunctor ⋙ f.toFunctor) ⋙ 𝒳.val.val.p = _
    rw [Functor.assoc, f.w]
    exact K.w
  let t : H ⋙ (fullSubcategoryBasedInclusion 𝒳 P).toFunctor ≅ K.toFunctor ⋙ f.toFunctor :=
    Iso.refl _
  have ht : ∀ w, 𝒳.val.val.p.IsHomLift (𝟙 ((fibredCategory B S hS Z.toFunctor).val.p.obj w))
      (t.hom.app w) := fun w => IsHomLift.id (Functor.congr_obj hH w)
  let eF := TwoFibreProductOver.lift (fullSubcategoryBased 𝒳 P).p
    (schemeFibredCategory B S hS W₀).val.p 𝒳.val.val.p
    (fullSubcategoryBasedInclusion 𝒳 P).toFunctor f.toFunctor
    (fibredCategory B S hS Z.toFunctor).val.p H K.toFunctor hH K.w t ht
  have hess : eF.EssSurj := by
    refine ⟨fun Y => ?_⟩
    obtain ⟨U, x, y, hx, hy, iso, vert⟩ := Y
    change y.left = U at hy
    subst hy
    have hy : P (f.obj y) := chartLocus_of_hom f Z iso.inv x.property
    have hyZ : y.hom ∈ Z.obj (op y.left) := (chartLocus_obj_iff hZ y).1 hy
    let w : (fibredCategory B S hS Z.toFunctor).val.obj := ⟨y.left, Discrete.mk ⟨y.hom, hyZ⟩⟩
    have hvi : 𝒳.val.val.p.IsHomLift (𝟙 y.left) iso.inv := by
      simpa using IsHomLift.inv 𝒳.val.val.p (𝟙 y.left) iso.hom
    let φ : eF.obj w ⟶ ⟨y.left, x, y, hx, rfl, iso, vert⟩ :=
      { hbase := 𝟙 y.left
        a := ObjectProperty.homMk iso.inv
        b := 𝟙 y
        ha := (Functor.isHomLift_comp_iff P.ι 𝒳.val.val.p _ _).2 hvi
        hb := IsHomLift.id rfl
        w := by
          show iso.inv ≫ iso.hom = 𝟙 _ ≫ f.map (𝟙 y)
          simp }
    have : IsIso φ := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ φ
      (by
        show IsIso (ObjectProperty.homMk iso.inv : (⟨_, hmem w⟩ : P.FullSubcategory) ⟶ x)
        have : IsIso (P.ι.map (ObjectProperty.homMk iso.inv :
            (⟨_, hmem w⟩ : P.FullSubcategory) ⟶ x)) := by
          show IsIso iso.inv
          infer_instance
        exact isIso_of_reflects_iso _ P.ι)
      (by change IsIso (𝟙 y); infer_instance)
    exact ⟨w, ⟨asIso φ⟩⟩
  let eB : (fibredCategory B S hS Z.toFunctor).val ⥤ᵇ Q.pt.val.val :=
    ⟨eF, TwoFibreProductOver.lift_comp_structureFunctor ..⟩
  let e : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZc.1 ⟶ Q.pt :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom eB)
  have hfa : eF.Faithful := TwoFibreProductOver.faithful_lift _ _ _ _ _ _ _ _ _ _ _ _
  have : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Faithful :=
    (inferInstance : P.ι.Faithful)
  have hfu : eF.Full := TwoFibreProductOver.full_lift _ _ _ _ _ _ _ _ _ _ _ _
  have he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom) :=
    { faithful := hfa, full := hfu, essSurj := hess }
  have : e.hom.hom.toFunctor.EssSurj := hess
  have hes : IsSurjective B S hS e := pointsMap_surjective_of_essSurj B S hS _ _ e.hom.hom
  have hZred : IsReducedStack B S hS (algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZc.1) :=
    (scheme_atlas_iff_etaleLocalProperty B S hS (fun X : Scheme.{u} => IsReduced X)
      Z.toFunctor hZc.1).2 hZr
  obtain ⟨V, a, hasurj, hasmooth, hV⟩ :=
    isReducedStack_of_isEquivalence_stackMorphism e he hes hZred
  exact ⟨V, a ≫ Q.fst, isSurjective_comp B S hS a Q.fst hasurj hsu,
    AlgebraicStacks.isSmooth_comp B S hS a Q.fst hasmooth hsm, hV⟩

end Reduced

/-! ### Existence -/

omit f in
/-- Let `𝒳` be an algebraic stack over `S` and let `T` be a closed subset of `|𝒳|`. There is a
closed substack `𝒵` of `𝒳` with (a) `|𝒵| = T` and (b) `𝒵` reduced, both asserted for every proof
that the full subcategory is an algebraic stack. -/
theorem exists_isClosedSubstack_isReducedStack_range_pointsMap_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsClosedSubstack 𝒳 P ∧
      ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = T ∧
          IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) := by
  obtain ⟨_hfib, _hst, _hdiag, W₀, f₀, hrep, hfprop⟩ := 𝒳.property
  let f : (schemeFibredCategory B S hS W₀).val ⥤ᵇ 𝒳.val.val := f₀
  have hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom f : schemeFibredCategory B S hS W₀ ⟶ 𝒳.val) hrep :=
    fun V y hy G hG he => (hfprop V y hy G hG he).2
  have hloc : IsChartLocallyEssSurj f :=
    localEssSurj_of_isSurjective_isSmooth B S hS (Bicategory.InducedBicategory.mkHom f) hrep
      hfprop
  have hfS : AlgebraicStacks.IsSmooth B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f) :
        schemeStack.{u, w} B S hS W₀ ⟶ 𝒳) :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hrep hsmooth
  have hfSs : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f) :
        schemeStack.{u, w} B S hS W₀ ⟶ 𝒳) :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ hrep).mpr
      (fun V y hy G hG he => (hfprop V y hy G hG he).1)
  have hZ := isChartInvariant_chartReducedSubspace f T hT hrep hsmooth
  have hZc : Space.IsClosedSubspace B S hS (chartReducedSubspace f T hT) :=
    Space.isClosedSubspace_reducedClosedSubspace B S hS (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B S hS W₀) _ _
  have hZr : Space.HasEtaleLocalProperty B S hS (chartReducedSubspace f T hT).toFunctor
      (fun X : Scheme.{u} => IsReduced X) :=
    Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS (yoneda.obj W₀)
      (isAlgebraicSpace_yoneda B S hS W₀) _ _
  exact ⟨chartLocus f (chartReducedSubspace f T hT), isClosedSubstack_chartLocus hZ hZc hloc,
    fun hP => ⟨range_pointsMap_chartLocus_chartReducedSubspace f T hT hZ hloc hP,
      isReducedStack_chartLocus f hZ hZc hZr hfS hfSs hP⟩⟩

/-- Every closed set of points of an algebraic stack carries a reduced induced algebraic stack
structure, `AlgebraicGeometry.Stack.IsReducedInducedStackStructure`. -/
theorem exists_isReducedInducedStackStructure
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsReducedInducedStackStructure B S hS T P := by
  obtain ⟨P, hP, h⟩ := exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳 T hT
  exact ⟨P, ⟨hP, fun hA => (h hA).1⟩, fun hA => (h hA).2⟩

/-- Every closed set of points of an algebraic stack is the image on points of a closed
immersion of algebraic stacks. -/
theorem exists_isClosedImmersion_range_pointsMap_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (T : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (i : 𝒵 ⟶ 𝒳),
      AlgebraicStacks.IsClosedImmersion B S hS i ∧
        Set.range (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom) = T := by
  obtain ⟨P, hP, h⟩ := exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳 T hT
  obtain ⟨hA, hi⟩ := hP.2
  exact ⟨fullSubcategoryAlgebraicStack 𝒳 P hA, fullSubcategoryInclusion 𝒳 P hA, hi, (h hA).1⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Existence and uniqueness -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (T : Set (AlgebraicStacks.points B S hS 𝒳)) (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T)

include hT

/-- Let `𝒳` be an algebraic stack over `S` and let `T` be a closed subset of its space of points
`|𝒳|`. There exists a unique closed substack `𝒵 ⊆ 𝒳` such that (a) `|𝒵| = T` and (b) `𝒵` is
reduced.

A closed substack is a property of the objects of `𝒳` cutting out a strictly full subcategory
which is an algebraic stack with closed immersion inclusion
(`AlgebraicGeometry.Stack.IsClosedSubstack`); its set of points is the image of the map on points
of its inclusion. Both clauses are stated for every proof that the full subcategory is an
algebraic stack. -/
@[stacks 0509]
theorem existsUnique_reducedClosedSubstack :
    ∃! P : ObjectProperty 𝒳.val.val.obj, IsClosedSubstack 𝒳 P ∧
      (∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP)) = T) ∧
      ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) := by
  obtain ⟨P, ⟨hc, hpts⟩, hred⟩ := exists_isReducedInducedStackStructure 𝒳 T hT
  refine ⟨P, ⟨hc, hpts, hred⟩, fun Q ⟨hQc, hQpts, hQred⟩ => ?_⟩
  exact IsReducedInducedStackStructure.unique B S hS ⟨⟨hQc, hQpts⟩, hQred⟩ ⟨⟨hc, hpts⟩, hred⟩

omit hT in
/-- Every algebraic stack has a reduction: a reduced closed substack whose inclusion is
surjective on points. -/
theorem exists_reduction :
    ∃ P : ObjectProperty 𝒳.val.val.obj, IsClosedSubstack 𝒳 P ∧
      ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) ∧
          IsSurjective B S hS (fullSubcategoryInclusion 𝒳 P hP) := by
  let _ := pointTopology B S hS 𝒳.val
  obtain ⟨P, ⟨hc, hpts⟩, hred⟩ := exists_isReducedInducedStackStructure 𝒳 Set.univ isClosed_univ
  exact ⟨P, hc, fun hP => ⟨hred hP, Set.range_eq_univ.1 (hpts hP)⟩⟩

end Main

end AlgebraicGeometry.Stack

end
