module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackBootstrap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# The tautological chart of an algebraic stack presented by a groupoid

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` and let `𝒳` be an algebraic
stack together with an equivalence `[U/R] ≃ 𝒳` over the site. The projection
`π : U ⟶ [U/R]` of Stacks 044R, followed by that equivalence, is a 1-morphism from the algebraic
stack of `U` to `𝒳`, the tautological chart of `𝒳`. Every property of morphisms of algebraic
spaces that is stable under base change and local on the base for the fppf topology passes from
the source map `s` to this chart; in particular the chart is smooth when `s` is, and has relative
dimension `d` at every point when `s` is smooth of relative dimension `d`, so that
`dim_x(𝒳) = dim_u(U) - d` at the image `x` of every `u ∈ |U|`.

## Main definitions

* `AlgebraicGeometry.Stack.quotientChart`: the chart `U ⟶ 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientChart`: the chart has every relative
  property the source map has.
* `AlgebraicGeometry.Stack.isSmooth_quotientChart`: the chart of a smooth groupoid is smooth.
* `AlgebraicGeometry.Stack.surjective_pointsMap_quotientChart`: the chart is surjective on
  points.
* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_of_hasRelativeProperty`: a 1-morphism from an
  algebraic space which is smooth of relative dimension `d` in the relative sense of Stacks 03YK
  has relative dimension `d` (Stacks 0DRG) at every point.
* `AlgebraicGeometry.Stack.dimensionAtPoint_quotientChart`: `dim_x(𝒳) = dim_u(U) - d` when the
  source map is smooth of relative dimension `d`.
* `AlgebraicGeometry.Stack.spacePointMap_quotientChart_eq_iff`: Stacks 04XJ for the chart, two
  points of `U` have the same image in `|𝒳|` exactly when they are joined by a point of `R`.
* `AlgebraicGeometry.Stack.isQuotientMap_spacePointMap_quotientChart`: `|𝒳|` carries the quotient
  topology of `|U|`.
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_of_quotientChart`: `𝒳` is locally Noetherian
  when `U` is.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04XJ](https://stacks.math.columbia.edu/tag/04XJ)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### Relative dimension from a relative property -/

/-- A 1-morphism from an algebraic space which is smooth of relative dimension `d` in the
relative sense of Stacks 03YK has relative dimension `d` at every point in the sense of
Stacks 0DRG. -/
theorem relativeDimensionAt_eq_of_hasRelativeProperty
    (T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace C S hS T)
    (𝒳 : AlgebraicStacks.{u, w} C S hS)
    (f : algebraicSpaceStack.{u, w} C S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType C S hS f) (d : ℕ)
    (hrep : IsRepresentableByAlgebraicSpaces C S hS f.hom.hom)
    (hrel : HasRelativeProperty.{u, u, u + 1, u} C S hS
      (Space.smoothOfRelativeDimensionProperty C S hS d) f.hom hrep)
    (t : Space.points C S hS T) :
    relativeDimensionAt.{u, w} C S hS T hT 𝒳 f hf t = ((d : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨p, q, -, -, hval⟩ := exists_eq_fieldFibreDimensionAt C S hS T hT 𝒳 f hf t
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} C S hS
    f.hom 𝒳.property (isRepresentableByAlgebraicSpace_fibredCategory C S hS T hT) p
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing C S hS W
    (fieldFibreSquare C S hS f.hom p).pt eW).surjective q
  have hdim : fieldFibreDimensionAt.{u, w} C S hS f.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS T hT) p q =
      Space.dimensionAtPoint C S hS W hW x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} C S hS _ _ _ p W hW eW x
  have hgft : Space.IsLocallyOfFiniteType C S hS
      (representingMap C S hS (fieldFibreSquare C S hS f.hom p).pt
        (schemeFibredCategory C S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreSquare C S hS f.hom p).snd) :=
    isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd.{u, w} C S hS f hf p
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda C S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  have hgd : Space.IsSmoothOfRelativeDimension C S hS d
      (representingMap C S hS (fieldFibreSquare C S hS f.hom p).pt
        (schemeFibredCategory C S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreSquare C S hS f.hom p).snd) :=
    prop_representingMap_of_hasRelativeProperty.{u, u} C S hS
      (Space.smoothOfRelativeDimensionProperty C S hS d)
      f.hom hrep hrel (schemeFibredCategory C S hS p.base)
      (fieldValuedPointMorphism C S hS 𝒳.val p) (fieldFibreSquare C S hS f.hom p).swap
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom (fieldValuedPointMorphism C S hS 𝒳.val p)))
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda C S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  rw [hval, hdim]
  exact (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback C S hS p
    IsPullback.of_id_snd hW hW (isAlgebraicSpace_yoneda C S hS p.base) hgft x (d : ℕ∞)).mpr
    (by simpa using hgd.2 x)

/-! ### The chart -/

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)
  (𝒳 : AlgebraicStacks.{u, w} C S hS)
  (e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.val.p)

/-- The tautological chart of an algebraic stack `𝒳` presented by a groupoid `(U, R, s, t, c)`:
the projection `U ⟶ [U/R]` of Stacks 044R followed by the presenting equivalence
`[U/R] ≃ 𝒳`. -/
noncomputable def quotientChart :
    algebraicSpaceStack.{u, w} C S hS G.objects.obj G.objects.property ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (quotientStackProjection G) ⟨e.hom.functor, e.hom.w⟩))

/-- Precomposed with the universe-lowering functor of `U`, the chart is the projection
`quotientStackProjectionHom G` followed by the presenting equivalence `e`. -/
theorem quotientChart_square :
    BasedFunctor.comp (objectSpaceLiftDown G) (quotientChart G 𝒳 e).hom.hom =
      BasedFunctor.comp (quotientStackProjectionHom G).hom ⟨e.hom.functor, e.hom.w⟩ :=
  rfl

/-- The universe-lowering functor from the lifted object space of `G` to the object space of `G`
is an equivalence of categories. -/
instance isEquivalence_objectSpaceLiftDown :
    (objectSpaceLiftDown G).toFunctor.IsEquivalence :=
  (ULiftHom.equiv.{u, u + 1, u + 1}
    (C := (fibredCategory C S hS G.objects.obj).val.obj)).isEquivalence_inverse

/-- The underlying based functor `[U/R] ⥤ 𝒳` of the presenting equivalence `e` is an equivalence
of categories. -/
instance isEquivalence_equivalenceOverHom :
    (⟨e.hom.functor, e.hom.w⟩ : quotientStack G ⥤ᵇ 𝒳.val.val).toFunctor.IsEquivalence :=
  e.toEquivalence.isEquivalence_functor

/-- The chart is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_quotientChart :
    IsRepresentableByAlgebraicSpaces C S hS (quotientChart G 𝒳 e).hom.hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := liftedObjectSpace G) (𝒳 := fibredCategory C S hS G.objects.obj)
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (𝒴 := 𝒳.val)
    (quotientStackProjectionHom G).hom (quotientChart G 𝒳 e).hom.hom
    (objectSpaceLiftDown G) ⟨e.hom.functor, e.hom.w⟩ (Iso.refl _)).mpr
    (representable_quotientStackProjectionHom G)

/-- Let `P` be a property of morphisms of algebraic spaces over `S`, stable under base change and
local on the base for the fppf topology. If the source map `s : R ⟶ U` has `P`, then so does the
chart, in the relative sense of Stacks 03YK. -/
theorem hasRelativeProperty_quotientChart (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} C S hS)]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} C S hS)]
    (hP : P G.source) :
    HasRelativeProperty.{u, u, u + 1, u} C S hS P (quotientChart G 𝒳 e).hom
      (isRepresentableByAlgebraicSpaces_quotientChart G 𝒳 e) :=
  (hasRelativeProperty_iff_of_equivalences' C S hS P
    (𝒳' := liftedObjectSpace G)
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (𝒳 := fibredCategory C S hS G.objects.obj) (𝒴 := 𝒳.val)
    (quotientStackProjectionHom G) (quotientChart G 𝒳 e).hom
    (objectSpaceLiftDown G) ⟨e.hom.functor, e.hom.w⟩ (Iso.refl _)
    (isRepresentableByAlgebraicSpaces_quotientChart G 𝒳 e)
    (representable_quotientStackProjectionHom G)).mpr
    (QuotientAtlas.hasRelativeProperty_of_representable
      (representable_quotientStackProjectionHom G) P hP)

/-- The chart of a groupoid whose source map is smooth is smooth. -/
theorem isSmooth_quotientChart (hs : Space.IsSmooth C S hS G.source.hom) :
    AlgebraicStacks.IsSmooth C S hS (quotientChart G 𝒳 e) :=
  hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} C S hS
    (fun _ _ k => Space.IsSmooth C S hS k) 𝒳.property _
    (isRepresentableByAlgebraicSpaces_quotientChart G 𝒳 e)
    (hasRelativeProperty_quotientChart G 𝒳 e (Space.smoothMorphismProperty C S hS) hs)

/-- The chart is surjective on points. -/
theorem surjective_pointsMap_quotientChart :
    Function.Surjective (pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
      (fibredCategory C S hS G.objects.obj).property 𝒳.val.property
      (quotientChart G 𝒳 e).hom.hom) := by
  intro x
  obtain ⟨y, hy⟩ := (bijective_pointsMap_of_basedEquivalence C S hS
    (isFiberedInGroupoids_quotientStack G) 𝒳.val.property e.toBasedEquivalence).2 x
  obtain ⟨z, hz⟩ := surjective_pointsMap_quotientStackProjection G y
  refine ⟨pointsMap C S hS (liftedFibredCategory G.objects)
    (isFiberedInGroupoids_liftedFibredCategory G.objects)
    (fibredCategory C S hS G.objects.obj).property (liftedFibredCategoryDown G.objects) z, ?_⟩
  rw [pointsMap_comp, ← hy, ← hz, quotientStackPointsMap, pointsMap_comp]
  rfl

/-- If the source map of the groupoid is smooth of relative dimension `d`, the chart has
relative dimension `d` (Stacks 0DRG) at every point. -/
theorem relativeDimensionAt_quotientChart (d : ℕ)
    (hd : Space.IsSmoothOfRelativeDimension C S hS d G.source.hom)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType C S hS (quotientChart G 𝒳 e))
    (t : Space.points C S hS G.objects.obj) :
    relativeDimensionAt.{u, w} C S hS G.objects.obj G.objects.property 𝒳
      (quotientChart G 𝒳 e) hf t = ((d : ℕ) : WithBot ℕ∞) :=
  relativeDimensionAt_eq_of_hasRelativeProperty G.objects.obj G.objects.property 𝒳
    (quotientChart G 𝒳 e) hf d (isRepresentableByAlgebraicSpaces_quotientChart G 𝒳 e)
    (hasRelativeProperty_quotientChart G 𝒳 e
      (Space.smoothOfRelativeDimensionProperty C S hS d) hd) t

/-- If the source map `s : R ⟶ U` of the presenting groupoid is smooth of relative dimension `d`,
the dimension of `𝒳` (Stacks 0AFN) at the image of a point `u ∈ |U|` is `dim_u(U) - d`. -/
theorem dimensionAtPoint_quotientChart (h𝒳 : IsLocallyNoetherianStack.{u, w} C S hS 𝒳)
    (d : ℕ) (hd : Space.IsSmoothOfRelativeDimension C S hS d G.source.hom)
    (t : Space.points C S hS G.objects.obj) :
    dimensionAtPoint C S hS 𝒳 h𝒳
        (pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
          (fibredCategory C S hS G.objects.obj).property 𝒳.val.property
          (quotientChart G 𝒳 e).hom.hom (stackPointOfSpacePoint C S hS G.objects.obj t)) =
      dimensionSubNat (Space.dimensionAtPoint C S hS G.objects.obj G.objects.property t) d :=
  dimensionAtPoint_eq_dimensionSubNat_of_isSmooth C S hS 𝒳 h𝒳 _ G.objects.property
    (quotientChart G 𝒳 e) (isSmooth_quotientChart G 𝒳 e hd.1)
    (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth C S hS _
      (isSmooth_quotientChart G 𝒳 e hd.1)) t rfl d
    (relativeDimensionAt_quotientChart G 𝒳 e d hd _ t)

/-- An algebraic stack presented by a smooth groupoid whose object space is locally Noetherian
is locally Noetherian. -/
theorem isLocallyNoetherianStack_of_quotientChart
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.val.p)
    (hs : Space.IsSmooth C S hS G.source.hom)
    (hU : Space.HasEtaleLocalProperty C S hS G.objects.obj
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z)) :
    IsLocallyNoetherianStack.{u, w} C S hS 𝒳 := by
  let : ObjectProperty.IsLocal (fun Z : Scheme.{u} => IsLocallyNoetherian Z)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  exact (exists_scheme_atlas_iff_exists_space_atlas C S hS _ 𝒳).2
    ⟨G.objects.obj, G.objects.property, quotientChart G 𝒳 e,
      surjective_pointsMap_quotientChart G 𝒳 e, isSmooth_quotientChart G 𝒳 e hs, hU⟩

/-! ### The points of a stack presented by a groupoid -/

/-- Precomposing a 1-morphism with the 1-morphism attached to a morphism of algebraic spaces acts
on points by the map on points of that morphism. -/
theorem spacePointMap_associatedMap_comp_apply
    {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (h : F ⟶ F')
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS))
    (b : (fibredCategory C S hS F').val ⥤ᵇ 𝒴.val) (x : Space.points C S hS F) :
    spacePointMap C S hS F 𝒴 (((associatedMap C S hS h).1.hom).comp b) x =
      spacePointMap C S hS F' 𝒴 b (Space.pointsMap C S hS F h x) := by
  induction x using Quot.inductionOn with
  | h p =>
    let assoc := associatedMap C S hS h
    let src := spaceFieldValuedPoint C S hS F p
    let mid := spaceFieldValuedPoint C S hS F' (Space.FieldValuedPoint.map C S hS F h p)
    have hbase : ((CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj).base = mid.obj.base :=
      BasedFunctor.w_obj assoc.1.hom src.obj
    have hobj : (CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj = mid.obj :=
      Pseudofunctor.CoGrothendieck.ext hbase (assoc.2 src.obj)
    have hobj' : (fieldValuedPointMap C S hS (fibredCategory C S hS F).val
          ((assoc.1.hom).comp b) src).obj =
        (fieldValuedPointMap C S hS (fibredCategory C S hS F').val b mid).obj :=
      congrArg b.toFunctor.obj hobj
    calc
      spacePointMap C S hS F 𝒴 ((assoc.1.hom).comp b) (p.class C S hS F) =
          pointClass C S hS 𝒴.val 𝒴.property
            (fieldValuedPointMap C S hS (fibredCategory C S hS F).val
              ((assoc.1.hom).comp b) src) :=
        spacePointMap_class C S hS F 𝒴 ((assoc.1.hom).comp b) p
      _ = pointClass C S hS 𝒴.val 𝒴.property
            (fieldValuedPointMap C S hS (fibredCategory C S hS F').val b mid) :=
        (class_eq_class_iff_hasCommonExtension C S hS 𝒴.val 𝒴.property _ _).2
          ⟨fieldValuedPointMap C S hS (fibredCategory C S hS F).val
            ((assoc.1.hom).comp b) src, ⟨𝟙 _⟩, ⟨eqToHom hobj'⟩⟩
      _ = spacePointMap C S hS F' 𝒴 b
            ((Space.FieldValuedPoint.map C S hS F h p).class C S hS F') :=
        (spacePointMap_class C S hS F' 𝒴 b (Space.FieldValuedPoint.map C S hS F h p)).symm
      _ = spacePointMap C S hS F' 𝒴 b (Space.pointsMap C S hS F h (p.class C S hS F)) :=
        congrArg (spacePointMap C S hS F' 𝒴 b) (Space.pointsMap_class C S hS F h p).symm

/-- The comparison of the points of an algebraic space with those of its universe-lifted
fibred category. -/
private noncomputable abbrev liftedPoint (X : AlgebraicSpaces C S hS) :
    Space.points C S hS X.obj →
      points C S hS (liftedFibredCategory X) (isFiberedInGroupoids_liftedFibredCategory X) :=
  pointsMap C S hS (fibredCategory C S hS X.obj).val (fibredCategory C S hS X.obj).property
      (isFiberedInGroupoids_liftedFibredCategory X) (liftedFibredCategoryUp X) ∘
    spacePointMap C S hS X.obj (fibredCategory C S hS X.obj)
      (BasedFunctor.id (fibredCategory C S hS X.obj).val)

private theorem liftedPoint_map {X Y : AlgebraicSpaces C S hS} (a : X ⟶ Y)
    (x : Space.points C S hS X.obj) :
    pointsMap C S hS (liftedFibredCategory X) (isFiberedInGroupoids_liftedFibredCategory X)
        (isFiberedInGroupoids_liftedFibredCategory Y) (liftedAssociatedMap a) (liftedPoint X x) =
      liftedPoint Y (Space.pointsMap C S hS X.obj a.hom x) := by
  simp only [liftedPoint, Function.comp_apply]
  rw [pointsMap_comp, ← spacePointMap_associatedMap_comp_apply, spacePointMap_comp]
  rfl

/-- The chart on `spacePointMap` is the map on points of the chart applied to the identity
comparison map. -/
private theorem spacePointMap_quotientChart_eq_pointsMap
    (x : Space.points C S hS G.objects.obj) :
    spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom x =
      pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
        (fibredCategory C S hS G.objects.obj).property 𝒳.val.property
        (quotientChart G 𝒳 e).hom.hom
        (spacePointMap C S hS G.objects.obj (fibredCategory C S hS G.objects.obj)
          (BasedFunctor.id _) x) := by
  have h := congrFun (spacePointMap_comp C S hS G.objects.obj (fibredCategory C S hS
    G.objects.obj) 𝒳.val (BasedFunctor.id _) (quotientChart G 𝒳 e).hom.hom) x
  rwa [BasedFunctor.id_comp] at h

private theorem spacePointMap_quotientChart_eq (x : Space.points C S hS G.objects.obj) :
    spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom x =
      pointsMap C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G) 𝒳.val.property
        ⟨e.hom.functor, e.hom.w⟩ (quotientStackPointsMap G (liftedPoint G.objects x)) := by
  rw [spacePointMap_quotientChart_eq_pointsMap, quotientStackPointsMap,
    liftedPoint, Function.comp_apply, pointsMap_comp, pointsMap_comp]
  rfl

/-- Two points of the object space `U` have the same image in `|𝒳|` under the chart exactly when
they are the source and the target of a point of the arrow space `R`. -/
theorem spacePointMap_quotientChart_eq_iff (x y : Space.points C S hS G.objects.obj) :
    spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom x =
        spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom y ↔
      ∃ r : Space.points C S hS G.arrows.obj,
        Space.pointsMap C S hS G.arrows.obj G.source.hom r = x ∧
          Space.pointsMap C S hS G.arrows.obj G.target.hom r = y := by
  rw [spacePointMap_quotientChart_eq, spacePointMap_quotientChart_eq]
  have hinj := (bijective_pointsMap_of_basedEquivalence C S hS
    (isFiberedInGroupoids_quotientStack G) 𝒳.val.property e.toBasedEquivalence).1
  have hU := bijective_pointsMap_spacePointMap G.objects
  have hR := bijective_pointsMap_spacePointMap G.arrows
  have hrange := range_pointsMap_source_target_quotientStack G
  constructor
  · intro hxy
    obtain ⟨r', hr'⟩ : (liftedPoint G.objects x, liftedPoint G.objects y) ∈
        Set.range (fun r : arrowSpacePoints G ↦ (sourcePointsMap G r, targetPointsMap G r)) := by
      rw [hrange]; exact hinj hxy
    obtain ⟨r, rfl⟩ := hR.2 r'
    exact ⟨r, hU.1 ((liftedPoint_map G.source r).symm.trans (congrArg Prod.fst hr')),
      hU.1 ((liftedPoint_map G.target r).symm.trans (congrArg Prod.snd hr'))⟩
  · rintro ⟨r, rfl, rfl⟩
    have hmem : (sourcePointsMap G (liftedPoint G.arrows r),
        targetPointsMap G (liftedPoint G.arrows r)) ∈
        {q : objectSpacePoints G × objectSpacePoints G |
          quotientStackPointsMap G q.1 = quotientStackPointsMap G q.2} := by
      rw [← hrange]; exact ⟨_, rfl⟩
    rw [← liftedPoint_map, ← liftedPoint_map]
    exact congrArg (pointsMap C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G)
      𝒳.val.property ⟨e.hom.functor, e.hom.w⟩) hmem

/-! ### The topology of a stack presented by a smooth groupoid -/

/-- The chart is surjective on points, read through the canonical map from the points of `U`. -/
theorem surjective_spacePointMap_quotientChart :
    Function.Surjective
      (spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom) := by
  intro x
  obtain ⟨z, hz⟩ := surjective_pointsMap_quotientChart G 𝒳 e x
  obtain ⟨t, rfl⟩ := (spacePointMap_id_bijective C S hS G.objects.obj).2 z
  exact ⟨t, (spacePointMap_quotientChart_eq_pointsMap G 𝒳 e t).trans hz⟩

/-- The chart of a groupoid with smooth source map is open on points. -/
theorem isOpenMap_spacePointMap_quotientChart (hs : Space.IsSmooth C S hS G.source.hom) :
    @IsOpenMap _ _ (Space.pointTopology C S hS G.objects.obj) (pointTopology C S hS 𝒳.val)
      (spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom) := by
  have hrel := hasRelativeProperty_quotientChart G 𝒳 e (Space.smoothMorphismProperty C S hS) hs
  refine isOpenMap_spacePointMap.{u, w} C S hS G.objects.obj G.objects.property 𝒳.val
    𝒳.property _ fun U y hy F hF hE => ?_
  have hsm := hrel U y hy F hF hE
  exact ⟨Space.isFlat_of_isSmooth C S hS _ hsm,
    Space.isLocallyOfFinitePresentation_of_isSmooth C S hS hsm⟩

/-- For a groupoid with smooth source map, `|𝒳|` carries the quotient topology of `|U|` along
the chart. -/
theorem isQuotientMap_spacePointMap_quotientChart (hs : Space.IsSmooth C S hS G.source.hom) :
    @Topology.IsQuotientMap _ _ (Space.pointTopology C S hS G.objects.obj)
      (pointTopology C S hS 𝒳.val)
      (spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom) := by
  let := Space.pointTopology C S hS G.objects.obj
  let := pointTopology C S hS 𝒳.val
  exact (isOpenMap_spacePointMap_quotientChart G 𝒳 e hs).isQuotientMap
    (continuous_spacePointMap C S hS _ G.objects.property 𝒳.val _)
    (surjective_spacePointMap_quotientChart G 𝒳 e)

/-- The image under the chart of the stack point of a point `t ∈ |U|` is the image of `t` under
`spacePointMap`. -/
theorem pointsMap_stackPointOfSpacePoint_quotientChart (t : Space.points C S hS G.objects.obj) :
    pointsMap C S hS (fibredCategory C S hS G.objects.obj).val
        (fibredCategory C S hS G.objects.obj).property 𝒳.val.property
        (quotientChart G 𝒳 e).hom.hom (stackPointOfSpacePoint C S hS G.objects.obj t) =
      spacePointMap C S hS G.objects.obj 𝒳.val (quotientChart G 𝒳 e).hom.hom t := by
  exact (spacePointMap_quotientChart_eq_pointsMap G 𝒳 e t).symm

end AlgebraicGeometry.Stack

end
