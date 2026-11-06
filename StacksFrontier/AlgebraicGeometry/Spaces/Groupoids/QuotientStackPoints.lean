module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RelationOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.Topology.Separation.KolmogorovQuotient

/-!
# The points of a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `[U/R]` be its quotient stack (Stacks 044Q). **Stacks
0DTZ** describes the points of `[U/R]`: the image of `|R| → |U| × |U|` is an equivalence relation
on the points of the object space, and `|[U/R]|` is the quotient of `|U|` by it.

## Main definitions

* `AlgebraicGeometry.Stack.spaceStackPointMap`: the canonical map on points of Stacks 04XL at a
  free morphism universe for the target.
* `AlgebraicGeometry.Stack.quotientStackPointMap`: the canonical map `|U| → |[U/R]|`.
* `AlgebraicGeometry.Stack.arrowSetoid`: the image of `|R| → |U| × |U|` as a setoid on `|U|`.

## Main results

* `AlgebraicGeometry.Stack.equivalence_sourceTargetRel_points`: the image of `|R| → |U| × |U|`
  is an equivalence relation.
* `AlgebraicGeometry.Stack.pointMap_eq_iff_sourceTargetRel`: two points of `|U|` have the same
  image in `|[U/R]|` exactly when they lie in that image.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_quotientStackProjection`: the projection
  `S_U ⟶ [U/R]` is surjective on objects in the sense of Stacks 06D4.
* `AlgebraicGeometry.Stack.surjective_quotientStackPointMap`: `|U| → |[U/R]|` is surjective.
* `AlgebraicGeometry.Stack.exists_quotientPointsEquiv`: `|[U/R]|` is the quotient of `|U|` by the
  relation, by an equivalence compatible with `|U| → |[U/R]|`.

## Implementation notes

**The hypotheses of Stacks 0DTZ are not used.** The source assumes the source and target maps of
the groupoid flat and locally of finite presentation, and uses that only to know that `[U/R]` is
an algebraic stack; every clause below is proved for an arbitrary groupoid in algebraic spaces,
so the statements here are stronger than the source's.

The relation cut out on `|U|` by the image of `|R| → |U| × |U|` is `Function.SourceTargetRel`
applied to the two maps on points induced by the source and the target, so no new relation is
introduced; it is the relation of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/RelationOnPoints.lean`, in the same
orientation, which relates the target of an arrow to its source. The equivalence-relation clause
is **Stacks 043F** applied to the pre-equivalence relation `(t, s) : R → U ×_B U` of **Stacks
043X**, and needs nothing about the quotient stack.

**Why the canonical map on points is rebuilt.** `AlgebraicGeometry.Stack.spacePointMap` of
Stacks 04XL is stated for a target whose morphism universe is that of the base site, whereas
`[U/R]` is a stackification and has its morphisms one universe up, so that declaration cannot be
applied to the quotient stack at all. `AlgebraicGeometry.Stack.spaceStackPointMap` is the same
construction with the target's universes free, and
`AlgebraicGeometry.Stack.spaceStackPointMap_eq_spacePointMap` identifies the two wherever the
latter can be formed, so what is proved below is the canonical map of Stacks 04XL and not a
lookalike.

Surjectivity does not go through Stacks 04XI
(`AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects`), which is stated for
algebraic stacks and would reintroduce the algebraicity of `[U/R]`. It is proved from
surjectivity on objects directly: a point of `|[U/R]|` is represented over a field spectrum, and
the local essential surjectivity of the projection — part (1) of **Stacks 044X**, which holds
because `[U/R]` is by construction a stackification — together with the fact that a covering
sieve of a field spectrum contains an arrow out of a field spectrum gives a lift over a field
extension.

## References

* [Stacks Project, Tag 043F](https://stacks.math.columbia.edu/tag/043F)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 0DTZ](https://stacks.math.columbia.edu/tag/0DTZ)
-/

@[expose] public section

open CategoryTheory

universe u v t

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The canonical map on points at a free morphism universe -/

/-- An object of the category of elements of a presheaf lying over an object of the site whose
underlying scheme is the spectrum of a field receives a morphism from a field-valued point of
that presheaf. -/
theorem exists_hom_spaceFieldValuedPoint (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (V : BigFppfOver C S hS) (hV : IsFieldObject C S hS V)
    (w : (fibredCategory C S hS F).val.obj)
    (hw : (fibredCategory C S hS F).val.p.obj w = V) :
    ∃ p : Space.FieldValuedPoint C S hS F,
      Nonempty ((spaceFieldValuedPoint C S hS F p).obj ⟶ w) := by
  obtain ⟨wb, wf⟩ := w
  obtain rfl : wb = V := hw
  obtain ⟨q, g, hq⟩ := exists_fieldValuedPoint_of_isFieldObject C S hS F wb hV wf.as
  exact ⟨q, ⟨{ base := g, fiber := Discrete.eqToHom hq.symm }⟩⟩

/-- The canonical map on points attached to a 1-morphism from the category of elements of a
presheaf to a category fibred in groupoids over the big fppf site of `S`.

This is `AlgebraicGeometry.Stack.spacePointMap` with the morphism universe of the target left
free, which is what a target produced by stackification needs. -/
noncomputable def spaceStackPointMap (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver C S hS)} (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (f : (fibredCategory C S hS F).val ⥤ᵇ 𝒳) :
    Space.points C S hS F → points C S hS 𝒳 h𝒳 :=
  Quot.lift
    (fun p => pointClass C S hS 𝒳 h𝒳
      (fieldValuedPointMap C S hS (fibredCategory C S hS F).val f
        (spaceFieldValuedPoint C S hS F p)))
    (fun _ _ h => (class_eq_class_iff_hasCommonExtension C S hS 𝒳 h𝒳 _ _).2
      (hasCommonExtension_fieldValuedPointMap C S hS (fibredCategory C S hS F).val f
        (hasCommonExtension_spaceFieldValuedPoint C S hS F h)))

/-- The value of `AlgebraicGeometry.Stack.spaceStackPointMap` on the class of a field-valued
point of the presheaf is the class of the image of that point. -/
theorem spaceStackPointMap_class (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver C S hS)} (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (f : (fibredCategory C S hS F).val ⥤ᵇ 𝒳) (p : Space.FieldValuedPoint C S hS F) :
    spaceStackPointMap F h𝒳 f (p.class C S hS F) =
      pointClass C S hS 𝒳 h𝒳
        (fieldValuedPointMap C S hS (fibredCategory C S hS F).val f
          (spaceFieldValuedPoint C S hS F p)) := rfl

/-- `AlgebraicGeometry.Stack.spaceStackPointMap` is the canonical map on points
`AlgebraicGeometry.Stack.spacePointMap` wherever the latter's universe restriction permits it
to be formed; the two are the same construction, read at a freer morphism universe. -/
theorem spaceStackPointMap_eq_spacePointMap (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS))
    (f : (fibredCategory C S hS F).val ⥤ᵇ 𝒳.val) :
    spaceStackPointMap F 𝒳.property f = spacePointMap C S hS F 𝒳 f := by
  funext z
  induction z using Quot.ind with
  | _ p => exact (spacePointMap_class C S hS F 𝒳 f p).symm

/-! ### The canonical map from the points of the object space -/

/-- The canonical map `|U| → |[U/R]|` from the points of the object space of a groupoid in
algebraic spaces to the points of its quotient stack, induced by the canonical projection of
Stacks 044R. -/
noncomputable abbrev quotientStackPointMap (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.points C S hS G.objects.obj →
      points C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
  spaceStackPointMap G.objects.obj (isFiberedInGroupoids_quotientStack G)
    (quotientStackProjection G)

/-- The image of the class of a field-valued point of the object space is the class of its image
under the projection. -/
private theorem quotientStackPointMap_class (G : GroupoidInAlgebraicSpaces C S hS B)
    (p : Space.FieldValuedPoint C S hS G.objects.obj) :
    quotientStackPointMap G (p.class C S hS G.objects.obj) =
      pointClass C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G)
        (fieldValuedPointMap C S hS (fibredCategory C S hS G.objects.obj).val
          (quotientStackProjection G) (spaceFieldValuedPoint C S hS G.objects.obj p)) :=
  spaceStackPointMap_class G.objects.obj (isFiberedInGroupoids_quotientStack G)
    (quotientStackProjection G) p

/-! ### The relation cut out on the points of the object space -/

/-- **Stacks 0DTZ.** For a groupoid in algebraic spaces `(U, R, s, t, c)` the image of
`|R| → |U| × |U|` is an equivalence relation on the points of the object space: the pair of
points related by a point of the arrow space is its target and its source, and the arrows over
each test scheme form a groupoid.

No hypothesis on the source and target maps is needed; the flatness and local finite presentation
of Stacks 0DTZ enter only through the algebraicity of the quotient stack. -/
@[stacks 0DTZ "the image of |R| in |U| x |U| is an equivalence relation, with no hypothesis \
on the source and target maps"]
theorem equivalence_sourceTargetRel_points (G : GroupoidInAlgebraicSpaces C S hS B) :
    Equivalence (Function.SourceTargetRel
      (Space.pointsMap C S hS G.arrows.obj G.source.hom)
      (Space.pointsMap C S hS G.arrows.obj G.target.hom)) := by
  simpa [Space.groupoidPreRelation, Space.PreRelation.source, Space.PreRelation.target] using
    Space.PreRelation.isPreEquivalenceRelation_sourceTargetRel
      (Space.groupoidPreRelation G) (Space.groupoidPreRelation_isPreEquivalenceRelation G)

/-! ### The fibres of the map on points -/

private theorem pointClass_eq_of_hom
    {𝒳 : BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (p q : FieldValuedPoint C S hS 𝒳) (hom : p.obj ⟶ q.obj) :
    pointClass C S hS 𝒳 h𝒳 p = pointClass C S hS 𝒳 h𝒳 q :=
  (class_eq_class_iff_hasCommonExtension C S hS 𝒳 h𝒳 p q).2 ⟨p, ⟨𝟙 _⟩, ⟨hom⟩⟩

private theorem spacePoint_class_eq_of_hom
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (p q : Space.FieldValuedPoint C S hS F)
    (hom : (spaceFieldValuedPoint C S hS F p).obj ⟶ (spaceFieldValuedPoint C S hS F q).obj) :
    p.class C S hS F = q.class C S hS F := by
  apply Quot.sound
  refine ⟨p, Space.FieldValuedPoint.dominates_refl C S hS F p, hom.base, ?_⟩
  have fiber : Discrete.mk p.value ⟶ Discrete.mk (F.map hom.base.op q.value) := hom.fiber
  exact fiber.eq.symm

private theorem associatedMap_spaceFieldValuedPoint
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ H)
    (p : Space.FieldValuedPoint C S hS F) :
    (associatedMap C S hS a).1.hom.obj (spaceFieldValuedPoint C S hS F p).obj =
      (spaceFieldValuedPoint C S hS H (Space.FieldValuedPoint.map C S hS F a p)).obj :=
  associatedMap_obj C S hS a _

private theorem pointsMap_class_eq_of_hom
    {F H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ H)
    (p : Space.FieldValuedPoint C S hS F) (q : Space.FieldValuedPoint C S hS H)
    {base : BigFppfOver C S hS} (x : F.obj (Opposite.op base)) (y : H.obj (Opposite.op base))
    (hxy : a.app (Opposite.op base) x = y)
    (f : (spaceFieldValuedPoint C S hS F p).obj ⟶ ⟨base, Discrete.mk x⟩)
    (g : (⟨base, Discrete.mk y⟩ : (fibredCategory C S hS H).val.obj) ⟶
      (spaceFieldValuedPoint C S hS H q).obj) :
    Space.pointsMap C S hS F a (p.class C S hS F) = q.class C S hS H := by
  rw [Space.pointsMap_class]
  apply spacePoint_class_eq_of_hom
  have h : (associatedMap C S hS a).1.hom.obj ⟨base, Discrete.mk x⟩ =
      (⟨base, Discrete.mk y⟩ : (fibredCategory C S hS H).val.obj) :=
    (associatedMap_obj C S hS a _).trans
      (congrArg (fun v => (⟨base, Discrete.mk v⟩ : (fibredCategory C S hS H).val.obj)) hxy)
  exact eqToHom (associatedMap_spaceFieldValuedPoint a p).symm ≫
    (associatedMap C S hS a).1.hom.map f ≫ eqToHom h ≫ g

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_QuotientStackPoints
    {Z₁ Z₂ Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    Limits.HasLimit (Limits.cospan g f) :=
  @Limits.HasLimitsOfShape.has_limit _ _ _ _ Limits.functorCategoryHasLimitsOfShape _

private theorem exists_arrow_of_vertical_iso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (base : BigFppfOver C S hS)
    (first second : G.objects.obj.obj (Opposite.op base))
    (iso : (quotientStackProjection G).obj ⟨base, Discrete.mk first⟩ ≅
      (quotientStackProjection G).obj ⟨base, Discrete.mk second⟩)
    (vertical : (quotientStack G).p.IsHomLift (𝟙 base) iso.hom) :
    ∃ arrow : G.arrows.obj.obj (Opposite.op base),
      G.source.hom.app (Opposite.op base) arrow = first ∧
        G.target.hom.app (Opposite.op base) arrow = second := by
  let firstPoint : (quotientStack G).p.Fiber base :=
    ⟨(quotientStackProjection G).obj ⟨base, Discrete.mk first⟩,
      (quotientStackProjection G).w_obj ⟨base, Discrete.mk first⟩⟩
  let secondPoint : (quotientStack G).p.Fiber base :=
    ⟨(quotientStackProjection G).obj ⟨base, Discrete.mk second⟩,
      (quotientStackProjection G).w_obj ⟨base, Discrete.mk second⟩⟩
  let fiberIso : firstPoint ≅ secondPoint := Functor.Fiber.isoMk iso vertical
  let sectionIso := (Functor.pullbackFiberIdIso firstPoint) ≪≫ fiberIso ≪≫
    (Functor.pullbackFiberIdIso secondPoint).symm
  let isoSection : ((quotientStack G).p.isomPresheaf
      firstPoint secondPoint).obj (Opposite.op (Over.mk (𝟙 base))) :=
    ⟨sectionIso.hom, inferInstanceAs (IsIso sectionIso.hom)⟩
  let comparison := isomPresheafPullbackIso G base first second
    firstPoint secondPoint (quotientStackProjection_obj G _) (quotientStackProjection_obj G _)
  let lift := (comparison.inv.app (Opposite.op (Over.mk (𝟙 base))) isoSection).down
  let arrow := arrowFiberOverSectionArrow G base first second (Over.mk (𝟙 base)) lift
  refine ⟨arrow, ?_⟩
  have condition := congrArg (fun map => map.app (Opposite.op base) lift.1)
    (CategoryTheory.Limits.pullback.condition
      (f := CategoryTheory.Limits.prod.lift (yonedaEquiv.symm second)
        (yonedaEquiv.symm first))
      (g := CategoryTheory.Limits.prod.lift G.target.hom G.source.hom))
  have target := congrArg (fun value =>
    (CategoryTheory.Limits.prod.fst (X := G.objects.obj) (Y := G.objects.obj)).app
      (Opposite.op base) value) condition
  have source := congrArg (fun value =>
    (CategoryTheory.Limits.prod.snd (X := G.objects.obj) (Y := G.objects.obj)).app
      (Opposite.op base) value) condition
  have lift_map : (CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.prod.lift (yonedaEquiv.symm second) (yonedaEquiv.symm first))
      (CategoryTheory.Limits.prod.lift G.target.hom G.source.hom)).app
        (Opposite.op base) lift.1 = 𝟙 base := lift.2
  constructor
  · simp only [← NatTrans.comp_app_apply, Category.assoc,
      CategoryTheory.Limits.prod.lift_snd] at source
    simpa [NatTrans.comp_app_apply, arrow, arrowFiberOverSectionArrow,
      lift_map, yonedaEquiv_symm_app] using source.symm
  · simp only [← NatTrans.comp_app_apply, Category.assoc,
      CategoryTheory.Limits.prod.lift_fst] at target
    simpa [NatTrans.comp_app_apply, arrow, arrowFiberOverSectionArrow,
      lift_map, yonedaEquiv_symm_app] using target.symm

private theorem pointMap_eq_of_arrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (point : Space.points C S hS G.arrows.obj) :
    quotientStackPointMap G (Space.pointsMap C S hS G.arrows.obj G.source.hom point) =
      quotientStackPointMap G (Space.pointsMap C S hS G.arrows.obj G.target.hom point) := by
  induction point using Quot.inductionOn with
  | h point =>
    rw [Space.pointsMap_class, Space.pointsMap_class, quotientStackPointMap_class,
      quotientStackPointMap_class]
    apply pointClass_eq_of_hom
    exact (quotientStackProjection G).map
        (eqToHom (associatedMap_spaceFieldValuedPoint G.source.hom point).symm) ≫
      (quotientStackTwoArrow G).app (spaceFieldValuedPoint C S hS G.arrows.obj point).obj ≫
      (quotientStackProjection G).map
        (eqToHom (associatedMap_spaceFieldValuedPoint G.target.hom point))

/-- In a category fibred in groupoids, the domains of two morphisms lying over the same base
morphism with a common codomain are isomorphic by an isomorphism lying over the identity. -/
private theorem _root_.CategoryTheory.Functor.IsFiberedInGroupoids.exists_iso_isHomLift_id
    {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮] {p : 𝒳 ⥤ 𝒮} (hp : p.IsFiberedInGroupoids)
    {R T : 𝒮} (f : R ⟶ T) {a b c : 𝒳} (φ : a ⟶ c) (ψ : b ⟶ c)
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ) :
    ∃ e : a ≅ b, p.IsHomLift (𝟙 R) e.hom := by
  have := hp.isStronglyCartesian_homLift f φ
  have := hp.isStronglyCartesian_homLift f ψ
  exact ⟨Functor.IsCartesian.domainUniqueUpToIso p f ψ φ, inferInstance⟩

private theorem sourceTargetRel_of_vertical_iso
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (first second : Space.FieldValuedPoint C S hS G.objects.obj)
    (base : BigFppfOver C S hS) (hbase : IsFieldObject C S hS base)
    (x y : G.objects.obj.obj (Opposite.op base))
    (iso : (quotientStackProjection G).obj ⟨base, Discrete.mk x⟩ ≅
      (quotientStackProjection G).obj ⟨base, Discrete.mk y⟩)
    (vertical : (quotientStack G).p.IsHomLift (𝟙 base) iso.hom)
    (f : (⟨base, Discrete.mk x⟩ : (fibredCategory C S hS G.objects.obj).val.obj) ⟶
      (spaceFieldValuedPoint C S hS G.objects.obj first).obj)
    (g : (⟨base, Discrete.mk y⟩ : (fibredCategory C S hS G.objects.obj).val.obj) ⟶
      (spaceFieldValuedPoint C S hS G.objects.obj second).obj) :
    Function.SourceTargetRel
      (Space.pointsMap C S hS G.arrows.obj G.target.hom)
      (Space.pointsMap C S hS G.arrows.obj G.source.hom)
      (first.class C S hS G.objects.obj) (second.class C S hS G.objects.obj) := by
  obtain ⟨arrow, hs, ht⟩ := exists_arrow_of_vertical_iso G base x y iso vertical
  obtain ⟨preimage, ⟨preimageHom⟩⟩ :=
    exists_hom_spaceFieldValuedPoint G.arrows.obj base hbase ⟨base, Discrete.mk arrow⟩ rfl
  exact ⟨preimage.class C S hS G.arrows.obj,
    pointsMap_class_eq_of_hom G.source.hom preimage first arrow x hs preimageHom f,
    pointsMap_class_eq_of_hom G.target.hom preimage second arrow y ht preimageHom g⟩

/-- A morphism in the quotient stack from an object over `base` to the image of an object of the
object space lifts, over a field object, to an object of the object space together with a
vertical isomorphism. -/
private theorem exists_vertical_iso_of_hom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (point : Space.FieldValuedPoint C S hS G.objects.obj) {c : (quotientStack G).obj}
    {base : BigFppfOver C S hS} (hc : (quotientStack G).p.obj c = base)
    (hom : c ⟶ (quotientStackProjection G).obj
      (spaceFieldValuedPoint C S hS G.objects.obj point).obj) :
    ∃ (value : G.objects.obj.obj (Opposite.op base))
      (_ : (⟨base, Discrete.mk value⟩ : (fibredCategory C S hS G.objects.obj).val.obj) ⟶
        (spaceFieldValuedPoint C S hS G.objects.obj point).obj)
      (e : (quotientStackProjection G).obj ⟨base, Discrete.mk value⟩ ≅ c),
      (quotientStack G).p.IsHomLift (𝟙 base) e.hom := by
  let projection := quotientStackProjection G
  let obj := (spaceFieldValuedPoint C S hS G.objects.obj point).obj
  let b := eqToHom hc.symm ≫ (quotientStack G).p.map hom ≫ eqToHom (projection.w_obj obj)
  let lift : (fibredCategory C S hS G.objects.obj).val.obj :=
    ⟨base, Discrete.mk (G.objects.obj.map b.op point.value)⟩
  let map : lift ⟶ obj := ⟨b, eqToHom rfl⟩
  have homOver : (quotientStack G).p.IsHomLift b hom :=
    CategoryTheory.IsHomLift.of_fac _ _ _ hc (projection.w_obj obj) rfl
  have mapOver : (fibredCategory C S hS G.objects.obj).val.p.IsHomLift b map := by
    change Functor.IsHomLift _ ((fibredCategory C S hS G.objects.obj).val.p.map map) _
    infer_instance
  obtain ⟨e, he⟩ := (isFiberedInGroupoids_quotientStack G).exists_iso_isHomLift_id
    b (projection.map map) hom inferInstance homOver
  exact ⟨_, map, e, he⟩

private theorem arrowRelation_of_pointMap_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (first second : Space.FieldValuedPoint C S hS G.objects.obj)
    (equal : quotientStackPointMap G (first.class C S hS G.objects.obj) =
      quotientStackPointMap G (second.class C S hS G.objects.obj)) :
    Function.SourceTargetRel
      (Space.pointsMap C S hS G.arrows.obj G.target.hom)
      (Space.pointsMap C S hS G.arrows.obj G.source.hom)
      (first.class C S hS G.objects.obj) (second.class C S hS G.objects.obj) := by
  rw [quotientStackPointMap_class, quotientStackPointMap_class] at equal
  obtain ⟨common, ⟨firstHom⟩, ⟨secondHom⟩⟩ :=
    (class_eq_class_iff_hasCommonExtension C S hS _
      (isFiberedInGroupoids_quotientStack G) _ _).1 equal
  obtain ⟨x, f, e₁, h₁⟩ := exists_vertical_iso_of_hom G first common.over firstHom
  obtain ⟨y, g, e₂, h₂⟩ := exists_vertical_iso_of_hom G second common.over secondHom
  exact sourceTargetRel_of_vertical_iso G first second common.base
    ⟨common.carrier, common.field, ⟨common.isSpec⟩⟩ x y (e₁ ≪≫ e₂.symm)
    (IsHomLift.comp_of_lift_id (quotientStack G).p common.base e₁.hom e₂.inv) f g

private theorem pointMap_eq_iff_arrowRelation
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (first second : Space.points C S hS G.objects.obj) :
    quotientStackPointMap G first = quotientStackPointMap G second ↔
      Function.SourceTargetRel
        (Space.pointsMap C S hS G.arrows.obj G.target.hom)
        (Space.pointsMap C S hS G.arrows.obj G.source.hom) first second := by
  constructor
  · induction first using Quot.inductionOn with
    | h first =>
      induction second using Quot.inductionOn with
      | h second => exact arrowRelation_of_pointMap_eq G first second
  · rintro ⟨arrow, rfl, rfl⟩
    exact pointMap_eq_of_arrow G arrow

/-- **Stacks 0DTZ.** Two points of the object space of a groupoid in algebraic spaces have the
same image in the points of the quotient stack exactly when they lie in the image of
`|R| → |U| × |U|`, that is exactly when some point of the arrow space has the first as its target
and the second as its source.

No hypothesis on the source and target maps is needed; the flatness and local finite presentation
of Stacks 0DTZ enter only through the algebraicity of the quotient stack. -/
@[stacks 0DTZ "the fibres of |U| -> |[U/R]| are the classes of the image of |R|, with no \
hypothesis on the source and target maps"]
theorem pointMap_eq_iff_sourceTargetRel
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (first second : Space.points C S hS G.objects.obj) :
    quotientStackPointMap G first = quotientStackPointMap G second ↔
      Function.SourceTargetRel
        (Space.pointsMap C S hS G.arrows.obj G.source.hom)
        (Space.pointsMap C S hS G.arrows.obj G.target.hom)
        first second := by
  rw [eq_comm, pointMap_eq_iff_arrowRelation]
  exact ⟨fun ⟨a, h₁, h₂⟩ => ⟨a, h₂, h₁⟩, fun ⟨a, h₁, h₂⟩ => ⟨a, h₂, h₁⟩⟩

/-! ### Surjectivity of the map on points -/

/-- **The canonical projection `S_U ⟶ [U/R]` is surjective on objects**, in the sense of
Stacks 06D4, with no hypothesis on the groupoid.

Local essential surjectivity of the projection, which is part (1) of Stacks 044X and holds
because `[U/R]` is by construction the stackification of the pointwise quotient prestack,
supplies a covering sieve of the base over whose members an object of `[U/R]` lifts; and a
covering sieve of the spectrum of a field contains an arrow out of the spectrum of a field. -/
theorem isSurjectiveOnObjects_quotientStackProjection
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsSurjectiveOnObjects C S hS (fibredCategory C S hS G.objects.obj).val.p
      (quotientStack G).p (quotientStackProjection G).toFunctor := by
  intro U hU y hy
  obtain ⟨R, hR, hlift⟩ := localEssSurj_quotientStackProjectionHom G U ⟨y, hy⟩
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology C S hS hU hR
  obtain ⟨z, φ, hφ⟩ := hlift hgR
  refine ⟨V, hV, g, (objectSpaceLiftDown G).obj z, ?_, φ, hφ⟩
  exact ((quotientStackProjectionHom G).hom.w_obj z).symm.trans
    (IsHomLift.domain_eq (quotientStack G).p g φ)

/-- **Stacks 0DTZ.** Every point of the quotient stack `[U/R]` of a groupoid in
algebraic spaces is the image of a point of the object space `U`.

No hypothesis on the groupoid is needed: a point of `|[U/R]|` is represented by an object over
the spectrum of a field, the projection is surjective on objects by
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_quotientStackProjection`, and the resulting
object of the object space over a field extension is dominated by a field-valued point of `U`
whose image therefore has a common refinement with the chosen representative. -/
@[stacks 0DTZ "|U| surjects onto the points of the quotient stack, with no hypothesis \
on the source and target maps"]
theorem surjective_quotientStackPointMap (G : GroupoidInAlgebraicSpaces C S hS B) :
    Function.Surjective (quotientStackPointMap G) := by
  intro z
  obtain ⟨q, rfl⟩ := Quotient.exists_rep z
  obtain ⟨V, hV, g, x, hx, α, hα⟩ := isSurjectiveOnObjects_quotientStackProjection G q.base
    ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩ q.obj q.over
  obtain ⟨p, ⟨ψ⟩⟩ := exists_hom_spaceFieldValuedPoint G.objects.obj V hV x hx
  exact ⟨p.class C S hS G.objects.obj, (class_eq_class_iff_hasCommonExtension C S hS
    (quotientStack G) (isFiberedInGroupoids_quotientStack G) _ q).2
      ⟨_, ⟨𝟙 _⟩, ⟨(quotientStackProjection G).map ψ ≫ α⟩⟩⟩

/-! ### The points of the quotient stack as a quotient -/

/-- The setoid on the points of the object space of a groupoid in algebraic spaces given by the
image of `|R| → |U| × |U|`, which is an equivalence relation by
`AlgebraicGeometry.Stack.equivalence_sourceTargetRel_points`. -/
def arrowSetoid (G : GroupoidInAlgebraicSpaces C S hS B) :
    Setoid (Space.points C S hS G.objects.obj) :=
  ⟨Function.SourceTargetRel
      (Space.pointsMap C S hS G.arrows.obj G.source.hom)
      (Space.pointsMap C S hS G.arrows.obj G.target.hom),
    equivalence_sourceTargetRel_points G⟩

/-- **Stacks 0DTZ.** The points of the quotient stack of a groupoid in algebraic spaces are the
quotient of the points of the object space by the image of `|R| → |U| × |U|`: there is an
equivalence of the quotient set with `|[U/R]|` carrying the class of a point of `|U|` to its
image under the canonical map, so the identification is the canonical one and not merely a
bijection of underlying sets.

No hypothesis on the source and target maps is needed; the flatness and local finite presentation
of Stacks 0DTZ enter only through the algebraicity of the quotient stack. -/
@[stacks 0DTZ "|[U/R]| is the quotient of |U| by that equivalence relation, with no hypothesis \
on the source and target maps"]
theorem exists_quotientPointsEquiv (G : GroupoidInAlgebraicSpaces C S hS B) :
    ∃ e : Quotient (arrowSetoid G) ≃
        points C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G),
      ∀ x : Space.points C S hS G.objects.obj,
        e (Quotient.mk _ x) = quotientStackPointMap G x := by
  let map : Quotient (arrowSetoid G) →
      points C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
    Quotient.lift (quotientStackPointMap G)
      fun _ _ => (pointMap_eq_iff_sourceTargetRel G _ _).2
  refine ⟨Equiv.ofBijective map ⟨?_, fun z =>
    (surjective_quotientStackPointMap G z).elim fun x h => ⟨Quotient.mk _ x, h⟩⟩, fun _ => rfl⟩
  rintro ⟨first⟩ ⟨second⟩ equal
  exact Quotient.sound ((pointMap_eq_iff_sourceTargetRel G first second).1 equal)

end AlgebraicGeometry.Stack

end
