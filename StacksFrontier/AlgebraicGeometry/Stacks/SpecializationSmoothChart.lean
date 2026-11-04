module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenBetween
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Lifting a specialization along a smooth chart of an algebraic stack (Stacks 0GVZ)

Let `𝒳` be an algebraic stack over `S` and let `f : U ⟶ 𝒳` be a smooth 1-morphism from an
algebraic space `U` over `S`. A specialization `x' ⤳ x` of points of `|𝒳|` lifts through any
point `u` of `|U|` above `x`, provided the point `x'` admits a quasi-compact field-valued
representative: there is a point `u'` of `|U|` above `x'` with `u' ⤳ u`. The condition on `x'`
is one of the equivalent conditions of **Stacks 0DTK**, the condition under which an algebraic
stack is called decent (**Stacks 0GW1**), and it is taken here in its existential form —
*some* morphism `Spec k ⟶ 𝒳` in the class of `x'` is quasi-compact — because that is the form
the argument consumes and the form Stacks 0GW1 quantifies.

## Main results

* `AlgebraicGeometry.Stack.exists_specializes_spacePointMap_eq`: **Stacks 0GVZ**.

## Implementation notes

The proof is the source's. It replaces `U` by an affine étale chart `m : h_W ⟶ U` through the
prescribed point, which is `AlgebraicGeometry.Space.exists_isAffine_etaleChart_pointsMap_eq`
applied to a member of an étale atlas of `U`, and then identifies the fibre of `|W| ⟶ |𝒳|` over
`x'` with the image on points of an algebraic space `Λ_W F` over `W`:

* `AlgebraicGeometry.Stack.range_fiberMap` is that identification. It is proved by comparing
  sections: a section of `F` over an object `T ⟶ W` of the site over `W` is the same as an
  arrow from the value of the chart at `T` to the object of the field-valued point
  (`AlgebraicGeometry.Stack.section_iff_hom_to_fieldPoint`, through the 2-Yoneda chosen lifts),
  and such an arrow exists exactly when the two field-valued points name the same point of
  `|𝒳|` (`AlgebraicGeometry.Stack.exists_dominating_point_with_hom`). The passage between
  sections of `F` on the site over `W` and sections of its lower-shriek extension on the site
  over `S` is `AlgebraicGeometry.Stack.exists_section_relocalize` and its converse.
* That algebraic space is quasi-compact over `W` by the hypothesis on `x'`, read through
  **Stacks 0402** (`AlgebraicGeometry.Stack.exists_algebraicSpace_over_baseChange`), and `W` is
  affine, so it has an affine étale surjective cover `T` (**Stacks 03H6**) and the induced
  morphism `T ⟶ W` of the site is a quasi-compact morphism of affine schemes.

Smoothness of `f` is used only through openness of `|U| ⟶ |𝒳|`
(`AlgebraicGeometry.Stack.isOpenMap_spacePointMap_of_isSmooth`): a smooth 1-morphism is
representable by algebraic spaces because the diagonal of an algebraic stack is
(**Stacks 045G**), hence satisfies the relative property of Stacks 04XB by **Stacks 06FM**, and
its represented base changes are then flat and locally of finite presentation, which is the
hypothesis of the openness clause of **Stacks 04XL**. Openness is what places `u` in the
closure of the fibre over `x'`, and `AlgebraicGeometry.exists_specializes_of_mem_closure_range`
— **Stacks 02JQ** — then produces the specialization inside the fibre, transported to the point
spaces of Stacks 03BX along `AlgebraicGeometry.Space.schemePointsHomeomorph`.

Both point spaces carry the topologies of Stacks 03BX and Stacks 04XL as local instances, so
that `⤳` reads directly; those definitions are not global instances.

## References

* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0GVZ](https://stacks.math.columbia.edu/tag/0GVZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.pointTopology pointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Topological preliminaries -/

/-- A point whose image is specialized to by `b` lies in the closure of the fibre over `b`, for
an open map. -/
private theorem mem_closure_fiber_of_isOpenMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (g : α → β) (hg : IsOpenMap g) {a : α} {b : β}
    (hab : b ⤳ g a) :
    a ∈ closure (g ⁻¹' ({b} : Set β)) :=
  mem_closure_iff.mpr fun V hV ha =>
    specializes_iff_forall_open.mp hab (g '' V) (hg V hV) ⟨a, ha, rfl⟩

/-! ### Specializations on the points of a represented algebraic space -/

/-- A point of a represented presheaf in the closure of the image of a morphism of the site
whose underlying morphism of schemes is quasi-compact is a specialization of a point of that
image. This is **Stacks 02JQ** read on the point spaces of Stacks 03BX, along the
homeomorphism `AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
private theorem exists_specializes_of_mem_closure_range_pointsMap
    {T W : BigFppfOver B S hS} (g : T ⟶ W)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g)]
    (q : Space.points B S hS (yoneda.obj W))
    (hq : q ∈ closure (Set.range (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g)))) :
    ∃ r : Space.points B S hS (yoneda.obj T),
      Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g) r ⤳ q := by
  have hcomp : ∀ z, Space.schemePointsHomeomorph B S hS W
      (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g) z) =
      ((BigFppfOver.toScheme B S hS).map g).base (Space.schemePointsHomeomorph B S hS T z) :=
    Space.pointsToScheme_pointsMap B S hS g
  have hrange : Space.schemePointsHomeomorph B S hS W ''
        Set.range (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g)) =
      Set.range (fun z => ((BigFppfOver.toScheme B S hS).map g).base z) := by
    ext y
    constructor
    · rintro ⟨-, ⟨z, rfl⟩, rfl⟩
      exact ⟨Space.schemePointsHomeomorph B S hS T z, (hcomp z).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := (Space.schemePointsHomeomorph B S hS T).surjective x
      exact ⟨_, ⟨z, rfl⟩, hcomp z⟩
  have hcl : Space.schemePointsHomeomorph B S hS W q ∈
      closure (Set.range (fun z => ((BigFppfOver.toScheme B S hS).map g).base z)) := by
    rw [← hrange]
    exact image_closure_subset_closure_image
      (Space.schemePointsHomeomorph B S hS W).continuous (Set.mem_image_of_mem _ hq)
  obtain ⟨z, hz⟩ :=
    exists_specializes_of_mem_closure_range ((BigFppfOver.toScheme B S hS).map g) hcl
  have hs := hz.map (Space.schemePointsHomeomorph B S hS W).symm.continuous
  rw [← Homeomorph.apply_symm_apply (Space.schemePointsHomeomorph B S hS T) z, ← hcomp,
    (Space.schemePointsHomeomorph B S hS W).symm_apply_apply,
    (Space.schemePointsHomeomorph B S hS W).symm_apply_apply] at hs
  exact ⟨_, hs⟩

/-! ### An affine étale chart of an algebraic space through a prescribed point -/

/-- Every point of an algebraic space over `S` is in the image, on points, of an étale chart of
that space by an *affine* scheme: refine an étale atlas by an affine open of one of its members,
which is `AlgebraicGeometry.Space.exists_isAffine_etaleChart_pointsMap_eq`. -/
private theorem exists_affine_etaleChart_pointsMap_eq
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (u : Space.points B S hS U) :
    ∃ (W : BigFppfOver B S hS) (m : yoneda.obj W ⟶ U) (q : Space.points B S hS (yoneda.obj W)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf m ∧
      Space.pointsMap B S hS (yoneda.obj W) m q = u := by
  obtain ⟨V, a, hasurj, haet⟩ := hU.exists_atlas
  obtain ⟨v, hv⟩ :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B S hS U hU V a).1 hasurj u
  obtain ⟨W, j, q, hWaff, hjet, hjq⟩ :=
    Space.exists_isAffine_etaleChart_pointsMap_eq B S hS V v
  have hQEc := Space.inverseImage_isStableUnderComposition B S hS
    AlgebraicGeometry.etale_isStableUnderComposition.{u}
  have hQEpc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  refine ⟨W, yoneda.map j ≫ a, q, hWaff,
    MorphismProperty.comp_mem _ (yoneda.map j) a hjet haet, ?_⟩
  rw [Space.pointsMap_comp_apply, hjq, hv]

/-! ### A smooth chart is open on points -/

/-- A smooth 1-morphism to an algebraic stack over `S` from the category of elements of an
algebraic space is open on the point spaces of Stacks 03BX and Stacks 04XL.

Smoothness in the sense of **Stacks 075U** is the existential smooth-diagram criterion; the
1-morphism is representable by algebraic spaces because the diagonal of an algebraic stack is
(**Stacks 045G**), so **Stacks 06FM** turns that criterion into the relative property of
Stacks 04XB, whose base changes are then flat and locally of finite presentation
(**Stacks 03ZF**, **Stacks 04AJ**). That is the hypothesis of the openness clause of
Stacks 04XL. -/
private theorem isOpenMap_spacePointMap_of_isSmooth
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (f : fibredCategory B S hS U ⟶ 𝒳)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) f) :
    IsOpenMap (spacePointMap B S hS U 𝒳 f.hom) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom :=
    isRepresentableFromAlgebraicSpaces_of_hasRepresentableDiagonal.{u, u, u + 1, u, u + 1}
      B S hS 𝒳 h𝒳.choose_spec.2.1 (fibredCategory B S hS U)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) f.hom
  -- pin the universe of the locality instance, which the relative property does not determine
  have _ : (spaceProperty B S hS (fun _ _ h => Space.IsSmooth B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := inferInstance
  have hrel := (hasPropertyOnSomeSmoothDiagram_iff_relative B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (isAlgebraicStack_fibredCategory B S hS U hU) h𝒳 f hrep).1 hf
  refine isOpenMap_spacePointMap B S hS U hU 𝒳 h𝒳 f.hom fun V y hy G hG hE => ?_
  have hsm := hrel V y hy G hG hE
  exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
    Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩

/-! ### The fibre of a chart over a point of the stack -/

/-- A 1-morphism to a category fibred in groupoids over the big fppf site of `S` from the slice
of the site over an object `W`, obtained from a 1-morphism out of the category of elements of a
presheaf `G` and a section `a : h_W ⟶ G`: the two models of `W` as a category fibred in
groupoids are identified by `AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence`. -/
private noncomputable def schemeMapToStack
    (W : BigFppfOver B S hS) (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (a : yoneda.obj W ⟶ G)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : fibredCategory B S hS G ⟶ 𝒳) :
    schemeFibredCategory B S hS W ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (schemeFibredCategoryEquivalence B S hS W).functor ≫
    (associatedMap B S hS a).1 ≫ f

/-- A presheaf on the site has a section over an object exactly when the category of elements
of a category fibred in groupoids equivalent to it has an object over that object. -/
private theorem nonempty_section_iff_object
    {C : Type*} [Category C] {A : Type*} [Category A]
    (p : A ⥤ C) (F : Cᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) (c : C) :
    Nonempty (F.obj (Opposite.op c)) ↔ ∃ a : A, p.obj a = c := by
  constructor
  · rintro ⟨s⟩
    exact ⟨e.inv.functor.obj ⟨c, Discrete.mk s⟩,
      congrArg (fun H => H.obj ⟨c, Discrete.mk s⟩) e.inv.w⟩
  · rintro ⟨a, ha⟩
    have ht : (e.hom.functor.obj a).base = c :=
      (congrArg (fun H => H.obj a) e.hom.w).trans ha
    exact ⟨F.map (eqToHom ht.symm).op (e.hom.functor.obj a).fiber.as⟩

/-- Two arrows of a category fibred in groupoids lying over one and the same arrow of the base,
with a common target, have isomorphic sources, by a vertical isomorphism. -/
private theorem exists_vertical_iso_of_lifts
    {C : Type*} [Category C] {A : Type*} [Category A]
    (p : A ⥤ C) (hp : p.IsFiberedInGroupoids)
    {c d : C} (g : c ⟶ d) {a b z : A} (f : a ⟶ z) (h : b ⟶ z)
    (hf : p.IsHomLift g f) (hh : p.IsHomLift g h) :
    ∃ e : a ≅ b, p.IsHomLift (𝟙 c) e.hom := by
  have _ := hp.isStronglyCartesian_homLift g f
  have _ := hp.isStronglyCartesian_homLift g h
  exact ⟨Functor.IsCartesian.domainUniqueUpToIso p g h f, inferInstance⟩

/-- `AlgebraicGeometry.Stack.nonempty_section_iff_object` for a presheaf representing the first
projection of a 2-fibre product over the site of an object: a section over `d` is the same as a
lift of the point of the apex, i.e. an object of the source of the second leg together with a
vertical isomorphism. -/
private theorem nonempty_section_iff_vertical_iso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {A : Type*} [Category A] {X : Type*} [Category X]
    (q : D ⥤ C) (p : A ⥤ C) (r : X ⥤ C)
    (y : D ⥤ X) (f : A ⥤ X) (F : Dᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst q p r y f)
      (presheafOfCategories (F ⋙ typeToCat)).p) (d : D) :
    Nonempty (F.obj (Opposite.op d)) ↔
      ∃ (a : A) (i : y.obj d ≅ f.obj a),
        p.obj a = q.obj d ∧ r.IsHomLift (𝟙 (q.obj d)) i.hom := by
  rw [nonempty_section_iff_object _ F e d]
  constructor
  · rintro ⟨⟨c, z, a, hz, ha, i, hi⟩, h⟩
    obtain rfl : z = d := h
    exact ⟨a, i, ha.trans hz.symm, hz ▸ hi⟩
  · rintro ⟨a, i, ha, hi⟩
    exact ⟨⟨q.obj d, d, a, rfl, ha, i, hi⟩, rfl⟩

/-- A section of a presheaf on the site over `W` over an object `T ⟶ W` gives a section of the
lower-shriek extension over `T` with prescribed structure morphism. -/
private theorem exists_section_relocalize
    (W : BigFppfOver B S hS)
    (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
    (Fy : SpacesOverSmallerBase B W.left.1 S W.left.2 hS W.hom)
    (i : Fy.1.left ≅ (OverShriek.relocalizePresheafFunctor W.hom).obj F)
    (hi : ∀ (T : BigFppfOver B S hS) (s : Fy.1.left.obj (Opposite.op T)),
      (Fy.1.hom.app (Opposite.op T) s).left = (i.hom.app (Opposite.op T) s).1.1)
    (T : BigFppfOver B S hS) (j : T ⟶ W)
    (s : F.obj (Opposite.op (Over.mk j.left))) :
    ∃ t : Fy.1.left.obj (Opposite.op T), Fy.1.hom.app (Opposite.op T) t = j := by
  let v : ((OverShriek.relocalizePresheafFunctor W.hom).obj F).obj
      (Opposite.op T) := ⟨⟨j.left, s⟩, j.w⟩
  refine ⟨i.inv.app _ v, ?_⟩
  apply Over.OverMorphism.ext
  rw [hi]
  exact congrArg (fun z => z.1.1)
    (ConcreteCategory.congr_hom (NatTrans.congr_app i.inv_hom_id (Opposite.op T)) v)

/-- Conversely a section of the lower-shriek extension over `T` gives a section of the presheaf
on the site over `W` over the object its structure morphism names. -/
private theorem nonempty_section_relocalize
    (W : BigFppfOver B S hS)
    (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
    (Fy : SpacesOverSmallerBase B W.left.1 S W.left.2 hS W.hom)
    (i : Fy.1.left ≅ (OverShriek.relocalizePresheafFunctor W.hom).obj F)
    (hi : ∀ (T : BigFppfOver B S hS) (s : Fy.1.left.obj (Opposite.op T)),
      (Fy.1.hom.app (Opposite.op T) s).left = (i.hom.app (Opposite.op T) s).1.1)
    (T : BigFppfOver B S hS) (s : Fy.1.left.obj (Opposite.op T)) :
    Nonempty (F.obj (Opposite.op (Over.mk (Fy.1.hom.app (Opposite.op T) s).left))) := by
  rw [hi]
  exact ⟨(i.hom.app (Opposite.op T) s).1.2⟩

/-- A presheaf representing the base change of the 1-morphism of a field-valued point along a
scheme-valued point of the stack has a section over an object of the site over `W` exactly when
the value of that point admits an arrow to the object of the field-valued point. -/
private theorem section_iff_hom_to_fieldPoint
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val)
    (W : BigFppfOver B S hS)
    (y : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map W.hom)
    (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map W.hom)
        (schemeFibredCategory B S hS p.base).val.p 𝒳.val.p y
        (CatFiberedInGroupoids.homFunctor (fieldValuedPointMorphism B S hS 𝒳 p)))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (d : BigFppfOver B W.left.1 W.left.2) :
    Nonempty (F.obj (Opposite.op d)) ↔ Nonempty (y.obj d ⟶ p.obj) := by
  rw [nonempty_section_iff_vertical_iso _ _ _ _ _ F e d]
  constructor
  · rintro ⟨a, i, -, -⟩
    exact ⟨i.hom ≫ (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property p.base
      (Functor.Fiber.mk p.over) a).φ⟩
  · rintro ⟨g⟩
    have hd : 𝒳.val.p.obj (y.obj d) = (Over.map W.hom).obj d :=
      congrArg (fun H => H.obj d) hy
    let k : (Over.map W.hom).obj d ⟶ p.base :=
      eqToHom hd.symm ≫ 𝒳.val.p.map g ≫ eqToHom p.over
    let a : Over p.base := Over.mk k
    let l := Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property p.base
      (Functor.Fiber.mk p.over) a
    have hg : 𝒳.val.p.IsHomLift k g :=
      IsHomLift.of_fac' _ k g hd p.over (by simp [k])
    obtain ⟨i, hi⟩ := exists_vertical_iso_of_lifts 𝒳.val.p 𝒳.property k g l.φ hg
      l.isStronglyCartesian.toIsHomLift
    exact ⟨a, i, rfl, hi⟩

/-- A 1-morphism out of the slice of the site over `W` names a scheme-valued point of the stack
lying over the structure morphism of `W`. -/
private theorem iteratedSliceBackward_comp_p
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : BigFppfOver B S hS) (f : schemeFibredCategory B S hS W ⟶ 𝒳) :
    (Over.iteratedSliceBackward W ⋙ f.hom.toFunctor) ⋙ 𝒳.val.p = Over.map W.hom :=
  congrArg (fun H => Over.iteratedSliceBackward W ⋙ H) f.hom.w

/-- `AlgebraicGeometry.Stack.section_iff_hom_to_fieldPoint` for the scheme-valued point attached
to a 1-morphism out of the slice of the site over `W`, read at an object `T ⟶ W` of that
slice. -/
private theorem section_iff_hom_to_fieldPoint_over
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val)
    (W : BigFppfOver B S hS)
    (f : schemeFibredCategory B S hS W ⟶ 𝒳)
    (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map W.hom)
        (schemeFibredCategory B S hS p.base).val.p 𝒳.val.p
        (Over.iteratedSliceBackward W ⋙ f.hom.toFunctor)
        (CatFiberedInGroupoids.homFunctor (fieldValuedPointMorphism B S hS 𝒳 p)))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {T : BigFppfOver B S hS} (j : T ⟶ W) :
    Nonempty (F.obj (Opposite.op (Over.mk j.left))) ↔
      Nonempty (f.hom.toFunctor.obj (Over.mk j) ⟶ p.obj) := by
  rw [section_iff_hom_to_fieldPoint B S hS 𝒳 p W _ (iteratedSliceBackward_comp_p B S hS 𝒳 W f) F e]
  let i := f.hom.toFunctor.mapIso ((Over.iteratedSliceEquiv W).unitIso.app (Over.mk j))
  exact ⟨fun ⟨g⟩ => ⟨i.hom ≫ g⟩, fun ⟨g⟩ => ⟨i.inv ≫ g⟩⟩

/-- The field-valued point of a category fibred in groupoids obtained by pushing a field-valued
point of a represented presheaf forward along a 1-morphism out of the slice of the site. -/
private noncomputable def schemeFieldPointMap
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : BigFppfOver B S hS)
    (f : schemeFibredCategory B S hS W ⟶ 𝒳)
    (q : Space.FieldValuedPoint B S hS (yoneda.obj W)) :
    FieldValuedPoint B S hS 𝒳.val where
  carrier := q.carrier
  field := q.field
  base := q.siteObject
  isSpec := Iso.refl _
  obj := f.hom.toFunctor.obj (Over.mk q.value)
  «over» := f.hom.w_obj _

/-- The point of the stack named by the image of a field-valued point of `h_W` under
`AlgebraicGeometry.Stack.schemeMapToStack` is its image under the canonical map on points of
Stacks 04XL. -/
private theorem schemeFieldPointMap_schemeMapToStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : BigFppfOver B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (m : yoneda.obj W ⟶ U) (f : fibredCategory B S hS U ⟶ 𝒳)
    (q : Space.FieldValuedPoint B S hS (yoneda.obj W)) :
    pointClass B S hS 𝒳.val 𝒳.property
      (schemeFieldPointMap B S hS 𝒳 W (schemeMapToStack B S hS W U m 𝒳 f) q) =
      spacePointMap B S hS U 𝒳 f.hom
        (Space.pointsMap B S hS (yoneda.obj W) m (q.class B S hS _)) := by
  rw [Space.pointsMap_class, spacePointMap_class]
  refine Quotient.sound ⟨_, ⟨𝟙 _⟩, ⟨eqToHom ?_⟩⟩
  change f.hom.obj ((associatedMap B S hS m).1.hom.obj
    ⟨q.siteObject, Discrete.mk q.value⟩) =
    f.hom.obj ⟨q.siteObject, Discrete.mk (m.app _ q.value)⟩
  exact congrArg f.hom.obj (associatedMap_obj B S hS m _)

/-- If a field-valued point of `h_W` and a field-valued point `p` of the stack name the same
point of the stack, then some extension of the former has an arrow to the object of `p`. -/
private theorem exists_dominating_point_with_hom
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (W : BigFppfOver B S hS)
    (f : schemeFibredCategory B S hS W ⟶ 𝒳)
    (q : Space.FieldValuedPoint B S hS (yoneda.obj W))
    (p : FieldValuedPoint B S hS 𝒳.val)
    (h : pointClass B S hS 𝒳.val 𝒳.property (schemeFieldPointMap B S hS 𝒳 W f q) =
        pointClass B S hS 𝒳.val 𝒳.property p) :
    ∃ t : Space.FieldValuedPoint B S hS (yoneda.obj W),
      Space.FieldValuedPoint.Dominates B S hS (yoneda.obj W) t q ∧
        Nonempty (f.hom.toFunctor.obj (Over.mk t.value) ⟶ p.obj) := by
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ :=
    (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val 𝒳.property _ _).mp h
  let Q := schemeFieldPointMap B S hS 𝒳 W f q
  let k : r.base ⟶ q.siteObject :=
    eqToHom r.over.symm ≫ 𝒳.val.p.map a ≫ eqToHom Q.over
  have ha : 𝒳.val.p.IsHomLift k a :=
    IsHomLift.of_fac _ k a r.over Q.over rfl
  obtain ⟨t₀, -⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS r.base
    (r.isSpec.inv.base (IsLocalRing.closedPoint r.carrier))
  obtain ⟨z, φ, hφ⟩ := 𝒳.property.exists_lift t₀.value r.obj r.over
  let g : t₀.siteObject ⟶ q.siteObject := t₀.value ≫ k
  let t := Space.FieldValuedPoint.map B S hS (yoneda.obj r.base)
    (yoneda.map (k ≫ q.value)) t₀
  have hw : (t₀.value ≫ k) ≫ q.value = t₀.value ≫ (k ≫ q.value) := Category.assoc _ _ _
  let j : Over.mk t.value ⟶ Over.mk q.value := Over.homMk g hw
  have hfj : 𝒳.val.p.IsHomLift g (f.hom.map j) := by
    have _ : (schemeFibredCategory B S hS W).val.p.IsHomLift g j := by
      change (Over.forget W).IsHomLift ((Over.forget W).map j) j
      infer_instance
    exact BasedFunctor.preserves_isHomLift f.hom g j
  have hφa : 𝒳.val.p.IsHomLift g (φ ≫ a) := by
    dsimp only [g]
    infer_instance
  obtain ⟨i, -⟩ := exists_vertical_iso_of_lifts 𝒳.val.p 𝒳.property g
    (f.hom.map j) (φ ≫ a) hfj hφa
  exact ⟨t, ⟨g, hw⟩, ⟨i.hom ≫ φ ≫ b⟩⟩

/-- **The image, on points, of an algebraic space representing the base change of a point of the
stack is the fibre of the chart over that point.** With `W` an object of the site, `m : h_W ⟶ U`
a section of an algebraic space with a 1-morphism `f : U ⟶ 𝒳`, and `p` a field-valued point of
`𝒳` whose base change along the scheme-valued point of `𝒳` named by `W` is represented by `F`,
the range of the map on points of the structure morphism of the lower-shriek extension of `F` is
exactly the set of points of `h_W` which the chart sends to the point of `p`. -/
private theorem range_fiberMap
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val)
    (W : BigFppfOver B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (m : yoneda.obj W ⟶ U) (f : fibredCategory B S hS U ⟶ 𝒳)
    (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map W.hom)
        (schemeFibredCategory B S hS p.base).val.p 𝒳.val.p
        (Over.iteratedSliceBackward W ⋙ (schemeMapToStack B S hS W U m 𝒳 f).hom.toFunctor)
        (CatFiberedInGroupoids.homFunctor (fieldValuedPointMorphism B S hS 𝒳 p)))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (Fy : SpacesOverSmallerBase B W.left.1 S W.left.2 hS W.hom)
    (i : Fy.1.left ≅ (OverShriek.relocalizePresheafFunctor W.hom).obj F)
    (hi : ∀ (T : BigFppfOver B S hS) (s : Fy.1.left.obj (Opposite.op T)),
      (Fy.1.hom.app (Opposite.op T) s).left = (i.hom.app (Opposite.op T) s).1.1) :
    Set.range (Space.pointsMap B S hS Fy.1.left Fy.1.hom) =
      {q | spacePointMap B S hS U 𝒳 f.hom
        (Space.pointsMap B S hS (yoneda.obj W) m q) =
        pointClass B S hS 𝒳.val 𝒳.property p} := by
  let fW := schemeMapToStack B S hS W U m 𝒳 f
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨r, rfl⟩ := Quot.exists_rep r
    let t := Space.FieldValuedPoint.map B S hS Fy.1.left Fy.1.hom r
    obtain ⟨a⟩ := (section_iff_hom_to_fieldPoint_over B S hS 𝒳 p W fW F e t.value).mp
      (nonempty_section_relocalize B S hS W F Fy i hi r.siteObject r.value)
    change spacePointMap B S hS U 𝒳 f.hom
      (Space.pointsMap B S hS (yoneda.obj W) m (t.class B S hS _)) = _
    exact (schemeFieldPointMap_schemeMapToStack B S hS 𝒳 W U m f t).symm.trans
      (Quotient.sound ⟨schemeFieldPointMap B S hS 𝒳 W fW t, ⟨𝟙 _⟩, ⟨a⟩⟩)
  · intro hq
    obtain ⟨q, rfl⟩ := Quot.exists_rep q
    obtain ⟨t, ht, ha⟩ := exists_dominating_point_with_hom B S hS 𝒳 W fW q p
      (by rwa [schemeFieldPointMap_schemeMapToStack])
    obtain ⟨s⟩ := (section_iff_hom_to_fieldPoint_over B S hS 𝒳 p W fW F e t.value).mpr ha
    obtain ⟨v, hv⟩ := exists_section_relocalize B S hS W F Fy i hi t.siteObject t.value s
    let r : Space.FieldValuedPoint B S hS Fy.1.left :=
      { carrier := t.carrier
        field := t.field
        contained := t.contained
        toBase := t.toBase
        value := v }
    refine ⟨r.class B S hS _, ?_⟩
    have hr : Space.FieldValuedPoint.map B S hS Fy.1.left Fy.1.hom r = t := by
      cases t
      dsimp only [Space.FieldValuedPoint.map, r]
      congr 1
    rw [Space.pointsMap_class, hr]
    exact Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
      ⟨t, Space.FieldValuedPoint.dominates_refl B S hS _ t, ht⟩

/-! ### Lifting the specialization -/

/-- **Stacks 0GVZ.** Let `𝒳` be an algebraic stack over `S`, let `f : U ⟶ 𝒳` be a smooth
1-morphism from an algebraic space `U` over `S`, let `x' ⤳ x` be a specialization of points of
`|𝒳|` and let `u` be a point of `|U|` with `f(u) = x`. If the point `x'` admits a quasi-compact
field-valued representative — one of the equivalent conditions of **Stacks 0DTK** for the pair
`(𝒳, x')` — then there is a specialization `u' ⤳ u` in `|U|` with `f(u') = x'`.

Smoothness of `f` enters twice. It makes `|U| ⟶ |𝒳|` an open map (**Stacks 06R7**), which is
what puts `u` in the closure of the fibre of `|U| ⟶ |𝒳|` over `x'`: an open neighbourhood of `u`
missing that fibre would have open image containing `x` but not `x'`. And it is what makes the
base change of the 1-morphism `Spec k ⟶ 𝒳` of the representative an algebraic space over the
affine chart, so that the fibre is the image, on points, of an affine scheme quasi-compact over
the chart; **Stacks 02JQ** then produces the specialization inside that fibre. -/
@[stacks 0GVZ]
theorem exists_specializes_spacePointMap_eq
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (f : fibredCategory B S hS U ⟶ 𝒳)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) f)
    {x x' : points B S hS 𝒳.val 𝒳.property} (hxx' : x' ⤳ x)
    (hx' : ∃ p : FieldValuedPoint B S hS 𝒳.val,
      pointClass B S hS 𝒳.val 𝒳.property p = x' ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳 p)
    (u : Space.points B S hS U) (hu : spacePointMap B S hS U 𝒳 f.hom u = x) :
    ∃ u' : Space.points B S hS U, u' ⤳ u ∧
      spacePointMap B S hS U 𝒳 f.hom u' = x' := by
  obtain ⟨p, hpclass, hrepQ, hrelQ⟩ := hx'
  -- An affine étale chart `m : h_W ⟶ U` of the source through the prescribed point.
  obtain ⟨W, m, qW, hWaff, hmet, hmu⟩ := exists_affine_etaleChart_pointsMap_eq B S hS U hU u
  -- The scheme-valued point of `𝒳` that the chart names.
  let y := Over.iteratedSliceBackward W ⋙ (schemeMapToStack B S hS W U m 𝒳 f).hom.toFunctor
  have hy : y ⋙ 𝒳.val.p = Over.map W.hom :=
    iteratedSliceBackward_comp_p B S hS 𝒳 W (schemeMapToStack B S hS W U m 𝒳 f)
  -- The base change of the 1-morphism of the representative along that point.
  obtain ⟨F, hF, Fy, hEquiv, hFyeq, ι, hι⟩ := exists_algebraicSpace_over_baseChange B S hS
    (fieldValuedPointMorphism B S hS 𝒳 p) hrepQ W y hy
  have hFqc : Space.IsQuasiCompact B S hS (algebraicSpaceMap B S hS W Fy).hom := by
    subst hFyeq
    exact hrelQ W y hy F hF hEquiv
  -- It is a quasi-compact algebraic space, the chart being affine.
  obtain ⟨T, aT, hTaff, hTsurj, -⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Fy.1.left
      Fy.property).mp <| Space.IsQuasiCompactSpace.of_iso B S hS
      (hFqc (yoneda.obj (Over.mk W.hom)) (isAlgebraicSpace_yoneda B S hS (Over.mk W.hom))
        (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS (Over.mk W.hom) hWaff) (𝟙 _))
      (asIso (pullback.snd (𝟙 (yoneda.obj (Over.mk W.hom)))
        (algebraicSpaceMap B S hS W Fy).hom))
  let g : T ⟶ W := Yoneda.fullyFaithful.preimage (aT ≫ Fy.1.hom)
  have hg : yoneda.map g = aT ≫ Fy.1.hom := Yoneda.fullyFaithful.map_preimage _
  -- The image of `|T|` in `|W|` is the fibre of the chart over `x'`.
  have hrange₀ : Set.range (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g)) =
      {q | spacePointMap B S hS U 𝒳 f.hom
        (Space.pointsMap B S hS (yoneda.obj W) m q) = x'} := by
    have hcomp : Space.pointsMap B S hS (yoneda.obj T) (aT ≫ Fy.1.hom) =
        Space.pointsMap B S hS Fy.1.left Fy.1.hom ∘ Space.pointsMap B S hS (yoneda.obj T) aT :=
      funext (Space.pointsMap_comp_apply B S hS aT Fy.1.hom)
    rw [hg, hcomp, ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS Fy.1.left
      Fy.property T aT).mp hTsurj).range_comp, ← hpclass]
    exact range_fiberMap B S hS 𝒳 p W U m f F hEquiv.some Fy ι hι
  -- The chart is open on points, so `u` is in the closure of that fibre.
  have hclosureW : qW ∈
      closure (Set.range (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g))) := by
    rw [hrange₀]
    exact mem_closure_fiber_of_isOpenMap _
      ((isOpenMap_spacePointMap_of_isSmooth B S hS 𝒳 h𝒳 U hU f hf).comp
        (Space.isOpenMap_pointsMap_of_etale B S hS hU W m hmet))
      (by rwa [Function.comp_apply, hmu, hu])
  -- Stacks 02JQ inside the chart.
  obtain ⟨r, hr⟩ := exists_specializes_of_mem_closure_range_pointsMap B S hS g qW hclosureW
  refine ⟨Space.pointsMap B S hS (yoneda.obj W) m
    (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map g) r), ?_,
    (Set.ext_iff.mp hrange₀ _).mp ⟨r, rfl⟩⟩
  rw [← hmu]
  exact hr.map (Space.continuous_pointsMap B S hS m)

end AlgebraicGeometry.Stack

end
