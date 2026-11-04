module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Points and base change

For presheaves on the big fppf site of `S` and a cartesian square

```
W ---> Z
|      |
v      v
X ---> Y
```

the four induced maps on the point sets of Tag 03BU form a commuting square of sets, hence a
map `|W| → |X| ×_{|Y|} |Z|`. This map is surjective, and surjectivity, openness and closedness
of the map on points transfer along a base change.

The comparison map is not injective in general, already for schemes: for a field `k` with two
extensions `K` and `L`, the fibre product `Spec K ×_{Spec k} Spec L` is the spectrum of
`K ⊗_k L`, which can have many points, while `|Spec K| ×_{|Spec k|} |Spec L|` has exactly one.

## Main results

* `AlgebraicGeometry.Space.exists_points_of_isPullback`: the comparison map of a cartesian
  square of presheaves is surjective onto the fibre product of the point sets;
  `AlgebraicGeometry.Space.range_pointsMap_prod_of_isPullback` is the same statement as an
  equality of sets.
* `AlgebraicGeometry.Space.surjective_pointsMap_of_isPullback`: a base change of a morphism
  surjective on points is surjective on points.
* `AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`: for a cartesian square,
  the preimage along the base map of the image of a set of points is the image of its preimage.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_isPullback` and
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isPullback`: closedness and openness of the
  map on points descend along a base change whose base map detects closed (resp. open) sets;
  `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_isCoinducing` and
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isCoinducing` assume instead that the base
  map is coinducing on points.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_pullback_fst_of_comp`: closedness of
  `|Z ×_Y X| → |Z|` from closedness of `|Z' ×_Y X| → |Z'|`, along a morphism `Z' ⟶ Z` which
  detects closed sets on points.
* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_presheafIsClosedMap` and
  `AlgebraicGeometry.Space.isClosedMap_pointsMap_pullback_fst_of_presheafIsClosedMap`: a
  morphism each of whose represented base changes is a closed map of schemes is closed on
  points, and so is each of its base changes by an arbitrary morphism of presheaves; the open
  analogues are `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafIsOpenMap` and
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_pullback_fst_of_presheafIsOpenMap`.

## Implementation notes

The hypotheses are `CategoryTheory.IsPullback` squares rather than
`CategoryTheory.Limits.pullback`, so that the results apply to any cartesian square of
presheaves; `AlgebraicGeometry.Space.exists_isPullback_pullback_fst_comp` gives the square
`Z' ×_Y X = (Z ×_Y X) ×_Z Z'`, which is not a plain pullback square.

The topologies are `AlgebraicGeometry.Space.pointTopology`, which is not an instance, and are
passed explicitly with `@`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Functoriality of the map on points, elementwise -/

/-- The map on points of a composite, applied to a point. -/
theorem pointsMap_comp_apply {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    (w : points B S hS F) :
    pointsMap B S hS F (α ≫ β) w = pointsMap B S hS G β (pointsMap B S hS F α w) :=
  congrFun (pointsMap_comp B S hS F α β) w

/-- A commuting square of presheaves induces a commuting square of maps on points. -/
theorem pointsMap_apply_comm {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (hw : p ≫ f = q ≫ g) (w : points B S hS W) :
    pointsMap B S hS X f (pointsMap B S hS W p w) =
      pointsMap B S hS Z g (pointsMap B S hS W q w) := by
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hw]

/-! ### Surjectivity of the comparison map -/

/-- A point of `F` has image the class of `x` under `p : F ⟶ X` if `x` is dominated by it via a
morphism `α` of the site carrying the value of `x` to the image of the value. -/
private theorem pointsMap_class_eq_of_map {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ X)
    (x : FieldValuedPoint B S hS X) (r : FieldValuedPoint B S hS F)
    (α : r.siteObject ⟶ x.siteObject)
    (h : X.map α.op x.value = p.app _ r.value) :
    pointsMap B S hS F p (FieldValuedPoint.class B S hS F r) =
      FieldValuedPoint.class B S hS X x := by
  rw [pointsMap_class]
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X
    ⟨_, FieldValuedPoint.dominates_refl B S hS X _, ⟨α, h⟩⟩

/-- The comparison map from the points of a fibre product of presheaves to the fibre product
of the point sets is surjective: a point of `X` and a point of `Z` with the same image in `Y`
are the images of a common point of a presheaf `W` sitting in a cartesian square over them. -/
@[stacks 03H4]
theorem exists_points_of_isPullback {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback p q f g) (a : points B S hS X) (b : points B S hS Z)
    (hab : pointsMap B S hS X f a = pointsMap B S hS Z g b) :
    ∃ w : points B S hS W,
      pointsMap B S hS W p w = a ∧ pointsMap B S hS W q w = b := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep a
  obtain ⟨z, rfl⟩ := Quot.exists_rep b
  rw [pointsMap_class, pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hab
  obtain ⟨r, α, β, hcomm⟩ : ∃ (r : FieldValuedPoint B S hS Y)
      (α : r.siteObject ⟶ x.siteObject) (β : r.siteObject ⟶ z.siteObject),
      Y.map α.op (f.app (Opposite.op x.siteObject) x.value) =
        Y.map β.op (g.app (Opposite.op z.siteObject) z.value) := by
    obtain ⟨r, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := hab
    exact ⟨r, α, β, hα.trans hβ.symm⟩
  have hsq : yonedaEquiv.symm (X.map α.op x.value) ≫ f =
      yonedaEquiv.symm (Z.map β.op z.value) ≫ g := by
    refine yonedaEquiv.injective ?_
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      NatTrans.naturality_apply, NatTrans.naturality_apply]
  refine ⟨FieldValuedPoint.class B S hS W
    { carrier := r.carrier, contained := r.contained, toBase := r.toBase
      value := yonedaEquiv (sq.lift _ _ hsq) }, ?_, ?_⟩
  · refine pointsMap_class_eq_of_map B S hS p _ _ α ?_
    rw [← yonedaEquiv_comp, sq.lift_fst, Equiv.apply_symm_apply]
  · refine pointsMap_class_eq_of_map B S hS q _ _ β ?_
    rw [← yonedaEquiv_comp, sq.lift_snd, Equiv.apply_symm_apply]

/-- The image of the comparison map of a cartesian square of presheaves is exactly the fibre
product of the point sets. -/
theorem range_pointsMap_prod_of_isPullback {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback p q f g) :
    Set.range (fun w : points B S hS W =>
        (pointsMap B S hS W p w, pointsMap B S hS W q w)) =
      {ab : points B S hS X × points B S hS Z |
        pointsMap B S hS X f ab.1 = pointsMap B S hS Z g ab.2} := by
  ext ab
  refine ⟨?_, fun hab ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    exact pointsMap_apply_comm B S hS sq.w w
  · obtain ⟨w, h₁, h₂⟩ := exists_points_of_isPullback B S hS sq ab.1 ab.2 hab
    exact ⟨w, Prod.ext h₁ h₂⟩

/-- A base change of a morphism of presheaves which is surjective
on points is surjective on points. -/
theorem surjective_pointsMap_of_isPullback {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (hp : Function.Surjective (pointsMap B S hS W p)) :
    Function.Surjective (pointsMap B S hS W' p') := by
  intro z
  obtain ⟨w, hw⟩ := hp (pointsMap B S hS Z' h z)
  obtain ⟨u, -, hu⟩ := exists_points_of_isPullback B S hS sq w z hw
  exact ⟨u, hu⟩

/-! ### Transfer of closedness and openness along a base change -/

/-- For a cartesian square of presheaves, the preimage along the base map of the image of a
set of points is the image of its preimage. -/
theorem preimage_image_pointsMap_of_isPullback {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (C : Set (points B S hS W)) :
    pointsMap B S hS Z' h ⁻¹' (pointsMap B S hS W p '' C) =
      pointsMap B S hS W' p' '' (pointsMap B S hS W' c ⁻¹' C) := by
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hwC, hw⟩
    obtain ⟨v, hv₁, hv₂⟩ := exists_points_of_isPullback B S hS sq w z hw
    exact ⟨v, by rwa [Set.mem_preimage, hv₁], hv₂⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, hv, pointsMap_apply_comm B S hS sq.w v⟩

/-- Closedness of the map on points descends along a base change whose base map detects
closed sets on points. -/
theorem isClosedMap_pointsMap_of_isPullback {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (hdet : ∀ C : Set (points B S hS Z),
      @IsClosed _ (pointTopology B S hS Z') (pointsMap B S hS Z' h ⁻¹' C) →
        @IsClosed _ (pointTopology B S hS Z) C)
    (hp' : @IsClosedMap _ _ (pointTopology B S hS W') (pointTopology B S hS Z')
      (pointsMap B S hS W' p')) :
    @IsClosedMap _ _ (pointTopology B S hS W) (pointTopology B S hS Z)
      (pointsMap B S hS W p) := by
  intro C hC
  refine hdet _ ?_
  rw [preimage_image_pointsMap_of_isPullback B S hS sq]
  exact hp' _ (@IsClosed.preimage _ _ (pointTopology B S hS W') (pointTopology B S hS W) _
    (continuous_pointsMap B S hS c) _ hC)

/-- Openness of the map on points descends along a base change whose base map detects open
sets on points. -/
theorem isOpenMap_pointsMap_of_isPullback {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (hdet : ∀ C : Set (points B S hS Z),
      @IsOpen _ (pointTopology B S hS Z') (pointsMap B S hS Z' h ⁻¹' C) →
        @IsOpen _ (pointTopology B S hS Z) C)
    (hp' : @IsOpenMap _ _ (pointTopology B S hS W') (pointTopology B S hS Z')
      (pointsMap B S hS W' p')) :
    @IsOpenMap _ _ (pointTopology B S hS W) (pointTopology B S hS Z)
      (pointsMap B S hS W p) := by
  intro C hC
  refine hdet _ ?_
  rw [preimage_image_pointsMap_of_isPullback B S hS sq]
  exact hp' _ (@IsOpen.preimage _ _ (pointTopology B S hS W') (pointTopology B S hS W) _
    (continuous_pointsMap B S hS c) _ hC)

/-- Closedness of the map on points descends along a base change whose base map is coinducing
on points — in particular along one which is a quotient map on points, by
`Topology.IsQuotientMap.isCoinducing`. -/
theorem isClosedMap_pointsMap_of_isCoinducing {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (hh : @Topology.IsCoinducing _ _ (pointTopology B S hS Z') (pointTopology B S hS Z)
      (pointsMap B S hS Z' h))
    (hp' : @IsClosedMap _ _ (pointTopology B S hS W') (pointTopology B S hS Z')
      (pointsMap B S hS W' p')) :
    @IsClosedMap _ _ (pointTopology B S hS W) (pointTopology B S hS Z)
      (pointsMap B S hS W p) :=
  isClosedMap_pointsMap_of_isPullback B S hS sq
    (fun C hC ↦ ((@Topology.isCoinducing_iff_isClosed _ _ (pointsMap B S hS Z' h)
      (pointTopology B S hS Z') (pointTopology B S hS Z)).mp hh C).mp hC) hp'

/-- Openness of the map on points descends along a base change whose base map is coinducing
on points. -/
theorem isOpenMap_pointsMap_of_isCoinducing {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (hh : @Topology.IsCoinducing _ _ (pointTopology B S hS Z') (pointTopology B S hS Z)
      (pointsMap B S hS Z' h))
    (hp' : @IsOpenMap _ _ (pointTopology B S hS W') (pointTopology B S hS Z')
      (pointsMap B S hS W' p')) :
    @IsOpenMap _ _ (pointTopology B S hS W) (pointTopology B S hS Z)
      (pointsMap B S hS W p) :=
  isOpenMap_pointsMap_of_isPullback B S hS sq
    (fun C hC ↦ ((@Topology.isCoinducing_iff _ _ (pointsMap B S hS Z' h)
      (pointTopology B S hS Z') (pointTopology B S hS Z)).mp hh C).mp hC) hp'

/-! ### The square of an iterated base change -/

/-- A base change of `f : X ⟶ Y` along a composite `Z' ⟶ Z ⟶ Y` is a base change along
`Z' ⟶ Z` of the base change along `Z ⟶ Y`: there is a cartesian square identifying
`Z' ×_Y X` with `(Z ×_Y X) ×_Z Z'`. -/
theorem exists_isPullback_pullback_fst_comp (f : X ⟶ Y) (g : Z ⟶ Y)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z' ⟶ Z) :
    ∃ m : pullback (a ≫ g) f ⟶ pullback g f,
      IsPullback m (pullback.fst (a ≫ g) f) (pullback.fst g f) a :=
  ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback (a ≫ g) f).flip
    (IsPullback.of_hasPullback g f).flip⟩

/-- Closedness of `|Z ×_Y X| → |Z|` from closedness of `|Z' ×_Y X| → |Z'|`, for a morphism
`a : Z' ⟶ Z` which detects closed sets on points. -/
theorem isClosedMap_pointsMap_pullback_fst_of_comp (f : X ⟶ Y) (g : Z ⟶ Y)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z' ⟶ Z)
    (hdet : ∀ C : Set (points B S hS Z),
      @IsClosed _ (pointTopology B S hS Z') (pointsMap B S hS Z' a ⁻¹' C) →
        @IsClosed _ (pointTopology B S hS Z) C)
    (hp' : @IsClosedMap _ _ (pointTopology B S hS (pullback (a ≫ g) f))
      (pointTopology B S hS Z') (pointsMap B S hS _ (pullback.fst (a ≫ g) f))) :
    @IsClosedMap _ _ (pointTopology B S hS (pullback g f)) (pointTopology B S hS Z)
      (pointsMap B S hS _ (pullback.fst g f)) := by
  obtain ⟨m, sq⟩ := exists_isPullback_pullback_fst_comp B S hS f g a
  exact isClosedMap_pointsMap_of_isPullback B S hS sq hdet hp'

/-- Openness of `|Z ×_Y X| → |Z|` from openness of `|Z' ×_Y X| → |Z'|`, for a morphism
`a : Z' ⟶ Z` which detects open sets on points. -/
theorem isOpenMap_pointsMap_pullback_fst_of_comp (f : X ⟶ Y) (g : Z ⟶ Y)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z' ⟶ Z)
    (hdet : ∀ C : Set (points B S hS Z),
      @IsOpen _ (pointTopology B S hS Z') (pointsMap B S hS Z' a ⁻¹' C) →
        @IsOpen _ (pointTopology B S hS Z) C)
    (hp' : @IsOpenMap _ _ (pointTopology B S hS (pullback (a ≫ g) f))
      (pointTopology B S hS Z') (pointsMap B S hS _ (pullback.fst (a ≫ g) f))) :
    @IsOpenMap _ _ (pointTopology B S hS (pullback g f)) (pointTopology B S hS Z)
      (pointsMap B S hS _ (pullback.fst g f)) := by
  obtain ⟨m, sq⟩ := exists_isPullback_pullback_fst_comp B S hS f g a
  exact isOpenMap_pointsMap_of_isPullback B S hS sq hdet hp'

/-- Surjectivity on points of `|Z' ×_Y X| → |Z'|` from surjectivity on points of
`|Z ×_Y X| → |Z|`, for a morphism `a : Z' ⟶ Z`. -/
theorem surjective_pointsMap_pullback_fst_of_comp (f : X ⟶ Y) (g : Z ⟶ Y)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z' ⟶ Z)
    (hp : Function.Surjective (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    Function.Surjective
      (pointsMap B S hS (pullback (a ≫ g) f) (pullback.fst (a ≫ g) f)) := by
  obtain ⟨m, sq⟩ := exists_isPullback_pullback_fst_comp B S hS f g a
  exact surjective_pointsMap_of_isPullback B S hS sq hp

/-! ### Point-set conditions from the represented base changes -/

/-- The property of a morphism of the big fppf site of `S` that its underlying map of schemes
is closed, tested after every represented base change, is stable under base change. -/
private instance presheafIsClosedMapIsStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (topologically @IsClosedMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- The property of a morphism of the big fppf site of `S` that its underlying map of schemes
is open, tested after every represented base change, is stable under base change. -/
private instance presheafIsOpenMapIsStableUnderBaseChange :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- A morphism of presheaves on the big fppf site of `S` each of whose represented base
changes is a closed map of schemes is closed on the point sets of Tag 03BU. -/
theorem isClosedMap_pointsMap_of_presheafIsClosedMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsClosedMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    @IsClosedMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := by
  intro C hC
  rw [← @isOpen_compl_iff _ _ (pointTopology B S hS G), isOpen_pointTopology_iff]
  intro U b
  rw [Set.preimage_compl, ← isOpen_yoneda_iff_isSchemeOpen,
    @isOpen_compl_iff _ _ (pointTopology B S hS (yoneda.obj U)),
    preimage_image_pointsMap_of_isPullback B S hS (hf.rep.isPullback b)]
  exact (isClosedMap_pointsMap_yoneda_iff B S hS (hf.rep.snd b)).mpr (hf.property_snd b) _
    (@IsClosed.preimage _ _ (pointTopology B S hS (yoneda.obj (hf.rep.pullback b)))
      (pointTopology B S hS F) _ (continuous_pointsMap B S hS (hf.rep.fst b)) _ hC)

/-- A morphism of presheaves on the big fppf site of `S` each of whose represented base
changes is an open map of schemes is open on the point sets of Tag 03BU. -/
theorem isOpenMap_pointsMap_of_presheafIsOpenMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    @IsOpenMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := by
  intro C hC
  rw [isOpen_pointTopology_iff]
  intro U b
  rw [← isOpen_yoneda_iff_isSchemeOpen,
    preimage_image_pointsMap_of_isPullback B S hS (hf.rep.isPullback b)]
  exact (isOpenMap_pointsMap_yoneda_iff B S hS (hf.rep.snd b)).mpr (hf.property_snd b) _
    (@IsOpen.preimage _ _ (pointTopology B S hS (yoneda.obj (hf.rep.pullback b)))
      (pointTopology B S hS F) _ (continuous_pointsMap B S hS (hf.rep.fst b)) _ hC)

/-- If every represented base change of `f : X ⟶ Y` is a closed map of schemes, then for every
morphism `g : Z ⟶ Y` of presheaves the base change `|Z ×_Y X| → |Z|` is a closed map for the
point topology. -/
theorem isClosedMap_pointsMap_pullback_fst_of_presheafIsClosedMap (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsClosedMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) (g : Z ⟶ Y) :
    @IsClosedMap _ _ (pointTopology B S hS (pullback g f)) (pointTopology B S hS Z)
      (pointsMap B S hS _ (pullback.fst g f)) :=
  isClosedMap_pointsMap_of_presheafIsClosedMap B S hS _
    (MorphismProperty.pullback_fst g f hf)

/-- If every represented base change of `f : X ⟶ Y` is an open map of schemes, then for every
morphism `g : Z ⟶ Y` of presheaves the base change `|Z ×_Y X| → |Z|` is an open map for the
point topology. -/
theorem isOpenMap_pointsMap_pullback_fst_of_presheafIsOpenMap (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) (g : Z ⟶ Y) :
    @IsOpenMap _ _ (pointTopology B S hS (pullback g f)) (pointTopology B S hS Z)
      (pointsMap B S hS _ (pullback.fst g f)) :=
  isOpenMap_pointsMap_of_presheafIsOpenMap B S hS _
    (MorphismProperty.pullback_fst g f hf)

end AlgebraicGeometry.Space

end
