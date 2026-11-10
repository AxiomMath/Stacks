module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Constructing invariant open subspaces of a groupoid in algebraic spaces

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S`. The *saturation* of a subspace `W` of the object space `U` is the subspace of `U`
whose point set is `s(t⁻¹(W))`: the objects which are the source of an arrow whose target lies
in `W`. It is the union of the `R`-orbits meeting `W`.

When the source morphism is open and `W` is an open subspace, the saturation is again an open
subspace, and it is invariant: an arrow whose source lies in it has its target in it, because
the orbit of a point of the saturation is the orbit of a point of `W`. When moreover the target
morphism is quasi-compact, the saturation of a quasi-compact open subspace is quasi-compact,
so the saturations of the members of an affine Zariski covering of `U` form a covering of `U`
by invariant quasi-compact open subspaces.

## Main definitions

All declarations below live in the `AlgebraicGeometry.Space` namespace.

* `sourceSaturationPoints`: the point set `s(t⁻¹(W))`.
* `sourceSaturation`: **Stacks 044G**, the subspace of the object space cut out by that point
  set.

## Main results

* `isOpen_sourceSaturationPoints` and `isOpenSubspace_sourceSaturation`: for an open source
  morphism the saturation of an open subspace is an open subspace.
* `isInvariantOpen_sourceSaturation`: **Stacks 044G, part (1)**, that open subspace is
  invariant.
* `isQuasiCompactSpace_sourceSaturation`: for a quasi-compact target morphism the saturation
  of a quasi-compact open subspace is quasi-compact.
* `exists_isZariskiCover_isInvariantOpen_isQuasiCompactSpace`: **Stacks 044G, part (2)**, the
  object space is covered by invariant quasi-compact open subspaces.

## Implementation notes

The saturation is built with `AlgebraicGeometry.Space.openSubspaceOfPoints`, the subspace cut
out by a set of points, rather than by inverting the order isomorphism of Stacks 03BZ. That
construction needs no hypothesis on the set or on the ambient presheaf, so the saturation is
defined for an arbitrary subspace `W` and its point set is identified unconditionally by
`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`; openness enters only where
it is used, and the hypotheses of the source are visible one at a time. In particular only
openness of the source is needed for part (1) and only quasi-compactness of the target for
part (2), whereas the source assumes both morphisms open, respectively open and quasi-compact.
The two assumptions are interchangeable for a groupoid, the inverse exchanging source and
target, so this is a genuine weakening of the hypotheses rather than a different statement.

Invariance is read on sections rather than on points: the inverse image of the subspace cut out
by a set of points is the subspace cut out by the preimage of that set
(`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`, now in
`StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence`), so the inclusion of inverse
images asked for by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantOpen` reduces to the inclusion
`s⁻¹(s(t⁻¹(W))) ⊆ t⁻¹(s(t⁻¹(W)))` of sets of points. That inclusion is the orbit transport
`mem_sourceSaturationPoints_target_of_source` below: given an arrow `p` whose source is the
source of an arrow `q` with target in `W`, the composite `q ∘ p⁻¹` is an arrow with source the
target of `p` and target in `W`. Composing arrows at a single test object is what the pointwise
groupoid structure of Stacks 043W provides, and the field-valued representatives of the two
points are first moved to a common test object, which is what
`AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff` supplies.

For part (2), the saturation receives the inverse image `t⁻¹(W)` through the factorisation of
Stacks 03IE, surjectively on points, and that inverse image is quasi-compact because it is
cartesian over `W` along `t`. Quasi-compactness then transfers along a surjection by Stacks
040W.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 044G](https://stacks.math.columbia.edu/tag/044G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images, for the subspace cut out by a set of points -/

/-- The inverse image of the subspace cut out by a set of points is the subspace cut out by the
preimage of that set: a section lands in the inverse image exactly when all of its points are
sent into the given set. -/
private alias preimage_openSubspaceOfPoints := preimage_openSubspaceOfPoints'

/-- The point set of the inverse image of a subspace is the preimage of its point set: the
inverse image is cartesian over the subspace by Stacks 083Q, and the point set of a fibre
product surjects onto the fibre product of the point sets. -/
private theorem range_pointsMap_ι_preimage
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F' ⟶ F) (W : Subfunctor F) :
    Set.range (pointsMap B S hS (W.preimage f).toFunctor (W.preimage f).ι) =
      pointsMap B S hS F' f ⁻¹' Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  simpa only [Set.image_univ, Set.preimage_univ] using
    (preimage_image_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage f W) Set.univ).symm

/-! ### The saturation of a subspace under the source and target maps -/

variable {A : AlgebraicSpaces B S hS}

/-- The set of points of the object space of a groupoid in algebraic spaces which are the
source of an arrow whose target lies in `W`, that is the set `s(t⁻¹(W))`. -/
noncomputable def sourceSaturationPoints (G : GroupoidInAlgebraicSpaces B S hS A)
    (W : Subfunctor G.objects.obj) : Set (points B S hS G.objects.obj) :=
  pointsMap B S hS G.arrows.obj G.source.hom ''
    (pointsMap B S hS G.arrows.obj G.target.hom ⁻¹'
      Set.range (pointsMap B S hS W.toFunctor W.ι))

/-- **Stacks 044G.** The *saturation* of a subspace `W` of the object space of a groupoid in
algebraic spaces: the subspace whose point set is `s(t⁻¹(W))`, the union of the orbits meeting
`W`. -/
@[stacks 044G "the saturation s(t⁻¹(W)) of a subspace of the object space"]
noncomputable def sourceSaturation (G : GroupoidInAlgebraicSpaces B S hS A)
    (W : Subfunctor G.objects.obj) : Subfunctor G.objects.obj :=
  openSubspaceOfPoints B S hS G.objects.obj (sourceSaturationPoints B S hS G W)

/-- The point set of the saturation of `W` is `s(t⁻¹(W))`. -/
@[simp]
theorem range_pointsMap_ι_sourceSaturation (G : GroupoidInAlgebraicSpaces B S hS A)
    (W : Subfunctor G.objects.obj) :
    Set.range (pointsMap B S hS (sourceSaturation B S hS G W).toFunctor
        (sourceSaturation B S hS G W).ι) =
      sourceSaturationPoints B S hS G W :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- A point of `W` is the source of an arrow whose target lies in `W`, namely of the identity
arrow at that point; so `W` is contained in its own saturation. -/
theorem range_pointsMap_ι_subset_sourceSaturationPoints
    (G : GroupoidInAlgebraicSpaces B S hS A) (W : Subfunctor G.objects.obj) :
    Set.range (pointsMap B S hS W.toFunctor W.ι) ⊆ sourceSaturationPoints B S hS G W := by
  rintro - ⟨w, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  let T := Opposite.op (p.siteObject B S hS W.toFunctor)
  let z := W.ι.app T p.value
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (G.objects.obj.obj T) := (H.pointwiseData T).groupoid
  let a := H.evaluationArrowEquiv T z z (𝟙 z)
  let r : FieldValuedPoint B S hS G.arrows.obj := ⟨p.carrier, p.contained, p.toBase, a.1⟩
  have key (f : G.arrows.obj ⟶ G.objects.obj) (hf : f.app T a.1 = z) :
      pointsMap B S hS G.arrows.obj f (r.class B S hS G.arrows.obj) =
        pointsMap B S hS W.toFunctor W.ι (p.class B S hS W.toFunctor) := by
    change Quot.mk _ (FieldValuedPoint.map B S hS G.arrows.obj f r) =
      Quot.mk _ (FieldValuedPoint.map B S hS W.toFunctor W.ι p)
    congr 1
    change FieldValuedPoint.mk p.carrier p.contained p.toBase (f.app T a.1) = _
    rw [hf]
    rfl
  exact ⟨r.class B S hS G.arrows.obj,
    ⟨p.class B S hS W.toFunctor, (key G.target.hom a.2.2).symm⟩, key G.source.hom a.2.1⟩

/-! ### Openness of the saturation -/

/-- For an open source morphism the saturation of an open subspace has open point set: the
inverse image `t⁻¹(W)` is open because `t` is continuous on points and the point set of an
open subspace is open, and its image under `s` is then open. -/
theorem isOpen_sourceSaturationPoints (G : GroupoidInAlgebraicSpaces B S hS A)
    (hs : IsOpenMorphism B S hS G.source.hom) (W : Subfunctor G.objects.obj)
    (hW : IsOpenSubspace B S hS W) :
    IsOpen (sourceSaturationPoints B S hS G W) :=
  hs _ ((continuous_pointsMap B S hS G.target.hom).isOpen_preimage _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2))

/-- For an open source morphism the saturation of an open subspace is an open subspace. -/
theorem isOpenSubspace_sourceSaturation (G : GroupoidInAlgebraicSpaces B S hS A)
    (hs : IsOpenMorphism B S hS G.source.hom) (W : Subfunctor G.objects.obj)
    (hW : IsOpenSubspace B S hS W) :
    IsOpenSubspace B S hS (sourceSaturation B S hS G W) :=
  isOpenSubspace_openSubspaceOfPoints B S hS G.objects.property _
    (isOpen_sourceSaturationPoints B S hS G hs W hW)

/-! ### Invariance of the saturation -/

/-- Transport of an arrow along the orbit relation: if two arrows `p` and `q` of a groupoid in
algebraic spaces have the same source, and the target of `q` lies in `W`, then there is an
arrow whose source is the target of `p` and whose target lies in `W`.

The two field-valued representatives are first moved to a common test object, where the
pointwise groupoid structure of Stacks 043W composes `q` with the inverse of `p`. -/
private theorem exists_source_eq_target_mem
    (G : GroupoidInAlgebraicSpaces B S hS A) (W : Subfunctor G.objects.obj)
    {p q : FieldValuedPoint B S hS G.arrows.obj}
    (hsource : pointsMap B S hS G.arrows.obj G.source.hom
          (p.class B S hS G.arrows.obj) =
        pointsMap B S hS G.arrows.obj G.source.hom (q.class B S hS G.arrows.obj))
    (hq : G.target.hom.app (Opposite.op (q.siteObject B S hS G.arrows.obj)) q.value ∈
      W.obj (Opposite.op (q.siteObject B S hS G.arrows.obj))) :
    ∃ r : FieldValuedPoint B S hS G.arrows.obj,
      pointsMap B S hS G.arrows.obj G.source.hom (r.class B S hS G.arrows.obj) =
          pointsMap B S hS G.arrows.obj G.target.hom (p.class B S hS G.arrows.obj) ∧
        G.target.hom.app (Opposite.op (r.siteObject B S hS G.arrows.obj)) r.value ∈
          W.obj (Opposite.op (r.siteObject B S hS G.arrows.obj)) := by
  let ps := FieldValuedPoint.map B S hS G.arrows.obj G.source.hom p
  let qs := FieldValuedPoint.map B S hS G.arrows.obj G.source.hom q
  obtain ⟨e, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G.objects.obj ps qs).mp hsource
  let T := Opposite.op (e.siteObject B S hS G.objects.obj)
  let a := G.arrows.obj.map i.op p.value
  let b := G.arrows.obj.map j.op q.value
  have hsrc : G.source.hom.app T a = G.source.hom.app T b :=
    calc G.source.hom.app T a = G.objects.obj.map i.op ps.value :=
          G.source.hom.naturality_apply i.op p.value
      _ = e.value := hi
      _ = G.objects.obj.map j.op qs.value := hj.symm
      _ = G.source.hom.app T b := (G.source.hom.naturality_apply j.op q.value).symm
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (G.objects.obj.obj T) := (H.pointwiseData T).groupoid
  let hom (x : G.arrows.obj.obj T) : G.source.hom.app T x ⟶ G.target.hom.app T x :=
    (H.evaluationArrowEquiv T _ _).symm ⟨x, rfl, rfl⟩
  let ch := inv (hom a) ≫ eqToHom hsrc ≫ hom b
  let d := H.evaluationArrowEquiv T (G.target.hom.app T a) (G.target.hom.app T b) ch
  let c := d.1
  have hcsrc : G.source.hom.app T c = G.target.hom.app T a := d.2.1
  have hctgt : G.target.hom.app T c = G.target.hom.app T b := d.2.2
  have hbmem : G.target.hom.app T b ∈ W.obj T := by
    rw [G.target.hom.naturality_apply j.op q.value]
    exact W.map j.op hq
  let r : FieldValuedPoint B S hS G.arrows.obj := ⟨e.carrier, e.contained, e.toBase, c⟩
  let tp := FieldValuedPoint.map B S hS G.arrows.obj G.target.hom p
  let common : FieldValuedPoint B S hS G.objects.obj :=
    ⟨e.carrier, e.contained, e.toBase, G.target.hom.app T a⟩
  have hdom₁ : FieldValuedPoint.Dominates B S hS G.objects.obj common
      (FieldValuedPoint.map B S hS G.arrows.obj G.source.hom r) := by
    refine ⟨𝟙 _, ?_⟩
    change G.objects.obj.map (𝟙 T) (G.source.hom.app T c) = G.target.hom.app T a
    simpa using hcsrc
  have hdom₂ : FieldValuedPoint.Dominates B S hS G.objects.obj common tp := by
    refine ⟨i, ?_⟩
    change G.objects.obj.map i.op tp.value = G.target.hom.app T a
    exact (G.target.hom.naturality_apply i.op p.value).symm
  refine ⟨r, ?_, ?_⟩
  · exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G.objects.obj
      ⟨common, hdom₁, hdom₂⟩
  · change G.target.hom.app T c ∈ W.obj T
    exact hctgt ▸ hbmem

/-- An arrow whose source lies in the saturation of `W` has its target in it: the source of the
arrow is the source of an arrow with target in `W`, and the composite of that arrow with the
inverse of the given one has source the target of the given arrow and target in `W`. -/
private theorem mem_sourceSaturationPoints_target_of_source
    (G : GroupoidInAlgebraicSpaces B S hS A) (W : Subfunctor G.objects.obj)
    {z : points B S hS G.arrows.obj}
    (hz : pointsMap B S hS G.arrows.obj G.source.hom z ∈
      sourceSaturationPoints B S hS G W) :
    pointsMap B S hS G.arrows.obj G.target.hom z ∈ sourceSaturationPoints B S hS G W := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  obtain ⟨y, hy, hys⟩ := hz
  rw [← range_pointsMap_ι_preimage B S hS G.target.hom W] at hy
  obtain ⟨y', rfl⟩ := hy
  obtain ⟨q', rfl⟩ := Quot.exists_rep y'
  obtain ⟨r, hrs, hrW⟩ := exists_source_eq_target_mem B S hS G W
    (q := FieldValuedPoint.map B S hS (W.preimage G.target.hom).toFunctor
      (W.preimage G.target.hom).ι q') hys.symm q'.value.property
  refine ⟨r.class B S hS G.arrows.obj, ⟨FieldValuedPoint.class B S hS W.toFunctor
    ⟨r.carrier, r.contained, r.toBase,
      ⟨G.target.hom.app (Opposite.op (r.siteObject B S hS G.arrows.obj)) r.value, hrW⟩⟩, ?_⟩,
    hrs⟩
  rw [pointsMap_class, pointsMap_class]
  rfl

/-- **Stacks 044G, part (1).** For an open source morphism the saturation of an open subspace of
the object space is an invariant open subspace. -/
@[stacks 044G "part (1): the saturation is an invariant open subspace"]
theorem isInvariantOpen_sourceSaturation (G : GroupoidInAlgebraicSpaces B S hS A)
    (hs : IsOpenMorphism B S hS G.source.hom) (W : Subfunctor G.objects.obj)
    (hW : IsOpenSubspace B S hS W) :
    GroupoidInAlgebraicSpaces.IsInvariantOpen G (sourceSaturation B S hS G W) := by
  refine ⟨isOpenSubspace_sourceSaturation B S hS G hs W hW, ?_⟩
  rw [sourceSaturation, preimage_openSubspaceOfPoints, preimage_openSubspaceOfPoints]
  exact openSubspaceOfPoints_mono B S hS fun _ hw ↦
    mem_sourceSaturationPoints_target_of_source B S hS G W hw

/-! ### Quasi-compactness of the saturation -/

/-- For an open source morphism and a quasi-compact target morphism, the saturation of a
quasi-compact open subspace is quasi-compact: the inverse image `t⁻¹(W)` is cartesian over `W`
along `t`, hence quasi-compact, and it maps onto the saturation on points. -/
theorem isQuasiCompactSpace_sourceSaturation (G : GroupoidInAlgebraicSpaces B S hS A)
    (hs : IsOpenMorphism B S hS G.source.hom)
    (ht : IsQuasiCompact B S hS G.target.hom) (W : Subfunctor G.objects.obj)
    (hW : IsOpenSubspace B S hS W) (hWqc : IsQuasiCompactSpace B S hS W.toFunctor) :
    IsQuasiCompactSpace B S hS (sourceSaturation B S hS G W).toFunctor := by
  have hsq := Subfunctor.isPullback_preimage G.target.hom W
  have hPalg : IsAlgebraicSpace B S hS (W.preimage G.target.hom).toFunctor :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hsq.isoPullback
      (isAlgebraicSpace_pullback B S hS W.ι G.target.hom hW.1 G.arrows.property
        G.objects.property)
  have hPqc : IsQuasiCompactSpace B S hS (W.preimage G.target.hom).toFunctor :=
    isQuasiCompactSpace_of_iso B S hS hsq.isoPullback.symm
      (ht W.toFunctor hW.1 hWqc W.ι)
  have hV := isOpenSubspace_sourceSaturation B S hS G hs W hW
  have hrange : Set.range (pointsMap B S hS (W.preimage G.target.hom).toFunctor
        ((W.preimage G.target.hom).ι ≫ G.source.hom)) =
      Set.range (pointsMap B S hS (sourceSaturation B S hS G W).toFunctor
        (sourceSaturation B S hS G W).ι) := by
    rw [range_pointsMap_ι_sourceSaturation, pointsMap_comp, Set.range_comp,
      range_pointsMap_ι_preimage]
    rfl
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS G.objects.property hPalg
    (sourceSaturation B S hS G W) hV _).mpr hrange.le
  refine isQuasiCompactSpace_of_isSurjective B S hS hPalg hV.1 g (fun x ↦ ?_) hPqc
  obtain ⟨y, hy⟩ := hrange.ge (Set.mem_range_self x)
  refine ⟨y, pointsMap_injective_of_mono B S hS (sourceSaturation B S hS G W).ι ?_⟩
  rwa [← pointsMap_comp_apply, hg]

/-! ### The covering by invariant quasi-compact open subspaces -/

/-- **Stacks 044G, part (2).** For an open source morphism and a quasi-compact target morphism,
the object space of a groupoid in algebraic spaces has a Zariski covering by invariant
quasi-compact open subspaces: the saturations of the members of an affine Zariski covering
supplied by Stacks 03FY. -/
@[stacks 044G "part (2): covering by invariant quasi-compact open subspaces"]
theorem exists_isZariskiCover_isInvariantOpen_isQuasiCompactSpace
    (G : GroupoidInAlgebraicSpaces B S hS A)
    (hs : IsOpenMorphism B S hS G.source.hom)
    (ht : IsQuasiCompact B S hS G.target.hom) :
    ∃ (I : Type u) (V : I → Subfunctor G.objects.obj),
      IsZariskiCover B S hS I V ∧
        ∀ i, GroupoidInAlgebraicSpaces.IsInvariantOpen G (V i) ∧
          IsQuasiCompactSpace B S hS (V i).toFunctor := by
  obtain ⟨I, W, hcover, hatlas⟩ :=
    exists_zariski_cover_affine_etale_atlas B S hS G.objects.obj G.objects.property
  refine ⟨I, fun i ↦ sourceSaturation B S hS G (W i), ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · refine (isZariskiCover_iff_iUnion_points B S hS G.objects.obj G.objects.property I _
      fun i ↦ isOpenSubspace_sourceSaturation B S hS G hs (W i) (hcover.1 i)).mpr ?_
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (isZariskiCover_iff_iUnion_points B S hS G.objects.obj G.objects.property I W
      hcover.1).mp hcover]
    refine Set.iUnion_mono fun i ↦ ?_
    rw [range_pointsMap_ι_sourceSaturation]
    exact range_pointsMap_ι_subset_sourceSaturationPoints B S hS G (W i)
  · exact isInvariantOpen_sourceSaturation B S hS G hs (W i) (hcover.1 i)
  · obtain ⟨U, f, -, hUaff, hfsurj, hfetale, -, -⟩ := hatlas i
    exact isQuasiCompactSpace_sourceSaturation B S hS G hs ht (W i) (hcover.1 i)
      ((isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
          (W i).toFunctor (hcover.1 i).1).mpr
        ⟨U, f, hUaff, hfsurj, isEtale_of_presheaf_etale B S hS hfetale⟩)

end AlgebraicGeometry.Space

end
