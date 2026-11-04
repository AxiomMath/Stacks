module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness

/-!
# Cycles on a good algebraic space decomposed into open and closed subspaces

In Situation 0EDT let `X/B` be good and let `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` be a decomposition of `X`
into open and closed subspaces which are again good over the base. Such a decomposition is
recorded by a family of open immersions `j_i : X_i ⟶ X` over the base whose sets of points are
pairwise disjoint and cover `|X|`; closedness of each piece is then automatic, the complement of
one piece being the union of the others. Along such a decomposition the groups of cycles form a
direct product,

`Z_k(X) = ∏_i Z_k(X_i)`,

with the projections given by restriction of cycles along the inclusions of the pieces.

## Main definitions

* `AlgebraicGeometry.Space.pieceRange`: the set of points of `X` lying on one member of a family
  of morphisms into `X`.
* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition`: a decomposition of a good algebraic
  space over the base into good open and closed subspaces.
* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.index`: the unique index whose piece
  contains a given integral closed subspace.
* `AlgebraicGeometry.Space.glueDecompositionCycle`: the cycle on `X` glued from a family of
  cycles on the pieces.
* `AlgebraicGeometry.Space.cycleGroupDecompositionEquiv`: the isomorphism
  `Z_k(X) ≅ ∏_i Z_k(X_i)`.

## Main results

* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.isOpen_pieceRange` and
  `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.isClosed_pieceRange`: each piece is open
  and closed.
* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.existsUnique_subset_pieceRange`: an
  integral closed subspace of `X` lies in exactly one piece.
* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.exists_closureImage_eq_index`: it is the
  closure of the image of an integral closed subspace of that piece.
* `AlgebraicGeometry.Space.isClopenSubspaceDecomposition_preimage`: a decomposition of `X` pulls
  back to one of `X'` along a morphism `X' ⟶ X`.
* `AlgebraicGeometry.Space.cycleGroupDecompositionEquiv`: the product decomposition of the groups
  of cycles along the decomposition.

## Implementation notes

The index type of the decomposition is allowed to live in any universe: the group of cycles on
`X` lives in `Type (u + 1)` while the product over the index type lives in `Type (max (u + 1) v)`,
and `AddEquiv` is heterogeneous in universes.

Goodness of each piece over the base is part of the datum, not derived from goodness of `X`.

## References

* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Definition

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {I : Type v} {U : I → (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The set of points of `X` lying on the `i`-th member of a family of morphisms into `X`, that
is, the image on points of that morphism. -/
abbrev pieceRange (j : ∀ i, U i ⟶ X) (i : I) : Set (points D.site D.base D.base_mem X) :=
  Set.range (pointsMap D.site D.base D.base_mem (U i) (j i))

/-- A decomposition `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` of a good algebraic space over the base into open
and closed subspaces: a family of open immersions over the base whose sources are again good and
whose sets of points are pairwise disjoint and cover `|X|`. -/
structure IsClopenSubspaceDecomposition (sX : X ⟶ D.space) (j : ∀ i, U i ⟶ X) : Prop where
  /-- The ambient space is good over the base. -/
  isGood : D.IsGood sX
  /-- Each piece is good over the base. -/
  isGoodPiece : ∀ i, D.IsGood (j i ≫ sX)
  /-- Each piece is an open subspace. -/
  isOpenImmersion : ∀ i, IsOpenImmersion D.site D.base D.base_mem (j i)
  /-- Distinct pieces have disjoint sets of points. -/
  disjoint : ∀ i i', i ≠ i' → Disjoint (pieceRange D j i) (pieceRange D j i')
  /-- The pieces cover the set of points of `X`. -/
  iUnion_pieceRange_eq_univ : (⋃ i, pieceRange D j i) = Set.univ

end Definition

section Pieces

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {I : Type v} {U : I → (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {j : ∀ i, U i ⟶ X}

namespace IsClopenSubspaceDecomposition

/-- The decomposed space is decent. -/
theorem isDecentSpace (h : IsClopenSubspaceDecomposition D sX j) :
    IsDecentSpace D.site D.base D.base_mem X :=
  D.isDecentSpace_of_isGood sX h.isGood

/-- Each piece is decent. -/
theorem isDecentSpacePiece (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    IsDecentSpace D.site D.base D.base_mem (U i) :=
  D.isDecentSpace_of_isGood (j i ≫ sX) (h.isGoodPiece i)

/-- The inclusion of a piece is an immersion. -/
theorem isImmersion (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    IsImmersion D.site D.base D.base_mem (j i) :=
  isImmersion_of_isOpenImmersion D.site D.base D.base_mem (h.isOpenImmersion i)

/-- The map on points of the inclusion of a piece is an open embedding. -/
theorem isOpenEmbedding_pointsMap (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    Topology.IsOpenEmbedding (pointsMap D.site D.base D.base_mem (U i) (j i)) :=
  isOpenEmbedding_pointsMap_of_isOpenImmersion D h.isGood.1 (h.isOpenImmersion i)

/-- Every point of `X` lies on some piece. -/
theorem exists_mem (h : IsClopenSubspaceDecomposition D sX j)
    (p : points D.site D.base D.base_mem X) : ∃ i, p ∈ pieceRange D j i :=
  Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp h.iUnion_pieceRange_eq_univ p)

/-- A point of `X` lies on at most one piece. -/
theorem eq_of_mem (h : IsClopenSubspaceDecomposition D sX j) {i i' : I}
    {p : points D.site D.base D.base_mem X} (hi : p ∈ pieceRange D j i)
    (hi' : p ∈ pieceRange D j i') : i = i' :=
  Classical.byContradiction fun hne => (h.disjoint i i' hne).le_bot ⟨hi, hi'⟩

/-- Each piece is open. -/
theorem isOpen_pieceRange (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    IsOpen (pieceRange D j i) :=
  isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem (j i)
    (h.isOpenImmersion i)

/-- The complement of a piece is the union of the other pieces. -/
theorem compl_pieceRange_eq (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    (pieceRange D j i)ᶜ = ⋃ i' ∈ ({i}ᶜ : Set I), pieceRange D j i' := by
  ext p
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
  refine ⟨fun hp => ?_, fun ⟨i', hi', hp⟩ hpi => hi' (h.eq_of_mem hp hpi)⟩
  obtain ⟨i', hi'⟩ := h.exists_mem p
  exact ⟨i', fun hii' => hp (hii' ▸ hi'), hi'⟩

/-- Each piece is closed. -/
theorem isClosed_pieceRange (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    IsClosed (pieceRange D j i) := by
  rw [← isOpen_compl_iff, h.compl_pieceRange_eq i]
  exact isOpen_biUnion fun i' _ => h.isOpen_pieceRange i'

/-- An integral closed subspace of `X` is contained in exactly one piece. -/
theorem existsUnique_subset_pieceRange (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ∃! i, subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ pieceRange D j i := by
  have hirr := isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z
  obtain ⟨p, hp⟩ := hirr.1
  obtain ⟨i, hi⟩ := h.exists_mem p
  exact ⟨i, hirr.isConnected.isPreconnected.subset_isClopen
    ⟨h.isClosed_pieceRange i, h.isOpen_pieceRange i⟩ ⟨p, hp, hi⟩,
    fun i' hi' => h.eq_of_mem (hi' hp) hi⟩

/-- The unique index whose piece contains a given integral closed subspace of `X`. -/
noncomputable def index (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : I :=
  (h.existsUnique_subset_pieceRange Z).choose

/-- An integral closed subspace of `X` is contained in the piece of its index. -/
theorem subspacePointSet_subset_pieceRange_index (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ pieceRange D j (h.index Z) :=
  (h.existsUnique_subset_pieceRange Z).choose_spec.1

/-- Any piece containing an integral closed subspace of `X` is the piece of its index. -/
theorem index_eq (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) {i : I}
    (hi : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ pieceRange D j i) :
    h.index Z = i :=
  ((h.existsUnique_subset_pieceRange Z).choose_spec.2 i hi).symm

/-- The integral closed subspace of `X` attached to one of the `i`-th piece: the closure of its
image. -/
noncomputable abbrev pieceClosureImage (h : IsClopenSubspaceDecomposition D sX j) (i : I)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (U i)) :
    IntegralClosedSubspace D.site D.base D.base_mem X :=
  IntegralClosedSubspace.closureImage D.site D.base D.base_mem h.isGood.1
    (D.isDecentSpace_of_isGood sX h.isGood) (j i) W

/-- The closure of the image of an integral closed subspace of the `i`-th piece stays inside that
piece. -/
theorem subspacePointSet_pieceClosureImage_subset (h : IsClopenSubspaceDecomposition D sX j)
    (i : I) (W : IntegralClosedSubspace D.site D.base D.base_mem (U i)) :
    subspacePointSet D.site D.base D.base_mem X (h.pieceClosureImage i W).subspace ⊆
      pieceRange D j i := by
  rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  exact (h.isClosed_pieceRange i).closure_subset_iff.2 (Set.image_subset_range _ _)

/-- The index of the closure of the image of an integral closed subspace of the `i`-th piece
is `i`. -/
theorem index_pieceClosureImage (h : IsClopenSubspaceDecomposition D sX j) (i : I)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (U i)) :
    h.index (h.pieceClosureImage i W) = i :=
  h.index_eq _ (h.subspacePointSet_pieceClosureImage_subset i W)

/-- The map taking the closure of the image of an integral closed subspace of a piece is
injective. -/
theorem injective_pieceClosureImage (h : IsClopenSubspaceDecomposition D sX j) (i : I) :
    Function.Injective (h.pieceClosureImage i) :=
  IntegralClosedSubspace.injective_closureImage D h.isGood.1 (h.isGoodPiece i).1
    h.isDecentSpace (h.isImmersion i)

/-- An integral closed subspace of `X` meeting the `i`-th piece is the closure of the image of an
integral closed subspace of that piece. -/
theorem exists_pieceClosureImage_eq (h : IsClopenSubspaceDecomposition D sX j) (i : I)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (subspacePointSet D.site D.base D.base_mem X Z.subspace ∩
      pieceRange D j i).Nonempty) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem (U i),
      h.pieceClosureImage i W = Z :=
  IntegralClosedSubspace.exists_closureImage_eq D h.isGood.1 (h.isGoodPiece i).1
    h.isDecentSpace (h.isDecentSpacePiece i) (h.isOpenImmersion i) Z hZ

/-- An integral closed subspace of `X` is the closure of the image of an integral closed subspace
of the piece of its index. -/
theorem exists_closureImage_eq_index (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem (U (h.index Z)),
      h.pieceClosureImage (h.index Z) W = Z := by
  refine h.exists_pieceClosureImage_eq (h.index Z) Z ?_
  obtain ⟨p, hp⟩ :=
    (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z).1
  exact ⟨p, hp, h.subspacePointSet_subset_pieceRange_index Z hp⟩

/-- The integral closed subspace of the piece of the index of `Z` whose image has closure `Z`. -/
noncomputable def pieceSubspace (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem (U (h.index Z)) :=
  (h.exists_closureImage_eq_index Z).choose

/-- The closure of the image of the integral closed subspace chosen on the piece of the index is
the subspace it came from. -/
theorem pieceClosureImage_pieceSubspace (h : IsClopenSubspaceDecomposition D sX j)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    h.pieceClosureImage (h.index Z) (h.pieceSubspace Z) = Z :=
  (h.exists_closureImage_eq_index Z).choose_spec

end IsClopenSubspaceDecomposition

/-! ### Pulling a decomposition back along a morphism -/

section Preimage

variable {X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {V : I → Subfunctor X}
    {sX' : X' ⟶ D.space}

/-- The set of points of `X'` lying on the preimage of a subspace is the preimage of its set of
points. -/
theorem pieceRange_preimage (f : X' ⟶ X) (i : I) :
    pieceRange D (fun i => ((V i).preimage f).ι) i =
      pointsMap D.site D.base D.base_mem X' f ⁻¹' pieceRange D (fun i => (V i).ι) i :=
  subspacePointSet_preimage D.site D.base D.base_mem f (V i)

/-- A decomposition of a good algebraic space over the base into good open and closed subspaces
pulls back along a morphism: if `X = V_0 ⊔ V_1 ⊔ V_2 ⊔ …` is such a decomposition and
`f : X' ⟶ X` is a morphism whose source is good and whose preimages of the pieces are good, then
the preimages form such a decomposition of `X'`. -/
@[stacks 0ES2 "the decomposition of X' obtained by pullback"]
theorem isClopenSubspaceDecomposition_preimage {sX : X ⟶ D.space} (f : X' ⟶ X)
    (h : IsClopenSubspaceDecomposition D sX fun i => (V i).ι) (hX' : D.IsGood sX')
    (hpiece : ∀ i, D.IsGood (((V i).preimage f).ι ≫ sX')) :
    IsClopenSubspaceDecomposition D sX' fun i => ((V i).preimage f).ι := by
  refine ⟨hX', hpiece, fun i => ?_, fun i i' hne => ?_, ?_⟩
  · exact (isOpenSubspace_preimage D.site D.base D.base_mem f (V i) h.isGood.1 hX'.1
      ⟨(h.isGoodPiece i).1, h.isOpenImmersion i⟩).2
  · rw [pieceRange_preimage f i, pieceRange_preimage f i']
    exact Disjoint.preimage _ (h.disjoint i i' hne)
  · rw [Set.iUnion_congr fun i => pieceRange_preimage f i, ← Set.preimage_iUnion,
      h.iUnion_pieceRange_eq_univ, Set.preimage_univ]

end Preimage

/-! ### Gluing a family of cycles on the pieces -/

/-- The coefficient family on `X` glued from a family of cycles on the pieces of a decomposition:
at an integral closed subspace `Z` of `X` it is the coefficient of the cycle on the piece of the
index of `Z` at the integral closed subspace of that piece whose image has closure `Z`. -/
noncomputable def glueDecompositionCoeff {k : ℤ}
    (h : IsClopenSubspaceDecomposition D sX j)
    (β : ∀ i, CycleGroup D (j i ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  (β (h.index Z)).1 (h.pieceSubspace Z)

/-- The glued coefficient at the closure of the image of an integral closed subspace of a piece
is the coefficient of the cycle on that piece. -/
theorem glueDecompositionCoeff_eq {k : ℤ} (h : IsClopenSubspaceDecomposition D sX j)
    (β : ∀ i, CycleGroup D (j i ≫ sX) k)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} {i : I}
    {W : IntegralClosedSubspace D.site D.base D.base_mem (U i)}
    (hW : h.pieceClosureImage i W = Z) :
    glueDecompositionCoeff h β Z = (β i).1 W := by
  have hidx : h.index Z = i := hW ▸ h.index_pieceClosureImage i W
  subst hidx
  have : h.pieceSubspace Z = W :=
    h.injective_pieceClosureImage _ ((h.pieceClosureImage_pieceSubspace Z).trans hW.symm)
  rw [glueDecompositionCoeff, this]

/-- The glued coefficient family of a family of `k`-cycles on the pieces is a `k`-cycle. -/
theorem glueDecompositionCoeff_mem_cyclesOfDimension {k : ℤ}
    (h : IsClopenSubspaceDecomposition D sX j)
    (β : ∀ i, CycleGroup D (j i ≫ sX) k) :
    glueDecompositionCoeff h β ∈ cyclesOfDimension D sX k := by
  refine ⟨fun p => ?_, fun Z hZ => ?_⟩
  · obtain ⟨i, q, rfl⟩ := id (h.exists_mem p)
    obtain ⟨t, ht, hfin⟩ := (β i).2.1 q
    obtain ⟨O, hOt, hO, hqO⟩ := mem_nhds_iff.mp ht
    have hemb := h.isOpenEmbedding_pointsMap i
    refine ⟨pointsMap D.site D.base D.base_mem (U i) (j i) '' O,
      (hemb.isOpenMap O hO).mem_nhds ⟨q, hqO, rfl⟩, ?_⟩
    refine (hfin.image (h.pieceClosureImage i)).subset ?_
    rintro Z ⟨x, hxZ, y, hyO, hxy⟩
    simp only [Set.mem_ite_empty_left] at hxZ
    obtain ⟨hZ0, hxZ⟩ := hxZ
    have hmeet : (subspacePointSet D.site D.base D.base_mem X Z.subspace ∩
        pieceRange D j i).Nonempty := ⟨x, hxZ, y, hxy⟩
    obtain ⟨W, rfl⟩ := h.exists_pieceClosureImage_eq i Z hmeet
    refine ⟨W, ?_, rfl⟩
    have hWne : (β i).1 W ≠ 0 := by
      rwa [← glueDecompositionCoeff_eq h β (rfl : h.pieceClosureImage i W = _)]
    rw [IntegralClosedSubspace.subspacePointSet_closureImage] at hxZ
    have hxnhds : pointsMap D.site D.base D.base_mem (U i) (j i) '' O ∈ nhds x :=
      (hemb.isOpenMap O hO).mem_nhds ⟨y, hyO, hxy⟩
    obtain ⟨z, ⟨w, hwO, hwz⟩, w', hw'W, hw'z⟩ := mem_closure_iff_nhds.mp hxZ _ hxnhds
    refine ⟨w, ?_, hOt hwO⟩
    simp only [Set.mem_ite_empty_left]
    exact ⟨hWne, hemb.injective (hwz.trans hw'z.symm) ▸ hw'W⟩
  · obtain ⟨W, hW⟩ := h.exists_closureImage_eq_index Z
    have hWne : (β (h.index Z)).1 W ≠ 0 := by
      rwa [← glueDecompositionCoeff_eq h β hW]
    rw [← hW, IntegralClosedSubspace.deltaDimension_closureImage D sX h.isGood.2.2 h.isGood.1
      (h.isGoodPiece (h.index Z)).1 h.isDecentSpace
      (h.isImmersion (h.index Z)) W]
    exact (β (h.index Z)).2.2 W hWne

/-- The `k`-cycle on `X` glued from a family of `k`-cycles on the pieces of a decomposition. -/
noncomputable def glueDecompositionCycle {k : ℤ} (h : IsClopenSubspaceDecomposition D sX j)
    (β : ∀ i, CycleGroup D (j i ≫ sX) k) : CycleGroup D sX k :=
  ⟨glueDecompositionCoeff h β, glueDecompositionCoeff_mem_cyclesOfDimension h β⟩

/-! ### The product decomposition of the groups of cycles -/

/-- Restriction of `k`-cycles to all the pieces of a decomposition at once. -/
noncomputable def cycleGroupDecompositionRestrict (h : IsClopenSubspaceDecomposition D sX j)
    (k : ℤ) : CycleGroup D sX k →+ ∀ i, CycleGroup D (j i ≫ sX) k where
  toFun α i := cycleGroupRestrict D sX h.isGood (j i ≫ sX) (h.isGoodPiece i)
    (h.isOpenImmersion i) rfl k α
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

/-- The coefficient of the restriction of a cycle to the `i`-th piece at an integral closed
subspace of that piece is the coefficient of the cycle at the closure of its image. -/
theorem cycleGroupDecompositionRestrict_apply (h : IsClopenSubspaceDecomposition D sX j) (k : ℤ)
    (α : CycleGroup D sX k) (i : I)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (U i)) :
    (cycleGroupDecompositionRestrict h k α i).1 W = α.1 (h.pieceClosureImage i W) :=
  rfl

/-- Restriction to the pieces is injective. -/
theorem injective_cycleGroupDecompositionRestrict (h : IsClopenSubspaceDecomposition D sX j)
    (k : ℤ) : Function.Injective (cycleGroupDecompositionRestrict h k) := by
  intro α γ hαγ
  refine Subtype.ext (funext fun Z => ?_)
  obtain ⟨W, hW⟩ := h.exists_closureImage_eq_index Z
  rw [← hW, ← cycleGroupDecompositionRestrict_apply h k α (h.index Z) W,
    ← cycleGroupDecompositionRestrict_apply h k γ (h.index Z) W, hαγ]

/-- Restriction to the pieces is surjective: a family of cycles on the pieces is the restriction
of the glued cycle. -/
theorem surjective_cycleGroupDecompositionRestrict (h : IsClopenSubspaceDecomposition D sX j)
    (k : ℤ) : Function.Surjective (cycleGroupDecompositionRestrict h k) := fun β =>
  ⟨glueDecompositionCycle h β, funext fun i => Subtype.ext (funext fun W =>
    glueDecompositionCoeff_eq h β (rfl : h.pieceClosureImage i W = _))⟩

/-- Along a decomposition `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` of a good algebraic space over the base into
good open and closed subspaces, the groups of `k`-cycles form a direct product
`Z_k(X) = ∏_i Z_k(X_i)`, the projections being restriction along the inclusions of the pieces. -/
@[stacks 0ES2 "the clause CH_*(X') = ∏ CH_*(X'_r), at the level of cycles"]
noncomputable def cycleGroupDecompositionEquiv (h : IsClopenSubspaceDecomposition D sX j)
    (k : ℤ) : CycleGroup D sX k ≃+ ∀ i, CycleGroup D (j i ≫ sX) k :=
  AddEquiv.ofBijective (cycleGroupDecompositionRestrict h k)
    ⟨injective_cycleGroupDecompositionRestrict h k,
      surjective_cycleGroupDecompositionRestrict h k⟩

/-- The isomorphism of the product decomposition is restriction to the pieces. -/
@[simp]
theorem cycleGroupDecompositionEquiv_apply (h : IsClopenSubspaceDecomposition D sX j) (k : ℤ)
    (α : CycleGroup D sX k) (i : I)
    (W : IntegralClosedSubspace D.site D.base D.base_mem (U i)) :
    (cycleGroupDecompositionEquiv h k α i).1 W = α.1 (h.pieceClosureImage i W) :=
  rfl

end Pieces

end AlgebraicGeometry.Space

end
