module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.AtIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The largest open subspace of the base over which a group algebraic space is quasi-finite

Let `G ⟶ B` be a group algebraic space over an algebraic space `B`. There is a largest open
subspace of `B` over which `G` is locally quasi-finite, and, `G` being locally of finite type,
forming it commutes with *arbitrary* base change of algebraic spaces. There is likewise a
largest open subspace of `B` over which `G` is unramified.

## Main definitions

* `AlgebraicGeometry.Space.locallyQuasiFiniteBaseLocus`: the union of all open subspaces of the
  base over which the group algebraic space is locally quasi-finite.
* `AlgebraicGeometry.Space.unramifiedBaseLocus`: the union of all open subspaces of the base
  over which the group algebraic space is unramified.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_locallyQuasiFiniteBaseLocus`: it is an open subspace.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_locallyQuasiFiniteBaseLocus`: the group is
  locally quasi-finite over it.
* `AlgebraicGeometry.Space.le_locallyQuasiFiniteBaseLocus`: it is the largest such open
  subspace.
* `AlgebraicGeometry.Space.locallyQuasiFiniteBaseLocus_preimage`: forming it commutes with
  arbitrary base change.
* `AlgebraicGeometry.Space.isOpenSubspace_unramifiedBaseLocus`,
  `AlgebraicGeometry.Space.isUnramified_unramifiedBaseLocus`,
  `AlgebraicGeometry.Space.le_unramifiedBaseLocus` and
  `AlgebraicGeometry.Space.unramifiedBaseLocus_preimage`: the same four statements in the
  unramified case.

## Implementation notes

Both loci are defined as suprema of subfunctors, so that maximality holds by `le_sSup` with no
hypothesis at all.

For the locally quasi-finite locus everything else goes through the identification of that
supremum with the open subspace of **Stacks 03BZ** cut out by the set of points of the base over
which the structure morphism is quasi-finite at the identity. That set is open, being the
inverse image of the quasi-finite locus of **Stacks 0ABM** under the map on points of the unit,
and it describes the locus because of the criterion of **Stacks 0DSI**,
`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_at_identity`, applied to the base change of
the group along each candidate open subspace. Compatibility with an arbitrary base change
`B' ⟶ B` is read off the same pointwise description: the identity section of the base-changed
group is the base change of the identity section, and the quasi-finite locus commutes with
arbitrary base change by part (2) of **Stacks 0ABM**, so the two point sets correspond. Two open
subspaces with the same point set agree, by part (1) of **Stacks 03BZ**.

For the unramified locus the identity is not used at all: the supremum is identified with the
open subspace cut out by the union of the point sets of the open subspaces over which the group
is unramified, and unramifiedness over that open subspace is checked at each point of the part
of the group above it by the pointwise criterion of **Stacks 03ZK**. At such a point one of the
open subspaces of the family contains its image, and the part of the group above that one meets
the part above the supremum in an open subspace which witnesses the pointwise condition: the
restriction of the group to it factors as a base change of an open immersion — unramified by
**Stacks 06CQ** and **Stacks 03ZJ** — followed by the restriction over the member of the family,
so **Stacks 03ZI** applies. The same bookkeeping, with **Stacks 06G6** for the converse
direction, identifies unramifiedness of the restriction above an open subspace of the base with
unramifiedness of the group on the inverse image of that open subspace.

Compatibility of the unramified locus with an arbitrary base change does use the identity, for
exactly the reason the quasi-finite case does: descending unramifiedness from a base change is a
statement about one point, not about an open subspace, so the supremum has to be identified with
the pointwise description first. That identification is the criterion of **Stacks 0DSI**,
`AlgebraicGeometry.Space.isUnramified_iff_at_identity`, and the point sets then correspond
because the unramified locus commutes with arbitrary base change, part (2) of **Stacks 05W2**,
which is `AlgebraicGeometry.Space.setOf_isUnramifiedAt_eq_preimage_of_isPullback`.

The restriction of the group over an open subspace `U` of the base is written as the second
projection `pullback.snd` out of the fibre product, which is the structure morphism of the base
change `AlgebraicGeometry.Space.GroupAlgebraicSpace.baseChange` of **Stacks 043I**.

## References

* [Stacks Project, Tag 0DSJ](https://stacks.math.columbia.edu/tag/0DSJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Point sets of inverse images of open subspaces -/

/-- The point set of the inverse image of an open subspace is the inverse image of its point
set. One inclusion is the factorization of the inverse image through the subspace, the other is
the lifting of points through a cartesian square, part (2) of Stacks 03H4. -/
private theorem range_pointsMap_preimage
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hF' : IsAlgebraicSpace B S hS F') (f : F' ⟶ F) (V : Subfunctor F)
    (hV : IsOpenSubspace B S hS V) :
    Set.range (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι) =
      pointsMap B S hS F' f ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  have hVpre : IsOpenSubspace B S hS (V.preimage f) :=
    isOpenSubspace_preimage B S hS f V hF hF' hV
  have hsq : IsPullback
      (ObjectProperty.homMk (V.fromPreimage f) :
        (⟨(V.preimage f).toFunctor, hVpre.1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨V.toFunctor, hV.1⟩)
      (ObjectProperty.homMk (V.preimage f).ι : _ ⟶ ⟨F', hF'⟩)
      (ObjectProperty.homMk V.ι : (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk f : (⟨F', hF'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f V)
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨z, rfl⟩
    refine ⟨pointsMap B S hS (V.preimage f).toFunctor (V.fromPreimage f) z, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  · rintro x ⟨v, hv⟩
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS hsq v x hv
    exact ⟨w, hw⟩

/-! ### The largest open subspace of the target over which a morphism is unramified -/

section UnramifiedLocus

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An open immersion of algebraic spaces over `S` is unramified: it is an immersion, so
Stacks 06CQ applies. -/
private theorem isUnramified_of_isOpenImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsOpenImmersion B S hS f) :
    IsUnramified B S hS f :=
  isUnramified_of_isImmersion B S hS hX hY (isImmersion_of_isOpenImmersion B S hS hf)

/-- The canonical morphism from the inverse image of an open subspace of the target to that open
subspace is a base change of the morphism, so unramifiedness transfers to it by Stacks 03ZJ. -/
private theorem isUnramified_fromPreimage (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {V : Subfunctor Y}
    (hV : IsOpenSubspace B S hS V) (hf : IsUnramified B S hS f) :
    IsUnramified B S hS (V.fromPreimage f) :=
  have hpre : IsOpenSubspace B S hS (V.preimage f) :=
    isOpenSubspace_preimage B S hS f V hY hX hV
  (isUnramified_isStableUnderBaseChange B S hS).of_isPullback
    (show IsPullback
      (ObjectProperty.homMk (V.preimage f).ι :
        (⟨(V.preimage f).toFunctor, hpre.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk (V.fromPreimage f) : _ ⟶ ⟨V.toFunctor, hV.1⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk V.ι : (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      from IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f V).flip) hf

/-- The restriction of a morphism of algebraic spaces over `S` above an open subspace of its
target is unramified exactly when the morphism itself is unramified on the inverse image of that
open subspace.

The inverse image is a fibre product, so the two restrictions differ by an isomorphism of the
source; the inclusion of the open subspace of the target is unramified, so one direction is
Stacks 03ZI and the other Stacks 06G6. -/
private theorem isUnramified_pullbackSnd_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {V : Subfunctor Y}
    (hV : IsOpenSubspace B S hS V) :
    IsUnramified B S hS (pullback.snd f V.ι) ↔
      IsUnramified B S hS ((V.preimage f).ι ≫ f) := by
  have hpre : IsOpenSubspace B S hS (V.preimage f) :=
    isOpenSubspace_preimage B S hS f V hY hX hV
  have hsq := (Subfunctor.isPullback_preimage f V).flip
  have hsnd : (hsq.isoIsPullback _ _ (IsPullback.of_hasPullback f V.ι)).hom ≫
      pullback.snd f V.ι = V.fromPreimage f :=
    IsPullback.isoIsPullback_hom_snd _ _ hsq (IsPullback.of_hasPullback f V.ι)
  have hiso := (holdsOnEveryEtaleChart_precomp_iso B S hS
    (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    (hsq.isoIsPullback _ _ (IsPullback.of_hasPullback f V.ι)) (pullback.snd f V.ι)).trans
      (Iff.of_eq (congrArg (IsUnramified B S hS) hsnd))
  refine hiso.trans ?_
  rw [show (V.preimage f).ι ≫ f = V.fromPreimage f ≫ V.ι from
    (Subfunctor.fromPreimage_ι V f).symm]
  exact ⟨fun h => isUnramified_comp B S hS hpre.1 hV.1 hY _ _ h
      (isUnramified_of_isOpenImmersion B S hS hV.1 hY hV.2),
    fun h => isUnramified_of_comp B S hS hpre.1 hV.1 hY _ _ h⟩

/-- The set of points of the target of a morphism of algebraic spaces over `S` lying in some
open subspace above which the morphism is unramified. -/
private def unramifiedBaseSet (f : X ⟶ Y) : Set (points B S hS Y) :=
  ⋃ V : {V : Subfunctor Y // IsOpenSubspace B S hS V ∧
      IsUnramified B S hS (pullback.snd f V.ι)},
    Set.range (pointsMap B S hS V.1.toFunctor V.1.ι)

/-- That set of points is open, being a union of point sets of open subspaces. -/
private theorem isOpen_unramifiedBaseSet (f : X ⟶ Y) :
    IsOpen (unramifiedBaseSet B S hS f) :=
  isOpen_iUnion fun V =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS V.1.ι V.2.1.2

/-- A morphism of algebraic spaces over `S` is unramified above the open subspace of its target
cut out by `AlgebraicGeometry.Space.unramifiedBaseSet`.

By the pointwise criterion of Stacks 03ZK it is enough to be unramified at each point of the
inverse image of that open subspace. Such a point maps to a point of some open subspace `V`
above which the morphism is unramified, and the inverse image of the part of the source above
`V` is then an open subspace of the inverse image carrying a point over it, on which the
morphism is unramified: it factors as a base change of an open immersion followed by the
restriction above `V`. -/
private theorem isUnramified_pullbackSnd_unramifiedBaseSet
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsUnramified B S hS (pullback.snd f
      (openSubspaceOfPoints B S hS Y (unramifiedBaseSet B S hS f)).ι) := by
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Y (unramifiedBaseSet B S hS f)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ (isOpen_unramifiedBaseSet B S hS f)
  have hWrange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := Y) (unramifiedBaseSet B S hS f)
  set W := openSubspaceOfPoints B S hS Y (unramifiedBaseSet B S hS f) with hWdef
  have hWpre : IsOpenSubspace B S hS (W.preimage f) :=
    isOpenSubspace_preimage B S hS f W hY hX hWopen
  rw [isUnramified_pullbackSnd_iff B S hS hX hY f hWopen]
  refine ((isUnramified_tfae B S hS hWpre.1 hY ((W.preimage f).ι ≫ f)).out 1 2).mpr fun x => ?_
  have himage : pointsMap B S hS (W.preimage f).toFunctor ((W.preimage f).ι ≫ f) x =
      pointsMap B S hS W.toFunctor W.ι
        (pointsMap B S hS (W.preimage f).toFunctor (W.fromPreimage f) x) := by
    rw [← Subfunctor.fromPreimage_ι, pointsMap_comp_apply]
  have hmem : pointsMap B S hS (W.preimage f).toFunctor ((W.preimage f).ι ≫ f) x ∈
      unramifiedBaseSet B S hS f := by
    rw [himage, ← hWrange]
    exact ⟨_, rfl⟩
  obtain ⟨V, hV⟩ := Set.mem_iUnion.mp hmem
  have hZopen : IsOpenSubspace B S hS (V.1.preimage f) :=
    isOpenSubspace_preimage B S hS f V.1 hY hX V.2.1
  have hOopen : IsOpenSubspace B S hS ((V.1.preimage f).preimage (W.preimage f).ι) :=
    isOpenSubspace_preimage B S hS (W.preimage f).ι (V.1.preimage f) hX hWpre.1 hZopen
  have hUnram : IsUnramified B S hS
      (((V.1.preimage f).preimage (W.preimage f).ι).ι ≫ ((W.preimage f).ι ≫ f)) := by
    rw [show ((V.1.preimage f).preimage (W.preimage f).ι).ι ≫ ((W.preimage f).ι ≫ f) =
        (V.1.preimage f).fromPreimage (W.preimage f).ι ≫ ((V.1.preimage f).ι ≫ f) by
      rw [← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc]]
    exact isUnramified_comp B S hS hOopen.1 hZopen.1 hY _ _
      (isUnramified_fromPreimage B S hS hWpre.1 hX (W.preimage f).ι hZopen
        (isUnramified_of_isOpenImmersion B S hS hWpre.1 hX hWpre.2))
      ((isUnramified_pullbackSnd_iff B S hS hX hY f V.2.1).mp V.2.2)
  have hx : x ∈ Set.range (pointsMap B S hS
      ((V.1.preimage f).preimage (W.preimage f).ι).toFunctor
      ((V.1.preimage f).preimage (W.preimage f).ι).ι) := by
    rw [range_pointsMap_preimage B S hS hX hWpre.1 (W.preimage f).ι (V.1.preimage f) hZopen,
      Set.mem_preimage, range_pointsMap_preimage B S hS hY hX f V.1 V.2.1, Set.mem_preimage,
      ← pointsMap_comp_apply]
    exact hV
  obtain ⟨x', hx'⟩ := hx
  exact ⟨(V.1.preimage f).preimage (W.preimage f).ι, hOopen, x', hx', hUnram⟩

/-- The supremum of the open subspaces of the target above which a morphism of algebraic spaces
over `S` is unramified is the open subspace cut out by
`AlgebraicGeometry.Space.unramifiedBaseSet`. -/
private theorem sSup_unramified_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    sSup {V : Subfunctor Y | IsOpenSubspace B S hS V ∧
        IsUnramified B S hS (pullback.snd f V.ι)} =
      openSubspaceOfPoints B S hS Y (unramifiedBaseSet B S hS f) := by
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Y (unramifiedBaseSet B S hS f)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ (isOpen_unramifiedBaseSet B S hS f)
  have hWrange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := Y) (unramifiedBaseSet B S hS f)
  refine le_antisymm (sSup_le fun V hV => ?_)
    (le_sSup ⟨hWopen, isUnramified_pullbackSnd_unramifiedBaseSet B S hS hX hY f⟩)
  refine le_of_range_pointsMap_ι_subset B S hS hWopen ?_
  rw [hWrange]
  exact fun x hx => Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hx⟩

end UnramifiedLocus

variable {Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hBs : IsAlgebraicSpace B S hS Bs}

/-! ### The identity section of a base change -/

/-- A base change of a group algebraic space locally of finite type is locally of finite
type. -/
private theorem isLocallyOfFiniteType_baseChange (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    IsLocallyOfFiniteType B S hS
      (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X.hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk G.obj.X.hom :
        (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)
      (ObjectProperty.homMk f : (⟨Bt, hBt⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)) hG

/-- The identity point of a base-changed group algebraic space projects to the identity point of
the group over the image of the point. -/
private theorem pointsMap_fst_one_baseChange (G : GroupAlgebraicSpace B S hS Bs hBs)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs)
    (b : points B S hS Bt) :
    pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f)
        (pointsMap B S hS Bt
          (MonObj.one (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left b) =
      pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left (pointsMap B S hS Bt f b) := by
  exact (pointsMap_comp_apply B S hS _ _ b).symm.trans <|
    (congrArg (fun k => pointsMap B S hS Bt k b)
      (one_baseChange_left_comp_fst B S hS G hBt f)).trans (pointsMap_comp_apply B S hS f _ b)

/-! ### The locally quasi-finite base locus -/

/-- Quasi-finiteness of a base-changed group algebraic space at the identity point over a point
of the new base is quasi-finiteness of the original one at the identity point over the image of
that point. -/
private theorem isQuasiFiniteAt_one_baseChange_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs)
    (b : points B S hS Bt) :
    IsQuasiFiniteAt B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X.hom
        (pointsMap B S hS Bt
          (MonObj.one (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left b) ↔
      IsQuasiFiniteAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left (pointsMap B S hS Bt f b)) := by
  have hlocus := setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk G.obj.X.hom :
        (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)
      (ObjectProperty.homMk f : (⟨Bt, hBt⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)) hG
  have hiff : ∀ x : points B S hS (pullback G.obj.X.hom f),
      IsQuasiFiniteAt B S hS (pullback.snd G.obj.X.hom f) x ↔
        IsQuasiFiniteAt B S hS G.obj.X.hom
          (pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f) x) :=
    fun x => Set.ext_iff.mp hlocus x
  have hpoint := pointsMap_fst_one_baseChange B S hS G hBt f b
  exact (hiff _).trans (Iff.of_eq (congrArg (IsQuasiFiniteAt B S hS G.obj.X.hom) hpoint))

/-- **Stacks 0DSI, over an arbitrary base change.** The base change of a group algebraic space
locally of finite type along a morphism of algebraic spaces is locally quasi-finite exactly when
the group is quasi-finite at the identity point over every point in the image of that
morphism. -/
private theorem isLocallyQuasiFinite_baseChange_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    IsLocallyQuasiFinite B S hS (pullback.snd G.obj.X.hom f) ↔
      ∀ b : points B S hS Bt, IsQuasiFiniteAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left
          (pointsMap B S hS Bt f b)) := by
  refine Iff.trans ?_
    (forall_congr' fun b => isQuasiFiniteAt_one_baseChange_iff B S hS G hG hBt f b)
  exact isLocallyQuasiFinite_iff_at_identity B S hS
    (GroupAlgebraicSpace.baseChange B S hS hBt f G)
    (isLocallyOfFiniteType_baseChange B S hS G hG hBt f)

/-- The set of points of the base over which a group algebraic space is quasi-finite at the
identity. -/
private def quasiFiniteAtOneSet (G : GroupAlgebraicSpace B S hS Bs hBs) :
    Set (points B S hS Bs) :=
  {b | IsQuasiFiniteAt B S hS G.obj.X.hom
    (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b)}

/-- The set of points of the base over which a group algebraic space is quasi-finite at the
identity is open: it is the inverse image of the quasi-finite locus of part (1) of Stacks 0ABM
under the continuous map on points induced by the unit. -/
private theorem isOpen_quasiFiniteAtOneSet (G : GroupAlgebraicSpace B S hS Bs hBs) :
    IsOpen (quasiFiniteAtOneSet B S hS G) :=
  (isOpen_setOf_isQuasiFiniteAt B S hS G.obj.X.hom).preimage
    (continuous_pointsMap B S hS (MonObj.one (X := G.obj.X)).left)

/-- **Stacks 0DSJ, the locally quasi-finite case.** The *locally quasi-finite base locus* of a
group algebraic space: the union of all open subspaces of the base over which it is locally
quasi-finite. -/
@[stacks 0DSJ "the locally quasi-finite base locus"]
def locallyQuasiFiniteBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs) : Subfunctor Bs :=
  sSup {U : Subfunctor Bs | IsOpenSubspace B S hS U ∧
    IsLocallyQuasiFinite B S hS (pullback.snd G.obj.X.hom U.ι)}

/-- **Stacks 0DSJ, maximality in the locally quasi-finite case.** Every open subspace of the
base over which a group algebraic space is locally quasi-finite is contained in its locally
quasi-finite base locus: it is a member of the family that locus is the supremum of. -/
@[stacks 0DSJ "maximality of the locally quasi-finite base locus"]
theorem le_locallyQuasiFiniteBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs)
    {U : Subfunctor Bs} (hU : IsOpenSubspace B S hS U)
    (hGU : IsLocallyQuasiFinite B S hS (pullback.snd G.obj.X.hom U.ι)) :
    U ≤ locallyQuasiFiniteBaseLocus B S hS G :=
  le_sSup ⟨hU, hGU⟩

/-- The locally quasi-finite base locus is the open subspace of Stacks 03BZ cut out by the set
of points of the base over which the group is quasi-finite at the identity.

Each member of the family the locus is the supremum of has its point set inside that set, by the
criterion of Stacks 0DSI for its own base change; and the open subspace cut out by that set is
itself a member of the family, by the same criterion. -/
private theorem locallyQuasiFiniteBaseLocus_eq (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    locallyQuasiFiniteBaseLocus B S hS G =
      openSubspaceOfPoints B S hS Bs (quasiFiniteAtOneSet B S hS G) := by
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Bs (quasiFiniteAtOneSet B S hS G)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_quasiFiniteAtOneSet B S hS G)
  have hWrange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := Bs) (quasiFiniteAtOneSet B S hS G)
  have hle : ∀ U : Subfunctor Bs, IsOpenSubspace B S hS U →
      IsLocallyQuasiFinite B S hS (pullback.snd G.obj.X.hom U.ι) →
      U ≤ openSubspaceOfPoints B S hS Bs (quasiFiniteAtOneSet B S hS G) := by
    intro U hU hGU
    refine le_of_range_pointsMap_ι_subset B S hS hWopen ?_
    rw [hWrange]
    rintro x ⟨b, rfl⟩
    exact (isLocallyQuasiFinite_baseChange_iff B S hS G hG hU.1 U.ι).mp hGU b
  refine le_antisymm (sSup_le fun U hU => hle U hU.1 hU.2) (le_sSup ⟨hWopen, ?_⟩)
  refine (isLocallyQuasiFinite_baseChange_iff B S hS G hG hWopen.1 _).mpr fun b => ?_
  exact hWrange.subset ⟨b, rfl⟩

/-- **Stacks 0DSJ, openness in the locally quasi-finite case.** The locally quasi-finite base
locus of a group algebraic space locally of finite type over its base is an open subspace. -/
@[stacks 0DSJ "openness of the locally quasi-finite base locus"]
theorem isOpenSubspace_locallyQuasiFiniteBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    IsOpenSubspace B S hS (locallyQuasiFiniteBaseLocus B S hS G) := by
  rw [locallyQuasiFiniteBaseLocus_eq B S hS G hG]
  exact isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_quasiFiniteAtOneSet B S hS G)

/-- **Stacks 0DSJ, the locally quasi-finite case.** A group algebraic space locally of finite
type over its base is locally quasi-finite over its locally quasi-finite base locus. -/
@[stacks 0DSJ "local quasi-finiteness over the locally quasi-finite base locus"]
theorem isLocallyQuasiFinite_locallyQuasiFiniteBaseLocus
    (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    IsLocallyQuasiFinite B S hS
      (pullback.snd G.obj.X.hom (locallyQuasiFiniteBaseLocus B S hS G).ι) := by
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Bs (quasiFiniteAtOneSet B S hS G)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_quasiFiniteAtOneSet B S hS G)
  rw [locallyQuasiFiniteBaseLocus_eq B S hS G hG]
  refine (isLocallyQuasiFinite_baseChange_iff B S hS G hG hWopen.1 _).mpr fun b => ?_
  exact (range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := Bs) (quasiFiniteAtOneSet B S hS G)).subset ⟨b, rfl⟩

/-! ### Compatibility with arbitrary base change -/

/-- **Stacks 0DSJ, base change in the locally quasi-finite case.** Forming the locally
quasi-finite base locus of a group algebraic space locally of finite type commutes with
arbitrary base change of algebraic spaces over `S`. -/
@[stacks 0DSJ "base change of the locally quasi-finite base locus"]
theorem locallyQuasiFiniteBaseLocus_preimage (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    locallyQuasiFiniteBaseLocus B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G) =
      (locallyQuasiFiniteBaseLocus B S hS G).preimage f := by
  have hG' := isLocallyOfFiniteType_baseChange B S hS G hG hBt f
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Bs (quasiFiniteAtOneSet B S hS G)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_quasiFiniteAtOneSet B S hS G)
  have hW'open : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS Bt
      (quasiFiniteAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G))) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBt _
      (isOpen_quasiFiniteAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G))
  have hsets : quasiFiniteAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G) =
      pointsMap B S hS Bt f ⁻¹' quasiFiniteAtOneSet B S hS G := by
    ext b
    exact isQuasiFiniteAt_one_baseChange_iff B S hS G hG hBt f b
  rw [locallyQuasiFiniteBaseLocus_eq B S hS _ hG',
    locallyQuasiFiniteBaseLocus_eq B S hS G hG]
  refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
    (isOpenSubspace_preimage B S hS f _ hBs hBt hWopen) ?_)
    (le_of_range_pointsMap_ι_subset B S hS hW'open ?_)
  · rw [range_pointsMap_preimage B S hS hBs hBt f _ hWopen,
      range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_openSubspaceOfPoints, hsets]
  · rw [range_pointsMap_preimage B S hS hBs hBt f _ hWopen,
      range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_openSubspaceOfPoints, hsets]

/-! ### The unramified base locus -/

/-- **Stacks 0DSJ, the unramified case.** The *unramified base locus* of a group algebraic
space: the union of all open subspaces of the base over which it is unramified. -/
@[stacks 0DSJ "the unramified base locus"]
def unramifiedBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs) : Subfunctor Bs :=
  sSup {U : Subfunctor Bs | IsOpenSubspace B S hS U ∧
    IsUnramified B S hS (pullback.snd G.obj.X.hom U.ι)}

/-- **Stacks 0DSJ, maximality in the unramified case.** Every open subspace of the base over
which a group algebraic space is unramified is contained in its unramified base locus: it is a
member of the family that locus is the supremum of. -/
@[stacks 0DSJ "maximality of the unramified base locus"]
theorem le_unramifiedBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs)
    {U : Subfunctor Bs} (hU : IsOpenSubspace B S hS U)
    (hGU : IsUnramified B S hS (pullback.snd G.obj.X.hom U.ι)) :
    U ≤ unramifiedBaseLocus B S hS G :=
  le_sSup ⟨hU, hGU⟩

/-- **Stacks 0DSJ, openness in the unramified case.** The unramified base locus of a group
algebraic space is an open subspace. -/
@[stacks 0DSJ "openness of the unramified base locus"]
theorem isOpenSubspace_unramifiedBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs) :
    IsOpenSubspace B S hS (unramifiedBaseLocus B S hS G) := by
  rw [unramifiedBaseLocus, sSup_unramified_eq B S hS G.property hBs G.obj.X.hom]
  exact isOpenSubspace_openSubspaceOfPoints B S hS hBs _
    (isOpen_unramifiedBaseSet B S hS G.obj.X.hom)

/-- **Stacks 0DSJ, the unramified case.** A group algebraic space is unramified over its
unramified base locus. -/
@[stacks 0DSJ "unramifiedness over the unramified base locus"]
theorem isUnramified_unramifiedBaseLocus (G : GroupAlgebraicSpace B S hS Bs hBs) :
    IsUnramified B S hS (pullback.snd G.obj.X.hom (unramifiedBaseLocus B S hS G).ι) := by
  rw [unramifiedBaseLocus, sSup_unramified_eq B S hS G.property hBs G.obj.X.hom]
  exact isUnramified_pullbackSnd_unramifiedBaseSet B S hS G.property hBs G.obj.X.hom

/-! ### Compatibility of the unramified base locus with arbitrary base change -/

/-- Unramifiedness of a base-changed group algebraic space at the identity point over a point of
the new base is unramifiedness of the original one at the identity point over the image of that
point.

The unit of the base change projects to the unit (`one_baseChange_left_comp_fst`), so the two
points correspond under the projection, and the unramified locus commutes with base change by
part (2) of Stacks 05W2. -/
private theorem isUnramifiedAt_one_baseChange_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs)
    (b : points B S hS Bt) :
    IsUnramifiedAt B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X.hom
        (pointsMap B S hS Bt
          (MonObj.one (X := (GroupAlgebraicSpace.baseChange B S hS hBt f G).obj.X)).left b) ↔
      IsUnramifiedAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left (pointsMap B S hS Bt f b)) := by
  have hlocus := setOf_isUnramifiedAt_eq_preimage_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk G.obj.X.hom :
        (⟨G.obj.X.left, G.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)
      (ObjectProperty.homMk f : (⟨Bt, hBt⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Bs, hBs⟩)) hG
  have hiff : ∀ x : points B S hS (pullback G.obj.X.hom f),
      IsUnramifiedAt B S hS (pullback.snd G.obj.X.hom f) x ↔
        IsUnramifiedAt B S hS G.obj.X.hom
          (pointsMap B S hS (pullback G.obj.X.hom f) (pullback.fst G.obj.X.hom f) x) :=
    fun x => Set.ext_iff.mp hlocus x
  have hpoint := pointsMap_fst_one_baseChange B S hS G hBt f b
  exact (hiff _).trans (Iff.of_eq (congrArg (IsUnramifiedAt B S hS G.obj.X.hom) hpoint))

/-- **Stacks 0DSI, over an arbitrary base change.** The base change of a group algebraic space
locally of finite type along a morphism of algebraic spaces is unramified exactly when the group
is unramified at the identity point over every point in the image of that morphism. -/
private theorem isUnramified_baseChange_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    IsUnramified B S hS (pullback.snd G.obj.X.hom f) ↔
      ∀ b : points B S hS Bt, IsUnramifiedAt B S hS G.obj.X.hom
        (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left
          (pointsMap B S hS Bt f b)) := by
  refine Iff.trans ?_
    (forall_congr' fun b => isUnramifiedAt_one_baseChange_iff B S hS G hG hBt f b)
  exact isUnramified_iff_at_identity B S hS
    (GroupAlgebraicSpace.baseChange B S hS hBt f G)
    (isLocallyOfFiniteType_baseChange B S hS G hG hBt f)

/-- The set of points of the base over which a group algebraic space is unramified at the
identity. -/
private def unramifiedAtOneSet (G : GroupAlgebraicSpace B S hS Bs hBs) :
    Set (points B S hS Bs) :=
  {b | IsUnramifiedAt B S hS G.obj.X.hom
    (pointsMap B S hS Bs (MonObj.one (X := G.obj.X)).left b)}

/-- The set of points of the base over which a group algebraic space is unramified at the
identity is open: it is the inverse image of the unramified locus of part (1) of Stacks 05W2
under the continuous map on points induced by the unit. -/
private theorem isOpen_unramifiedAtOneSet (G : GroupAlgebraicSpace B S hS Bs hBs) :
    IsOpen (unramifiedAtOneSet B S hS G) :=
  (isOpen_setOf_isUnramifiedAt B S hS G.obj.X.hom).preimage
    (continuous_pointsMap B S hS (MonObj.one (X := G.obj.X)).left)

/-- The unramified base locus is the open subspace of Stacks 03BZ cut out by the set of points of
the base over which the group is unramified at the identity.

Each member of the family the locus is the supremum of has its point set inside that set, by the
criterion of Stacks 0DSI for its own base change; and the open subspace cut out by that set is
itself a member of the family, by the same criterion. -/
private theorem unramifiedBaseLocus_eq (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) :
    unramifiedBaseLocus B S hS G =
      openSubspaceOfPoints B S hS Bs (unramifiedAtOneSet B S hS G) := by
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Bs (unramifiedAtOneSet B S hS G)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_unramifiedAtOneSet B S hS G)
  have hWrange := range_pointsMap_ι_openSubspaceOfPoints B S hS
    (F := Bs) (unramifiedAtOneSet B S hS G)
  have hle : ∀ U : Subfunctor Bs, IsOpenSubspace B S hS U →
      IsUnramified B S hS (pullback.snd G.obj.X.hom U.ι) →
      U ≤ openSubspaceOfPoints B S hS Bs (unramifiedAtOneSet B S hS G) := by
    intro U hU hGU
    refine le_of_range_pointsMap_ι_subset B S hS hWopen ?_
    rw [hWrange]
    rintro x ⟨b, rfl⟩
    exact (isUnramified_baseChange_iff B S hS G hG hU.1 U.ι).mp hGU b
  refine le_antisymm (sSup_le fun U hU => hle U hU.1 hU.2) (le_sSup ⟨hWopen, ?_⟩)
  refine (isUnramified_baseChange_iff B S hS G hG hWopen.1 _).mpr fun b => ?_
  exact hWrange.subset ⟨b, rfl⟩

/-- **Stacks 0DSJ, base change in the unramified case.** Forming the unramified base locus of a
group algebraic space locally of finite type commutes with arbitrary base change of algebraic
spaces over `S`. -/
@[stacks 0DSJ "base change of the unramified base locus"]
theorem unramifiedBaseLocus_preimage (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom)
    {Bt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hBt : IsAlgebraicSpace B S hS Bt) (f : Bt ⟶ Bs) :
    unramifiedBaseLocus B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G) =
      (unramifiedBaseLocus B S hS G).preimage f := by
  have hG' := isLocallyOfFiniteType_baseChange B S hS G hG hBt f
  have hWopen : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Bs (unramifiedAtOneSet B S hS G)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBs _ (isOpen_unramifiedAtOneSet B S hS G)
  have hW'open : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS Bt
      (unramifiedAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G))) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hBt _
      (isOpen_unramifiedAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G))
  have hsets : unramifiedAtOneSet B S hS (GroupAlgebraicSpace.baseChange B S hS hBt f G) =
      pointsMap B S hS Bt f ⁻¹' unramifiedAtOneSet B S hS G := by
    ext b
    exact isUnramifiedAt_one_baseChange_iff B S hS G hG hBt f b
  rw [unramifiedBaseLocus_eq B S hS _ hG', unramifiedBaseLocus_eq B S hS G hG]
  refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
    (isOpenSubspace_preimage B S hS f _ hBs hBt hWopen) ?_)
    (le_of_range_pointsMap_ι_subset B S hS hW'open ?_)
  · rw [range_pointsMap_preimage B S hS hBs hBt f _ hWopen,
      range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_openSubspaceOfPoints, hsets]
  · rw [range_pointsMap_preimage B S hS hBs hBt f _ hWopen,
      range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_openSubspaceOfPoints, hsets]

/-! ### Membership in the base loci -/

/-- **A section of the base lies in the locally quasi-finite base locus exactly when the group is
locally quasi-finite over it.** For a group algebraic space `G` locally of finite type over `Bs`
and a section `s` of `Bs` over an object `X` of the site, `s` lies in the locally quasi-finite base
locus exactly when the base change of `G` along the corresponding morphism `h_X ⟶ Bs` is locally
quasi-finite. -/
theorem mem_locallyQuasiFiniteBaseLocus_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) {X : (BigFppfOver B S hS)ᵒᵖ}
    (s : Bs.obj X) :
    s ∈ (locallyQuasiFiniteBaseLocus B S hS G).obj X ↔
      IsLocallyQuasiFinite B S hS (pullback.snd G.obj.X.hom (yonedaEquiv.symm s)) := by
  rw [locallyQuasiFiniteBaseLocus_eq B S hS G hG, mem_openSubspaceOfPoints_iff,
    isLocallyQuasiFinite_baseChange_iff B S hS G hG (isAlgebraicSpace_yoneda B S hS X.unop),
    Set.range_subset_iff]
  rfl

/-- **A section of the base lies in the unramified base locus exactly when the group is unramified
over it.** For a group algebraic space `G` locally of finite type over `Bs` and a section `s` of
`Bs` over an object `X` of the site, `s` lies in the unramified base locus exactly when the base
change of `G` along the corresponding morphism `h_X ⟶ Bs` is unramified. -/
theorem mem_unramifiedBaseLocus_iff (G : GroupAlgebraicSpace B S hS Bs hBs)
    (hG : IsLocallyOfFiniteType B S hS G.obj.X.hom) {X : (BigFppfOver B S hS)ᵒᵖ}
    (s : Bs.obj X) :
    s ∈ (unramifiedBaseLocus B S hS G).obj X ↔
      IsUnramified B S hS (pullback.snd G.obj.X.hom (yonedaEquiv.symm s)) := by
  rw [unramifiedBaseLocus_eq B S hS G hG, mem_openSubspaceOfPoints_iff,
    isUnramified_baseChange_iff B S hS G hG (isAlgebraicSpace_yoneda B S hS X.unop),
    Set.range_subset_iff]
  rfl

end AlgebraicGeometry.Space

end
