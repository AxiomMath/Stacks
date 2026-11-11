module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantAffineNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# The schematic locus of an algebraic space with a finite étale cover

If an algebraic space `F` over a scheme `S` admits a finite, étale, surjective morphism from an
object of the big fppf site whose underlying scheme is quasi-separated, then every point of `F`
of codimension zero lies in an open subspace of `F` which is a scheme, and the schematic locus
of Tag 03JH is therefore dense.

The open subspace is built as the source prescribes. The relation `R = U ×_F U` has finite
étale projections, so the fibre of `|U| → |F|` above a codimension-zero point is a finite set of
generic points of irreducible components of `U`; quasi-separatedness puts that fibre inside an
affine open, which may be enlarged to an `R`-invariant affine open `W`. The subspace of `F` cut
out by `W` is then open by Tag 07TW, its relation is the restriction of `R` to `W` and is affine
with finite locally free projections, and so the subspace is represented by the spectrum of the
ring of invariant functions, by Tag 03BM.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isAffine_atlas_of_isFiniteLocallyFree_relation`:
  an algebraic space with an affine surjective étale atlas whose relation is affine with finite
  locally free projections is represented by a scheme.
* `AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_invariantSubspace`: the subspace
  cut out by an invariant affine open of a finite étale chart is an open subspace and is
  representable.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_mem_range`: a codimension-zero
  point of an algebraic space with a finite étale cover by a quasi-separated scheme lies in a
  representable open subspace.
* `AlgebraicGeometry.Space.codimensionZero_mem_schematicLocus` and
  `AlgebraicGeometry.Space.denseRange_schematicLocus`: the two assertions of Tag 0BAS.

## Implementation notes

The source of Tag 0BAS deduces the quotient `W/R_W` from Tags 03BC, 03BM and 02WU. Here the
quotient is not formed: the subspace of `F` cut out by `W` is already available as
`AlgebraicGeometry.Space.invariantSubspace`, with the base change of the chart along it
identified with the functor of points of `W` by
`AlgebraicGeometry.Space.exists_isPullback_yoneda_presentation`, which is the content of
Tag 02WU for this subspace. What remains is to recognise that subspace as a scheme, and that is
Tag 03BM in the shape
`AlgebraicGeometry.Space.exists_quotient_of_isFiniteLocallyFree_relation`.

That the relation of the subspace is finite over `W` is where the invariance of `W` is used, and
it is used only through the cartesian square above: the atlas of the subspace is the base change
of the finite morphism `q` along the inclusion of the subspace, so it is finite, and hence so is
its own kernel pair.

Openness of the subspace is Tag 07TW, whose three statements are proved in the library in
`StacksFrontier/AlgebraicGeometry/Descent/ImmersionEtaleDescent.lean`. Only the open-immersion
case is used here, and for it the effective descent of open immersions,
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`, suffices.

## References

* [Stacks Project, Tag 0BAS](https://stacks.math.columbia.edu/tag/0BAS)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An algebraic space over `S` with a surjective étale atlas whose source is affine and whose
relation is affine with finite locally free projections is represented by a scheme.

This is Tag 03BM read through the atlas: the spectrum of the ring of invariant functions of the
relation receives a surjective finite locally free morphism from the atlas with the same kernel
pair, so it represents the space. -/
theorem isRepresentable_of_isAffine_atlas_of_isFiniteLocallyFree_relation
    (hF : IsAlgebraicSpace B S hS F) {R : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (t s : R ⟶ U) (hR : IsPullback (yoneda.map t) (yoneda.map s) q q)
    (hqsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R))
    (hflfs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (hflft : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t)) :
    F.IsRepresentable := by
  classical
  have _ : IsAffine ((Over.post B.inclusion).obj U).left := hUaff
  have _ : IsAffine ((Over.post B.inclusion).obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map s).left := hflfs
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map t).left := hflft
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) := isEquivalenceRelation_of_isPullback B S hS q t s hR
  obtain ⟨A, _, g, π, hsize, hflf, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hAcontains : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize U.left.2
  obtain ⟨m, e, -, -⟩ :=
    exists_iso_yoneda_of_isPullback B S hS hF q t s hR hqsurj hqetale
      (U' := Over.mk (⟨g⟩ : B.obj hAcontains ⟶ B.obj hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  exact Functor.IsRepresentable.mk' e.symm

/-- If a morphism to an algebraic space is representably finite and étale, then each projection
of a pullback square of it with itself is finite locally free. -/
private theorem isFiniteLocallyFree_map_of_isPullback
    {q : yoneda.obj U ⟶ F} {R : BigFppfOver B S hS} {t s : R ⟶ U}
    (hqfinite : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) q q) :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) := by
  have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map s) :=
    hqfinite.property q _ _ hR
  have : Etale ((BigFppfOver.toScheme B S hS).map s) := hqetale.property q _ _ hR
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    _).mpr ⟨inferInstance, inferInstance, inferInstance⟩

/-- The subspace of an algebraic space cut out by an affine open of a finite étale chart which
is invariant under the relation of that chart is an open subspace and is represented by a
scheme.

Openness is Tag 07TW for open immersions, whose descent hypothesis is discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`.
Representability is Tag 03BM: the base change of the chart along the inclusion of the subspace
is the functor of points of the affine open, so it is an affine surjective étale atlas of the
subspace, and it is finite, so its kernel pair is affine with finite locally free
projections. -/
theorem isOpenSubspace_and_isRepresentable_invariantSubspace
    (hF : IsAlgebraicSpace B S hS F) (q : yoneda.obj U ⟶ F)
    (hqsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqfinite : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) (hWaff : IsAffineOpen W)
    (hWinv : IsInvariantSubscheme B S hS hqsurj (Subobject.mk W.ι)) :
    IsOpenSubspace B S hS (invariantSubspace B S hS q (Subobject.mk W.ι)) ∧
      (invariantSubspace B S hS q (Subobject.mk W.ι)).toFunctor.IsRepresentable := by
  classical
  have hZopen : _root_.AlgebraicGeometry.IsOpenImmersion (Subobject.mk W.ι).arrow :=
    _root_.AlgebraicGeometry.isOpenImmersion_subobjectMk_opens_arrow W
  have hZimm : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk W.ι).arrow := inferInstance
  obtain ⟨hGalg, hGι⟩ := isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hqsurj hqetale
    (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS)
    hF (Subobject.mk W.ι) hZimm hZopen hWinv
  refine ⟨⟨hGalg, hGι⟩, ?_⟩
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS (Subobject.mk W.ι) hZimm
  obtain ⟨k, hksq⟩ :=
    exists_isPullback_yoneda_presentation B S hS hqsurj (Subobject.mk W.ι) hWinv i e hei
  have hksurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) k :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hksq.flip hqsurj
  have hketale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) k :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hksq.flip hqetale
  have hkfinite : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) k :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hksq.flip hqfinite
  have hA : IsPullback (yoneda.map (hksurj.rep.fst' k)) (yoneda.map (hksurj.rep.snd k)) k k :=
    hksurj.rep.isPullback' k
  have hflfs := isFiniteLocallyFree_map_of_isPullback B S hS hkfinite hketale hA
  have hflft := isFiniteLocallyFree_map_of_isPullback B S hS hkfinite hketale hA.flip
  have hWaff' : IsAffine (W : Scheme.{u}) := hWaff
  have hZaff : IsAffine ((Subobject.mk W.ι : Scheme.{u})) :=
    IsAffine.of_isIso (Subobject.underlyingIso W.ι).hom
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := IsAffine.of_isIso e.hom
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hksurj.rep.pullback k)) :=
    isAffine_of_isFinite ((BigFppfOver.toScheme B S hS).map (hksurj.rep.snd k))
      (hkfinite.property k _ _ hA) hVaff
  exact isRepresentable_of_isAffine_atlas_of_isFiniteLocallyFree_relation B S hS hGalg k
    (hksurj.rep.fst' k) (hksurj.rep.snd k) hA hksurj hketale hVaff hAaff hflfs hflft

/-- A point of codimension zero of an algebraic space over `S` admitting a finite, étale,
surjective morphism from an object of the site with quasi-separated underlying scheme lies in an
open subspace which is a scheme.

This is the geometric content of Tag 0BAS. -/
theorem exists_isRepresentable_isOpenSubspace_mem_range
    (hF : IsAlgebraicSpace B S hS F) (q : yoneda.obj U ⟶ F)
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hqfinite : IsFinite B S hS q) (hqetale : IsEtale B S hS q)
    (hqsurj : IsSurjective B S hS q) (x : points B S hS F)
    (hx : localRingDimension B S hS x = 0) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  have hqsurj' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q :=
    (surjective_iff_surjective_pointsMap B S hS F hF U q).2 hqsurj
  have hqetale' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q :=
    presheaf_etale_of_isEtale B S hS hqetale
  have hqfinite' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q :=
    ((isFinite_iff_representable B S hS q
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF).mp hqfinite).2
  have hR : IsPullback (yoneda.map (atlasRelationTarget B S hS hqsurj'))
      (yoneda.map (atlasRelationSource B S hS hqsurj')) q q := hqsurj'.rep.isPullback' q
  have hsE' : Etale ((Over.post B.inclusion).map
      (atlasRelationSource B S hS hqsurj')).left :=
    hqetale'.property q _ _ hR
  have htE' : Etale ((Over.post B.inclusion).map
      (atlasRelationTarget B S hS hqsurj')).left :=
    hqetale'.property q _ _ hR.flip
  have hflfs : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map
      (atlasRelationSource B S hS hqsurj')).left :=
    isFiniteLocallyFree_map_of_isPullback B S hS hqfinite' hqetale' hR
  have hflft : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map
      (atlasRelationTarget B S hS hqsurj')).left :=
    isFiniteLocallyFree_map_of_isPullback B S hS hqfinite' hqetale' hR.flip
  have hequiv : IsEquivalenceRelation
      ((Over.post B.inclusion).map (atlasRelationTarget B S hS hqsurj'))
      ((Over.post B.inclusion).map (atlasRelationSource B S hS hqsurj')) :=
    isEquivalenceRelation_of_isPullback B S hS q _ _ hR
  have hle : MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS) := by
    intro A A' f hf
    have _ : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map f) := hf
    change QuasiCompact ((BigFppfOver.toScheme B S hS).map f)
    infer_instance
  have hqcfst : IsQuasiCompact B S hS (pullback.fst q q) :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (MorphismProperty.relative_monotone hle (pullback.fst q q)
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
          (IsPullback.of_hasPullback q q).flip hqfinite'))
  have hqcsnd : IsQuasiCompact B S hS (pullback.snd q q) :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (MorphismProperty.relative_monotone hle (pullback.snd q q)
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
          (IsPullback.of_hasPullback q q) hqfinite'))
  obtain ⟨a₀, ha₀⟩ := hqsurj x
  obtain ⟨W₀, hW₀aff, hW₀mem⟩ :=
    exists_isAffineOpen_fiber_subset B S hS hF U q hqetale hqcfst hqcsnd hUqs hx
  have horbit : ∀ r : (BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hqsurj'),
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hqsurj')).base r =
          pointsToScheme B S hS U a₀ →
        ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hqsurj')).base r ∈ W₀ := by
    intro r hr
    obtain ⟨b, hb⟩ := surjective_pointsToScheme B S hS (atlasRelation B S hS hqsurj') r
    have hbs : pointsMap B S hS (yoneda.obj (atlasRelation B S hS hqsurj'))
        (yoneda.map (atlasRelationSource B S hS hqsurj')) b = a₀ := by
      refine injective_pointsToScheme B S hS U ?_
      rwa [pointsToScheme_pointsMap, hb]
    have hbt : pointsMap B S hS (yoneda.obj U) q
        (pointsMap B S hS (yoneda.obj (atlasRelation B S hS hqsurj'))
          (yoneda.map (atlasRelationTarget B S hS hqsurj')) b) = x := by
      rw [pointsMap_eq_of_isPullback_relation B S hS q _ _ hR b, hbs, ha₀]
    have hmem := hW₀mem _ hbt
    rwa [pointsToScheme_pointsMap, hb] at hmem
  obtain ⟨W, hWaff, hWmem, hWinvset⟩ :
      ∃ W : ((BigFppfOver.toScheme B S hS).obj U).Opens, IsAffineOpen W ∧
        pointsToScheme B S hS U a₀ ∈ W ∧
        ∀ r : (BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hqsurj'),
          (((BigFppfOver.toScheme B S hS).map
              (atlasRelationSource B S hS hqsurj')).base r ∈ W ↔
            ((BigFppfOver.toScheme B S hS).map
              (atlasRelationTarget B S hS hqsurj')).base r ∈ W) :=
    exists_isAffineOpen_invariant_of_isFiniteLocallyFree
      ((Over.post B.inclusion).map (atlasRelationTarget B S hS hqsurj'))
      ((Over.post B.inclusion).map (atlasRelationSource B S hS hqsurj'))
      (pointsToScheme B S hS U a₀) W₀ hW₀aff horbit
  have hWinv : IsInvariantSubscheme B S hS hqsurj' (Subobject.mk W.ι) := by
    have hopens : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hqsurj') ⁻¹ᵁ W =
        (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hqsurj') ⁻¹ᵁ W := by
      ext r
      exact (hWinvset r).symm
    change (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
        (atlasRelationTarget B S hS hqsurj'))).obj (Subobject.mk W.ι) =
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
        (atlasRelationSource B S hS hqsurj'))).obj (Subobject.mk W.ι)
    rw [subobjectPullback_mk_opens_ι, subobjectPullback_mk_opens_ι, hopens]
  obtain ⟨hGopen, hGrep⟩ := isOpenSubspace_and_isRepresentable_invariantSubspace B S hS hF q
    hqsurj' hqetale' hqfinite' W hWaff hWinv
  refine ⟨invariantSubspace B S hS q (Subobject.mk W.ι), hGopen, hGrep, ?_⟩
  have hZimm : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk W.ι).arrow := by
    have := _root_.AlgebraicGeometry.isOpenImmersion_subobjectMk_opens_arrow W
    infer_instance
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS (Subobject.mk W.ι) hZimm
  obtain ⟨k, hksq⟩ :=
    exists_isPullback_yoneda_presentation B S hS hqsurj' (Subobject.mk W.ι) hWinv i e hei
  have harrow : (Subobject.underlyingIso W.ι).symm.hom ≫ (Subobject.mk W.ι).arrow = W.ι :=
    Subobject.underlyingIso_arrow _
  have hfac : ((Subobject.underlyingIso W.ι).symm.hom ≫ e.inv) ≫
      (BigFppfOver.toScheme B S hS).map i = W.ι := by
    rw [← hei, Category.assoc, e.inv_hom_id_assoc, harrow]
  obtain ⟨a', ha'⟩ : ∃ a' : points B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map i) a' = a₀ := by
    obtain ⟨a', ha'⟩ := surjective_pointsToScheme B S hS V
      (((Subobject.underlyingIso W.ι).symm.hom ≫ e.inv)
        ⟨pointsToScheme B S hS U a₀, hWmem⟩)
    refine ⟨a', injective_pointsToScheme B S hS U ?_⟩
    rw [pointsToScheme_pointsMap, ha']
    change (((Subobject.underlyingIso W.ι).symm.hom ≫ e.inv) ≫
        (BigFppfOver.toScheme B S hS).map i)
      ⟨pointsToScheme B S hS U a₀, hWmem⟩ = pointsToScheme B S hS U a₀
    rw [hfac]
    rfl
  refine ⟨pointsMap B S hS (yoneda.obj V) k a', ?_⟩
  rw [← pointsMap_comp_apply, hksq.w, pointsMap_comp_apply, ha', ha₀]

variable (F)

/-- **Stacks 0BAS, codimension-zero points.** If an algebraic space over `S` admits a finite,
étale, surjective morphism from an object of the site whose underlying scheme is
quasi-separated, then every point of codimension zero lies in the schematic locus of
Tag 03JH. -/
@[stacks 0BAS "codimension-zero points"]
theorem codimensionZero_mem_schematicLocus (hF : IsAlgebraicSpace B S hS F)
    (hcover : ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F),
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsFinite B S hS q ∧ IsEtale B S hS q ∧ IsSurjective B S hS q)
    (x : points B S hS F) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  obtain ⟨U, q, hUqs, hqfinite, hqetale, hqsurj⟩ := hcover
  obtain ⟨G, hGopen, hGrep, hxG⟩ :=
    exists_isRepresentable_isOpenSubspace_mem_range B S hS hF q hUqs hqfinite hqetale hqsurj x hx
  exact range_pointsMap_ι_le_schematicLocus B S hS G hGopen hGrep hxG

/-- **Stacks 0BAS, density.** If an algebraic space over `S` admits a finite, étale, surjective
morphism from an object of the site whose underlying scheme is quasi-separated, then the
schematic locus of Tag 03JH is dense in its space of points. -/
@[stacks 0BAS "density"]
theorem denseRange_schematicLocus (hF : IsAlgebraicSpace B S hS F)
    (hcover : ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F),
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsFinite B S hS q ∧ IsEtale B S hS q ∧ IsSurjective B S hS q) :
    DenseRange (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) :=
  (codimensionZeroPoints_dense B S hS hF).mono fun x hx =>
    codimensionZero_mem_schematicLocus B S hS F hF hcover x hx

end AlgebraicGeometry.Space

end
