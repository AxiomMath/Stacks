module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The open locus over which a morphism factors through an open immersion

Let `i : X ⟶ Y` be an open immersion of algebraic spaces over `S` and let `r : A ⟶ Y` be a
morphism from an algebraic space carrying a *closed* morphism `q : A ⟶ T`. The set of points of
`A` at which `r` does not land in `X` is closed, so its image in `T` is closed and its
complement is an open subspace `W` of `T`. For a morphism `g : T' ⟶ T` the base change
`A ×_T T' ⟶ Y` factors through `X` exactly when `g` factors through `W`: the first condition is
a condition on the points of `A ×_T T'`, which by Stacks 03H4 are the pairs of a point of `A`
and a point of `T'` agreeing in `T`.

This is the openness statement behind the Hilbert functor of an open subspace: `A` is the closed
subspace carried by a family, `q` its (proper, hence closed) structure morphism to the test
scheme, and `W` the locus over which the family is a family in the open subspace.

Also here are the two ingredients the argument needs about open immersions with an arbitrary
source: the point set of the range of a monomorphism is the image of its point map, and a
morphism factors through an open immersion exactly when its points do.

## Main definitions

* `AlgebraicGeometry.Space.factorizationLocus` is the subfunctor `W` of `T`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_factorizationLocus`: it is an open subspace.
* `AlgebraicGeometry.Space.factorsThrough_factorizationLocus_iff`: its universal property.
* `AlgebraicGeometry.Space.factorsThrough_isOpenImmersion_iff_points`: factoring through an open
  immersion is a condition on points, which is Stacks 03IE read for an open immersion rather
  than for an open subspace.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isOpenSubspace_range_preimage`: a monomorphism of
  presheaves whose range has open inverse image in every scheme-valued point of the target is an
  open immersion.

## Implementation notes

The locus is `AlgebraicGeometry.Space.openSubspaceOfPoints` of an explicit set of points, so it
is a construction and not a choice of a subfunctor from an existence statement; its point set is
computed by part (1) of Stacks 03BZ.

`AlgebraicGeometry.Space.pointTopology` is a local instance throughout, and the topological
closedness of a set of points is written `_root_.IsClosed`, as elsewhere in this directory.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions with an arbitrary source -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Precomposing with an isomorphism does not change the image of the point map. -/
theorem range_pointsMap_comp_isIso {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ F')
    [IsIso e] (f : F' ⟶ G) :
    Set.range (pointsMap B S hS F (e ≫ f)) = Set.range (pointsMap B S hS F' f) := by
  rw [pointsMap_comp, Set.range_comp, (pointsMap_surjective_of_isIso B S hS e).range_eq,
    Set.image_univ]

/-- Precomposing an open immersion with an isomorphism gives an open immersion. -/
private theorem isOpenImmersion_comp_of_isIso {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : P ⟶ Q) [IsIso e] {f : Q ⟶ R} (hf : IsOpenImmersion B S hS f) :
    IsOpenImmersion B S hS (e ≫ f) :=
  MorphismProperty.RespectsIso.precomp _ e f hf

/-- **Stacks 03IE for an open immersion.** A morphism of algebraic spaces over `S` factors
through an open immersion exactly when the image of its point set is contained in the image of
the point set of that open immersion. -/
theorem factorsThrough_isOpenImmersion_iff_points {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (i : F ⟶ G) (hi : IsOpenImmersion B S hS i) (f : H ⟶ G) :
    (∃ g : H ⟶ F, g ≫ i = f) ↔
      Set.range (pointsMap B S hS H f) ⊆ Set.range (pointsMap B S hS F i) := by
  have _ : Mono i := mono_of_presheaf_isOpenImmersion hi
  have hinvι : inv (Subfunctor.toRange i) ≫ i = (Subfunctor.range i).ι := by
    apply (cancel_epi (Subfunctor.toRange i)).1
    simp
  -- The range of an open immersion with algebraic source is an open subspace. This is
  -- `AlgebraicGeometry.Space.isOpenSubspace_range_of_isAlgebraicSpace` of
  -- `StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae`; it is reproved
  -- here rather than imported because that module's import cone declares
  -- `AlgebraicGeometry.Space.pointsMap_surjective_of_isIso` a second time, with a different
  -- signature, which shadows the one this file uses.
  have hI : IsOpenSubspace B S hS (Subfunctor.range i) := by
    refine ⟨hF.of_iso (asIso (Subfunctor.toRange i)), ?_⟩
    rw [← hinvι]
    exact isOpenImmersion_comp_of_isIso B S hS _ hi
  rw [← range_pointsMap_ι_range B S hS i,
    ← factorsThrough_openSubspace_iff_points B S hS hG hH (Subfunctor.range i) hI f]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g ≫ Subfunctor.toRange i, by simpa using hg⟩
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ inv (Subfunctor.toRange i), ?_⟩
    simpa only [Category.assoc, hinvι] using hg

/-- A monomorphism of presheaves on the big fppf site of `S` whose range has open inverse image
under every scheme-valued point of its target is an open immersion.

Each base change of the morphism to a scheme-valued point of the target has that inverse image
as its range, and is a monomorphism, so it is the inclusion of an open subspace read through the
comparison with its range. -/
theorem isOpenImmersion_of_isOpenSubspace_range_preimage (f : F ⟶ G) [Mono f]
    (h : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ G),
      IsOpenSubspace B S hS ((Subfunctor.range f).preimage g)) :
    IsOpenImmersion B S hS f := by
  apply MorphismProperty.presheaf_of_forall_presheaf_pullback_snd
  intro T g
  have _ : Mono (pullback.snd f g) := pullback.snd_of_mono
  have hι : IsOpenImmersion B S hS (Subfunctor.range (pullback.snd f g)).ι := by
    rw [Subfunctor.range_eq_preimage_of_isPullback (IsPullback.of_hasPullback f g).flip]
    exact (h T g).2
  simpa only [Subfunctor.toRange_ι] using
    isOpenImmersion_comp_of_isIso B S hS (Subfunctor.toRange (pullback.snd f g)) hι

/-! ### The factorization locus -/

variable {X Y A T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The locus in `T` over which a morphism `r : A ⟶ Y` factors through an open immersion
`i : X ⟶ Y`, for a morphism `q : A ⟶ T`: the subfunctor of `T` cut out by the complement of the
image under `q` of the set of points of `A` at which `r` does not land in `X`. -/
def factorizationLocus (i : X ⟶ Y) (r : A ⟶ Y) (q : A ⟶ T) : Subfunctor T :=
  openSubspaceOfPoints B S hS T
    (pointsMap B S hS A q ''
      (pointsMap B S hS A r ⁻¹' (Set.range (pointsMap B S hS X i))ᶜ))ᶜ

/-- The set of points of `A` at which `r` does not land in the open immersion `i` is closed. -/
theorem isClosed_notFactoring {i : X ⟶ Y}
    (hi : IsOpenImmersion B S hS i) (r : A ⟶ Y) :
    _root_.IsClosed (pointsMap B S hS A r ⁻¹' (Set.range (pointsMap B S hS X i))ᶜ) :=
  (isOpen_range_pointsMap_of_isOpenImmersion B S hS i hi).isClosed_compl.preimage
    (continuous_pointsMap B S hS r)

/-- The point set of the factorization locus is the complement of the image of the set of points
at which `r` does not land in `X`. -/
theorem range_pointsMap_ι_factorizationLocus (i : X ⟶ Y) (r : A ⟶ Y) (q : A ⟶ T) :
    Set.range (pointsMap B S hS (factorizationLocus B S hS i r q).toFunctor
      (factorizationLocus B S hS i r q).ι) =
      (pointsMap B S hS A q ''
        (pointsMap B S hS A r ⁻¹' (Set.range (pointsMap B S hS X i))ᶜ))ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The factorization locus is an open subspace of `T`: the set of points at which `r` does not
land in `X` is closed, hence so is its image under the closed morphism `q`. -/
theorem isOpenSubspace_factorizationLocus
    (hT : IsAlgebraicSpace B S hS T) {i : X ⟶ Y} (hi : IsOpenImmersion B S hS i)
    (r : A ⟶ Y) {q : A ⟶ T} (hq : IsClosedMorphism B S hS q) :
    IsOpenSubspace B S hS (factorizationLocus B S hS i r q) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hT _
    (hq _ (isClosed_notFactoring B S hS hi r)).isOpen_compl

/-- **The universal property of the factorization locus.** A morphism `g : T' ⟶ T` factors
through the factorization locus exactly when the base change of `r` along `g` factors through
the open immersion `i`.

Both sides are conditions on points: the left-hand side says that no point of `A` lying over a
point in the image of `g` fails to land in `X`, and the right-hand side says the same about the
points of the fibre product `A ×_T T'`, which by Stacks 03H4 are exactly such pairs of points. -/
theorem factorsThrough_factorizationLocus_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (hT : IsAlgebraicSpace B S hS T) {i : X ⟶ Y} (hi : IsOpenImmersion B S hS i)
    (r : A ⟶ Y) {q : A ⟶ T} (hq : IsClosedMorphism B S hS q)
    {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT' : IsAlgebraicSpace B S hS T') (g : T' ⟶ T) :
    (∃ l : T' ⟶ (factorizationLocus B S hS i r q).toFunctor,
        l ≫ (factorizationLocus B S hS i r q).ι = g) ↔
      ∃ l : pullback q g ⟶ X, l ≫ i = pullback.fst q g ≫ r := by
  rw [factorsThrough_openSubspace_iff_points B S hS hT hT' _
      (isOpenSubspace_factorizationLocus B S hS hT hi r hq) g,
    range_pointsMap_ι_factorizationLocus B S hS i r q,
    factorsThrough_isOpenImmersion_iff_points B S hS hX hY
      (isAlgebraicSpace_pullback B S hS q g hA hT' hT) i hi]
  constructor
  · rintro hgood _ ⟨p, rfl⟩
    have hc : pointsMap B S hS A q (pointsMap B S hS (pullback q g) (pullback.fst q g) p) =
        pointsMap B S hS T' g (pointsMap B S hS (pullback q g) (pullback.snd q g) p) := by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, pullback.condition]
    by_contra hn
    refine hgood ⟨pointsMap B S hS (pullback q g) (pullback.snd q g) p, rfl⟩
      ⟨pointsMap B S hS (pullback q g) (pullback.fst q g) p, ?_, hc⟩
    simpa only [Set.mem_preimage, Set.mem_compl_iff, ← pointsMap_comp_apply] using hn
  · rintro hgood _ ⟨t, rfl⟩ ⟨a, ha, hat⟩
    obtain ⟨p, hp, -⟩ := exists_point_of_isPullback_presheaf B S hS
      (IsPullback.of_hasPullback q g) a t hat
    refine ha ?_
    rw [← hp, ← pointsMap_comp_apply]
    exact hgood ⟨p, rfl⟩

end AlgebraicGeometry.Space

end
