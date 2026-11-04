module

public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The support of a small étale direct image along a morphism with closed image

Let `f : Y ⟶ X` be a relatively representable morphism of algebraic spaces over a scheme `S`
whose induced map on point sets has closed range. This file proves that the small étale direct
image of an abelian sheaf along `f` is supported on that range, and deduces that an abelian
sheaf on `X_étale` lying in the essential image of the direct image along an *integral*
morphism is supported on the image of the point set of `Y`.

This is Étale Cohomology 04FX for algebraic spaces and for a morphism more general than a
closed immersion, and it is one of the two inclusions of the essential-image clause of
Stacks 0AEH, part (2); the other inclusion, and the clause itself, are in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveEssentialImage.lean`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isClosed_range`
  is the support bound for a representable morphism with closed point-set range, and
  `AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isIntegralHom`
  is its specialization to an integral morphism, whose point-set range is closed by Stacks 0415
  and Stacks 0CZG.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage_of_isIntegralHom` is one inclusion
  of the essential image of Stacks 0AEH, part (2): an abelian sheaf on the small étale site of
  `X` isomorphic to a direct image along an integral morphism `f : Y ⟶ X` is supported on the
  image of the point set of `Y`.

## Implementation notes

The proofs are those of
`AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset` and
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage` for a closed immersion, with the
closed immersion replaced by the two properties of it those proofs use: relative
representability, which makes the chart base change and hence the direct image exist, and
closedness of the range of the induced map on point sets, which makes the complement of the
preimage of that range in a chart open and so comparable with the largest open zero locus of a
section. Nothing else about a closed immersion enters, which is why the bound holds for every
integral morphism.

The converse inclusion of Stacks 0AEH, part (2) is not proved here. It is
`AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom`, in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveEssentialImage.lean`, where
the two inclusions are assembled into
`AlgebraicGeometry.Space.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective`.
That route is the stalkwise one by which
`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion`
settles the same clause of Stacks 04E5 for a closed immersion, and it needs neither a
factorization of `f` through the closed subspace its point set cuts out nor the topological
invariance of the small étale site: the one step of the closed-immersion argument that uses more
than representability and closedness of the image is the lifting of a geometric point, and that
step survives because a geometric point is the spectrum of an algebraically closed field, over
which a nonempty integral algebra has a retraction.

## References

* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {Y X : AlgebraicSpaces B S hS}

/-- The preimage in the point set of an étale chart of `X` of the point set of a morphism
`f : Y ⟶ X` with closed range is closed, by continuity of the map induced on point sets. -/
theorem isClosed_chartPreimage_of_isClosed_range (f : Y ⟶ X)
    (hc : IsClosed (Set.range (pointsMap B S hS Y.1 f.hom)))
    (V : SmallEtale B S hS X.1) : IsClosed (chartPreimage B S hS f V) :=
  hc.preimage (continuous_pointsMap B S hS V.obj.hom)

/-- The complement of the preimage of the point set of a representable morphism with closed
range is contained in the largest open zero locus of every section of a direct image along it:
a chart over `V` avoiding that preimage has empty base change along `f`, so it carries only the
zero section. -/
theorem compl_chartPreimage_le_largestOpenZeroLocus_of_isClosed_range (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom)
    (hc : IsClosed (Set.range (pointsMap B S hS Y.1 f.hom)))
    (G : abelianSheaves.{w} B S hS Y) (V : SmallEtale B S hS X.1)
    (σ : ((smallEtaleAbelianPushforward B S hS f hr).obj G).obj.obj (op V)) :
    (⟨(chartPreimage B S hS f V)ᶜ,
          (isClosed_chartPreimage_of_isClosed_range B S hS f hc V).isOpen_compl⟩ :
        TopologicalSpace.Opens _) ≤
      largestOpenZeroLocus B S hS X.1
        ((smallEtaleAbelianPushforward B S hS f hr).obj G) V σ := by
  refine largestOpenZeroLocus_maximal B S hS X.1 _ V σ _ fun W g hg => ?_
  refine smallEtaleAbelianPushforward_restrict_eq_zero B S hS f hr G g ?_ σ
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
  exact hg y (chartPreimage_subset_preimage B S hS f g hy)

/-- **The support of a small étale direct image, for a representable morphism with closed
image.** For a relatively representable morphism `f : Y ⟶ X` of algebraic spaces over `S` whose
induced map on point sets has closed range, and an abelian sheaf `G` on the small étale site of
`Y`, the support of `f_*G` is contained in that range.

This is Étale Cohomology 04FX transported to algebraic spaces. The support is computed through
its sections description, Stacks 04KB: a point in the support of a section of `f_*G` over a
chart `V` lies outside the largest open zero locus of that section, hence inside the preimage
of the range. -/
theorem supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isClosed_range (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom)
    (hc : IsClosed (Set.range (pointsMap B S hS Y.1 f.hom)))
    (G : abelianSheaves.{w} B S hS Y) :
    supportOfSheaf B S hS X.1 ((smallEtaleAbelianPushforward B S hS f hr).obj G) ⊆
      Set.range (pointsMap B S hS Y.1 f.hom) := by
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.property]
  simp only [Set.iUnion_subset_iff]
  intro V σ y hy
  obtain ⟨v, hv, rfl⟩ := hy
  by_contra hmem
  exact hv ((compl_chartPreimage_le_largestOpenZeroLocus_of_isClosed_range
    B S hS f hr hc G V σ) hmem)

/-- **The point set of an integral morphism of algebraic spaces is closed.** An integral
morphism is universally closed by Stacks 0415, hence closed on point sets by Stacks 0CZG, and
the range is the image of the whole point set. -/
theorem isClosed_range_pointsMap_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) :
    IsClosed (Set.range (pointsMap B S hS Y.1 f.hom)) := by
  have h := isClosed_of_universallyClosed B S hS X.property f.hom
    (universallyClosed_of_isIntegralHom B S hS Y.property X.property hf)
    Set.univ isClosed_univ
  simpa only [Set.image_univ] using h

/-- **The support of a small étale direct image along an integral morphism.** For an integral
morphism `f : Y ⟶ X` of algebraic spaces over `S` and an abelian sheaf `G` on the small étale
site of `Y`, the support of `f_*G` is contained in the image of the point set of `Y`. -/
theorem supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (G : abelianSheaves.{w} B S hS Y) :
    supportOfSheaf B S hS X.1 ((smallEtaleAbelianPushforward B S hS f
          ((isIntegralHom_iff_representable B S hS f.hom Y.property X.property).mp hf).1).obj
        G) ⊆
      Set.range (pointsMap B S hS Y.1 f.hom) :=
  supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isClosed_range B S hS f _
    (isClosed_range_pointsMap_of_isIntegralHom B S hS f hf) G

/-- **Stacks 0AEH, part (2), one inclusion of the essential image.** An abelian sheaf on the
small étale site of `X` isomorphic to a small étale direct image along an integral morphism
`f : Y ⟶ X` of algebraic spaces over `S` is supported on the image of the point set of `Y`.

An isomorphism of abelian sheaves is locally surjective, so by part (5) of Stacks 04KB it does
not enlarge the support, and the support of the direct image is bounded by
`AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isIntegralHom`.

Universal injectivity of `f`, which Stacks 0AEH also assumes, is not used: this inclusion holds
for every integral morphism. It is one inclusion of the clause and carries no tag; the clause
itself is
`AlgebraicGeometry.Space.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective`. -/
@[stacks 0AEH "part (2), the inclusion only: a sheaf in the essential image of f_{small,*} \
is supported on f(|Y|), for an integral morphism and with no universal injectivity needed. \
The converse inclusion, and with it the full iff of part (2), is \
AlgebraicGeometry.Space.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective; \
part (1) is ...smallEtalePushforward_essImage_iff_of_integral_universallyInjective. Both \
are proved at the source's own hypotheses"]
theorem supportOfSheaf_subset_of_essImage_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (F : abelianSheaves.{w} B S hS X)
    (hF : (smallEtaleAbelianPushforward B S hS f
      ((isIntegralHom_iff_representable B S hS f.hom Y.property X.property).mp hf).1).essImage
        F) :
    supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Y.1 f.hom) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  intro x hx
  exact supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isIntegralHom B S hS f hf G
    (supportOfSheaf_subset_of_isLocallySurjective B S hS X.1 X.property e.hom hx)

end AlgebraicGeometry.Space

end
