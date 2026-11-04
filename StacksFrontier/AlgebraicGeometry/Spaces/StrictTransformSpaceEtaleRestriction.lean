module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplementAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleRestriction

/-!
# The strict transform of an algebraic space and étale restriction

Let `S` be a scheme, let `b : A' ⟶ A` be a morphism of algebraic spaces over `S`, let
`E ⊆ A'` be a subspace of its source and let `f : X ⟶ A` be an algebraic space over `A`.  The
strict transform of `X` with respect to the pair `(b, E)`, Stacks 0862 part (2) in the form
`AlgebraicGeometry.Space.strictTransformSubfunctor`, is a closed subspace of `X ×_A A'`.

Suppose given a second such situation `w : U ⟶ V`, `v' : V' ⟶ V`, `E' ⊆ V'` mapping to the
first by a morphism `u : U ⟶ X` and a morphism `m : V' ⟶ A'`, and let
`can : U ×_V V' ⟶ X ×_A A'` be the induced morphism.  If `can` is étale and the points of `E'`
are the inverse image under `|m|` of the points of `E`, then the strict transform of `U` is
contained in the inverse image along `can` of the strict transform of `X`, and the two are
*equal* as soon as the strict transform of `X` is honestly cut out by the ideal of sections
supported on the exceptional preimage.

This is the geometry-free core of part (2) of Stacks 0863, where `b` is the blowup of `A` in a
closed subspace `Z`, `E = b^{-1}Z` its exceptional divisor, `v'` the blowup of `V` in `Z ×_A V`
and `E'` its exceptional divisor; the hypotheses on `can` and on the points of `E'` are then
supplied by part (1) of that tag.  See
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupStrictTransformSpaceEtale.lean`.  Under the
identification `U ×_V V' = (X ×_A A') ×_X U` of part (1) the inverse image along `can` of a
subspace of `X ×_A A'` *is* its base change along `u`, so the equality is the tag's assertion
`U' = X' ×_X U`.

## Main results

* `AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`: the ideal of sections of
  `𝒪_{U ×_V V'}` supported on the inverse image of a set of points is, at an étale chart, the
  ideal of sections of `𝒪_{X ×_A A'}` supported on that set at the postcomposed chart.  This is
  the étale compatibility that the source of Stacks 0863 cites Stacks 0859 for.
* The hypothesis on the supported sets shared by the results below — that the supported set of
  the second situation is the inverse image under `|can|` of the supported set of the first — is
  `AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage_of_comp_eq`, stated in
  `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformEtaleRestriction.lean`, which this file
  imports.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_le_preimage_of_isEtale`: **the strict
  transform of `U` is contained in the inverse image along `can` of the strict transform of
  `X`**, with no further hypothesis.
* `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq`:
  the two are equal as soon as some closed subspace of `X ×_A A'` has the ideal of supported
  sections as its defining ideal sheaf, and
  `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_isCartesianOnAffineCharts`
  the same from cartesianity of that ideal on the affine charts.
* `AlgebraicGeometry.Space.strictTransform_exists_of_isQuasiCompact_openComplement` and
  `AlgebraicGeometry.Space.strictTransform_exists_of_isAffineHom_openComplement`: such a closed
  subspace exists as soon as the inclusion of the complement of the exceptional preimage is
  quasi-compact, respectively affine.  Hence
  `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_isAffineHom_openComplement`.
* `AlgebraicGeometry.Space.isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor`:
  an effective Cartier divisor on an algebraic space is a locally principal closed subspace, and
  `AlgebraicGeometry.Space.isAffineHom_openComplement_exceptionalPreimage` the affineness that
  Stacks 083X and Stacks 083D then give for the complement of the exceptional preimage.
* `AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor` and
  `AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor`:
  **the identification with no hypothesis beyond the source's**, for a pair `(b, E)` whose `E`
  is an effective Cartier divisor on `A'` — which is what the exceptional divisor of a blowup
  is.

## Implementation notes

The strict transform of a space is the infimum of those closed subspaces whose defining ideal
is dominated, at every affine étale chart, by the ideal of supported sections.  Two facts drive
everything here.

First, a chart of `U ×_V V'` is a chart of `X ×_A A'` with the *same* underlying scheme, by
`AlgebraicGeometry.Space.smallEtalePostcomp`, and under that identification both the defining
ideal of an inverse image and the ideal of supported sections are unchanged:  the first is
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`, Stacks 04CO, and
the second is `AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`, which is the
chartwise support comparison
`AlgebraicGeometry.Space.sectionSupportedOn_etaleAbelianRestriction_iff` read for the structure
sheaf — étale restriction of modules performs no change of scalars, so the abelian sheaf
underlying `𝒪_{U ×_V V'}` *is* the étale restriction of the one underlying `𝒪_{X ×_A A'}`, and
the comparison is an equality of ideals rather than an isomorphism.  The source cites
Stacks 0859 for this compatibility, which is an abuse: that tag has no base-change clause.  What
is used is the defining chartwise description of the supported-section subsheaf, and neither
quasi-coherence nor a finite type ideal nor ideal-power torsion enters.

Second, the inverse image along `can` of a member of the family defining the strict transform of
`X` is therefore a member of the family defining the strict transform of `U`:  closedness is
Stacks 083Q and the ideal domination is the two chartwise identifications, affineness of a chart
being a property of its underlying scheme and so unchanged by postcomposition.  Since
`CategoryTheory.Subfunctor.preimage` is computed pointwise as a preimage of sets, the infimum of
the second family is contained in the inverse image of the infimum of the first — that is the
unconditional inclusion, and it is the half of the identification that holds with no
quasi-coherence anywhere.

The reverse inclusion is not available at this generality: a closed subspace of `U ×_V V'` need
not be the inverse image of one of `X ×_A A'`, `can` being étale but not surjective, so the
second family is not the image of the first and the infima cannot be compared the other way.
What repairs it is knowing that the first infimum is cut out by an ideal:  then
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq` identifies the
first strict transform with that closed subspace, the two chartwise identifications show that its
inverse image is cut out by the ideal of supported sections of the second situation, and the same
lemma applied there identifies the second strict transform with that inverse image.

Existence of such a closed subspace is reduced, by
`AlgebraicGeometry.Space.strictTransform_exists_of_cartesian` and Descent Proposition 03DX(2) in
the form `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, to
quasi-coherence of the ideal of supported sections, which is part (3) of Stacks 0859,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSectionsSubmodule`.  Its hypotheses are
discharged here except one: the supported set is closed because the exceptional preimage is a
closed subspace (Stacks 083Q and Stacks 04CD), its complement is the point set of the open
subspace `AlgebraicGeometry.Space.openComplement` (Stacks 03BZ), and the structure sheaf is
quasi-coherent (`SheafOfModules.isQuasicoherentOnSite_unit`, Stacks 03DL(6)); what is carried is
quasi-compactness of the inclusion of that complement, equivalently — through
`AlgebraicGeometry.Space.isQuasiCompact_of_isAffineHom'` — affineness of it.

That affineness is in turn supplied, with no hypothesis, whenever `E` is an effective Cartier
divisor on `A'`.  Three steps: the defining ideal sheaf of an effective Cartier divisor is
invertible, hence finite locally free of rank one on the small étale site because that site is
locally ringed (Stacks 04KH,
`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`), hence locally generated by one
section — that is
`AlgebraicGeometry.Space.isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor`,
Stacks 083B(1) for an effective Cartier divisor; local principality passes to the inverse image
`pr_{A'}^{-1}E` by Stacks 083X,
`AlgebraicGeometry.Space.isLocallyPrincipal_preimage`; and the complement of a locally principal
closed subspace has affine inclusion by Stacks 083D,
`AlgebraicGeometry.Space.isAffineHom_ι_openComplement`.

## A duplication to resolve

`AlgebraicGeometry.Space.isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor` is
the statement of `AlgebraicGeometry.Space.isLocallyPrincipal_of_isEffectiveCartierDivisor` in
`StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierComplement.lean`, which reaches it through
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.isLocallyGeneratedByOnSite_one` instead
of through the covering-family form of the rank-one datum.  The proof here is written against
`Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_locallyEitherUnit` and
`Stacks.SheafOfModules.isLocallyGeneratedByOnSite_of_coversTop` and so needs neither that bridge
nor that file; a dedup pass should keep one of the two.

## References

* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083D](https://stacks.math.columbia.edu/tag/083D)
* [Stacks Project, Tag 083X](https://stacks.math.columbia.edu/tag/083X)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ideal of supported sections under étale restriction -/

section Chartwise

variable {W W' : AlgebraicSpaces B S hS}

/-- **The ideal of supported sections commutes with étale restriction, chartwise.**  Let
`can : W' ⟶ W` be an étale morphism of algebraic spaces, let `T` be a set of points of `W` and
let `T'` be its inverse image in the points of `W'`.  Then the sections of `𝒪_{W'}` over an
étale chart `V` of `W'` that are supported on `T'` are exactly the sections of `𝒪_W` over the
postcomposed chart `V ⟶ W' ⟶ W` that are supported on `T`.

The two are ideals in one and the same ring of regular functions: postcomposition of charts
leaves the underlying scheme unchanged, so the structure sheaf of `W` restricts to the structure
sheaf of `W'` on the nose and no change of scalars occurs.  That is why this is an equality of
ideals and not merely an isomorphism.  The support condition itself is unchanged by
`AlgebraicGeometry.Space.sectionSupportedOn_etaleAbelianRestriction_iff`.

This is the compatibility that the proof of Stacks 0863 cites Stacks 0859 for; it is proved from
the defining chartwise description of the supported-section subsheaf and uses none of the clauses
of that tag. -/
theorem supportedSectionsUnit_obj_postcomp (can : W' ⟶ W) (hcan : IsEtale B S hS can.hom)
    (T : Set (points B S hS W.1)) (T' : Set (points B S hS W'.1))
    (hT : T' = pointsMap B S hS W'.1 can.hom ⁻¹' T)
    (V : SmallEtale B S hS W'.1) :
    (supportedSectionsSubmodule B S hS W'.1 W'.2 T'
        (SheafOfModules.unit (structureRingSheaf B S hS W'))).toSubmodule.obj (op V) =
      (supportedSectionsSubmodule B S hS W.1 W.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS W))).toSubmodule.obj
        (op ((smallEtalePostcomp B S hS can hcan).obj V)) := by
  subst hT
  exact SetLike.ext fun s => sectionSupportedOn_etaleAbelianRestriction_iff B S hS can hcan T
    (moduleAddSheaf B S hS W.1 W.2 (SheafOfModules.unit (structureRingSheaf B S hS W))) V s

end Chartwise

/-! ### The strict transform of a space under étale restriction -/

section Restriction

variable {A X A' U V V' : AlgebraicSpaces B S hS}

/-- The strict-transform ideal of the second situation is, at a chart, the one of the first
situation at the postcomposed chart. -/
private theorem strictTransformIdealSubmodule_obj_postcomp (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E)
    (V₀ : SmallEtale B S hS (strictTransformPullback B S hS w v').1) :
    (strictTransformIdealSubmodule B S hS w v' E').toSubmodule.obj (op V₀) =
      (strictTransformIdealSubmodule B S hS f b E).toSubmodule.obj
        (op ((smallEtalePostcomp B S hS can hcan).obj V₀)) :=
  supportedSectionsUnit_obj_postcomp B S hS can hcan _ _ hT V₀

/-- **The strict transform of `U` is contained in the inverse image of the strict transform of
`X`.**  In the situation of two strict-transform data joined by an étale
`can : U ×_V V' ⟶ X ×_A A'` whose supported set is the inverse image of the first supported set,
the strict transform of `U` is contained in `can^{-1}` of the strict transform of `X`.

No quasi-coherence and no further geometry: the inverse image along `can` of a closed subspace
of `X ×_A A'` whose defining ideal is dominated by the ideal of supported sections is a closed
subspace of `U ×_V V'` with the same property, by Stacks 083Q together with the two chartwise
identifications `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`
and `AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`, and the infimum of subfunctors
is computed pointwise as an intersection of sets. -/
theorem strictTransformSubfunctor_le_preimage_of_isEtale (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E) :
    strictTransformSubfunctor B S hS w v' E' ≤
      (strictTransformSubfunctor B S hS f b E).preimage can.hom := by
  intro n x hx
  rw [strictTransformSubfunctor] at hx
  rintro _ ⟨Z, ⟨hZcl, hZle⟩, rfl⟩
  refine hx _ ⟨Z.preimage can.hom, ⟨isClosedSubspace_preimage B S hS can.hom Z
    (strictTransformPullback B S hS f b).2 (strictTransformPullback B S hS w v').2 hZcl,
    fun V₀ hV₀ => ?_⟩, rfl⟩
  rw [definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS can hcan ⟨Z, hZcl⟩ V₀,
    strictTransformIdealSubmodule_obj_postcomp B S hS f b E w v' E' can hcan hT]
  exact hZle _ hV₀

/-- **The strict transform of `U` is the inverse image of the strict transform of `X`, once the
latter is cut out by its ideal.**  If some closed subspace of `X ×_A A'` has the ideal of
sections supported on `|pr_{A'}^{-1}E|` as its defining ideal sheaf, then the strict transform
of `U` is exactly `can^{-1}` of the strict transform of `X`.

The hypothesis is about the first situation alone and mentions neither `U`, `V`, `V'` nor `can`;
it is the existence statement that
`AlgebraicGeometry.Space.strictTransform_exists_of_cartesian` supplies from quasi-coherence of
that ideal, and under it
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq` identifies both
strict transforms with closed subspaces:  the first with the given one, and the second with its
inverse image, whose defining ideal sheaf is computed chartwise by Stacks 04CO and
`AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`. -/
theorem strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq
    (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1)
    (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E)
    (hex : ∃ Z₀ : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z₀ =
        strictTransformIdealSubmodule B S hS f b E) :
    strictTransformSubfunctor B S hS w v' E' =
      (strictTransformSubfunctor B S hS f b E).preimage can.hom := by
  obtain ⟨Z₀, hZ₀⟩ := hex
  have hpre : definingIdealSheaf B S hS (strictTransformPullback B S hS w v')
      ⟨Z₀.1.preimage can.hom, isClosedSubspace_preimage B S hS can.hom Z₀.1
        (strictTransformPullback B S hS f b).2
        (strictTransformPullback B S hS w v').2 Z₀.2⟩ =
      strictTransformIdealSubmodule B S hS w v' E' := by
    refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V₀ => ?_)
    refine (definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS can hcan Z₀
      V₀.unop).trans ?_
    refine Eq.trans (congrArg (fun N => N.toSubmodule.obj
      (op ((smallEtalePostcomp B S hS can hcan).obj V₀.unop))) hZ₀) ?_
    exact (strictTransformIdealSubmodule_obj_postcomp B S hS f b E w v' E' can hcan hT V₀.unop).symm
  rw [strictTransformSubfunctor_eq_of_definingIdealSheaf_eq B S hS w v' E' _ hpre,
    strictTransformSubfunctor_eq_of_definingIdealSheaf_eq B S hS f b E Z₀ hZ₀]

/-- **The strict transform of `U` is the inverse image of the strict transform of `X` whenever
the ideal of supported sections is cartesian on the affine charts.**  This is
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq`
with the existence hypothesis discharged by
`AlgebraicGeometry.Space.strictTransform_exists_of_cartesian`. -/
theorem strictTransformSubfunctor_eq_preimage_of_isCartesianOnAffineCharts
    (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1)
    (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E)
    (hcart : IsCartesianOnAffineCharts
      (strictTransformIdealSubmodule B S hS f b E).toSheafOfModules) :
    strictTransformSubfunctor B S hS w v' E' =
      (strictTransformSubfunctor B S hS f b E).preimage can.hom :=
  strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq B S hS f b E w v' E'
    can hcan hT (strictTransform_exists_of_cartesian B S hS f b E hcart)

end Restriction

/-! ### The strict transform is cut out by its ideal off a quasi-compact complement -/

section Existence

variable {A X A' : AlgebraicSpaces B S hS}

/-- **The strict transform of `X` is cut out by the ideal of supported sections as soon as the
inclusion of the complement of the exceptional preimage is quasi-compact.**

This is part (3) of Stacks 0859,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSectionsSubmodule`, applied to the
structure sheaf:  the supported set is the point set of the closed subspace `pr_{A'}^{-1}E`,
hence closed by Stacks 04CD; its complement is the point set of the open subspace
`AlgebraicGeometry.Space.openComplement` by Stacks 03BZ, which is an open subspace by the same
closedness; and the structure sheaf is quasi-coherent by Stacks 03DL(6).  Quasi-coherence of the
ideal is cartesianity on affine charts by Descent Proposition 03DX(2), and
`AlgebraicGeometry.Space.strictTransform_exists_of_cartesian` concludes. -/
theorem strictTransform_exists_of_isQuasiCompact_openComplement (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (hE : IsClosedSubspace B S hS E)
    (hqc : IsQuasiCompact B S hS
      (openComplement B S hS (exceptionalPreimage B S hS f b E)).ι) :
    ∃ Z : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z =
        strictTransformIdealSubmodule B S hS f b E := by
  have hcl : IsClosedSubspace B S hS (exceptionalPreimage B S hS f b E) :=
    exceptionalPreimage_isClosedSubspace B S hS f b E hE
  have hTclosed : IsClosed (exceptionalPreimageSet B S hS f b E) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2 _ hcl.2
  refine strictTransform_exists_of_cartesian B S hS f b E ?_
  refine (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS
    (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2 _).mp ?_
  exact isQuasicoherentOnSite_supportedSectionsSubmodule B S hS
    (strictTransformPullback B S hS f b).2
    (SheafOfModules.unit (structureRingSheaf B S hS (strictTransformPullback B S hS f b)))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hTclosed
    (isOpenSubspace_openComplement B S hS (strictTransformPullback B S hS f b).2 _ hcl)
    (range_pointsMap_ι_openComplement B S hS _) hqc

/-- **The strict transform of `X` is cut out by the ideal of supported sections as soon as the
inclusion of the complement of the exceptional preimage is affine.**  An affine morphism of
algebraic spaces is quasi-compact,
`AlgebraicGeometry.Space.isQuasiCompact_of_isAffineHom'`, so this is
`AlgebraicGeometry.Space.strictTransform_exists_of_isQuasiCompact_openComplement`.

Affineness of that inclusion is the affineness half of Stacks 07ZU; for a locally principal
closed subspace of an algebraic space it is Stacks 083D. -/
theorem strictTransform_exists_of_isAffineHom_openComplement (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (hE : IsClosedSubspace B S hS E)
    (haff : IsAffineHom B S hS
      (openComplement B S hS (exceptionalPreimage B S hS f b E)).ι) :
    ∃ Z : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z =
        strictTransformIdealSubmodule B S hS f b E :=
  strictTransform_exists_of_isQuasiCompact_openComplement B S hS f b E hE
    (isQuasiCompact_of_isAffineHom' B S hS _
      (isOpenSubspace_openComplement B S hS (strictTransformPullback B S hS f b).2 _
        (exceptionalPreimage_isClosedSubspace B S hS f b E hE)).1
      (strictTransformPullback B S hS f b).2 haff)

/-- **An effective Cartier divisor on an algebraic space is a locally principal closed
subspace** — Stacks 083B, part (1) for an effective Cartier divisor.

Its defining ideal sheaf is an invertible `𝒪_X`-module by definition.  The small étale site of
an algebraic space is locally ringed, Stacks 04KH in the form
`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`, so the converse clause of
Stacks 0B8Q applies and the ideal sheaf is finite locally free of rank one:  there is a covering
family of the site on each member of which it has a generating family indexed by `Fin 1`.  That
is precisely local generation by one section,
`Stacks.SheafOfModules.isLocallyGeneratedByOnSite_of_coversTop`.

The same statement is reached by a different route in
`StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierComplement.lean`; see the module
documentation. -/
theorem isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor
    (W : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS W.1)
    (hD : IsEffectiveCartierDivisor B S hS W D) :
    IsLocallyPrincipal B S hS W D := by
  have h₁ : HasWeakSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u})
  have h₂ : (smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS W.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  have h₃ : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite B S hS W.1 W.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O).property
      (definingIdealSheaf B S hS W D).toSheafOfModules :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD
  have hflf := Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_locallyEitherUnit
    (smallEtaleRingedSite B S hS W.1 W.2).O
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O).property
    (definingIdealSheaf B S hS W D).toSheafOfModules
    (smallEtaleRingedSite_isLocallyRinged B S hS W.1 W.2).2
  obtain ⟨q, -, hr⟩ := hflf.exists_isFiniteLocallyFreeOfRankData
  exact Stacks.SheafOfModules.isLocallyGeneratedByOnSite_of_coversTop _ 1 q.X q.coversTop
    fun i => ⟨q.generators i, hr i⟩

/-- **The complement of the exceptional preimage has affine inclusion whenever `E` is locally
principal.**  Local principality passes to the inverse image `pr_{A'}^{-1}E` by Stacks 083X,
`AlgebraicGeometry.Space.isLocallyPrincipal_preimage`, and the inclusion of the complement of a
locally principal closed subspace is affine by Stacks 083D,
`AlgebraicGeometry.Space.isAffineHom_ι_openComplement`. -/
theorem isAffineHom_openComplement_exceptionalPreimage (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (hE : IsClosedSubspace B S hS E)
    (hlp : IsLocallyPrincipal B S hS A' ⟨E, hE⟩) :
    IsAffineHom B S hS
      (openComplement B S hS (exceptionalPreimage B S hS f b E)).ι :=
  isAffineHom_ι_openComplement B S hS
    (strictTransformPullback B S hS f b)
    ⟨exceptionalPreimage B S hS f b E,
      exceptionalPreimage_isClosedSubspace B S hS f b E hE⟩
    (isLocallyPrincipal_preimage B S hS (strictTransformPullbackToBlowUp B S hS f b)
      ⟨E, hE⟩ hlp)

/-- **The strict transform of `X` is cut out by the ideal of supported sections whenever `E` is
a locally principal closed subspace of `A'`.** -/
theorem strictTransform_exists_of_isLocallyPrincipal (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1) (hE : IsClosedSubspace B S hS E)
    (hlp : IsLocallyPrincipal B S hS A' ⟨E, hE⟩) :
    ∃ Z : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z =
        strictTransformIdealSubmodule B S hS f b E :=
  strictTransform_exists_of_isAffineHom_openComplement B S hS f b E hE
    (isAffineHom_openComplement_exceptionalPreimage B S hS f b E hE hlp)

/-- **The strict transform of `X` is cut out by the ideal of supported sections whenever `E` is
an effective Cartier divisor on `A'`**, which is what the exceptional divisor of a blowup is.

This is the whole of the preamble that Stacks 0862 needs, with no hypothesis left over:  an
effective Cartier divisor is locally principal, its inverse image is locally principal, the
complement of that has affine hence quasi-compact inclusion, and part (3) of Stacks 0859 then
makes the ideal of supported sections quasi-coherent. -/
theorem strictTransform_exists_of_isEffectiveCartierDivisor (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (hE : IsEffectiveCartierDivisor B S hS A' E) :
    ∃ Z : ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1,
      definingIdealSheaf B S hS (strictTransformPullback B S hS f b) Z =
        strictTransformIdealSubmodule B S hS f b E.1 :=
  strictTransform_exists_of_isLocallyPrincipal B S hS f b E.1 E.2
    (isLocallyPrincipal_definingIdealSheaf_of_isEffectiveCartierDivisor B S hS A' E hE)

end Existence

/-! ### The identification under the affineness hypothesis -/

section Geometric

variable {A X A' U V V' : AlgebraicSpaces B S hS}

/-- **The strict transform of `U` is the inverse image of the strict transform of `X`, under the
affineness of the complement of the exceptional preimage.**  This is
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq`
with the existence hypothesis supplied by
`AlgebraicGeometry.Space.strictTransform_exists_of_isAffineHom_openComplement`.

The carried hypothesis is geometry of the first situation only — the inclusion of
`(X ×_A A') ∖ pr_{A'}^{-1}E` is affine — and is independent of the conclusion, which is a
statement about the second situation and the comparison `can`. -/
theorem strictTransformSubfunctor_eq_preimage_of_isAffineHom_openComplement
    (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1) (hE : IsClosedSubspace B S hS E)
    (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E)
    (haff : IsAffineHom B S hS
      (openComplement B S hS (exceptionalPreimage B S hS f b E)).ι) :
    strictTransformSubfunctor B S hS w v' E' =
      (strictTransformSubfunctor B S hS f b E).preimage can.hom :=
  strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq B S hS f b E w v' E'
    can hcan hT (strictTransform_exists_of_isAffineHom_openComplement B S hS f b E hE haff)

/-- **The strict transform of `U` is the inverse image of the strict transform of `X`, with no
hypothesis beyond the source's**, as soon as the subspace `E ⊆ A'` of the first situation is an
effective Cartier divisor — which is what the exceptional divisor of a blowup is.

This is the geometry-free core of Stacks 0863 part (2) in its final form.  The existence of a
closed subspace cut out by the ideal of supported sections, which is the only thing the
identification needs beyond the étale comparison, is
`AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor`. -/
theorem strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor
    (f : X ⟶ A) (b : A' ⟶ A) (E : ClosedSubspaces B S hS A'.1)
    (hE : IsEffectiveCartierDivisor B S hS A' E)
    (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hT : exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E.1) :
    strictTransformSubfunctor B S hS w v' E' =
      (strictTransformSubfunctor B S hS f b E.1).preimage can.hom :=
  strictTransformSubfunctor_eq_preimage_of_exists_definingIdealSheaf_eq B S hS f b E.1 w v' E'
    can hcan hT (strictTransform_exists_of_isEffectiveCartierDivisor B S hS f b E hE)

end Geometric

end AlgebraicGeometry.Space

end
