module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformBlowupComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections

/-!
# The comparison of Stacks 0864 is an isomorphism off the exceptional preimage

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed subspace,
let `b : A' ⟶ A` be the blowup of `A` in `Z`, let `f : X ⟶ A` be an algebraic space over `A` and
let `b'' : X'' ⟶ X` be the blowup of `X` in `f⁻¹Z`.  Stacks 0864, clause (1) asserts that the
canonical comparison `i : X'' ⟶ X ×_A A'` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformBlowupComparison.lean` is a closed immersion
whose image is the strict transform of `X`.

This file proves that `i` is an **isomorphism over the complement of the exceptional preimage**
`pr_{A'}^{-1}(b⁻¹Z) ⊆ X ×_A A'`, which is the part of that assertion visible to the universal
property of the blowup alone.  Over that complement the centre pulls back to a closed subspace
with no points, so the complement — and likewise its inverse image in `X''` — is an object of
the category `𝒞` of Stacks 085U for the centre `f⁻¹Z`, and the two unique morphisms to `X''` that
finality supplies are mutually inverse to the restriction of `i`.

## Main definitions

* `AlgebraicGeometry.Space.exceptionalPreimageClosedSubspace`: the exceptional preimage
  `pr_{A'}^{-1}(b⁻¹Z)` as a closed subspace of `X ×_A A'`.
* `AlgebraicGeometry.Space.exceptionalPreimageComplement`: its open complement, and
  `AlgebraicGeometry.Space.exceptionalPreimageComplementSpace`,
  `AlgebraicGeometry.Space.exceptionalPreimageComplementι` the algebraic space it is and its
  inclusion.

## Main results

* `AlgebraicGeometry.Space.preimage_exceptionalPreimage_eq_preimage_centre`: the inverse image of
  the exceptional preimage along a morphism to `X ×_A A'` is the inverse image of `Z` along the
  composite to `A`.  This is the cartesian square of `X ×_A A'` read on subfunctors, and it is
  what makes the complement an object of `𝒞`.
* `AlgebraicGeometry.Space.isPullbackDefined_preimageClosedSubspace_of_factorsThrough`: a
  morphism to `X ×_A A'` factoring through the complement of the exceptional preimage has `f⁻¹Z`
  pulling back to an effective Cartier divisor, namely to a closed subspace with no points.
* `AlgebraicGeometry.Space.exists_section_strictTransformBlowUpComparison_of_isBlowupAlong`: the
  comparison `i` admits a **section over the complement of the exceptional preimage**.  This is
  the space-level counterpart of the scheme-level
  `AlgebraicGeometry.exceptionalComplementToBlowUpComap_comp` of Stacks 080E, which obtains it
  from the strict transform being the scheme-theoretic image of that complement; here it comes
  from the universal property of `b''` and the uniqueness of the classifying morphism of `b`.
* `AlgebraicGeometry.Space.isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong`:
  **the comparison is an isomorphism over the complement of the exceptional preimage**, for two
  arbitrary blowups; and
  `AlgebraicGeometry.Space.isIso_fromPreimage_exceptionalPreimageComplement`, the same for the
  blowups *constructed* in Stacks 085Q and hence with no hypothesis that anything is a blowup.
* `AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`: **for a blowup
  the strict transform of `X` is honestly cut out by the ideal of sections supported on the
  exceptional preimage**, with no hypothesis beyond `b` being the blowup of `A` in `Z`.  The
  definition of `AlgebraicGeometry.Space.strictTransform` is an infimum of closed subspaces and
  in general need not be cut out by that ideal at all.
* `AlgebraicGeometry.Space.preimage_exceptionalPreimageSet_strictTransformBlowUpComparison`: the
  inverse image under `|i|` of the point set of the exceptional preimage is the point set of the
  exceptional divisor of `b''`.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections`:
  the direct image along `i` of the quotient of an `𝒪_{X''}`-module by its sections supported on
  the exceptional divisor of `b''` has **no sections supported on the exceptional preimage**.
  This is the hypothesis `hQ` of `AlgebraicGeometry.Space.exists_strictTransformSheafIso` at the
  target `Q = i_*F''` of clause (2), discharged with no hypothesis beyond the two blowups.

## Implementation notes

The argument is the one of `AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`
(Stacks 085T, part (1)) transplanted from the blowup `b` to the comparison `i`, and it uses only
`AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`.

Everything rests on one subfunctor identity,
`AlgebraicGeometry.Space.preimage_exceptionalPreimage_eq_preimage_centre`: for a morphism
`g : Y ⟶ X ×_A A'` the inverse image of `pr_{A'}^{-1}(b⁻¹Z)` along `g` and the inverse image of
`Z` along `g ≫ pr_X ≫ f` are *the same* subfunctor, because `pr_X ≫ f = pr_{A'} ≫ b`.  So if `g`
factors through the complement of the exceptional preimage, then `f⁻¹Z` pulls back along
`g ≫ pr_X` to a closed subspace with no points
(`AlgebraicGeometry.Space.isEmpty_points_preimage_of_disjoint`), hence to an effective Cartier
divisor (`AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_isEmpty_points`).

That applies to the inclusion of the complement itself and to the inclusion of its inverse image
in `X''`, so each receives a unique morphism to `X''` over `X`.  The section is the first of
them: its composite with `i` agrees with the inclusion of the complement on the projection to
`X` by construction, and on the projection to `A'` by the uniqueness of the classifying morphism
`AlgebraicGeometry.Space.strictTransformBlowUpClassifying` of `b`, so the two agree because
`X ×_A A'` is the fibre product.  The section lands in the inverse image of the complement, and
the two composites with the restriction of `i` are the identities, the second by the uniqueness
of the lift out of that inverse image.

## What is not proved

**Clause (1) of Stacks 0864 is not proved, here or anywhere in this library:** that `i` is a
closed immersion, and that its image is `AlgebraicGeometry.Space.strictTransformSubfunctor`.
Neither follows from the isomorphism proved here, which says nothing about `i` over the
exceptional preimage — precisely where a closed immersion is not an isomorphism.

Two inputs that older notes in this library record as missing are in fact available, and neither
closes the clause.

* Stacks 0863, part (2) **is** available with no hypothesis beyond the source's:
  `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isBlowupAlong` of
  `StacksFrontier/AlgebraicGeometry/Spaces/BlowupStrictTransformSpaceEtale.lean`.  The "what is not
  proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformBlowupComparison.lean` says otherwise and
  is out of date.
* That the strict transform is honestly cut out by the ideal of supported sections **is**
  available for a blowup:
  `AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong` below, which
  rests on `AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor`.

What the source's argument needs over and above those is the reduction itself: it checks the
clause étale-locally on `X` and quotes the scheme case, Stacks 080E part (1),
`AlgebraicGeometry.strictTransformBlowUpι`.  **The descent half of that reduction is available in
full**, and is recorded here so that it is not looked for again:

* being a closed immersion descends along a single surjective étale chart of the target,
  `AlgebraicGeometry.Space.isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart` of
  `StacksFrontier/AlgebraicGeometry/Descent/ClosedImmersionEtaleDescent.lean`, and the equivalence
  `AlgebraicGeometry.Space.isClosedImmersion_tfae` of Stacks 03M4, in
  `StacksFrontier/AlgebraicGeometry/Descent/ClosedImmersionLocalCriterion.lean`; and it is fpqc
  local on the target by Stacks 0420,
  `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`;
* the image subfunctor base changes on the nose,
  `CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SubspacePreimage.lean`, with no hypothesis at all, and
  two subfunctors agreeing after pullback along a locally surjective morphism are equal,
  `CategoryTheory.Subfunctor.eq_of_isLocallySurjective` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SchematicLocus.lean`, fed by Stacks 05VM,
  `AlgebraicGeometry.Space.points_locallySurjective`.

Exactly one thing is missing: a comparison identifying the space-level strict transform of a
*representable* algebraic space with the scheme-level one.
`AlgebraicGeometry.Space.strictTransformSubfunctor` is built from
`AlgebraicGeometry.Space.supportedSectionsSubmodule` on the small étale site and nothing relates
it to `Stacks.StrictTransform.ideal`, which is built from `AlgebraicGeometry.supportedSections`
on the Zariski site; so the scheme case cannot be quoted at a chart.  That comparison is
Stacks 03DX, part (2), whose unavailability the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` record;
the same obstruction is the one the "what is not proved" sections of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformLocalGenerators.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformFittingRank.lean` record for Stacks 0CZP
and 0CZQ.

A second route avoids the scheme case and runs inside the universal property.  It is blocked on
two statements of independent interest, neither of which this library has.

* That the inverse image of the centre on the strict transform is an effective Cartier divisor —
  the space-level counterpart of `AlgebraicGeometry.isCartierOver_strictTransform`, which the
  scheme level obtains from the strict transform being the scheme-theoretic image of the affine
  complement of the exceptional preimage.  Granted it, the universal property of `b''` yields an
  `l : X' ⟶ X''` over `X` with `l ≫ i` the inclusion of the strict transform, hence one of the
  two inclusions of the image assertion.
* That the structure sheaf of an algebraic space has no nonzero local section supported on an
  effective Cartier divisor.  Granted it, the ideal of supported sections pulls back to zero
  along `i` and the other inclusion follows.  The scheme-theoretic density that proves it *is*
  available — `isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor` of
  `StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierComplement.lean` — but the step from
  density to the vanishing of supported sections is not stated.

Clause (2) of Stacks 0864, that the strict transform of a module is the direct image along `i` of
the strict transform relative to `b''`, is not proved either.  It is the universal property
`AlgebraicGeometry.Space.exists_strictTransformSheafIso` applied at `Q = i_*F''`, and of its
three hypotheses exactly one is settled here: `hQ` is
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections`,
unconditionally.  The other two are not.

* `Epi q` needs the direct image along `i` to be right exact and the unit of Stacks 03D7 to be an
  epimorphism, and both hold for a *closed immersion* — the space-level Stacks 08KS, in
  `AlgebraicGeometry.Space.preservesEpimorphisms_modulePushforward_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated` fed
  `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`, each of which
  takes `IsClosedImmersion i.hom` as a hypothesis.  That `i` is a closed immersion is the first
  half of clause (1) and is not proved.
* `hq`, that `q` kills only sections supported on the exceptional preimage, is what the
  isomorphism proved here is the geometric half of: it additionally needs that the unit
  `G ⟶ i_*i^*G` of Stacks 03D7 is injective on the sections over a chart factoring through `i`,
  which is not stated for algebraic spaces — the small étale site has no restriction adjunction
  along an open subspace, so the scheme-level route through
  `AlgebraicGeometry.isIso_restrictFunctor_map_unit_of_section` is unavailable.

## References

* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A X A' X'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1) (b'' : X'' ⟶ X)

/-- The underlying subfunctor of an inverse image of a closed subspace is the inverse image of
its underlying subfunctor. -/
private theorem coe_preimageClosedSubspace {Y W : AlgebraicSpaces B S hS} (g : Y ⟶ W)
    (D : ClosedSubspaces B S hS W.1) :
    (preimageClosedSubspace g D).1 = D.1.preimage g.hom :=
  rfl

/-- A closed subspace whose underlying subfunctor has no points is an effective Cartier divisor:
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_isEmpty_points` with the subfunctor
presented in another shape. -/
private theorem isEffectiveCartierDivisor_of_subfunctor_eq_of_isEmpty
    {Y : AlgebraicSpaces B S hS} (D : ClosedSubspaces B S hS Y.1) (G : Subfunctor Y.1)
    (h : D.1 = G) (hG : IsEmpty (points B S hS G.toFunctor)) :
    IsEffectiveCartierDivisor B S hS Y D :=
  isEffectiveCartierDivisor_of_isEmpty_points B S hS Y D (by rw [h]; exact hG)

/-! ### The exceptional preimage and its open complement -/

/-- The exceptional preimage `pr_{A'}^{-1}(b⁻¹Z) ⊆ X ×_A A'` as a closed subspace, by
Stacks 083Q in the form `AlgebraicGeometry.Space.exceptionalPreimage_isClosedSubspace`. -/
abbrev exceptionalPreimageClosedSubspace :
    ClosedSubspaces B S hS (strictTransformPullback B S hS f b).1 :=
  ⟨exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1,
    exceptionalPreimage_isClosedSubspace B S hS f b (preimageClosedSubspace b Z).1
      (preimageClosedSubspace b Z).2⟩

/-- The open complement of the exceptional preimage in `X ×_A A'`. -/
abbrev exceptionalPreimageComplement :
    OpenSubspaces B S hS (strictTransformPullback B S hS f b).1 :=
  openComplementOfClosedSubspace B S hS (strictTransformPullback B S hS f b)
    (exceptionalPreimageClosedSubspace B S hS f b Z)

/-- The complement of the exceptional preimage as an algebraic space over `S`. -/
abbrev exceptionalPreimageComplementSpace : AlgebraicSpaces B S hS :=
  ⟨(exceptionalPreimageComplement B S hS f b Z).1.toFunctor,
    (exceptionalPreimageComplement B S hS f b Z).2.1⟩

/-- The inclusion of the complement of the exceptional preimage into `X ×_A A'`. -/
abbrev exceptionalPreimageComplementι :
    exceptionalPreimageComplementSpace B S hS f b Z ⟶ strictTransformPullback B S hS f b :=
  ObjectProperty.homMk (exceptionalPreimageComplement B S hS f b Z).1.ι

/-! ### The inverse image of the centre along a morphism to the base change -/

/-- **The two inverse images of the centre agree.**  For a morphism `g : Y ⟶ X ×_A A'` the
inverse image along `g` of the exceptional preimage `pr_{A'}^{-1}(b⁻¹Z)` is the inverse image of
the centre `Z` along the composite `Y ⟶ X ×_A A' ⟶ X ⟶ A`.

This is the cartesian square `pr_X ≫ f = pr_{A'} ≫ b` read on subfunctors. -/
theorem preimage_exceptionalPreimage_eq_preimage_centre {Y : AlgebraicSpaces B S hS}
    (g : Y.1 ⟶ (strictTransformPullback B S hS f b).1) :
    (exceptionalPreimageClosedSubspace B S hS f b Z).1.preimage g =
      Z.1.preimage (g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) := by
  have hsq : (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom =
      (strictTransformPullbackToBlowUp B S hS f b).hom ≫ b.hom :=
    congrArg (·.hom) (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w
  rw [hsq]
  change ((Z.1.preimage b.hom).preimage
    (strictTransformPullbackToBlowUp B S hS f b).hom).preimage g = _
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, Category.assoc]

/-- The inverse image of `f⁻¹Z` along `Y ⟶ X ×_A A' ⟶ X` is the inverse image of `Z` along the
composite to `A`. -/
theorem preimage_preimageClosedSubspace_comp_toSource {Y : AlgebraicSpaces B S hS}
    (g : Y.1 ⟶ (strictTransformPullback B S hS f b).1) :
    (preimageClosedSubspace f Z).1.preimage
        (g ≫ (strictTransformPullbackToSource B S hS f b).hom) =
      Z.1.preimage (g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) := by
  rw [coe_preimageClosedSubspace, ← Subfunctor.preimage_comp, Category.assoc]

/-- **The centre has no points over the complement of the exceptional preimage.**  For a morphism
`g : Y ⟶ X ×_A A'` factoring through the complement of the exceptional preimage, the inverse
image of the centre `Z` along `Y ⟶ X ×_A A' ⟶ X ⟶ A` is a subfunctor with no points.

The inverse image in question is the inverse image of the exceptional preimage along `g`, by
`AlgebraicGeometry.Space.preimage_exceptionalPreimage_eq_preimage_centre`, and the exceptional
preimage is disjoint from its own complement. -/
theorem isEmpty_points_preimage_centre_of_factorsThrough {Y : AlgebraicSpaces B S hS}
    (g : Y.1 ⟶ (strictTransformPullback B S hS f b).1)
    (k : Y.1 ⟶ (exceptionalPreimageComplement B S hS f b Z).1.toFunctor)
    (hk : k ≫ (exceptionalPreimageComplement B S hS f b Z).1.ι = g) :
    IsEmpty (points B S hS (Z.1.preimage
      (g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom)).toFunctor) := by
  have h0 := isEmpty_points_preimage_of_disjoint B S hS
    (exceptionalPreimageClosedSubspace B S hS f b Z).1
    (exceptionalPreimageComplement B S hS f b Z).1
    (disjoint_subspacePointSet_openComplement B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageClosedSubspace B S hS f b Z))
    g k hk
  rwa [preimage_exceptionalPreimage_eq_preimage_centre B S hS f b Z g] at h0

/-- **The complement of the exceptional preimage is an object of the category of Stacks 085U for
the centre `f⁻¹Z`.**  For a morphism `y : Y ⟶ X` which is the composite of a morphism
`g : Y ⟶ X ×_A A'` factoring through the complement of the exceptional preimage with the
projection `pr_X`, the inverse image of `f⁻¹Z` along `y` is an effective Cartier divisor on `Y`:
it has no points. -/
theorem isPullbackDefined_preimageClosedSubspace_of_factorsThrough {Y : AlgebraicSpaces B S hS}
    (y : Y ⟶ X) (g : Y.1 ⟶ (strictTransformPullback B S hS f b).1)
    (hy : y.hom = g ≫ (strictTransformPullbackToSource B S hS f b).hom)
    (k : Y.1 ⟶ (exceptionalPreimageComplement B S hS f b Z).1.toFunctor)
    (hk : k ≫ (exceptionalPreimageComplement B S hS f b Z).1.ι = g) :
    IsPullbackDefined B S hS y (preimageClosedSubspace f Z) :=
  have heq : (preimageClosedSubspace f Z).1.preimage y.hom =
      Z.1.preimage (g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) :=
    hy ▸ preimage_preimageClosedSubspace_comp_toSource B S hS f b Z g
  isEffectiveCartierDivisor_of_subfunctor_eq_of_isEmpty B S hS _ _ heq
    (isEmpty_points_preimage_centre_of_factorsThrough B S hS f b Z g k hk)

/-- **The complement of the exceptional preimage is an object of the category of Stacks 085U for
the centre `Z`.**  The same statement for the composite to `A` and the centre `Z` itself, which
is what the uniqueness of the classifying morphism of `b` is applied to. -/
theorem isPullbackDefined_centre_of_factorsThrough {Y : AlgebraicSpaces B S hS}
    (y : Y ⟶ A) (g : Y.1 ⟶ (strictTransformPullback B S hS f b).1)
    (hy : y.hom = g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom)
    (k : Y.1 ⟶ (exceptionalPreimageComplement B S hS f b Z).1.toFunctor)
    (hk : k ≫ (exceptionalPreimageComplement B S hS f b Z).1.ι = g) :
    IsPullbackDefined B S hS y Z :=
  have heq : Z.1.preimage y.hom =
      Z.1.preimage (g ≫ (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) := by
    rw [hy]
  isEffectiveCartierDivisor_of_subfunctor_eq_of_isEmpty B S hS _ _ heq
    (isEmpty_points_preimage_centre_of_factorsThrough B S hS f b Z g k hk)

/-! ### The section of the comparison over the complement -/

/-- **The comparison of Stacks 0864, clause (1) has a section over the complement of the
exceptional preimage.**  There is a morphism `k : (X ×_A A') ∖ pr_{A'}^{-1}(b⁻¹Z) ⟶ X''` with
`k ≫ i` the inclusion of that complement.

The complement is an object of the category of Stacks 085U for the centre `f⁻¹Z`
(`AlgebraicGeometry.Space.isPullbackDefined_preimageClosedSubspace_of_factorsThrough`), so the
universal property of `b''` produces `k` with `k ≫ b''` the composite to `X`.  Then `k ≫ i` and the
inclusion agree after `pr_X`, because `i ≫ pr_X = b''`, and after `pr_{A'}`, because both
composites with `b` are the composite to `A` and the classifying morphism of `b` out of the
complement is unique; so they agree, `X ×_A A'` being the fibre product.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.exceptionalComplementToBlowUpComap_comp` of Stacks 080E. -/
theorem exists_section_strictTransformBlowUpComparison_of_isBlowupAlong
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    ∃ k : exceptionalPreimageComplementSpace B S hS f b Z ⟶ X'',
      k ≫ strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' =
        exceptionalPreimageComplementι B S hS f b Z := by
  obtain ⟨k, hk, -⟩ := hb''.existsUnique_lift
    (exceptionalPreimageComplementι B S hS f b Z ≫ strictTransformPullbackToSource B S hS f b)
    (isPullbackDefined_preimageClosedSubspace_of_factorsThrough B S hS f b Z _
      (exceptionalPreimageComplementι B S hS f b Z).hom rfl (𝟙 _) (Category.id_comp _))
  refine ⟨k, (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).hom_ext ?_ ?_⟩
  · rw [Category.assoc, strictTransformBlowUpComparison_comp_toSource, hk]
  · rw [Category.assoc, strictTransformBlowUpComparison_comp_toBlowUp]
    refine (hb.existsUnique_lift
      (exceptionalPreimageComplementι B S hS f b Z ≫
        strictTransformPullbackToSource B S hS f b ≫ f)
      (isPullbackDefined_centre_of_factorsThrough B S hS f b Z _
        (exceptionalPreimageComplementι B S hS f b Z).hom rfl (𝟙 _)
        (Category.id_comp _))).unique ?_ ?_
    · rw [Category.assoc, strictTransformBlowUpClassifying_comp, ← Category.assoc, hk,
        Category.assoc]
    · rw [Category.assoc, ← (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w]

/-! ### The comparison is an isomorphism over the complement -/

/-- **The canonical comparison of Stacks 0864, clause (1) is an isomorphism over the complement
of the exceptional preimage.**  The restriction

```
i⁻¹((X ×_A A') ∖ pr_{A'}^{-1}(b⁻¹Z)) ⟶ (X ×_A A') ∖ pr_{A'}^{-1}(b⁻¹Z)
```

of `i : X'' ⟶ X ×_A A'` is an isomorphism.

The section of
`AlgebraicGeometry.Space.exists_section_strictTransformBlowUpComparison_of_isBlowupAlong` lands
in the inverse image of the complement, and the composite in that order is the identity because
the inclusion of the complement is a monomorphism.  The composite in the other order is the
identity because both it and the identity are morphisms from that inverse image to `X''` over
`X`, along which `f⁻¹Z` pulls back to an effective Cartier divisor, and the universal property of
`b''` has only one such.

This is the general form, for two arbitrary blowups.  The form carrying no hypothesis that
anything is a blowup, which is the one the tag is attached to, is
`AlgebraicGeometry.Space.isIso_fromPreimage_exceptionalPreimageComplement`. -/
theorem isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    IsIso ((exceptionalPreimageComplement B S hS f b Z).1.fromPreimage
      (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom) := by
  obtain ⟨k, hki⟩ :=
    exists_section_strictTransformBlowUpComparison_of_isBlowupAlong B S hS f b Z b'' hb hb''
  set i := strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' with hi
  set U := exceptionalPreimageComplement B S hS f b Z with hU
  have hkhom : k.hom ≫ i.hom = U.1.ι :=
    congrArg (·.hom) hki
  have hPalg : IsAlgebraicSpace B S hS (U.1.preimage i.hom).toFunctor :=
    isAlgebraicSpace_of_iso B S hS
      (Subfunctor.isPullback_preimage i.hom U.1).isoPullback.symm
      (isAlgebraicSpace_pullback B S hS U.1.ι i.hom U.2.1 X''.2
        (strictTransformPullback B S hS f b).2)
  set P : AlgebraicSpaces B S hS := ⟨(U.1.preimage i.hom).toFunctor, hPalg⟩ with hP
  set p : P.1 ⟶ (exceptionalPreimageComplementSpace B S hS f b Z).1 :=
    U.1.fromPreimage i.hom with hp
  -- The section lands in the inverse image of the complement.
  have hrange : Subfunctor.range k.hom ≤ U.1.preimage i.hom := by
    rintro T x ⟨v, rfl⟩
    change i.hom.app T (k.hom.app T v) ∈ U.1.obj T
    exact (congrArg (fun φ => φ.app T v) hkhom) ▸ v.2
  set inv : (exceptionalPreimageComplementSpace B S hS f b Z).1 ⟶ P.1 :=
    Subfunctor.lift k.hom hrange with hinv
  have hinvι : inv ≫ (U.1.preimage i.hom).ι = k.hom := Subfunctor.lift_ι _ _
  have hright : inv ≫ p = 𝟙 (exceptionalPreimageComplementSpace B S hS f b Z).1 := by
    refine (cancel_mono U.1.ι).1 ?_
    rw [Category.assoc, hp, Subfunctor.fromPreimage_ι, ← Category.assoc, hinvι, hkhom,
      Category.id_comp]
  -- The inverse image of the complement is likewise an object of the category of Stacks 085U.
  have hfac : p ≫ U.1.ι = (U.1.preimage i.hom).ι ≫ i.hom := Subfunctor.fromPreimage_ι _ _
  have hb''hom : i.hom ≫ (strictTransformPullbackToSource B S hS f b).hom = b''.hom :=
    congrArg (·.hom) (strictTransformBlowUpComparison_comp_toSource B S hS f b Z b'' hb hb'')
  have hyP : ((ObjectProperty.homMk (U.1.preimage i.hom).ι : P ⟶ X'') ≫ b'').hom =
      ((U.1.preimage i.hom).ι ≫ i.hom) ≫
        (strictTransformPullbackToSource B S hS f b).hom := by
    change (U.1.preimage i.hom).ι ≫ b''.hom = _
    rw [Category.assoc, hb''hom]
  have hPcart : IsPullbackDefined B S hS
      ((ObjectProperty.homMk (U.1.preimage i.hom).ι : P ⟶ X'') ≫ b'')
      (preimageClosedSubspace f Z) :=
    isPullbackDefined_preimageClosedSubspace_of_factorsThrough B S hS f b Z _
      ((U.1.preimage i.hom).ι ≫ i.hom) hyP p hfac
  obtain ⟨c, -, huniq⟩ := hb''.existsUnique_lift
    ((ObjectProperty.homMk (U.1.preimage i.hom).ι : P ⟶ X'') ≫ b'') hPcart
  have hleft : p ≫ inv = 𝟙 P.1 := by
    refine (cancel_mono (U.1.preimage i.hom).ι).1 ?_
    rw [Category.assoc, hinvι, Category.id_comp]
    have h₁ : (ObjectProperty.homMk (p ≫ k.hom) : P ⟶ X'') ≫ b'' =
        (ObjectProperty.homMk (U.1.preimage i.hom).ι : P ⟶ X'') ≫ b'' := by
      refine ObjectProperty.hom_ext _ ?_
      change (p ≫ k.hom) ≫ b''.hom = (U.1.preimage i.hom).ι ≫ b''.hom
      rw [← hb''hom, Category.assoc, ← Category.assoc k.hom, hkhom, ← Category.assoc p, hfac,
        Category.assoc]
    exact congrArg (·.hom) ((huniq _ h₁).trans (huniq _ rfl).symm)
  exact ⟨inv, hleft, hright⟩

/-! ### The strict transform of a blowup is honestly cut out by the supported-sections ideal -/

/-- **For a blowup the strict transform of `X` is honestly cut out by the ideal of sections
supported on the exceptional preimage.**  The defining ideal sheaf of
`AlgebraicGeometry.Space.strictTransform` is
`AlgebraicGeometry.Space.strictTransformIdealSubmodule`, with no hypothesis beyond `b` being the
blowup of `A` in `Z`.

`AlgebraicGeometry.Space.strictTransform` is defined as the infimum of the closed subspaces whose
defining ideal is dominated, chart by chart, by the ideal of supported sections, which in general
need not be cut out by that ideal at all.  For a blowup it is:  the exceptional divisor `b⁻¹Z` is
an effective Cartier divisor on `A'` — one half of the universal property of Stacks 085U,
`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined` — so
`AlgebraicGeometry.Space.strictTransform_exists_of_isEffectiveCartierDivisor` produces a closed
subspace with that defining ideal, and
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_of_definingIdealSheaf_eq` identifies the
infimum with it. -/
theorem definingIdealSheaf_strictTransform_of_isBlowupAlong (hb : IsBlowupAlong B S hS Z b) :
    definingIdealSheaf B S hS (strictTransformPullback B S hS f b)
        (strictTransform B S hS f b (preimageClosedSubspace b Z).1) =
      strictTransformIdealSubmodule B S hS f b (preimageClosedSubspace b Z).1 := by
  obtain ⟨Z₀, hZ₀⟩ := strictTransform_exists_of_isEffectiveCartierDivisor B S hS f b
    (preimageClosedSubspace b Z) hb.isPullbackDefined
  have h : strictTransform B S hS f b (preimageClosedSubspace b Z).1 = Z₀ :=
    Subtype.ext (strictTransformSubfunctor_eq_of_definingIdealSheaf_eq B S hS f b
      (preimageClosedSubspace b Z).1 Z₀ hZ₀)
  rw [h]
  exact hZ₀

/-! ### The direct image along the comparison has no supported sections -/

/-- **The point sets of the two exceptional divisors correspond under the comparison.**  The
inverse image under `|i|` of the point set of the exceptional preimage
`pr_{A'}^{-1}(b⁻¹Z) ⊆ X ×_A A'` is the point set of the exceptional divisor
`b''⁻¹(f⁻¹Z) ⊆ X''`.

This is the subfunctor identity
`preimage_exceptionalPreimage_strictTransformBlowUpComparison_of_isBlowupAlong` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformBlowupComparison.lean` read on points, by
Stacks 03H4 in the form `AlgebraicGeometry.Space.range_pointsMap_preimage_ι`. -/
theorem preimage_exceptionalPreimageSet_strictTransformBlowUpComparison
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    pointsMap B S hS X''.1 (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom ⁻¹'
        exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1 =
      subspacePointSet B S hS X''.1
        (preimageClosedSubspace b'' (preimageClosedSubspace f Z)).1 := by
  rw [← range_pointsMap_preimage_ι B S hS
    (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom
    (exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1)]
  exact congrArg (fun D : Subfunctor X''.1 => Set.range (pointsMap B S hS D.toFunctor D.ι))
    (preimage_exceptionalPreimage_strictTransformBlowUpComparison_of_isBlowupAlong
      B S hS f b Z b'' hb hb'')

/-- **The direct image along the comparison of a strict transform relative to `b''` has no
sections supported on the exceptional preimage.**  For an `𝒪_{X''}`-module `G`, the direct image
along `i : X'' ⟶ X ×_A A'` of the quotient of `G` by its sections supported on the exceptional
divisor `b''⁻¹(f⁻¹Z)` has no nonzero local section supported on `pr_{A'}^{-1}(b⁻¹Z)`.

This is the hypothesis `hQ` of `AlgebraicGeometry.Space.exists_strictTransformSheafIso` at the
target `Q = i_*F''` of Stacks 0864, clause (2), and it is proved here with no hypothesis beyond
the two blowups: the quotient has no sections supported on the exceptional divisor of `b''`
(`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule`, whose
closedness hypothesis holds because that divisor is a closed subspace), the inverse image under
`|i|` of the exceptional preimage is that divisor's point set
(`AlgebraicGeometry.Space.preimage_exceptionalPreimageSet_strictTransformBlowUpComparison`), and
a direct image inherits having no supported sections
(`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_of_preimage`).

The two hypotheses of clause (2) that remain are `Epi q` and `hq`; see the module
documentation. -/
theorem hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'')
    (G : Modules.{u, u} B S hS X''.1 X''.2) :
    HasNoSectionsSupportedIn B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)
      ((modulePushforward B S hS
          (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'')).obj
        (cokernel (supportedSectionsSubmodule B S hS X''.1 X''.2
          (subspacePointSet B S hS X''.1
            (preimageClosedSubspace b'' (preimageClosedSubspace f Z)).1) G).ι)) := by
  have hTclosed : IsClosed (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2 _
      (exceptionalPreimage_isClosedSubspace B S hS f b (preimageClosedSubspace b Z).1
        (preimageClosedSubspace b Z).2).2
  have hT''closed : IsClosed (subspacePointSet B S hS X''.1
      (preimageClosedSubspace b'' (preimageClosedSubspace f Z)).1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS X''.2 _
      (preimageClosedSubspace b'' (preimageClosedSubspace f Z)).2.2
  refine hasNoSectionsSupportedIn_modulePushforward_of_preimage B S hS _ _ hTclosed _ ?_
  rw [preimage_exceptionalPreimageSet_strictTransformBlowUpComparison B S hS f b Z b'' hb hb'']
  exact hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule B S hS X'' _ hT''closed G

/-! ### The comparison for the blowups constructed in Stacks 085Q

Nothing below assumes that anything
*is* a blowup: `b` is the morphism `AlgebraicGeometry.Space.blowUpAlongHom'` constructed in
Stacks 085Q for the centre `Z ⊆ A`, `b''` is the same construction for the centre `f⁻¹Z ⊆ X`, and
that each is the blowup of its centre is the theorem
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`.  What is carried instead is the
construction data of Stacks 085Q, once for each of the two spaces being blown up, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformBlowupComparison.lean`.
-/

section Constructed

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (P : Presentation B S hS A.obj A.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (P'' : Presentation B S hS X.obj X.property)
  (hcU'' : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace f Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace f Z)) P'').relativeProj)
  (hcR'' : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace f Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace f Z)) P'').relativeProj)
  (hcRR'' : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace f Z))
      (isCartesianOnAffineCharts_centreIdeal (preimageClosedSubspace f Z)) P'').relativeProj)

/-- **The canonical comparison of Stacks 0864, clause (1) is an isomorphism over the complement
of the exceptional preimage.**  For `b : A' ⟶ A` the blowing up of `A` in `Z` and
`b'' : X'' ⟶ X` the blowing up of `X` in `f⁻¹Z`, both as *constructed* in Stacks 085Q, the
restriction of the comparison `i : X'' ⟶ X ×_A A'` over the complement of
`pr_{A'}^{-1}(b⁻¹Z)` in `X ×_A A'` is an isomorphism.

That `i` is a closed immersion with image the strict transform of `X` is **not** proved; see the
module documentation. -/
theorem isIso_fromPreimage_exceptionalPreimageComplement :
    IsIso (Subfunctor.fromPreimage
      (exceptionalPreimageComplement B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) Z).1
      (strictTransformBlowUpComparison' B S hS f Z P hcU hcR hcRR P''
        hcU'' hcR'' hcRR'').hom) :=
  isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong B S hS f
    (blowUpAlongHom' Z P hcU hcR hcRR) Z
    (blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')
    (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR)
    (isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')

end Constructed

end AlgebraicGeometry.Space

end
