module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# The canonical comparison from the blowup of the inverse-image centre

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed subspace
and let `b : A' ⟶ A` be the blowup of `A` in `Z`.  For an algebraic space `f : X ⟶ A` over `A`
let `b'' : X'' ⟶ X` be the blowup of `X` in the inverse image `f⁻¹Z`.  Stacks 0864 part (1)
asserts that the strict transform of `X` — the closed subspace of `X ×_A A'` of Stacks 0862
part (2) — *is* that blowup, and the source's proof says this by producing a canonical morphism
`i : X'' ⟶ X ×_A A'` and asserting that `i` is a closed immersion whose image is the strict
transform.

This file constructs that morphism `i` and proves what can be proved about it without the
étale-local reduction to the scheme case: that `i` exists, that it is the **unique** morphism
`X'' ⟶ X ×_A A'` over `X`, and that it identifies the exceptional divisor of `b''` with the
inverse image in `X ×_A A'` of the exceptional divisor of `b`.

The construction and the general forms of those statements are carried out for arbitrary
blowups, named by the universal property `AlgebraicGeometry.Space.IsBlowupAlong` of Stacks 085U.
The two **tagged** statements, however, are stated for the blowups *constructed* in Stacks 085Q,
`AlgebraicGeometry.Space.blowUpAlongHom'`, so that nothing at all about `b` or `b''` is assumed:
that each is the blowup of its centre is then the theorem
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`.  What the tagged statements do carry is
the construction data of Stacks 085Q itself — an étale presentation of the space being blown up,
the `HasSheafify` universe choice, and the three `B.Contains` side conditions on the relative
`Proj`s that `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.  Nothing is
assumed about the centre beyond its being a closed subspace.

The base algebraic space of the chapter is written `A` here and the blowup `B'` of the chapter
is written `A'`, as in `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean`, the name `B`
being taken by the ambient big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformBlowUpClassifying` is the classifying morphism
  `c : X'' ⟶ A'` of the blowup `b`, obtained from the universal property of `b` applied to
  `b'' ≫ f`.
* `AlgebraicGeometry.Space.strictTransformBlowUpComparison` is the canonical comparison
  `i : X'' ⟶ X ×_A A'` of Stacks 0864 part (1), the morphism with components `b''` and `c`.
* `AlgebraicGeometry.Space.strictTransformBlowUpComparison'` is that comparison for the two
  blowups *constructed* in Stacks 085Q, with no hypothesis that anything is a blowup.

## Main results

* `AlgebraicGeometry.Space.isPullbackDefined_comp_of_isBlowupAlong_preimage`: the inverse image
  of `Z` along `X'' ⟶ X ⟶ A` is an effective Cartier divisor on `X''`.  This is what makes the
  universal property of `b` applicable to `b'' ≫ f`.
* `AlgebraicGeometry.Space.strictTransformBlowUpComparison_comp_toSource` and
  `AlgebraicGeometry.Space.strictTransformBlowUpComparison_comp_toBlowUp`: the two components
  of the comparison.
* `AlgebraicGeometry.Space.existsUnique_strictTransformBlowUpComparison`: **the comparison of
  Stacks 0864 part (1) is the unique morphism `X'' ⟶ X ×_A A'` over `X`.**  This is the precise
  sense in which it is canonical.  It is stated for the blowups of Stacks 085Q; the form taking
  two arbitrary blowups as hypotheses is
  `AlgebraicGeometry.Space.existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong`.
* `AlgebraicGeometry.Space.preimage_exceptionalPreimage_strictTransformBlowUpComparison`: the
  inverse image along the comparison of the preimage in `X ×_A A'` of the exceptional divisor
  of `b` is the exceptional divisor of `b''`, again for the blowups of Stacks 085Q; and
  `AlgebraicGeometry.Space.isPullbackDefined_exceptionalPreimage_strictTransformBlowUpComparison`
  records that it is therefore an effective Cartier divisor on `X''`.
* `AlgebraicGeometry.Space.isIso_strictTransformBlowUpComparison_of_isFlat`: for a flat `f` the
  comparison is an isomorphism, since then `X ×_A A' ⟶ X` is itself the blowup of `X` in
  `f⁻¹Z` by Stacks 085S.

## Implementation notes

The comparison is built from the two universal properties and nothing else.  The inverse image
of `Z` along the composite `X'' ⟶ X ⟶ A` is the inverse image along `b''` of `f⁻¹Z`, by
`CategoryTheory.Subfunctor.preimage_comp`, hence an effective Cartier divisor because `b''` is
the blowup of `X` in `f⁻¹Z`; so the universal property of `b` produces a unique classifying
morphism `c : X'' ⟶ A'` with `c ≫ b = b'' ≫ f`, and the cartesian square
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct` turns the pair `(b'', c)` into
`i : X'' ⟶ X ×_A A'`.

Uniqueness of `i` over `X` is the same universal property read backwards: a morphism
`j : X'' ⟶ X ×_A A'` with `j ≫ pr_X = b''` has `(j ≫ pr_{A'}) ≫ b = b'' ≫ f`, so
`j ≫ pr_{A'} = c` by the uniqueness of the classifying morphism, and then `j = i` because the
square is cartesian.  Note that it is *only* the projection to `X` that has to be prescribed;
the projection to `A'` is determined by it.

The identification of the exceptional divisors is pure subfunctor algebra: the preimage of the
exceptional divisor `b⁻¹Z ⊆ A'` in `X ×_A A'` pulls back along `i` to the preimage of `Z` along
`i ≫ pr_{A'} ≫ b = b'' ≫ f`, which is the preimage along `b''` of `f⁻¹Z`.

## What is not proved

**Clause (1) of Stacks 0864 is not proved here in full**, and nothing here carries a
`@[stacks 0864]` attribute.  Two declarations below cover clause (1) only *in part*: the
existence and uniqueness of the comparison, and its effect on the exceptional
divisors.  What is missing is the geometric half of the
clause: that the comparison `i` is a closed immersion, and that its image is the strict transform
`AlgebraicGeometry.Space.strictTransformSubfunctor` of Stacks 0862 part (2).

Both of the inputs Stacks 0864 is proved from are available.  The universal property of
Stacks 085U is what the present file uses.  The scheme case is Stacks 080E part (1),
`AlgebraicGeometry.strictTransformBlowUpIso` with its closed immersion
`AlgebraicGeometry.strictTransformBlowUpι`, in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/InverseImageCentre.lean`.  What is missing is
the *reduction* of the one to the other: the source says the assertion "may be verified
étale-locally on `X`", and that step is **Stacks 0863 part (2)**, the identification of the
strict transform of an étale chart with the base change of the strict transform.  Part (1) of
Stacks 0863 is available,
`AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEtaleLocalization.lean`, whose own "what is not
proved" section records that part (2) is not; part (2) rests on the compatibility of the
supported-sections subsheaf of Stacks 0859 with pullback along an étale morphism, which is not
stated for algebraic spaces either, and on the strict transform being honestly cut out by the
ideal of supported sections, which the "what is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean` records as unavailable.

Stacks 0863 part (2) is not a weaker form of the clause proved here nor of the clause left
unproved: it is a statement about restricting the strict transform to an étale chart, mentions
neither the blowup of the inverse-image centre nor the comparison `i`, and is what the source
invokes before the scheme case is applied.  The present file anticipates none of it.

Clause (2) of Stacks 0864, the identification of the strict transform of a quasi-coherent
module with a direct image along `i`, is not proved here either; it rests on the space-level
analogue of Stacks 08KS.

## References

* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A X A' X'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1) (b'' : X'' ⟶ X)

/-- **The centre pulls back to an effective Cartier divisor on the blowup of the inverse-image
centre.**  If `b'' : X'' ⟶ X` is the blowup of `X` in the inverse image `f⁻¹Z` of a closed
subspace `Z ⊆ A` along `f : X ⟶ A`, then the inverse image of `Z` along the composite
`X'' ⟶ X ⟶ A` is an effective Cartier divisor on `X''`.

The two closed subspaces have the same underlying subfunctor, by
`CategoryTheory.Subfunctor.preimage_comp`, and the inverse image of `f⁻¹Z` along `b''` is the
exceptional divisor of `b''`. -/
theorem isPullbackDefined_comp_of_isBlowupAlong_preimage
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    IsPullbackDefined B S hS (b'' ≫ f) Z :=
  isEffectiveCartierDivisor_of_subfunctor_eq
    (D' := preimageClosedSubspace b'' (preimageClosedSubspace f Z))
    (Subfunctor.preimage_comp Z.1 b''.hom f.hom) hb''.isPullbackDefined

/-- **The classifying morphism of the blowup of the base.**  The unique morphism
`c : X'' ⟶ A'` with `c ≫ b = b'' ≫ f`, for `b : A' ⟶ A` the blowup of `A` in `Z` and
`b'' : X'' ⟶ X` the blowup of `X` in `f⁻¹Z`.

It exists by the universal property of `b`, Stacks 085U, applied to the morphism `b'' ≫ f`,
along which `Z` pulls back to an effective Cartier divisor by
`AlgebraicGeometry.Space.isPullbackDefined_comp_of_isBlowupAlong_preimage`. -/
def strictTransformBlowUpClassifying (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') : X'' ⟶ A' :=
  (hb.existsUnique_lift (b'' ≫ f)
    (isPullbackDefined_comp_of_isBlowupAlong_preimage B S hS f Z b'' hb'')).choose

/-- The classifying morphism lies over `A`: its composite with the blowup `b` of the base is
`X'' ⟶ X ⟶ A`. -/
theorem strictTransformBlowUpClassifying_comp (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    strictTransformBlowUpClassifying B S hS f b Z b'' hb hb'' ≫ b = b'' ≫ f :=
  (hb.existsUnique_lift (b'' ≫ f)
    (isPullbackDefined_comp_of_isBlowupAlong_preimage B S hS f Z b'' hb'')).choose_spec.1

/-- **The canonical comparison of Stacks 0864 part (1).**  The morphism
`i : X'' ⟶ X ×_A A'` from the blowup of `X` in `f⁻¹Z` to the base change of the blowup of `A`
in `Z`, with components the blowup morphism `b''` and the classifying morphism
`AlgebraicGeometry.Space.strictTransformBlowUpClassifying`.

Stacks 0864 part (1) asserts that this morphism is a closed immersion whose image is the strict
transform of `X`; neither assertion is proved here, see the module documentation. -/
def strictTransformBlowUpComparison (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    X'' ⟶ strictTransformPullback B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift b''
    (strictTransformBlowUpClassifying B S hS f b Z b'' hb hb'')
    (strictTransformBlowUpClassifying_comp B S hS f b Z b'' hb hb'').symm

/-- The comparison is a morphism over `X`: its composite with the projection
`pr_X : X ×_A A' ⟶ X` is the blowup morphism `b'' : X'' ⟶ X`. -/
theorem strictTransformBlowUpComparison_comp_toSource (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' ≫
      strictTransformPullbackToSource B S hS f b = b'' :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_fst _ _ _

/-- The composite of the comparison with the projection `pr_{A'} : X ×_A A' ⟶ A'` is the
classifying morphism of the blowup of the base. -/
theorem strictTransformBlowUpComparison_comp_toBlowUp (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' ≫
        strictTransformPullbackToBlowUp B S hS f b =
      strictTransformBlowUpClassifying B S hS f b Z b'' hb hb'' :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_snd _ _ _

/-- **The comparison morphism of Stacks 0864 part (1) is canonical: it is the one and only
morphism from the blowup of `X` in `f⁻¹Z` to `X ×_A A'` over `X`.**

Only the projection to `X` is prescribed.  The projection to `A'` is then forced: for any
`j : X'' ⟶ X ×_A A'` over `X` the composite `(j ≫ pr_{A'}) ≫ b` equals `b'' ≫ f`, and the
universal property of the blowup `b` of `A` in `Z` has exactly one morphism `X'' ⟶ A'` with
that property, namely `AlgebraicGeometry.Space.strictTransformBlowUpClassifying`.  Since
`X ×_A A'` is the fibre product, prescribing both projections prescribes `j`.

This is the general form, for two arbitrary blowups.  The form carrying no hypothesis that
anything is a blowup, which is the one the tag is attached to, is
`AlgebraicGeometry.Space.existsUnique_strictTransformBlowUpComparison`. -/
theorem existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    ∃! i : X'' ⟶ strictTransformPullback B S hS f b,
      i ≫ strictTransformPullbackToSource B S hS f b = b'' := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  refine ⟨strictTransformBlowUpComparison B S hS f b Z b'' hb hb'',
    strictTransformBlowUpComparison_comp_toSource B S hS f b Z b'' hb hb'', fun j hj => ?_⟩
  refine sq.hom_ext ?_ ?_
  · rw [hj, strictTransformBlowUpComparison_comp_toSource]
  · rw [strictTransformBlowUpComparison_comp_toBlowUp]
    refine (hb.existsUnique_lift (b'' ≫ f)
      (isPullbackDefined_comp_of_isBlowupAlong_preimage B S hS f Z b'' hb'')).unique ?_
      (strictTransformBlowUpClassifying_comp B S hS f b Z b'' hb hb'')
    rw [Category.assoc, ← sq.w, ← Category.assoc, hj]

/-- **The comparison identifies the two exceptional divisors.**  The inverse image, along the
canonical comparison `i : X'' ⟶ X ×_A A'`, of the preimage in `X ×_A A'` of the exceptional
divisor `b⁻¹Z ⊆ A'` is the exceptional divisor `b''⁻¹(f⁻¹Z) ⊆ X''`.

This is what makes the comparison of Stacks 0864 part (1) a comparison *of blowups with their
exceptional divisors*, and is the space-level counterpart of
`AlgebraicGeometry.exceptionalPreimage_eq_preimage_support_comap` of Stacks 080E.  It is pure
subfunctor algebra: `i ≫ pr_{A'} ≫ b = b'' ≫ f` by construction, and taking preimages of `Z`
along the two spellings of that composite gives the two sides.

This is the general form, for two arbitrary blowups.  The form carrying no hypothesis that
anything is a blowup, which is the one the tag is attached to, is
`AlgebraicGeometry.Space.preimage_exceptionalPreimage_strictTransformBlowUpComparison`. -/
theorem preimage_exceptionalPreimage_strictTransformBlowUpComparison_of_isBlowupAlong
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    (exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1).preimage
        (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'').hom =
      (preimageClosedSubspace b'' (preimageClosedSubspace f Z)).1 := by
  have h : strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' ≫
      strictTransformPullbackToBlowUp B S hS f b ≫ b = b'' ≫ f := by
    rw [← Category.assoc, strictTransformBlowUpComparison_comp_toBlowUp,
      strictTransformBlowUpClassifying_comp]
  exact (Subfunctor.preimage_comp ..).symm.trans
    ((congrArg (fun k : X'' ⟶ A => Z.1.preimage k.hom) h).trans (Subfunctor.preimage_comp ..))

/-- **The ambient exceptional preimage pulls back to an effective Cartier divisor along the
comparison.**  The preimage in `X ×_A A'` of the exceptional divisor of `b` is, along the
canonical comparison `i : X'' ⟶ X ×_A A'`, an effective Cartier divisor on `X''`.

By `AlgebraicGeometry.Space.preimage_exceptionalPreimage_strictTransformBlowUpComparison` that
inverse image is the exceptional divisor of `b''`, which is an effective Cartier divisor
because `b''` is the blowup of `X` in `f⁻¹Z`. -/
theorem isPullbackDefined_exceptionalPreimage_strictTransformBlowUpComparison
    (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'') :
    IsPullbackDefined B S hS (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'')
      (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b)
        (preimageClosedSubspace b Z)) :=
  isEffectiveCartierDivisor_of_subfunctor_eq
    (preimage_exceptionalPreimage_strictTransformBlowUpComparison_of_isBlowupAlong
      B S hS f b Z b'' hb hb'')
    hb''.isPullbackDefined

/-- **For a flat `f` the comparison is an isomorphism.**  If `f : X ⟶ A` is flat then the
projection `X ×_A A' ⟶ X` is itself the blowup of `X` in `f⁻¹Z` by Stacks 085S, so it and
`b''` are two blowups of `X` in the same centre; the isomorphism over `X` between them is the
canonical comparison, by its uniqueness.

This is the case of Stacks 0864 part (1) in which the strict transform is all of `X ×_A A'`;
that it is, is not proved here, and the statement is therefore about the comparison and not
about the strict transform. -/
theorem isIso_strictTransformBlowUpComparison_of_isFlat (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z) b'')
    (hflat : IsFlat B S hS f.hom) :
    IsIso (strictTransformBlowUpComparison B S hS f b Z b'' hb hb'') := by
  obtain ⟨e, he⟩ := hb''.exists_iso
    (isBlowupAlong_preimage_of_isPullback_of_isFlat hflat hb
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b))
  have hE : e.hom = strictTransformBlowUpComparison B S hS f b Z b'' hb hb'' :=
    (existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong
      B S hS f b Z b'' hb hb'').unique he
      (strictTransformBlowUpComparison_comp_toSource B S hS f b Z b'' hb hb'')
  rw [← hE]
  infer_instance

/-! ### The comparison for the blowups constructed in Stacks 085Q

Nothing below assumes that
anything *is* a blowup: `b` is the morphism `AlgebraicGeometry.Space.blowUpAlongHom'` constructed
in Stacks 085Q for the centre `Z ⊆ A`, `b''` is the same construction for the centre `f⁻¹Z ⊆ X`,
and that each is the blowup of its centre is the theorem
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`.  What is carried instead is the
construction data of Stacks 085Q, once for each of the two spaces being blown up: an étale
presentation, the `HasSheafify` universe choice, and the three `B.Contains` side conditions on
the relative `Proj`s that `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks
for.  Nothing is assumed about `Z` beyond its being a closed subspace.
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

/-- **The canonical comparison of Stacks 0864 part (1) between the two constructed blowups.**
The morphism `i : X'' ⟶ X ×_A A'` for `b : A' ⟶ A` the blowing up of `A` in `Z` and
`b'' : X'' ⟶ X` the blowing up of `X` in `f⁻¹Z`, both as *constructed* in Stacks 085Q.

This is `AlgebraicGeometry.Space.strictTransformBlowUpComparison` with its two hypotheses
supplied by `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` rather than assumed. -/
def strictTransformBlowUpComparison' :
    blowUpAlong' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'' ⟶
      strictTransformPullback B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) :=
  strictTransformBlowUpComparison B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) Z
    (blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')
    (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR)
    (isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')

/-- **The comparison morphism of Stacks 0864 part (1) is canonical: it is the one and only
morphism from the blowup of `X` in `f⁻¹Z` to `X ×_A A'` over `X`.**

Only the projection to `X` is prescribed; the projection to `A'` is then forced by the universal
property of the blowup of `A` in `Z`, as `X ×_A A'` is the fibre product.  Both blowups are the
ones constructed in Stacks 085Q, so that no hypothesis of the form "`b` is a blowup" is
carried. -/
theorem existsUnique_strictTransformBlowUpComparison :
    ∃! i : blowUpAlong' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'' ⟶
        strictTransformPullback B S hS f (blowUpAlongHom' Z P hcU hcR hcRR),
      i ≫ strictTransformPullbackToSource B S hS f (blowUpAlongHom' Z P hcU hcR hcRR) =
        blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'' :=
  existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong B S hS f
    (blowUpAlongHom' Z P hcU hcR hcRR) Z
    (blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')
    (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR)
    (isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')

/-- **The comparison identifies the two exceptional divisors.**  The inverse image, along the
canonical comparison `i : X'' ⟶ X ×_A A'`, of the preimage in `X ×_A A'` of the exceptional
divisor `b⁻¹Z ⊆ A'` is the exceptional divisor `b''⁻¹(f⁻¹Z) ⊆ X''`.

This is what makes the comparison of Stacks 0864 part (1) a comparison *of blowups with their
exceptional divisors*, and is the space-level counterpart of
`AlgebraicGeometry.exceptionalPreimage_eq_preimage_support_comap` of Stacks 080E.  Both blowups
are the ones constructed in Stacks 085Q, so that no hypothesis of the form "`b` is a blowup" is
carried. -/
theorem preimage_exceptionalPreimage_strictTransformBlowUpComparison :
    (exceptionalPreimage B S hS f (blowUpAlongHom' Z P hcU hcR hcRR)
        (preimageClosedSubspace (blowUpAlongHom' Z P hcU hcR hcRR) Z).1).preimage
        (strictTransformBlowUpComparison' B S hS f Z P hcU hcR hcRR P''
          hcU'' hcR'' hcRR'').hom =
      (preimageClosedSubspace
        (blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')
        (preimageClosedSubspace f Z)).1 :=
  preimage_exceptionalPreimage_strictTransformBlowUpComparison_of_isBlowupAlong B S hS f
    (blowUpAlongHom' Z P hcU hcR hcRR) Z
    (blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')
    (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR)
    (isBlowupAlong_blowUpAlongHom' (preimageClosedSubspace f Z) P'' hcU'' hcR'' hcRR'')

end Constructed

end AlgebraicGeometry.Space

end
