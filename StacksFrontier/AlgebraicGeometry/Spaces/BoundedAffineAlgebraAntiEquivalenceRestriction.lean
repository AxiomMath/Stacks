module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence

/-!
# An anti-equivalence of Stacks 081V restricts to the bounded one

`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is this development's rendering of
Stacks 081V with the tag's unrestricted target, and it is refuted: by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart` a
single affine étale chart whose regular functions are not the zero ring empties it.
`AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` is the same data with the target cut
down to the quasi-coherent algebras satisfying
`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff`, and no argument empties that.

This file proves that the second hypothesis is *weaker* than the first: an unrestricted
anti-equivalence restricts to a bounded one, `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.
toBounded`.  That is what licenses moving a theorem from the unrestricted hypothesis to the
bounded one: a conclusion drawn from the bounded structure is drawn from strictly less, so it is a
strictly stronger theorem.  (Stacks 081W itself no longer rests on either structure: it is
delivered by `AlgebraicGeometry.Space.boundedRelativeSpec` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded`, with no anti-equivalence in its
statement.)

## Main definitions

* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.boundedFunctor` and
  `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.boundedPushforward` are the
  anti-equivalence and the direct-image functor of an unrestricted anti-equivalence, with their
  common target cut down to `AlgebraicGeometry.Space.BoundedQuasicoherentAlgebra`.
* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.boundedEquivalence` is the first of those
  read as an equivalence of categories.
* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.toBounded` is the restriction itself: the
  bounded anti-equivalence structure carried by an unrestricted one.

## Main results

* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.sectionsBelowCutoff`: **given an
  unrestricted anti-equivalence, the size condition holds for every quasi-coherent algebra.**  This
  is the contrapositive of
  `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections`, and
  it is why the restriction costs nothing: cutting the target down to
  `AlgebraicGeometry.Space.BoundedQuasicoherentAlgebra` removes no object the hypothesis allows to
  exist in the first place.

## Implementation notes

**Why the implication is the right way round.**  The target restriction is to a full subcategory
closed under isomorphism (`AlgebraicGeometry.Space.isClosedUnderIsomorphisms_sectionsBelowCutoff`)
and the source side satisfies the bound unconditionally
(`AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff`), so one expects the
restriction of an unrestricted anti-equivalence to land in the bounded target and to stay an
equivalence.  What makes it an equivalence onto the bounded target rather than merely a functor
into it is sharper than that expectation: under the hypothesis `E` the bounded target *is* the
whole of `AlgebraicGeometry.Space.QuasicoherentAlgebra`, by
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.sectionsBelowCutoff`.  Essential surjectivity
of the lift is then the counit of `E` itself, and fullness and faithfulness are inherited from `E`
because `CategoryTheory.ObjectProperty.lift` composed with the inclusion is `E`'s own functor
definitionally.  For the same reason `pushforward_obj` and `pushforward_map` transfer unchanged.

So this is not a second route to the size obstruction and does not weaken it: the obstruction says
there is an algebra the bound excludes, and this says `E` would deny that algebra exists.  The two
together are
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`, which
is proved elsewhere and is not reproved here.

**What is not here.**  The converse fails to be available for the obvious reason: a bounded
anti-equivalence says nothing about the quasi-coherent algebras with at least `B.cutoff` sections
over a chart, and by
`AlgebraicGeometry.Space.not_mem_essImage_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections`
no affine morphism produces one, so no bounded anti-equivalence can be extended to an unrestricted
one over a space that has such an algebra.  Nor is a bounded counterpart of
`AlgebraicGeometry.Space.BaseChangeCompatibility` introduced; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence` record why that should
be a refactor of the unrestricted structure rather than a copy of it.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace AffineAlgebraAntiEquivalence

/-- **An anti-equivalence of Stacks 081V with the tag's unrestricted target forces the size
condition on every quasi-coherent algebra.**  If `E` exists then no quasi-coherent `𝒪_X`-algebra
has `B.cutoff` or more sections over an étale chart of `X`, because one that did would refute `E`
by `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections`.

This is the exact sense in which restricting the target of `E` to
`AlgebraicGeometry.Space.BoundedQuasicoherentAlgebra` discards nothing: under `E` the restriction
is no restriction at all. -/
theorem sectionsBelowCutoff (E : AffineAlgebraAntiEquivalence B S hS)
    {X : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS X) :
    AlgebraSheaf.SectionsBelowCutoff B S hS A.obj := fun V =>
  not_le.1 fun hA =>
    not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections B S hS V A hA ⟨E⟩

/-- The anti-equivalence of `E`, with its target cut down to the quasi-coherent `𝒪_X`-algebras
satisfying the size condition.  The restriction is legitimate by
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.sectionsBelowCutoff`. -/
abbrev boundedFunctor (E : AffineAlgebraAntiEquivalence B S hS) (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ⥤ BoundedQuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift
    (fun A : QuasicoherentAlgebra B S hS X =>
      AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
    (E.equivalence X).functor fun _ => E.sectionsBelowCutoff _

/-- The direct-image functor of `E`, with its target cut down to the quasi-coherent `𝒪_X`-algebras
satisfying the size condition. -/
abbrev boundedPushforward (E : AffineAlgebraAntiEquivalence B S hS)
    (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ⥤ BoundedQuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift
    (fun A : QuasicoherentAlgebra B S hS X =>
      AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
    (E.pushforward X) fun _ => E.sectionsBelowCutoff _

/-- The restriction of `E` to the bounded target is essentially surjective: the preimage of a
bounded algebra is the one `E` already provides, and the isomorphism is the counit of `E`. -/
theorem essSurj_boundedFunctor (E : AffineAlgebraAntiEquivalence B S hS)
    (X : AlgebraicSpaces B S hS) :
    (E.boundedFunctor X).EssSurj :=
  ⟨fun A => ⟨(E.equivalence X).inverse.obj A.obj,
    ⟨(boundedQuasicoherentAlgebraInclusion B S hS X).preimageIso
      ((E.equivalence X).counitIso.app A.obj)⟩⟩⟩

/-- The restriction of `E` to the bounded target is an equivalence: it is essentially surjective
by `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.essSurj_boundedFunctor`, and full and
faithful because composing it with the inclusion of the bounded algebras gives back `E`'s own
functor. -/
theorem isEquivalence_boundedFunctor (E : AffineAlgebraAntiEquivalence B S hS)
    (X : AlgebraicSpaces B S hS) :
    (E.boundedFunctor X).IsEquivalence :=
  have := E.essSurj_boundedFunctor X
  { }

/-- The anti-equivalence of `E` against the bounded target, as an equivalence of categories. -/
def boundedEquivalence (E : AffineAlgebraAntiEquivalence B S hS)
    (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ≌ BoundedQuasicoherentAlgebra B S hS X :=
  haveI := E.isEquivalence_boundedFunctor X
  (E.boundedFunctor X).asEquivalence

/-- **An anti-equivalence of Stacks 081V with the tag's unrestricted target restricts to one with
the bounded target.**  Hence `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` is a
*weaker* hypothesis than `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, and a theorem
proved from the former is stronger than the same theorem proved from the latter, the latter's
hypothesis being refuted outright by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`.
Stacks 081W rests on neither: it is delivered by `AlgebraicGeometry.Space.boundedRelativeSpec` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded`.

Only the two functors change, and only in their codomain; the two identifications with direct image
are `E`'s own, because the inclusion of the bounded algebras is definitionally a left inverse of
`CategoryTheory.ObjectProperty.lift`. -/
def toBounded (E : AffineAlgebraAntiEquivalence B S hS) :
    BoundedAffineAlgebraAntiEquivalence B S hS where
  equivalence := E.boundedEquivalence
  pushforward := E.boundedPushforward
  pushforward_obj := E.pushforward_obj
  pushforward_map := E.pushforward_map
  pushforwardIso X :=
    Functor.fullyFaithfulCancelRight (boundedQuasicoherentAlgebraInclusion B S hS X)
      (E.pushforwardIso X)

end AffineAlgebraAntiEquivalence

end AlgebraicGeometry.Space

end
