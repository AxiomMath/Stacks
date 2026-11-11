module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicate
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel

/-!
# The twisted inverse image of a closed immersion of `FTS S`

Let `i : X ⟶ Y` be a closed immersion of schemes separated and of finite type over a Noetherian
base, that is, a morphism of the category `AlgebraicGeometry.FTS` of [Stacks, Tag 0F42] whose
underlying morphism of schemes is a closed immersion. Then the twisted inverse image `i^!` is
derived sheaf Hom out of the structure sheaf of the closed subscheme,
`i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)`.

This is [Stacks, Tag 0AA2] (Lemma 48.17.4), whose proof in the source reads in full: *"This is a
restatement of Lemma 48.9.7"*, the latter being [Stacks, Tag 0A9X].

## Main definitions

* `Stacks.Duality.IsDerivedSheafHomRightAdjoint` — the conclusion of [Stacks, Tag 0A9X] for one
  closed immersion and one candidate right adjoint: the right adjoint agrees, on bounded-below
  complexes with quasi-coherent cohomology, with the right derived functor of sheaf Hom with
  exact support of [Stacks, Tag 0A76].
* `Stacks.Duality.affineHomQuasiCoherentDerivedPushforward` — the restriction of `Ri_*` to the
  quasi-coherent derived categories for an affine morphism, with no quasi-coherence hypothesis
  supplied.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom` — part (1) of
  [Stacks, Tag 08D5] for an affine morphism, at the derived category in force here.
* `Stacks.Duality.tag0A9XHypothesis` — the conclusion of [Stacks, Tag 0A9X] in the form this
  file consumes, proved rather than assumed.
* `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts` — [Stacks, Tag 0AA2], in the reduction
  form that carries the conclusion of [Stacks, Tag 0A9X] as a hypothesis.
* `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` —
  **[Stacks, Tag 0AA2] with that hypothesis discharged**.

## Implementation notes

The twisted inverse image is taken as an *explicit parameter together with its characterising
hypothesis*: the functor `a` and an adjunction
`Stacks.Duality.affineHomQuasiCoherentDerivedPushforward i.left ⊣ a` are arguments. Nothing is
constructed, chosen, or assumed to exist — the existence of a right adjoint is [Stacks, Tag 0A9E],
which is not available unconditionally in this tree:
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward` is that tag
for a quasi-compact quasi-separated morphism with quasi-compact target, and it still carries
[Stacks, Tag 08DZ] — proved only at `CategoryTheory.HasDerivedCategory.standard`, hence about a
different category — and [Stacks, Tag 09IS], which is not proved at all. This is the idiom of
`Stacks.Duality.sheafyTrace`, and it is
why the statement needs no compactification of `i`. It is also the idiom of [Stacks, Tag 0A9X]
itself: `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` takes the same pair of
arguments, and a right adjoint being unique up to canonical isomorphism, a statement about an
arbitrary one is a statement about `i^!`.

That the derived direct image restricts to the quasi-coherent derived categories at all is *not*
a hypothesis: a closed immersion is an affine morphism, so part (1) of [Stacks, Tag 08D5] applies,
and `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom` reads
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom` at
the model in force. The functor the adjunction is about is therefore the canonical
`Stacks.Duality.affineHomQuasiCoherentDerivedPushforward`, not one depending on a supplied proof.

The content of [Stacks, Tag 0A9X] enters through the predicate
`Stacks.Duality.Tag0A9XHypothesis`, which quantifies that tag's conclusion over all closed
immersions of schemes satisfying the hypotheses it asks for. The *restatement* is proved against
that predicate as a hypothesis `h0A9X` by
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts`: in Situation 48.16.1 those hypotheses --
quasi-compactness and quasi-separatedness of the target, and pseudo-coherence of the immersion --
are automatic, by `AlgebraicGeometry.FTS.compactSpace`,
`AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace` and
`AlgebraicGeometry.FTS.pseudoCoherent_left_of_isClosedImmersion`.

The predicate is then *proved*, not assumed: `Stacks.Duality.tag0A9XHypothesis` is
`Stacks.Duality.tag0A9X` — the content of [Stacks, Tag 0A9X], in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHom.lean`, stated there in
the uniform form this file consumes — instantiated at
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`, the quasi-coherence
proof a closed immersion supplies on its own. So [Stacks, Tag 0AA2] holds with no hypothesis
about [Stacks, Tag 0A9X] at all, which is
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion`. Both forms are kept: the
reduction is the restatement step on its own, independent of how [Stacks, Tag 0A9X] is proved.

Both derived categories are taken here at `HasDerivedCategory.standard`, by the local attribute
below, and that is now a choice of *this* file and not of the tag it consumes:
`Stacks.Duality.IsDerivedSheafHomRightAdjointAtModel` and
`Stacks.Duality.isDerivedSheafHomRightAdjointAtModel_of_compactSpace` carry the model of each
derived category as an instance parameter, so they are available at the locally small model of
[Stacks, Tag 079Q] too. The local attribute carries priority `10000` because the import closure
supplies global instances of the same class, through
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`.

The standard model is not, however, a model at which the hypotheses of this statement can be
met: the `a` and `adj` it takes are a right adjoint of `Ri_*` on `D_QCoh`, and that is produced
by [Stacks, Tag 0A9E] only at the locally small model, Brown representability needing the direct
sums indexed by the morphism universe. A caller holding the [Stacks, Tag 0A9E] adjunction wants
`Stacks.Duality.isDerivedSheafHomRightAdjoint_twistedInverseImage` of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointLocallySmall.lean`, which is
[Stacks, Tag 0A9X] with `a` supplied, rather than this restatement of it for `FTS S`.

## References

* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **Derived direct image along an affine morphism of schemes preserves quasi-coherent
cohomology.** This is part (1) of [Stacks, Tag 08D5] for an affine morphism, read at the standard
derived category; it is what makes `Ri_*` restrict to `D_QCoh` with no hypothesis supplied, for
`i` a closed immersion.

It is the model-free
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`,
which being stated at an arbitrary chosen model of the two derived categories is available at the
model in force here. -/
theorem isQuasicoherent_homology_derivedPushforward_of_isAffineHom {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsAffineHom i] (K : quasiCoherentDerivedCategory Z) (n : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules n).obj
      ((derivedPushforward i).obj K.obj)).IsQuasicoherent :=
  AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom i K.obj K.2 n

/-- **The restriction of `Ri_*` to `D_QCoh` for an affine morphism of schemes**, with no
quasi-coherence hypothesis supplied: it is discharged by
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`. A closed immersion is
affine, so this is the functor `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` whose right adjoint is `i^!`. -/
abbrev affineHomQuasiCoherentDerivedPushforward {Z W : Scheme.{u}} (i : Z ⟶ W) [IsAffineHom i] :
    quasiCoherentDerivedCategory Z ⥤ quasiCoherentDerivedCategory W :=
  quasiCoherentDerivedPushforward i (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i)

/-- The statement of [Stacks, Tag 0A9X], as a hypothesis: for a pseudo-coherent closed immersion
into a quasi-compact and quasi-separated scheme, any right adjoint of the derived direct image
on complexes with quasi-coherent cohomology is derived sheaf Hom out of the structure sheaf of
the closed subscheme, on bounded-below complexes.

The right adjoint appears as an explicit parameter `a` together with the adjunction that
characterises it, so no existence statement is used and nothing is chosen. The derived direct
image it is adjoint to is the canonical
`Stacks.Duality.affineHomQuasiCoherentDerivedPushforward`, a closed immersion being affine; no
quasi-coherence hypothesis is quantified over. -/
def Tag0A9XHypothesis : Prop :=
  ∀ {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i],
    CompactSpace W → QuasiSeparatedSpace W → PseudoCoherent i →
    ∀ (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z),
      (affineHomQuasiCoherentDerivedPushforward i ⊣ a) → IsDerivedSheafHomRightAdjoint i a

/-- **The hypothesis `Stacks.Duality.Tag0A9XHypothesis` holds.** It is
`Stacks.Duality.tag0A9X` — the content of [Stacks, Tag 0A9X] in the uniform form, proved in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHom.lean` — instantiated
at the quasi-coherence proof a closed immersion supplies on its own,
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`. That instantiation is
all there is to it: `Stacks.Duality.affineHomQuasiCoherentDerivedPushforward i` is by definition
`quasiCoherentDerivedPushforward i` at that proof, which is the functor `tag0A9X` quantifies its
`hpush` over.

So nothing in this file assumes [Stacks, Tag 0A9X] any more; see
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion`. -/
theorem tag0A9XHypothesis : Tag0A9XHypothesis.{u} :=
  fun i _ hqc hqs hpc a adj =>
    tag0A9X i hqc hqs hpc (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i) a adj

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4).** In Situation 48.16.1, let `i : X ⟶ Y` be a
morphism of `FTS S` whose underlying morphism of schemes is a closed immersion, and let `a` be a
right adjoint of `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a`, which is `i^!`, is derived sheaf
Hom out of `𝒪_X`:
`i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with quasi-coherent cohomology.

The source proves this by saying that it is a restatement of [Stacks, Tag 0A9X]; the restatement
is exactly the discharge of that tag's hypotheses in Situation 48.16.1, which is what is done
here.

This is the reduction form, which takes the conclusion of [Stacks, Tag 0A9X] as the hypothesis
`h0A9X`. **That hypothesis is no longer hypothetical**: it is `Stacks.Duality.tag0A9XHypothesis`,
and the tag with it discharged is
`Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` below. The reduction is
kept because it is the restatement step on its own, independent of how [Stacks, Tag 0A9X] is
proved.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`.

This reduction form carries the conclusion of [Stacks, Tag 0A9X] as the hypothesis `h0A9X`; it
is superseded by `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion`. -/
theorem isDerivedSheafHomRightAdjoint_of_fts (h0A9X : Tag0A9XHypothesis.{u})
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left]
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
    (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) :
    IsDerivedSheafHomRightAdjoint i.left a :=
  h0A9X i.left inferInstance inferInstance
    (FTS.pseudoCoherent_left_of_isClosedImmersion i) a adj

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4), with nothing about Tag 0A9X assumed.** In
Situation 48.16.1, let `i : X ⟶ Y` be a morphism of `FTS S` whose underlying morphism of schemes
is a closed immersion, and let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a`, which is `i^!`, is derived sheaf Hom out of `𝒪_X`:
`i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with quasi-coherent cohomology.

This is `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts` with its hypothesis `h0A9X`
discharged by `Stacks.Duality.tag0A9XHypothesis`, which is the content of [Stacks, Tag 0A9X]
(`Stacks.Duality.tag0A9X`) read at the canonical restriction of `Ri_*` to the quasi-coherent
derived categories. Two of the three things the tag's proof needs are therefore not hypotheses:
the conclusion of [Stacks, Tag 0A9X], and the preservation of quasi-coherent cohomology by `Ri_*`
(part (1) of [Stacks, Tag 08D5], a closed immersion being affine).

What remains a parameter is `i^!` itself, the functor `a` together with the adjunction `adj`
characterising it, exactly as in `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent`
([Stacks, Tag 0A9X]) and in `Stacks.Duality.sheafyTrace`. Its existence is [Stacks, Tag 0A9E]; a right adjoint being unique up to canonical isomorphism,
the statement about an arbitrary one says the same thing as the statement about the one that tag
produces.

This declaration is not registered as [Stacks, Tag 0AA2] or as clause (5) of
[Stacks, Section 0AU3]: the full statement, with `i^!` produced for every object of `FTS S` and
no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem isDerivedSheafHomRightAdjoint_of_fts_closedImmersion
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left]
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
    (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) :
    IsDerivedSheafHomRightAdjoint i.left a :=
  isDerivedSheafHomRightAdjoint_of_fts tag0A9XHypothesis.{u} i a adj

end Stacks.Duality

end
