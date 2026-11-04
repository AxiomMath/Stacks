module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage

/-!
# Properness of blowups, and the image of a space in an admissible blowup

Let `S` be a scheme and let `X` be an algebraic space over `S`.  Two statements about blowups of
`X` are treated here.

The first is that a blowup `b : X' ⟶ X` of `X` in a closed subspace `Z ⊆ X` cut out by an ideal
of finite type is a proper morphism, Stacks 085Z.

The second, Stacks 0F49, concerns a morphism `X ⟶ T` and a morphism `Y ⟶ T` of algebraic spaces
over `S`, an open subspace `U ⊆ X`, and a quasi-compact morphism `V ⟶ X ×_T Y` whose composite
with the first projection factors through `U`.  Writing `Z ⊆ X ×_T Y` for the scheme-theoretic
image of that morphism and `b : X' ⟶ X` for a `U`-admissible blowup, the scheme-theoretic image
of `V ⟶ X' ×_T Y` is the strict transform of `Z` with respect to `b`.

The base algebraic space of the source is written `T` here, the name `B` being taken by the
ambient big fppf site; and `X' ×_T Y` is spelled `(X ×_T Y) ×_X X'`, which is the shape the
strict transform of `StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform` lives over and which
is canonically the same algebraic space.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isBlowupAlong`: a blowup of `X` in a closed subspace of
  finite presentation is proper, given some proper blowup of `X` in that centre.  Stacks 085Z
  itself, with no such hypothesis, is
  `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart`.
* `AlgebraicGeometry.Space.isProper_of_isAdmissibleBlowup` reads the same statement off for a
  `U`-admissible blowup of Stacks 086B.
* `AlgebraicGeometry.Space.isQuasiCompact_of_comp_fiberProductFirst` is step (3) of the source's
  proof of Stacks 0F49: a morphism to `(X ×_T Y) ×_X X'` whose composite with the projection to
  `X ×_T Y` is quasi-compact is itself quasi-compact, because that projection is a base change
  of an admissible blowup, hence proper, hence separated, hence quasi-separated, so that
  Stacks 03KS applies.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient` is the
  half of **Stacks 0F49** that is proved here from upstream inputs: the scheme-theoretic image
  of the lift is contained in the strict transform.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient` is the
  equality asserted by Stacks 0F49.  It carries **no** Stacks 0F49 attribute, because one
  of its hypotheses is the reverse inclusion of its own conclusion; see its docstring.

## What is assumed

Neither statement here is proved unconditionally, and each carries the inputs it is missing as
explicit, named hypotheses.  **A hypothesis-carrying statement is not the tag proved outright**,
and the clause string of the Stacks 0F49 attribute says so.

**The hypotheses below are of two different kinds, and the difference decides where an
attribute may go.**  `hRelativeProj`, `hfac` and `himm` are *upstream*: each is the conclusion
of an earlier tag, and each is strictly weaker than, and logically prior to, the conclusion it
is used to reach.  A statement resting only on those is a conditional proof,
and may carry its tag.  `hdense` is *not* upstream: it is one of the two inclusions making up
the equality of Stacks 0F49, so a statement of that equality resting on `hdense` has half of
its own conclusion among its hypotheses.  Such a statement may not carry the tag, and
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient` does not.

* `hRelativeProj`, in `AlgebraicGeometry.Space.isProper_of_isBlowupAlong`, asks for *some*
  proper blowup of `X` in the given centre.  That is the content of Stacks 085R together with
  the construction of Stacks 085Q, which builds the blowup as the relative `Proj` of the Rees
  algebra and so rests on relative `Proj` for algebraic spaces, Stacks 084A and 084B.  The
  hypothesis is not needed for Stacks 085Z:
  `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart`, which imports this module,
  proves the tag without it.
* `hfac`, in
  `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient`, asks
  that the lift of `V` to `(X ×_T Y) ×_X X'` factor through the strict transform.  In the source
  this is the morphism `V ⟶ Z'` that the proof uses without comment: `V` lies over `U`, the
  blowup is an isomorphism away from its centre by Stacks 085T part (1), and the centre is
  disjoint from `U`, so over `U` the strict transform of `Z` agrees with `Z`.  Stacks 085T is
  not available, for the same reason as above.
* `himm` asks that the image of the strict transform in `(X ×_T Y) ×_X X'` be a closed subspace.
  That is step (1) of the source's proof, which identifies the strict transform as a closed
  subspace of `X' ×_X Z`; the identification of a strict transform with a base change is
  Stacks 0863 part (2).
* `hdense` asks that this image be contained in the scheme-theoretic image of the lift, given
  the quasi-compactness of the lift that this file proves.  This is steps (4) and (5) of the
  source's proof: Stacks 082Z gives that the two agree away from the exceptional divisor, and
  the strict transform has no nonzero sections of its structure sheaf supported on the
  exceptional divisor, which is Stacks 0863 part (3) together with the preamble of the section
  containing Stacks 0862.  The "what is not proved" section of
  `StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform` records that this preamble is exactly
  what the library lacks.  **This hypothesis is the reverse inclusion of the equality of
  Stacks 0F49**, not an upstream statement, which is why only the inclusion theorem and not the
  equality carries the tag.

Nothing is weakened in exchange.  The conclusion of
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient` is one
of the two inclusions making up what Stacks 0F49 asserts, and is tagged as that inclusion and
not as the equality.

## Implementation notes

`AlgebraicGeometry.Space.isProper_of_isBlowupAlong` treats Stacks 085Z through the universal
property, not through the construction.  Being the blowup of `X` in `Z` is
`AlgebraicGeometry.Space.IsBlowupAlong`, finality in the category of
Stacks 085U, so any two blowups of `X` in `Z` are isomorphic over `X` by
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`; properness is invariant under
precomposition with an isomorphism because `AlgebraicGeometry.Space.properProperty` is
stable under base change, hence respects isomorphisms.  So the properness of one blowup in a
given centre is the properness of every blowup in that centre, and the missing input is confined
to the existence half.

The finite-type condition on the ideal cutting out the centre is spelled, as in Stacks 086B and
in `AlgebraicGeometry.Space.IsAdmissibleBlowup`, as finite presentation of the closed immersion
of the centre; it enters only as the antecedent of `hRelativeProj`, which is where the source
uses it.

For Stacks 0F49 the exceptional divisor is `Zc.1.preimage b.hom`, the inverse image of the
centre along the blowup, which is the subspace `E` of the source.  The strict transform is
`AlgebraicGeometry.Space.strictTransform` of Stacks 0862 applied to the scheme-theoretic image
`Z` viewed as an algebraic space over `X`, so it is a closed subspace of `Z ×_X X'`, and
`AlgebraicGeometry.Space.strictTransformInAmbient` is its image in `(X ×_T Y) ×_X X'` under the
morphism induced by the closed immersion of `Z` into `X ×_T Y`.

## References

* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 0F49](https://stacks.math.columbia.edu/tag/0F49)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Properness of a blowup -/

section Properness

variable {X X' : AlgebraicSpaces B S hS}

/-- **A blowup in a finitely presented centre is proper, given some proper blowup in that
centre.**  A blowup `b : X' ⟶ X` of an algebraic space `X` in a closed subspace `Z ⊆ X` whose
closed immersion is of finite presentation is a proper morphism, provided `hRelativeProj`
supplies *some* proper blowup of `X` in `Z`.

This is a special case of
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`, which needs no
`hRelativeProj`.  That theorem lives in
`StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart`, which imports this module, so
it is not available here and the statement keeps its own proof.

Given the hypothesis the conclusion is a consequence of the universal property alone: `b` and
the proper blowup supplied by `hRelativeProj` are both final in the category of Stacks 085U, so
they are isomorphic over `X`, and properness is stable under precomposition with an isomorphism.
In particular the properness of `b` does not depend on which blowup of `X` in `Z` one starts
from. -/
theorem isProper_of_isBlowupAlong (Z : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hfp : IsFinitePresentation B S hS Z.1.ι)
    (hRelativeProj : IsFinitePresentation B S hS Z.1.ι →
      ∃ (X'' : AlgebraicSpaces B S hS) (b'' : X'' ⟶ X),
        IsBlowupAlong B S hS Z b'' ∧ IsProper B S hS b''.hom)
    (hb : IsBlowupAlong B S hS Z b) :
    IsProper B S hS b.hom := by
  obtain ⟨X'', b'', hb'', hproper⟩ := hRelativeProj hfp
  obtain ⟨e, he⟩ := hb.exists_iso hb''
  have h : properProperty B S hS (e.hom ≫ b'') :=
    MorphismProperty.RespectsIso.precomp (properProperty B S hS) e.hom b'' hproper
  rw [he] at h
  exact h

/-- **Stacks 085Z for a `U`-admissible blowup.**  A `U`-admissible blowup of Stacks 086B is a
blowup of `X` in a closed subspace whose closed immersion is of finite presentation, so it is
proper as soon as blowups in such centres exist and are proper.

The hypothesis `hRelativeProj` is the one of
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong`, quantified over the possible centres
because admissibility leaves the centre existentially bound; it stands for Stacks 085R together
with the construction of Stacks 085Q. -/
theorem isProper_of_isAdmissibleBlowup (U : OpenSubspaces B S hS X.1) (b : X' ⟶ X)
    (hRelativeProj : ∀ Z : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Z.1.ι →
      ∃ (X'' : AlgebraicSpaces B S hS) (b'' : X'' ⟶ X),
        IsBlowupAlong B S hS Z b'' ∧ IsProper B S hS b''.hom)
    (hb : IsAdmissibleBlowup B S hS U b) :
    IsProper B S hS b.hom := by
  obtain ⟨Z, hfp, -, hbl⟩ := hb
  exact isProper_of_isBlowupAlong B S hS Z b hfp (hRelativeProj Z) hbl

end Properness

/-! ### The ambient fibre products of Stacks 0F49 -/

section Ambient

variable {T X Y X' : AlgebraicSpaces B S hS}

/-- The first projection `pr_X : X ×_T Y ⟶ X`. -/
noncomputable abbrev fiberProductFirst (p : X ⟶ T) (q : Y ⟶ T) :
    AlgebraicSpaces.fiberProduct B S hS p q ⟶ X :=
  ObjectProperty.homMk (pullback.fst p.hom q.hom)

/-- A closed subspace of an algebraic space over `S`, as an algebraic space over `S`. -/
abbrev closedSubspaceSpace (W : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS W.1) :
    AlgebraicSpaces B S hS :=
  ⟨Z.1.toFunctor, Z.2.1⟩

/-- A closed subspace `Z ⊆ X ×_T Y`, viewed as an algebraic space over `X` through the first
projection.  The strict transform of `Z` with respect to a blowup of `X` is taken along this
morphism. -/
noncomputable abbrev closedSubspaceFirst (p : X ⟶ T) (q : Y ⟶ T)
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1) :
    closedSubspaceSpace B S hS (AlgebraicSpaces.fiberProduct B S hS p q) Z ⟶ X :=
  ObjectProperty.homMk (Z.1.ι ≫ (fiberProductFirst B S hS p q).hom)

/-- The morphism `Z ×_X X' ⟶ (X ×_T Y) ×_X X'` induced by the closed immersion of a closed
subspace `Z ⊆ X ×_T Y`, along which the strict transform of `Z` is viewed inside `X' ×_T Y`.

It is a closed immersion, being a base change of the closed immersion of `Z`; that this is so is
step (1) of the source's proof of Stacks 0F49, and it is not proved here but asked for as the
hypothesis `himm` of
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient`. -/
noncomputable def strictTransformToAmbient (p : X ⟶ T) (q : Y ⟶ T) (b : X' ⟶ X)
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1) :
    (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Z) b).1 ⟶
      (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1 :=
  pullback.lift (f := (fiberProductFirst B S hS p q).hom) (g := b.hom)
    (pullback.fst (closedSubspaceFirst B S hS p q Z).hom b.hom ≫ Z.1.ι)
    (pullback.snd (closedSubspaceFirst B S hS p q Z).hom b.hom)
    ((Category.assoc _ _ _).trans pullback.condition)

/-- **The strict transform of `Z ⊆ X ×_T Y`, viewed inside `(X ×_T Y) ×_X X'`.**  For a blowup
`b : X' ⟶ X` of `X` in a closed subspace `Zc ⊆ X`, this is the image of the strict transform of
Stacks 0862 — a closed subspace of `Z ×_X X'`, taken relative to the exceptional divisor
`Zc.1.preimage b.hom` — under
`AlgebraicGeometry.Space.strictTransformToAmbient`.

This is the right-hand side of Stacks 0F49. -/
noncomputable def strictTransformInAmbient (p : X ⟶ T) (q : Y ⟶ T) (b : X' ⟶ X)
    (Zc : ClosedSubspaces B S hS X.1)
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1) :
    Subfunctor (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1 :=
  Subfunctor.range
    ((strictTransform B S hS (closedSubspaceFirst B S hS p q Z) b
      (Zc.1.preimage b.hom)).1.ι ≫ strictTransformToAmbient B S hS p q b Z)

end Ambient

/-! ### The image of a space in an admissible blowup -/

section Image

variable {T X Y V X' : AlgebraicSpaces B S hS}

/-- **Step (3) of the source's proof of Stacks 0F49.**  Let `b : X' ⟶ X` be a `U`-admissible
blowup and let `v' : V ⟶ (X ×_T Y) ×_X X'` be a morphism whose composite with the projection to
`X ×_T Y` is quasi-compact.  Then `v'` is quasi-compact.

The projection `(X ×_T Y) ×_X X' ⟶ X ×_T Y` is a base change of `b`, so it is proper by
Stacks 04WP and `AlgebraicGeometry.Space.isProper_of_isAdmissibleBlowup`, hence separated, hence
quasi-separated; and a morphism whose composite with a quasi-separated morphism is quasi-compact
is quasi-compact, which is Stacks 03KS.

The hypothesis `hRelativeProj` is inherited from
`AlgebraicGeometry.Space.isProper_of_isAdmissibleBlowup` and stands for Stacks 085R together
with the construction of Stacks 085Q; see the module documentation. -/
theorem isQuasiCompact_of_comp_fiberProductFirst (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (b : X' ⟶ X)
    (hRelativeProj : ∀ Z : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Z.1.ι →
      ∃ (X'' : AlgebraicSpaces B S hS) (b'' : X'' ⟶ X),
        IsBlowupAlong B S hS Z b'' ∧ IsProper B S hS b''.hom)
    (hb : IsAdmissibleBlowup B S hS U b)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : IsQuasiCompact B S hS
      (v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom)) :
    IsQuasiCompact B S hS v' := by
  have hbp : IsProper B S hS b.hom :=
    isProper_of_isAdmissibleBlowup B S hS U b hRelativeProj hb
  have hproj : IsProper B S hS (pullback.fst (fiberProductFirst B S hS p q).hom b.hom) :=
    isProper_pullback_fst B S hS X'.property X.property
      (AlgebraicSpaces.fiberProduct B S hS p q).property b.hom
      (fiberProductFirst B S hS p q).hom hbp
  exact isQuasiCompact_of_comp_of_isQuasiSeparated B S hS v'
    (pullback.fst (fiberProductFirst B S hS p q).hom b.hom) V.property
    (AlgebraicSpaces.fiberProduct B S hS p q).property hv'
    (isQuasiSeparated_of_isSeparated B S hS hproj.1)

/-- **One inclusion of Stacks 0F49, with Stacks 085T and 0863 as explicit hypotheses.**  Let
`X ⟶ T` and `Y ⟶ T` be morphisms of algebraic spaces over `S`, let `U ⊆ X` be an open subspace,
let `v : V ⟶ X ×_T Y` be a morphism whose composite with the first projection factors through
`U`, and let `Z` be the scheme-theoretic image of `v`.  Let `b : X' ⟶ X` be the blowup of `X` in
a closed subspace `Zc` of finite presentation whose points are disjoint from those of `U` — that
is, a `U`-admissible blowup of Stacks 086B.  Then the scheme-theoretic image of the lift
`v' : V ⟶ X' ×_T Y` is **contained in** the strict transform of `Z` with respect to `b`.

Here `X' ×_T Y` is spelled `(X ×_T Y) ×_X X'`, the strict transform of Stacks 0862 is taken of
`Z` viewed as an algebraic space over `X`, and its image in the ambient space is
`AlgebraicGeometry.Space.strictTransformInAmbient`.

Stacks 0F49 asserts that the two are equal.  This is the inclusion of the scheme-theoretic image
in the strict transform, and only that; it is not the tag's equality, and the clause string of
the attribute says which inclusion it is.  The reverse inclusion is the content the library
cannot reach; see
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient`.

Two hypotheses stand for inputs the library does not have, and both are *upstream* of this
conclusion — each is the conclusion of a tag that is missing, and neither mentions the
scheme-theoretic image of the lift:

* `hfac` is the source's morphism `V ⟶ Z'`, which comes from Stacks 085T part (1): the blowup is
  an isomorphism away from its centre, and `V` lies over `U`, which is disjoint from the centre;
* `himm` is step (1) of the source's proof, that the strict transform is a closed subspace of
  `X' ×_X Z`, which is Stacks 0863 part (2).

Given those, the inclusion is the minimality of the scheme-theoretic image, Stacks 082X in the
form `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le`: the strict transform is a
closed subspace through which the lift factors.  Quasi-compactness of `v` is not needed for this
half and so is not carried; the source uses it only in the reverse inclusion. -/
@[stacks 0F49 "the inclusion of the scheme-theoretic image in the strict transform"]
theorem schemeTheoreticImageSubfunctor_le_strictTransformInAmbient (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hfp : IsFinitePresentation B S hS Zc.1.ι)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1)
    (hfac : IsAdmissibleBlowup B S hS U b →
      Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1 →
      Subfunctor.range v' ≤ strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property))
    (himm : IsClosedSubspace B S hS (strictTransformInAmbient B S hS p q b Zc
      (schemeTheoreticImage B S hS v.hom
        (AlgebraicSpaces.fiberProduct B S hS p q).property))) :
    schemeTheoreticImageSubfunctor B S hS v' ≤
      strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property) :=
  schemeTheoreticImageSubfunctor_le B S hS v' himm
    (hfac (isAdmissibleBlowup_of_isBlowupAlong hfp hdisj hbl) hvU)

/-- **The equality asserted by Stacks 0F49, with its reverse inclusion among the hypotheses.**
The setting is that of
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient`, with `v`
quasi-compact as the source requires: the scheme-theoretic image of the lift
`v' : V ⟶ X' ×_T Y` equals the strict transform of `Z` with respect to the `U`-admissible blowup
`b`.

**This declaration carries no Stacks 0F49 attribute, and may not.**  Its hypothesis
`hdense` is the inclusion of the strict transform in the scheme-theoretic image — that is, the
reverse inclusion of its own conclusion — rather than a statement upstream of it, and the
antecedent of `hdense` is discharged inside this proof.  Attaching the tag here would register
Stacks 0F49 as covered by a statement one of whose two halves is assumed.  The attribute sits
instead on the inclusion that is genuinely derived, from hypotheses that are upstream tags.

The declaration is still worth having.  `hfac` and `himm` stand for Stacks 085T part (1) and
Stacks 0863 part (2); `hdense` is steps (4) and (5) of the source's proof, which combine
Stacks 082Z with the absence of nonzero sections of `𝒪_{Z'}` supported on the exceptional
divisor from Stacks 0863 part (3) and the preamble of the section containing Stacks 0862.  When
those land, `hdense` is discharged and this equality — the tag's own conclusion — follows, at
which point the attribute can move here.  Step (3) of the source's proof, the quasi-compactness
of the lift, is *not* assumed: it is supplied by
`AlgebraicGeometry.Space.isQuasiCompact_of_comp_fiberProductFirst` from Stacks 085Z and
Stacks 03KS, and handed to `hdense`. -/
theorem schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hfp : IsFinitePresentation B S hS Zc.1.ι)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (hRelativeProj : ∀ Z : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Z.1.ι →
      ∃ (X'' : AlgebraicSpaces B S hS) (b'' : X'' ⟶ X),
        IsBlowupAlong B S hS Z b'' ∧ IsProper B S hS b''.hom)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (hv : IsQuasiCompact B S hS v.hom)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1)
    (hfac : IsAdmissibleBlowup B S hS U b →
      Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1 →
      Subfunctor.range v' ≤ strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property))
    (himm : IsClosedSubspace B S hS (strictTransformInAmbient B S hS p q b Zc
      (schemeTheoreticImage B S hS v.hom
        (AlgebraicSpaces.fiberProduct B S hS p q).property)))
    (hdense : IsQuasiCompact B S hS v' →
      strictTransformInAmbient B S hS p q b Zc
          (schemeTheoreticImage B S hS v.hom
            (AlgebraicSpaces.fiberProduct B S hS p q).property) ≤
        schemeTheoreticImageSubfunctor B S hS v') :
    schemeTheoreticImageSubfunctor B S hS v' =
      strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property) := by
  have hadm : IsAdmissibleBlowup B S hS U b :=
    isAdmissibleBlowup_of_isBlowupAlong hfp hdisj hbl
  have hqc : IsQuasiCompact B S hS v' :=
    isQuasiCompact_of_comp_fiberProductFirst B S hS p q U b hRelativeProj hadm v'
      (by rw [hv']; exact hv)
  exact le_antisymm
    (schemeTheoreticImageSubfunctor_le_strictTransformInAmbient B S hS p q U Zc b hfp hdisj hbl
      v v' hvU hfac himm)
    (hdense hqc)

end Image

end AlgebraicGeometry.Space

end
