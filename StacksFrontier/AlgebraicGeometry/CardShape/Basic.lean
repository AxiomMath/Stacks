module

public import StacksFrontier.AlgebraicGeometry.FilteredCardIndex.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.Basic

/-!
# The colimit of [Stacks, Tag 0817] in the shape its statement asks for

[Stacks, Tag 0817] asks for an **indexing preorder in `Type u`**, a diagram of algebra sheaves
over it, and a colimiting cocone with vertex `A`.  What the repository proves about the finite
quasi-coherent subalgebras of `A` is stated over the category
`Stacks.AlgebraicGeometry.FiniteSubalgebras.FiniteSubalgebra A`, a full subcategory of
`CategoryTheory.Subobject A`, which is neither a preorder *type* nor a type in `Type u`.

`Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` already closes that gap in
general: from a filtered, essentially `u`-small index it produces a nonempty directed preorder in
`Type u`.  What it is never applied to is the cocone of tag 0817.  Both of its specialisations to
algebra sheaves hard-code the predicate
`IsQuasicoherent ∧ IsFinite ∧ IsFinitePresentation`, and the objects of tag 0817's diagram are
the finite quasi-coherent *subalgebras* of `A`, which are **not** of finite presentation — so
neither specialisation can be instantiated at the very diagram the tag is about.  This file
supplies the instantiation, at the predicate the subalgebras actually satisfy.

## Main results

* `exists_finite_index_of_isFiltered`:
  `Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` at the predicate
  `IsQuasicoherent ∧ IsFinite` and at `Type u`.  This is the variant of
  `Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_isFiltered` with the finite
  presentation conjunct dropped; see the implementation notes on why it is a new declaration
  rather than an edit there.
* `exists_small_index_finite_of_isColimit`: given that the canonical cocone of the finite
  quasi-coherent subalgebras of an integral quasi-coherent algebra sheaf is colimiting, the
  conclusion of [Stacks, Tag 0817] **in the shape of its statement** — index in `Type u`, nonempty directed
  preorder, diagram, colimiting cocone — with every object of the diagram quasi-coherent and
  finite.  No hypothesis on `X`.
* `exists_small_index_finite_of_affineSections`: the same from the affine sections statement
  alone, again with no hypothesis on `X`.
* `exists_small_index_finite_of_isAffine`: the same, unconditionally, for an affine scheme.

## Where the tag sits, and what is still open

Part (1) of [Stacks, Tag 0817] covers two assertions and both are proved, in
`Stacks.AlgebraicGeometry.FiniteSubalgebras`: directedness as `isFiltered_finiteSubalgebra`,
unconditionally, and the colimit as `nonempty_isColimit_finiteSubalgebraCocone`, for a
quasi-compact and quasi-separated scheme.  Those two declarations are the covering set and carry
the attribute; the declarations below are a repackaging of the colimit into the shape of the
tag's conclusion and are not assertions of the tag, so they carry no attribute.

The algebra-level extension step that the colimit assertion needs — the algebra analogue of
[Stacks, Tag 01PF] — is
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section`.  It
*is* obtained from the module statement of tag 01PF: the construction sending a finite type
quasi-coherent submodule to the subalgebra it generates is
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.genSubalg`.

Part (2) of the tag additionally asks that every object of the diagram be of **finite
presentation**.  Nothing here asserts that, and no subalgebra of `A` need satisfy it; see the
implementation notes.

## Implementation notes

The conclusion asserts `IsQuasicoherent` and `IsFinite` of the objects of the diagram, and not
`IsFinitePresentation`, because the objects *are* the finite quasi-coherent subalgebras of `A`
and those are not finitely presented in general.  Supplying finite presentation means replacing
each subalgebra by an approximating system, which is [Stacks, Tag 086N], and then composing two
filtered colimits.  That composition does **not** follow from the two statements as the
Stacks Project states them.  [Stacks, Tag 086N] is an existential — for each finite `B` *some* directed
system of finite, finitely presented algebras has colimit `B` — and a bare existential provides
no compatibility between the systems chosen for `B` and for a larger `B'`, which is precisely
what a colimit of colimits needs: a morphism out of `B`'s approximation has to be lifted through
`B'`'s.  The Stacks proof supplies that lifting from [Stacks, Tag 01BS].  So the finite
presentation half of tag 0817 is not a packaging question, and the packaging closed here does not
advance it.

`exists_finite_index_of_isFiltered` duplicates the *shape* of
`Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_isFiltered` with one conjunct
removed.  The right form is a single statement over an arbitrary predicate, which is exactly what
`Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` is; the two algebra-sheaf
specialisations beneath it would then be instances of one declaration.  That is an edit to
`FilteredCardIndex/Basic.lean`, which this file does not make.

The universe `u` must be pinned by the *signature* and not left to instance search.  Written with
`[EssentiallySmall.{w} D]` and `w` free, instance search solves the smallness goal at the
universe of `D` itself — at the call site `CategoryTheory.Subobject A` in `Type (u + 1)` — and the
application then fails with `stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`,
which names neither `EssentiallySmall` nor the instance that fired.  Writing
`[EssentiallySmall.{u} D]` after the explicit `A : AlgebraSheaf X` fixes `u` before the instance
goal is formed.  This is the same reason
`Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_isFiltered` exists as a
separate specialisation rather than being inlined at its call sites.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.FiniteSubalgebras

universe v₂ u₂ u

namespace Stacks.AlgebraicGeometry.Tag0817CardShape

variable {X : Scheme.{u}}

/-- **A filtered, essentially `u`-small system of quasi-coherent finite algebra sheaves with
colimit `A` gives a directed system over a preorder in `Type u`.**

This is `Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered` at the predicate
`IsQuasicoherent ∧ IsFinite`, with the universe of the new index pinned to that of the scheme by
the signature.  It is the variant of
`Stacks.FilteredCardIndex.exists_finite_finitePresentation_index_of_isFiltered` needed for
[Stacks, Tag 0817]'s *subalgebra* diagram, whose objects are not of finite presentation. -/
theorem exists_finite_index_of_isFiltered (A : AlgebraSheaf X)
    {D : Type u₂} [Category.{v₂} D] [IsFiltered D] [EssentiallySmall.{u} D]
    {G : D ⥤ AlgebraSheaf X} (t : G ⟶ (Functor.const D).obj A)
    (ht : IsColimit (Cocone.mk A t))
    (hG : ∀ d, (G.obj d).IsQuasicoherent ∧ (G.obj d).IsFinite) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite :=
  Stacks.FilteredCardIndex.exists_directed_index_of_isFiltered t ht
    (fun B => B.IsQuasicoherent ∧ B.IsFinite) hG

/-- **The conclusion of [Stacks, Tag 0817] in the shape its statement asks for, from the colimit
assertion over the finite quasi-coherent subalgebras.**

Let `A` be an integral quasi-coherent sheaf of commutative `𝒪_X`-algebras whose canonical cocone
of finite quasi-coherent subalgebras is colimiting.  Then there are an indexing type in `Type u`,
a nonempty directed preorder on it, a diagram of algebra sheaves over it and a colimiting cocone
with vertex `A`, every object of the diagram being quasi-coherent and finite.

No hypothesis on `X` is used: not quasi-compactness, not quasi-separatedness, not affineness.
Everything the shape of the statement demands beyond
`Stacks.AlgebraicGeometry.FiniteSubalgebras.finiteSubalgebraCocone` is free — the index is
essentially `u`-small through Mathlib's `CategoryTheory.small_subobject` over
`Stacks.UnderWellPowered.wellPowered`, and it is filtered, hence nonempty and directed after
reindexing, by `isFiltered_finiteSubalgebra`.

**No attribute is attached.** The conclusion omits `IsFinitePresentation`, which tag 0817's
`finite_finitely_presented_approximation` label asserts, and the hypothesis
`Nonempty (IsColimit (finiteSubalgebraCocone A))` is not one the tag grants. -/
theorem exists_small_index_finite_of_isColimit (A : AlgebraSheaf X)
    (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral)
    (hcolim : Nonempty (IsColimit (finiteSubalgebraCocone A))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite := by
  obtain ⟨hc⟩ := hcolim
  have : IsFiltered (FiniteSubalgebra A) := isFiltered_finiteSubalgebra A hAqc hAint
  exact exists_finite_index_of_isFiltered A (finiteSubalgebraCocone A).ι hc fun B => B.property

/-- **The conclusion of [Stacks, Tag 0817] in the shape of its statement, from the affine sections
statement alone.**  An integral quasi-coherent sheaf of commutative `𝒪_X`-algebras is a directed colimit,
over an index in `Type u`, of quasi-coherent finite algebra sheaves, as soon as every section
over every affine open comes from a finite quasi-coherent subalgebra.

No hypothesis on `X` is used.  This composes
`nonempty_isColimit_finiteSubalgebraCocone_of_affineSections` with
`exists_small_index_finite_of_isColimit`; the hypothesis `hsec` is discharged, for a
quasi-compact and quasi-separated scheme, by `exists_small_index_finite_of_qcqs` below.

No attribute is attached: this is a repackaging of the colimit assertion into the shape of the
tag's conclusion, not an assertion of the tag, and `hsec` is a hypothesis the tag does not
have. -/
theorem exists_small_index_finite_of_affineSections (A : AlgebraSheaf X)
    (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral)
    (hsec : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (op U),
      ∃ (B : FiniteSubalgebra A) (y : (B.obj : AlgebraSheaf X).right.obj.obj (op U)),
        B.obj.arrow.right.hom.app (op U) y = x) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite :=
  exists_small_index_finite_of_isColimit A hAqc hAint
    (nonempty_isColimit_finiteSubalgebraCocone_of_affineSections A hAqc hAint hsec)

/-- **The conclusion of [Stacks, Tag 0817] in the shape of its statement, for an affine scheme.**  An
integral quasi-coherent sheaf of commutative `𝒪_X`-algebras on an affine scheme is a directed
colimit, indexed by a nonempty directed preorder in `Type u`, of quasi-coherent finite algebra
sheaves.

This is subsumed by `exists_small_index_finite_of_qcqs` below; it is kept because it goes through
the affine-scheme sections statement of
`Stacks.AlgebraicGeometry.SubalgebraAffineSections`, which needs no [Stacks, Tag 01PF].  No
attribute is attached: the declaration is a repackaging of part (1) of the tag, whose covering set
is the two declarations named in the module documentation. -/
theorem exists_small_index_finite_of_isAffine [IsAffine X] (A : AlgebraSheaf X)
    (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite :=
  exists_small_index_finite_of_isColimit A hAqc hAint
    (nonempty_isColimit_finiteSubalgebraCocone_of_isAffine A hAqc hAint)

/-- **The conclusion of part (1) of [Stacks, Tag 0817] in the shape its statement asks for.**  On
a quasi-compact and quasi-separated scheme an integral quasi-coherent sheaf of commutative
`𝒪_X`-algebras is a directed colimit, indexed by a nonempty directed preorder in `Type u`, of
quasi-coherent finite algebra sheaves.

This is `exists_small_index_finite_of_isColimit` with the colimit assertion supplied by
`Stacks.AlgebraicGeometry.FiniteSubalgebras.nonempty_isColimit_finiteSubalgebraCocone`.  No
attribute is attached: the covering set of part (1) of the tag is the two declarations named in
the module documentation, and the conclusion here omits the finite presentation that part (2)
asserts. -/
theorem exists_small_index_finite_of_qcqs [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AlgebraSheaf X) (hAqc : AlgebraSheaf.IsQuasicoherent A) (hAint : A.IsIntegral) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite :=
  exists_small_index_finite_of_isColimit A hAqc hAint
    (nonempty_isColimit_finiteSubalgebraCocone A hAqc hAint)

end Stacks.AlgebraicGeometry.Tag0817CardShape

end
