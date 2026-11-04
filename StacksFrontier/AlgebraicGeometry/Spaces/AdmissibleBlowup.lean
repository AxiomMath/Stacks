module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# Admissible blowups of algebraic spaces

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `U ⊆ X` be an open
subspace.  A morphism `f : X' ⟶ X` of algebraic spaces is a *`U`-admissible blowup* when there
is a closed subspace `Z ⊆ X` whose inclusion is of finite presentation and whose points are
disjoint from those of `U`, such that `X'` is, over `X`, the blowup of `X` in `Z`.

This is the algebraic-space mirror of the scheme-level `Stacks.Blowup.IsAdmissibleBlowup` of
Tag 080K in `StacksFrontier/AlgebraicGeometry/Blowup/Admissible.lean`, and follows its design: the
predicate is an `abbrev` with its existential witnesses exposed, because the downstream tags
086C-086F all quantify over admissible blowups and have to produce or consume the centre
directly.

## How "the blowup of `X` in `Z`" is said here, and why that is the source statement

The scheme-level file can name the blowup: it writes `Stacks.Blowup.blowUp I` and asks for an
isomorphism `X' ≅ blowUp I` over `X`.  For algebraic spaces the library has the construction and
its universal property, but in separate files, and the predicate below is phrased from the
universal property alone so that it does not drag the construction's parameters in.  Tag 085Q
defines the blowup of an algebraic space as the relative `Proj` of the Rees algebra
`⨁_{n ≥ 0} 𝓘^n`, and
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean` builds it:
`AlgebraicGeometry.Space.blowUpAlong`, `AlgebraicGeometry.Space.blowUpAlongHom` and
`AlgebraicGeometry.Space.exceptionalDivisor` carry Tag 085Q, glued by étale descent from the
relative `Proj` of the Rees algebra on an étale chart, with the descent datum's
equivalence-relation field carried as a parameter.  Tag 084A is registered for the value of the
functor of quadruples; Tag 084B is still a hypothesis, carried by the two cartesian fields of
`AlgebraicGeometry.Space.RelativeProjGlueingData`, which the Rees case proves outright.

So the blowup is named here by its **universal property** instead of by its construction.
Tag 085U states it: for a closed subspace `Z ⊆ X`, let `𝒞` be the full subcategory of
`Spaces/X` consisting of those `Y ⟶ X` for which the inverse image of `Z` is an effective
Cartier divisor on `Y`; then the blowup `b : X' ⟶ X` of `X` in `Z` is a final object of `𝒞`.
Accordingly `AlgebraicGeometry.Space.IsBlowupAlong Z f` says that `f`, viewed as an object of
`𝒞`, is a terminal object of `𝒞`.

This is equivalent to the source's phrasing, and not a weakening of it, in both directions:

* a final object of `𝒞` is isomorphic, over `X`, to any other final object of `𝒞`, and the
  blowup of `X` in `Z` is one such by Tag 085U; so `IsBlowupAlong Z f` gives exactly "`X'` is
  isomorphic to the blowup of `X` in `Z`, compatibly with the morphisms to `X`";
* conversely an object of `Spaces/X` isomorphic over `X` to a final object of `𝒞` is itself a
  final object of `𝒞`.

Both directions are the uniqueness of terminal objects, and nothing beyond Tag 085U is used.
The first is available here as a theorem rather than as a remark:
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso` derives the isomorphism over `X` of any two
blowups of `X` in `Z`, and `AlgebraicGeometry.Space.IsAdmissibleBlowup.exists_iso_blowup`
restates admissibility in the source's own words — there is a finitely presented centre `Z`
disjoint from `U` such that `X'` is isomorphic over `X` to *any* blowup of `X` in `Z`.

The category `𝒞` is `AlgebraicGeometry.Space.CartierOver`, cut out of `Over X` by the object
property `AlgebraicGeometry.Space.IsCartierOver`, which is the Tag 083Y predicate
`AlgebraicGeometry.Space.IsPullbackDefined` applied to the structure morphism.  This is the exact
analogue of the scheme-level `Stacks.AlgebraicGeometry.BlowUpUniversal.IsCartierOver` and
`Stacks.AlgebraicGeometry.BlowUpUniversal.CartierOver` of Tag 0806.

**No `@[stacks 085U]` attribute is attached here, because Tag 085U is registered elsewhere.**
Tag 085U asserts that the blowup *is* final in `𝒞`, and it is proved:
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupFinality.lean` carries the tag, for the blowup
`AlgebraicGeometry.Space.blowUpAlongHom'` of Tag 085Q, with the three `B.Contains` side
conditions on the relative `Proj`s which the construction itself takes and nothing else
assumed.  Its two halves are recovered from it by projection -- membership as
`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined`, which is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreCartier.lean`, and finality as
`AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`, available directly as
`AlgebraicGeometry.Space.existsUnique_lift_blowUpAlongHom'`.

So the predicate `AlgebraicGeometry.Space.IsBlowupAlong` of this file is inhabited by the
constructed blowup, and a result proved for that blowup reaches an arbitrary one through
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso` below; see
`AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupDivisorPullback.lean` (Tag 085X) for that pattern,
whose transport step is
`AlgebraicGeometry.Space.isPullbackDefined_of_iso_over` in the same file.  What this file
supplies is the category `𝒞` whose statement 085U is about, and the consequences of finality
that are stated for an arbitrary blowup.

## Main definitions

* `AlgebraicGeometry.Space.IsCartierOver` is the defining object property of the category `𝒞`
  of Tag 085U: the inverse image of the centre is an effective Cartier divisor.
* `AlgebraicGeometry.Space.CartierOver` is the category `𝒞` itself.
* `AlgebraicGeometry.Space.IsBlowupAlong` says that a morphism to `X` is the blowup of `X` in a
  closed subspace, in the sense of being a terminal object of `𝒞`.
* `AlgebraicGeometry.Space.IsAdmissibleBlowup` is Tag 086B, the predicate of being a
  `U`-admissible blowup.

## Main results

* `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`: any two blowups of `X` in the same closed
  subspace are isomorphic over `X`.
* `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined`: the inverse image of the centre
  along a blowup is an effective Cartier divisor, that is, the exceptional divisor of the blowup
  is an effective Cartier divisor.
* `AlgebraicGeometry.Space.isAdmissibleBlowup_of_isBlowupAlong` recognizes a blowup in a
  finitely presented centre disjoint from `U` as `U`-admissible.
* `AlgebraicGeometry.Space.IsAdmissibleBlowup.exists_iso_blowup` is admissibility in the
  source's phrasing: a finitely presented centre disjoint from `U`, over which `X'` is
  isomorphic to any blowup of `X` in that centre.

## Implementation notes

The centre is a `AlgebraicGeometry.Space.ClosedSubspaces` of Tag 0CYZ, a subfunctor of `X`
together with the proof that it is a closed subspace; its closed immersion into `X` is the
inclusion `CategoryTheory.Subfunctor.ι`, and "of finite presentation" is Tag 03XP part (3),
`AlgebraicGeometry.Space.IsFinitePresentation`, applied to that inclusion.  This is how the
source reads the datum: a closed immersion `Z ⟶ X` of finite presentation.

"`Z` disjoint from `U`" is disjointness of the underlying sets of points, through the library's
`AlgebraicGeometry.Space.subspacePointSet`.  That mirrors the scheme-level file, which asks for
`Disjoint (U : Set X) (I.support : Set X)`.  One could instead ask that the subfunctor
`U ⊓ Z` be dominated by an "empty subfunctor"; disjointness of point sets is used here because
it is stated in the library's own vocabulary and because the bottom of the lattice of
subfunctors is *not* the empty algebraic space — the empty algebraic space has a section over
the empty test scheme — so lattice disjointness would be the wrong condition.

The open subspace `U` is taken bundled, as an `AlgebraicGeometry.Space.OpenSubspaces` of Tag
02YZ, so that openness is carried by the type exactly as `X.Opens` carries it in the
scheme-level file.

## References

* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X X' X'' : AlgebraicSpaces B S hS}

/-! ### The category `𝒞` of Tag 085U -/

/-- An object `Y ⟶ X` of `Spaces/X` lies in the category `𝒞` of Tag 085U, for a closed
subspace `Z ⊆ X`, when the inverse image of `Z` in `Y` is an effective Cartier divisor, that
is, when the pullback of `Z` along the structure morphism is defined in the sense of Tag
083Y. -/
abbrev IsCartierOver (Z : ClosedSubspaces B S hS X.1) : ObjectProperty (Over X) :=
  fun Y => IsPullbackDefined B S hS Y.hom Z

/-- The category `𝒞` of Tag 085U: the full subcategory of `Spaces/X` consisting of those
`Y ⟶ X` for which the inverse image of the centre `Z` is an effective Cartier divisor on
`Y`. -/
abbrev CartierOver (Z : ClosedSubspaces B S hS X.1) :=
  (IsCartierOver B S hS Z).FullSubcategory

/-! ### Being the blowup in a closed subspace -/

/-- A morphism `f : X' ⟶ X` of algebraic spaces **is the blowup of `X` in the closed subspace
`Z`** when it is an object of the category `𝒞` of Tag 085U and is a terminal object there.

By Tag 085U the blowup of `X` in `Z` is a final object of `𝒞`, and a final object of `𝒞` is
isomorphic over `X` to any other; so this says exactly that `X'` is isomorphic to the blowup of
`X` in `Z` compatibly with the morphisms to `X`.  It is phrased this way, and not through the
construction of Tag 085Q -- which the library does have, as
`AlgebraicGeometry.Space.blowUpAlongHom` -- so that it carries none of that construction's
parameters.  The constructed blowup satisfies it:
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupFinality.lean` is Tag 085U. -/
abbrev IsBlowupAlong (Z : ClosedSubspaces B S hS X.1) (f : X' ⟶ X) : Prop :=
  ∃ h : IsCartierOver B S hS Z (Over.mk f),
    Nonempty (IsTerminal (⟨Over.mk f, h⟩ : CartierOver B S hS Z))

namespace IsBlowupAlong

variable {B S hS}

/-- The inverse image of the centre along a blowup is an effective Cartier divisor: the
exceptional divisor of the blowup of `X` in `Z` is an effective Cartier divisor on `X'`.  This
is membership in the category `𝒞` of Tag 085U, which is one half of being its final object. -/
theorem isPullbackDefined {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X}
    (h : IsBlowupAlong B S hS Z f) : IsPullbackDefined B S hS f Z :=
  h.choose

/-- **Any two blowups of `X` in the same closed subspace are isomorphic over `X`.**  Both are
terminal objects of the category `𝒞` of Tag 085U, so they are uniquely isomorphic there; a
morphism of a full subcategory of `Spaces/X` is a morphism of `Spaces/X`, so the isomorphism is
an isomorphism of the sources commuting with the morphisms to `X`.

This is the step that makes `AlgebraicGeometry.Space.IsBlowupAlong` a faithful rendering of the
source's "`X'` is isomorphic to the blowup of `X` in `Z`". -/
theorem exists_iso {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X} {g : X'' ⟶ X}
    (hf : IsBlowupAlong B S hS Z f) (hg : IsBlowupAlong B S hS Z g) :
    ∃ e : X' ≅ X'', e.hom ≫ g = f := by
  obtain ⟨hf', ⟨tf⟩⟩ := hf
  obtain ⟨hg', ⟨tg⟩⟩ := hg
  exact ⟨(Over.forget X).mapIso
      ((ObjectProperty.ι (IsCartierOver B S hS Z)).mapIso (tf.uniqueUpToIso tg)),
    Over.w ((ObjectProperty.ι (IsCartierOver B S hS Z)).map (tf.uniqueUpToIso tg).hom)⟩

end IsBlowupAlong

/-! ### Admissible blowups -/

/-- **Stacks 086B.** A morphism `f : X' ⟶ X` of algebraic spaces over `S` is a
**`U`-admissible blowup**, for an open subspace `U ⊆ X`, when there is a closed subspace
`Z ⊆ X` whose closed immersion into `X` is of finite presentation and whose points are disjoint
from those of `U`, such that `f` exhibits `X'` as the blowup of `X` in `Z`.

Being the blowup of `X` in `Z` is `AlgebraicGeometry.Space.IsBlowupAlong`, the universal
property of Tag 085U: `f` is a terminal object of the category of algebraic spaces over `X` on
which the inverse image of `Z` is an effective Cartier divisor.  Since terminal objects are
unique up to unique isomorphism and the blowup of `X` in `Z` is such a terminal object, this is
the source's "`X'` is isomorphic to the blowup of `X` in `Z`"; see the module documentation, and
`AlgebraicGeometry.Space.IsAdmissibleBlowup.exists_iso_blowup` for that reading as a
theorem. -/
@[stacks 086B]
abbrev IsAdmissibleBlowup (U : OpenSubspaces B S hS X.1) (f : X' ⟶ X) : Prop :=
  ∃ Z : ClosedSubspaces B S hS X.1,
    IsFinitePresentation B S hS Z.1.ι ∧
      Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1) ∧
        IsBlowupAlong B S hS Z f

variable {B S hS}

/-- The blowup of `X` in a finitely presented centre whose points are disjoint from those of
`U` is a `U`-admissible blowup. -/
theorem isAdmissibleBlowup_of_isBlowupAlong {U : OpenSubspaces B S hS X.1}
    {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X}
    (hfp : IsFinitePresentation B S hS Z.1.ι)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1))
    (hb : IsBlowupAlong B S hS Z f) : IsAdmissibleBlowup B S hS U f :=
  ⟨Z, hfp, hdisj, hb⟩

namespace IsAdmissibleBlowup

/-- **A `U`-admissible blowup in the source's own phrasing.**  If `f : X' ⟶ X` is a
`U`-admissible blowup then there is a closed subspace `Z ⊆ X`, of finite presentation over `X`
and with points disjoint from those of `U`, such that `X'` is isomorphic over `X` to *any*
blowup of `X` in `Z`.

The blowup of `X` in `Z` is unique up to isomorphism over `X` once it exists, so this is Tag
086B as the source states it: a finitely presented closed subspace `Z` disjoint from `U` with
`X'` isomorphic to the blowup of `X` in `Z`.  No construction of the blowup is needed to say
it. -/
theorem exists_iso_blowup {U : OpenSubspaces B S hS X.1} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup B S hS U f) :
    ∃ Z : ClosedSubspaces B S hS X.1,
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1) ∧
          ∀ (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X), IsBlowupAlong B S hS Z g →
            ∃ e : X' ≅ Y, e.hom ≫ g = f := by
  obtain ⟨Z, hfp, hdisj, hb⟩ := h
  exact ⟨Z, hfp, hdisj, fun _ _ hg => hb.exists_iso hg⟩

/-- The inverse image of the centre exhibiting a `U`-admissible blowup is an effective Cartier
divisor on the source: the exceptional divisor of an admissible blowup is an effective Cartier
divisor. -/
theorem exists_isPullbackDefined {U : OpenSubspaces B S hS X.1} {f : X' ⟶ X}
    (h : IsAdmissibleBlowup B S hS U f) :
    ∃ Z : ClosedSubspaces B S hS X.1, IsPullbackDefined B S hS f Z := by
  obtain ⟨Z, -, -, hb⟩ := h
  exact ⟨Z, hb.isPullbackDefined⟩

end IsAdmissibleBlowup

end AlgebraicGeometry.Space

end
