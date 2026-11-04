module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Identification
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.DegreeOnePiece
import Mathlib.Tactic.TFAE
import StacksCore.Tactic.StacksAttribute

/-!
# Projectivity over a base carrying an ample invertible sheaf

Over a scheme `S` on which some invertible module is ample, the eight conditions of Tag 0B45 on
a morphism `f : X ⟶ S` agree: projectivity in the projective-bundle sense, H-projectivity,
properness together with quasi-projectivity, properness together with H-quasi-projectivity,
properness together with an ample invertible module on `X`, properness together with an
`f`-ample invertible module, properness together with an `f`-very ample invertible module, and
the presentation of `X` as the relative homogeneous spectrum over `S` of a quasi-coherent graded
`𝒪_S`-algebra generated in degree one whose degree-one piece is of finite type.

## Main results

* `AlgebraicGeometry.exists_sheafGradedAlgebra_of_isClosedImmersion`: clause (8) for a closed
  subscheme of the relative Proj of a graded algebra generated in degree one with degree-one
  piece of finite type. This is Tag 0801 followed by the source's one-line observation that the
  graded quotient again satisfies clause (8)'s two conditions.
* `AlgebraicGeometry.exists_sheafGradedAlgebra_of_isProjective`: **clause (1) implies clause
  (8)**, by applying the previous result to the closed immersion into a projective bundle that
  clause (1) is.
* `AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`: conditions (1) to (7) of Tag
  0B45. This is the cycle described below, closed on its own; it is the form a consumer that does
  not want clause (8) should use. It carries no Tag 0B45 attribute: seven of the eight conditions
  is a component of the tag, and the whole tag is registered on
  `AlgebraicGeometry.isProjective_tfae_of_exists_isAmple`.
* `AlgebraicGeometry.isProjective_tfae_of_exists_isAmple`: **all eight conditions of Tag 0B45,
  with nothing assumed beyond the source's own hypothesis on the base.** This carries the
  registration.
* `AlgebraicGeometry.isProjective_tfae_of_exists_isAmple'`: the same statement, read off the
  previous one.

Both of the source's citations for clause (8) are now theorems. Tag 0B3U for (8) ⟹ (1) is
`AlgebraicGeometry.isProjective_relativeProj_toBase` of
`StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymSurjective`, and Tag 0801 for
the converse is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer` of
`StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Identification`.

## The route through the eight conditions

Conditions (1) to (4) and (7) are closed into the cycle (1) ⟹ (7) ⟹ (3) ⟹ (4) ⟹ (2) ⟹ (1), and
**every step of it is unconditional**:

* (1) ⟹ (7) is the source's "follows directly from the definitions". A projective morphism is a
  closed immersion `i : X ⟶ 𝐏(ℰ)` over `S` for a quasi-coherent `ℰ` of finite type; a closed
  immersion is an immersion, so `i^* 𝒪_{𝐏(ℰ)}(1)` is `f`-very ample by the very definition of
  Tag 01VM, and `f` is proper because `𝐏(ℰ) ⟶ S` is. Both halves are
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic`:
  `AlgebraicGeometry.IsProjective.isProper` and
  `AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple`.
* (7) ⟹ (3) is Tag 01VN — a relatively very ample module on the source of a quasi-compact
  morphism is relatively ample — together with the fact that a proper morphism is of finite type.
* (3) ⟹ (4) is Tag 087S part (2), `AlgebraicGeometry.isHQuasiProjective_of_isQuasiProjective`,
  which is where the ample module on `S` is used.
* (4) ⟹ (2) is clause (2) of Tag 0BCL,
  `AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`, which this
  repository has with no hypothesis on the base.
* (2) ⟹ (1) is clause (2) of Tag 01W9, `AlgebraicGeometry.IsProjectiveMorphism.isProjective`,
  through the identification `ℙⁿ_S = 𝐏(𝒪_S^{n+1})` of Tag 01OE.

That cycle, together with the two conditions hanging off it below, is
`AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`, which carries no hypothesis beyond
the ample module on `S`; the eight-condition statement is that theorem plus the two implications
attaching clause (8). Consumers that need only conditions (1) to (7) — the closure properties of
Tag 0B46, for instance — should use it, and then assume nothing.

Conditions (5) and (6) hang off (3): (3) ⟺ (5) is Tag 0892 part (1) in one direction and
Tag 01VS in the other, both proved, and (3) ⟺ (6) is the unfolding of
`AlgebraicGeometry.IsQuasiProjective` against the fact that a proper morphism is of finite type.

So clause (1) of Tag 0BCL is **not** assumed, and neither is Tag 0B42, which would otherwise
serve, the first for (1) ⟺ (3) and the second for (3) ⟺ (4), (3) ⟺ (5) and (3) ⟺ (7). In their
place the proof uses the properness of the projective bundle of a quasi-coherent module of finite
type, which is a theorem, and the observation that the very ample module of
condition (7) is read off the definition of condition (1) rather than manufactured from an
immersion into `ℙⁿ_S`. Tag 01VT's (5) ⟹ (3), which a route through Tag 0B42 needs for (3) ⟺ (7),
is therefore not needed here at all.

## How clause (8) is reached

Both of the source's citations for clause (8) are theorems, so **nothing is assumed.**

Tag 0B3U, the source's (8) ⟹ (1), is
`AlgebraicGeometry.isProjective_relativeProj_toBase` of
`StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymSurjective`, under the source's
own hypotheses and nothing else. The three pieces it rests on are the universal property of the
sheafified symmetric algebra over a base that is not affine,
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`; the canonical
graded-algebra map `Sym(𝒜₁) ⟶ 𝒜`, `Stacks.Tag01VMRelativeVeryAmple.canonicalSymHom`; and its
surjectivity on homogeneous sections over the affine opens of the base in every positive degree,
`Stacks.Tag01VMRelativeVeryAmple.eventuallySurjectiveOnAffineSections_canonicalSymHom`. With
those, Tag 07ZK (1) and (2) give the closed immersion `Proj_S(𝒜) ⟶ 𝐏(𝒜₁)` over `S`, and `𝒜₁` is
quasi-coherent of finite type, so it exhibits clause (1).

Tag 0801, the converse, is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer` of
`StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Identification`: a closed subscheme of a
relative Proj with quasi-compact structure morphism *is* the relative Proj of the quotient of the
graded algebra by the degreewise kernel `ℐ_d = ker (𝒜_d ⟶ p_*((i_*𝒪_Z)(d)))`. It carries the
`@[stacks 0801]` attribute and assumes nothing the source does not.

**It is applied at clause (1), not at clause (2), and that is the cheap route.**
`AlgebraicGeometry.IsProjective` is *defined* as a closed immersion `j : X ⟶ 𝐏(ℰ)` over `S` for a
quasi-coherent `ℰ` of finite type, and `𝐏(ℰ)` is `Stacks.SymGraded.schemeProjectiveBundle ℰ _`,
which is `Stacks.AlgebraicGeometry.RelativeProj.relativeProj (Stacks.SymGraded`
`.schemeSheafGradedAlgebra ℰ _)` by definition. So Tag 0801 applies to `j` directly, with no
presentation of `ℙⁿ_S` as a relative Proj and no appeal to Tag 01OE. Its three hypotheses on
`Sym(ℰ)` are proved: generation in degree one over every affine open is
`Stacks.SymGraded.isGeneratedInDegreeOneAt_schemeSheafGradedAlgebra`, quasi-compactness of the
projection is `Stacks.SymGraded.quasiCompact_schemeProjectiveBundleToBase`, and the degree-one
piece is `ℰ` itself by `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso`, so it is of
finite type by `Stacks.SheafOfModules.isFiniteType_of_iso`.

The source's own one-line observation that the graded quotient "works" is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isGeneratedInDegreeOneAt_quotAlgebra` and
`isFiniteType_quotPiece`, used in
`AlgebraicGeometry.exists_sheafGradedAlgebra_of_isClosedImmersion`.

Tag 0801 therefore enters as a theorem, in the generality the source states it, and not as a
hypothesis of the eight-clause statements.

## Implementation notes

Clause (8) identifies `X` with `Proj_S(𝒜)` by an isomorphism over `S` rather than by an equality
of schemes, which is how the source's "`X = Proj_S(𝒜)`" is read everywhere in this repository.
The graded algebra is `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, whose
homogeneous pieces are quasi-coherent by one of its fields, so quasi-coherence of `𝒜` is not a
separate hypothesis; generation in degree one is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne`, which is the source's
"generated by `𝒜₁` over `𝒜₀`" — the degree-zero piece of a `SheafGradedAlgebra` is an arbitrary
quasi-coherent module, not the structure sheaf, so nothing is lost there.

"`f` is of finite type" is the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`, the spelling of Tag 01T1 that this repository uses throughout.

Invertibility of the module quantified over in clauses (5), (6) and (7) is existentially bound
as data and reinstated as a local instance, because there is nothing for instance synthesis to
key on while the module is being quantified over. Clause (6) is written at the invertibility
spelling of `AlgebraicGeometry.IsQuasiProjective`, so that (3) ⟺ (6) is the unfolding of a
conjunction.

`AlgebraicGeometry.isProjective_tfae_of_exists_isAmple'` has the same statement and the same
hypothesis as `AlgebraicGeometry.isProjective_tfae_of_exists_isAmple`; the two were once
distinguished by how much of the source's apparatus each assumed, and are no longer. Both used to
take `h0801`, Tag 0801 as a hypothesis, and so could carry no Tag 0B45 attribute, a tag counting
only on a declaration proved under the source's own hypotheses. **That input is now discharged**:
Tag 0801 is proved in full generality as
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer`, `h0801` is
gone from both, and the registration for the whole tag is on
`AlgebraicGeometry.isProjective_tfae_of_exists_isAmple`, the eight-condition equivalence.

## References

* [Stacks Project, Tag 0B45](https://stacks.math.columbia.edu/tag/0B45)
* [Stacks Project, Tag 0B42](https://stacks.math.columbia.edu/tag/0B42)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 0B3U](https://stacks.math.columbia.edu/tag/0B3U)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace AlgebraicGeometry

/-! ### Clause (8), from a closed subscheme of a relative Proj generated in degree one -/

/-- **A closed subscheme of a relative Proj generated in degree one exhibits clause (8) of
Stacks Tag 0B45.** If `A₀` is a quasi-coherent graded `𝒪_T`-algebra generated in degree one over
every affine open of the base, with `A₀₁` of finite type and `Proj_T(A₀) ⟶ T` quasi-compact, and
`j : Z ⟶ Proj_T(A₀)` is a closed immersion, then `Z` is the relative Proj over `T` of a
quasi-coherent graded algebra which is again generated in degree one and has degree-one piece of
finite type.

This is Stacks Tag 0801 — `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal`
`.exists_iso_projQuotient_twistKer`, which needs only the quasi-compactness — followed by the
source's one-line observation that the graded quotient "works", which is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isGeneratedInDegreeOneAt_quotAlgebra` and
`isFiniteType_quotPiece`. The twists are not a hypothesis:
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` produces a `TwistData` for
every quasi-coherent graded algebra on every scheme with no hypothesis, which is Tag 01NR's
existence assertion. -/
theorem exists_sheafGradedAlgebra_of_isClosedImmersion {T : Scheme.{u}}
    (A₀ : SheafGradedAlgebra.{u} T)
    (hgen : ∀ U : T.Opens, IsAffineOpen U → A₀.IsGeneratedInDegreeOneAt U)
    (hfin : (A₀.piece 1).IsFiniteType) [QuasiCompact (relativeProj A₀).toBase]
    {Z : Scheme.{u}} (j : Z ⟶ (relativeProj A₀).scheme) (hj : IsClosedImmersion j) :
    ∃ A : SheafGradedAlgebra.{u} T,
      Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A ∧
        (A.piece 1).IsFiniteType ∧
        ∃ e : Z ≅ (relativeProj A).scheme,
          e.hom ≫ (relativeProj A).toBase = j ≫ (relativeProj A₀).toBase := by
  have := hj
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer A₀
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A₀) j
  refine ⟨Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra A₀ _, fun U hU => ?_,
    Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isFiniteType_quotPiece A₀ _ 1 hfin,
    e, ?_⟩
  · exact SheafGradedAlgebra.adjoin_grading_one_eq_top _ U
      (Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isGeneratedInDegreeOneAt_quotAlgebra
        A₀ _ U hU (hgen U hU))
  · rw [← Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.projQuotientHom_comp_toBase A₀ _,
      ← Category.assoc, he]

/-- **Stacks Tag 0B45, clause (1) implies clause (8).** A projective morphism exhibits its source
as the relative homogeneous spectrum of a quasi-coherent graded `𝒪_S`-algebra generated in degree
one whose degree-one piece is of finite type.

`AlgebraicGeometry.IsProjective` *is* a closed immersion `j : X ⟶ 𝐏(ℰ)` over `S` for a
quasi-coherent `ℰ` of finite type, and `𝐏(ℰ)` *is* `Proj_S(Sym(ℰ))` by definition
(`Stacks.SymGraded.schemeProjectiveBundle`), so no presentation of projective space as a relative
Proj is needed: `exists_sheafGradedAlgebra_of_isClosedImmersion` applies to `j` at once. Its three
hypotheses on `Sym(ℰ)` are proved —
`Stacks.SymGraded.isGeneratedInDegreeOneAt_schemeSheafGradedAlgebra`,
`Stacks.SymGraded.quasiCompact_schemeProjectiveBundleToBase`, and, for the degree-one piece,
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso`, which identifies `Sym¹(ℰ)` with `ℰ`. -/
@[stacks 0B45 "clause (8), reached from clause (1)"]
theorem exists_sheafGradedAlgebra_of_isProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsProjective f) :
    ∃ A : SheafGradedAlgebra.{u} S,
      Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A ∧
        (A.piece 1).IsFiniteType ∧
        ∃ e : X ≅ (relativeProj A).scheme, e.hom ≫ (relativeProj A).toBase = f := by
  replace hf : ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
      (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
      (i : X ⟶ (Stacks.SymGraded.schemeProjectiveBundle E hqc).scheme),
      IsClosedImmersion i ∧
        i ≫ (Stacks.SymGraded.schemeProjectiveBundle E hqc).toBase = f := hf
  obtain ⟨E, hEqc, hEft, hqc, j, hj, hjf⟩ := hf
  let := hEqc
  let := hEft
  have : QuasiCompact (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase :=
    Stacks.SymGraded.quasiCompact_schemeProjectiveBundleToBase E hqc
  have hfin : ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece 1).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso (Scheme.Modules.symmetricAlgebraGenIso S E)
  obtain ⟨A, hgen, hft, e, he⟩ := exists_sheafGradedAlgebra_of_isClosedImmersion
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)
    (fun U hU => Stacks.SymGraded.isGeneratedInDegreeOneAt_schemeSheafGradedAlgebra E hqc hU)
    hfin j hj
  exact ⟨A, hgen, hft, e, he.trans hjf⟩

/-! ### The criteria -/

/-- A proper morphism with a relatively ample invertible module is quasi-projective. -/
private theorem isQuasiProjective_and_isProper_of_isRelativelyAmple {X S : Scheme.{u}}
    (f : X ⟶ S) (hp : IsProper f) (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L)
    (h : letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L) :
    IsQuasiProjective f ∧ IsProper f :=
  have := hp
  ⟨⟨⟨inferInstance, inferInstance⟩, L, hL, h⟩, hp⟩

/-- **Conditions (1) to (7) of Stacks Project, Tag 0B45, with nothing assumed.** Let `S` be a
scheme carrying an ample invertible module and let `f : X ⟶ S` be a morphism of schemes. The
following are equivalent:

1. `f` is projective;
2. `f` is H-projective;
3. `f` is quasi-projective and proper;
4. `f` is H-quasi-projective and proper;
5. `f` is proper and `X` carries an ample invertible module;
6. `f` is proper and carries an `f`-ample invertible module;
7. `f` is proper and carries an `f`-very ample invertible module.

This is the cycle (1) ⟹ (7) ⟹ (3) ⟹ (4) ⟹ (2) ⟹ (1) with (5) and (6) hung off (3); see the
module documentation for each step. No hypothesis beyond the ample module on `S` enters, so this
is the form in which the criteria are usable by a caller that does not want clause (8) — Tag
0B46's closure properties, for instance, which consume exactly conditions (2) and (5).

Tag 0B45 asserts the equivalence of **eight** conditions; this is the equivalence of the first
seven, which is a component of the tag and not the tag.

No `@[stacks 0B45]` attribute here, deliberately. Tag 0801, which the eight-condition statement
needs, is proved in full generality as
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer`, and the
whole tag is registered on `AlgebraicGeometry.isProjective_tfae_of_exists_isAmple` below, which
assumes nothing beyond the source's hypothesis on the base. A tag goes only on a declaration
stating the whole tag, and this theorem is a component of it. It is the cycle closed on its own,
and a consumer that does not need clause (8) should use it. -/
theorem isProjective_tfae_seven_of_exists_isAmple
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    List.TFAE
      [IsProjective f,
        IsProjectiveMorphism f,
        IsQuasiProjective f ∧ IsProper f,
        IsHQuasiProjective f ∧ IsProper f,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Ample.IsAmple X L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L),
            letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L := hL
            Stacks.RelativeAmple.IsRelativelyAmple f L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L] := by
  obtain ⟨M, hM, hSample⟩ := hS
  have : Stacks.Ample.IsInvertibleModule S M := hM
  tfae_have 1 → 7 := fun h => ⟨h.isProper, h.exists_isRelativelyVeryAmple⟩
  tfae_have 7 → 3 := by
    rintro ⟨hp, L, hL, hvamp⟩
    have : Stacks.Ample.IsInvertibleModule X L := hL
    exact isQuasiProjective_and_isProper_of_isRelativelyAmple f hp L hL
      ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp
        (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f L inferInstance
          hvamp))
  tfae_have 3 → 4 := fun h => ⟨isHQuasiProjective_of_isQuasiProjective f M hSample h.1, h.2⟩
  tfae_have 2 → 1 := IsProjectiveMorphism.isProjective
  tfae_have 2 ↔ 4 := isProjectiveMorphism_iff_isHQuasiProjective_and_isProper
  tfae_have 4 → 3 := fun h => ⟨isQuasiProjective_of_isHQuasiProjective f h.1, h.2⟩
  tfae_have 3 → 5 := fun h => ⟨h.2, exists_isAmple_of_isQuasiProjective f M hSample h.1⟩
  tfae_have 5 → 3 := by
    rintro ⟨hp, hL⟩
    have := hp
    exact ⟨isQuasiProjective_of_isHQuasiProjective f
      (isHQuasiProjective_of_exists_isAmple f inferInstance inferInstance hL), hp⟩
  tfae_have 3 ↔ 6 := by
    refine ⟨fun h => ⟨h.2, h.1.2⟩, ?_⟩
    rintro ⟨hp, L, hL, hamp⟩
    exact isQuasiProjective_and_isProper_of_isRelativelyAmple f hp L hL hamp
  tfae_finish

/-- **Stacks Project, Tag 0B45.** Let `S` be a scheme carrying an ample invertible module and let
`f : X ⟶ S` be a morphism of schemes. The following are equivalent:

1. `f` is projective;
2. `f` is H-projective;
3. `f` is quasi-projective and proper;
4. `f` is H-quasi-projective and proper;
5. `f` is proper and `X` carries an ample invertible module;
6. `f` is proper and carries an `f`-ample invertible module;
7. `f` is proper and carries an `f`-very ample invertible module;
8. `X` is, over `S`, the relative homogeneous spectrum of a quasi-coherent graded `𝒪_S`-algebra
   generated in degree one over its degree-zero part whose degree-one piece is of finite type.

**Nothing is assumed beyond the source's own hypothesis on the base.** Conditions (1) to (7) are
`AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`; (8) ⟹ (1) is the source's
citation Tag 0B3U, `AlgebraicGeometry.isProjective_relativeProj_toBase`; and (1) ⟹ (8) is the
source's other citation, Tag 0801, applied to the closed immersion `X ⟶ 𝐏(ℰ)` that clause (1)
*is*, which is `AlgebraicGeometry.exists_sheafGradedAlgebra_of_isProjective` above. -/
@[stacks 0B45]
theorem isProjective_tfae_of_exists_isAmple
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    List.TFAE
      [IsProjective f,
        IsProjectiveMorphism f,
        IsQuasiProjective f ∧ IsProper f,
        IsHQuasiProjective f ∧ IsProper f,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Ample.IsAmple X L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L),
            letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L := hL
            Stacks.RelativeAmple.IsRelativelyAmple f L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L,
        ∃ A : SheafGradedAlgebra.{u} S,
          Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A ∧
            (A.piece 1).IsFiniteType ∧
            ∃ e : X ≅ (relativeProj A).scheme,
              e.hom ≫ (relativeProj A).toBase = f] := by
  have h7 := isProjective_tfae_seven_of_exists_isAmple f hS
  tfae_have 1 ↔ 2 := h7.out 1 2
  tfae_have 1 ↔ 3 := h7.out 1 3
  tfae_have 1 ↔ 4 := h7.out 1 4
  tfae_have 1 ↔ 5 := h7.out 1 5
  tfae_have 1 ↔ 6 := h7.out 1 6
  tfae_have 1 ↔ 7 := h7.out 1 7
  tfae_have 1 → 8 := exists_sheafGradedAlgebra_of_isProjective
  tfae_have 8 → 1 := by
    rintro ⟨A, hgen, hfin, e, he⟩
    have h := IsProjective.comp_iso e (isProjective_relativeProj_toBase A hgen hfin)
    rw [he] at h
    exact h
  tfae_finish

/-- **Stacks Project, Tag 0B45.** The same eight conditions as
`AlgebraicGeometry.isProjective_tfae_of_exists_isAmple`, under the same hypothesis.

The two declarations were distinguished by how much of the source's apparatus each assumed; now
that clause (1) of Tag 0BCL, Tag 01VT's (5) ⟹ (3) and Tag 0801 are all discharged, the statements
agree and neither assumes anything. -/
-- No second `@[stacks 0B45]` here: this is the previous theorem restated, and the registration
-- belongs on the declaration that proves it.
theorem isProjective_tfae_of_exists_isAmple'
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : ∃ (M : S.Modules) (hM : Stacks.Ample.IsInvertibleModule S M),
      letI : Stacks.Ample.IsInvertibleModule S M := hM
      Stacks.Ample.IsAmple S M) :
    List.TFAE
      [IsProjective f,
        IsProjectiveMorphism f,
        IsQuasiProjective f ∧ IsProper f,
        IsHQuasiProjective f ∧ IsProper f,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Ample.IsAmple X L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L),
            letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
              X.ringCatSheaf.2 L := hL
            Stacks.RelativeAmple.IsRelativelyAmple f L,
        IsProper f ∧
          ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
            letI : Stacks.Ample.IsInvertibleModule X L := hL
            Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L,
        ∃ A : SheafGradedAlgebra.{u} S,
          Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A ∧
            (A.piece 1).IsFiniteType ∧
            ∃ e : X ≅ (relativeProj A).scheme,
              e.hom ≫ (relativeProj A).toBase = f] :=
  isProjective_tfae_of_exists_isAmple f hS

end AlgebraicGeometry

end
