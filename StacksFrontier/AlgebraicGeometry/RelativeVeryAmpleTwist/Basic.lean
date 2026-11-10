module

public import StacksFrontier.AlgebraicGeometry.ChartBasis.Basic

/-!
# Relative very ampleness, Stacks Tag 01VM, as a predicate

Stacks Tag 01VM reads: *there exist a quasi-coherent `𝒪_S`-module `E` and an immersion
`i : X ⟶ 𝐏(E)` over `S` such that `L ≅ i^* 𝒪_{𝐏(E)}(1)`.* Three further tags bottom out in it —
both labels of Tag 01VU have it as their entire right-hand side, and clauses (3) and (4) of
Tag 01VT's six-way `List.TFAE` are the same predicate — so until it exists over library names
those labels are *unstatable*, not merely unproved.

**Both objects the definition names are now constructed**, and Stacks Tag 01VM stated at them,
with the tag, is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` in `DegreeOne.lean`; it implies
the predicate below, by `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_isDegreeOneTwist`. What
this file supplies is the weaker, purely local predicate and Stacks Tag 01VN's content against
it. The rest of this documentation is the measurement as it stood when only one of the two was
available.

* `𝐏(E)` **is** constructed, over an arbitrary base: it is
  `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of
  `Stacks.SymGraded.schemeSheafGradedAlgebra E hqc`, equivalently
  `Stacks.SymGraded.schemeProjectiveBundle`, and its one hypothesis
  `Stacks.SymGraded.IsQuasicoherentPieces E` is discharged for every quasi-coherent `E` by
  `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`. That is `symAlgebra` below.
* `𝒪_{𝐏(E)}(1)` **is too, as of
  `Stacks.AlgebraicGeometry.ChartCocycleRigidity.symGluedTwistOne`**, with no hypothesis beyond
  quasi-coherence of `E`. The paragraph this replaces said it was not, on the ground that naming
  it as the source does needs the glued graded algebra of Stacks Tag 01NR, a value of
  `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, of which none is constructed anywhere
  in either tree. That is still true of `TwistData`, and it is not what the definition needs: the
  degree-one glued twist alone suffices, and degree-one rigidity makes
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle (Sym(E)) 1` unconditional.

The choice made in this file is therefore *how to quantify over* the twist rather than name it.
The decision taken here, and why, is in the implementation notes: the twist is quantified
over as an invertible module on `𝐏(E)` that is a degree-one twist **in the only sense any
consumer uses**, namely that over each affine open `V` of the base it agrees with the absolute
`𝒪(1)` of `Proj(Sym(E)(V))` under the twist-datum-free chart identification
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`.

## Main definitions

* `Stacks.Tag01VMRelativeVeryAmple.symAlgebra`: `Sym(E)` as graded-algebra data on the base, for
  a quasi-coherent `E`, so that `𝐏(E)` is `relativeProj (symAlgebra E)`.
* `Stacks.Tag01VMRelativeVeryAmple.IsDegreeOneTwist`: an `𝒪_{𝐏(A)}`-module is a *degree-one
  twist* of a relative `Proj` when its restriction to the inverse image of every affine open `V`
  of the base is the absolute twist `𝒪(1)` on `Proj(A(V))`, transported along the chart
  identification.
* `Stacks.Tag01VMRelativeVeryAmple.IsRelativelyVeryAmple`: **Stacks Tag 01VM.**

## Main results

* `Stacks.Tag01VMRelativeVeryAmple.isRelativelyVeryAmple_of_immersion`: the introduction rule —
  a quasi-coherent `E`, a degree-one twist on `𝐏(E)`, an immersion over the base and an
  isomorphism give relative very ampleness. This is the form the producing directions of
  Tags 01VT and 01VU meet.
* `Stacks.Tag01VMRelativeVeryAmple.isDegreeOneTwist_piece_one` and
  `isRelativelyVeryAmple_of_hasRelativeVeryAmpleTwist`: **the comparison with the narrow
  predicate already in the tree.** A twist datum's degree-one piece is a degree-one twist, so
  `Stacks.Tag01VNChartBasis.HasRelativeVeryAmpleTwist` implies `IsRelativelyVeryAmple`.
* `Stacks.Tag01VMRelativeVeryAmple.isBasisNonvanishing_preimage_of_isDegreeOneTwist`: clause (3)
  of Stacks Tag 01Q3 passes from the affine chart to the inverse image of its affine open for
  *any* degree-one twist, not only for the degree-one piece of a twist datum.
* `Stacks.Tag01VMRelativeVeryAmple.hasRelativeBasisImmersion_of_isRelativelyVeryAmple`: relative
  very ampleness gives `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion`.
* `Stacks.Tag01VMRelativeVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple`: **the content of
  Stacks Tag 01VN against this predicate**, on `Stacks.Tag01VNChartBasis.ProjOneBasisClause` as
  its only premise — the same single premise the narrow form already carried. So widening the
  hypothesis costs nothing downstream.

## Implementation notes

**The shape is a `Prop`-valued `def` with invertibility as an instance binder, matching
`Stacks.RelativeAmple.IsRelativelyAmple`** (`../RelativeAmple/Basic.lean:161`), and not a class
and not a structure. All three of those tags use the predicate as one side of a biconditional,
where nothing is synthesised and no witness is projected out by name, so synthesis buys nothing and
bundled data would have to be destructured at every use. Invertibility of `L` is an instance
binder rather than a conjunct because that is what the source does — Tag 01VM's preamble is
"let `L` be an invertible `𝒪_X`-module", not "`L` is invertible and …" — and because the
predicate then composes with relative ampleness, which makes the same trade. The body does not
use the instance; `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` is written the same way
for the same reason.

**Why the twist is quantified over by its chart behaviour and not by a twist datum.** The
alternative, taken by `Stacks.Tag01VNChartBasis.HasRelativeVeryAmpleTwist`, is to quantify over a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` and use its degree-one piece. The
descendant cone decides against it. Every consumer of Tag 01VM in those three tags either

* *consumes* it — Tag 01VN, hence (2) ⟹ (1) of Tag 01VU and (3) ⟹ (2) of Tag 01VT — and so wants
  the predicate as weak as honesty allows; or
* *produces* it — (5) ⟹ (3) and (6) ⟹ (4) of Tag 01VT, which the source discharges with "as
  `𝐏ⁿ_S` is a projective bundle over `S` … from the definition of a relatively very ample
  sheaf", and (1) ⟹ (3) of Tag 01VU, which goes through Tag 01VT — and so *also* wants the
  predicate as weak as honesty allows.

A twist datum is a nine-field structure carrying the glued graded algebra, its quasi-coherence,
its commutativity, its chart comparisons, their compatibility with product and unit, and the
degreewise map `ψ` to the direct image together with three laws for it. Of all of that, the
ampleness argument uses
exactly one field: `TwistData.chartData.chartIso`, the chart comparison in degree one. Demanding
the rest inside the definition would import Tag 01NR's entire gluing problem into the *statement*
of Tags 01VT and 01VU, making their producing directions strictly harder than Tag 01NR — the same
statement contamination that rules out spelling Tag 01VM by naming the projective bundle twist of
Tag 01OB directly, since that twist is built from Tag 01NR's glued graded algebra and no value of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed anywhere.

`IsDegreeOneTwist` keeps that one field and drops the other eight. The cost is stated plainly under
"What is not proved" below: a module is pinned by this condition only locally, so the predicate is
*weaker* than the source's, and the implication proved here runs one way only.

**`Scheme.Modules.pullback` and `modulePullback` are both used**, in the places their neighbours
use them: the chart comparisons of `Stacks.Tag01VNChartBasis.chartTwistIso` are stated with the
former and the ampleness development with the latter, and for a morphism of schemes they are the
same functor.

## What is not proved, and no tag is attached

**No `stacks` attribute is attached, to Tag 01VM or to anything else.** Tag 01VM is a definition
whose covering set is that definition, and the predicate below is weaker than it — see the next
paragraph — so claiming the tag would be a false promotion. The tag is carried by
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` in `DegreeOne.lean`, which names the twist.
Tag 01VN's own content appears here
only with `Stacks.Tag01VNChartBasis.ProjOneBasisClause` as a hypothesis the source does not
have, so its tag is withheld under clause 2 of the covering-set rule exactly as it is on
`Stacks.Tag01VNChartBasis.isRelativelyAmple_of_hasRelativeVeryAmpleTwist`.

**The predicate is weaker than the source's, and the converse implication is not proved.** Two
modules on `𝐏(E)` that are locally isomorphic need not be globally isomorphic, so
`IsDegreeOneTwist` does not determine its module up to isomorphism, and the implication
`IsRelativelyVeryAmple → HasRelativeVeryAmpleTwist` would require assembling a full twist datum
from chart data — Stacks Tag 01NR itself. What *is* proved is the implication in the direction
that is available, plus the fact that nothing downstream notices the difference: Tag 01VN's
content goes through on the weaker predicate with the same single premise.

**`IsDegreeOneTwist` is exhibited at a term**, by
`Stacks.Tag01VMVeryAmple.isDegreeOneTwist_twistOne` in `DegreeOne.lean`: the glued degree-one
twist of `𝐏(E)` satisfies it unconditionally. So the predicate is reached without a twist
datum (`isDegreeOneTwist_piece_one`), and its satisfiability does not reduce to Tag 01NR.
Constructing a degree-one twist directly over an affine base is still not enough: the
condition is asked at *every* affine open of the base, not at a covering of it, because that is
what `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion` consumes.

**The bridge Tag 01VT's proof needs is absent.** Clauses (5) and (6) of Tag 01VT speak of
`𝐏ⁿ_S`, whose `𝒪(1)` *is* constructed in this tree as
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`; turning that into
`IsRelativelyVeryAmple` is the source's appeal to [Stacks, Tag 01OE], an identification of `𝐏ⁿ_S`
with `𝐏(𝒪_S^{⊕(n+1)})` carrying one `𝒪(1)` to the other. Nothing in either tree states it. That
is the one piece of infrastructure between the definition below and clauses (3), (4) of Tag 01VT.

## References

* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry

universe u

namespace Stacks.Tag01VMRelativeVeryAmple

/-! ### `Sym(E)` and the projective bundle it defines -/

/-- **`Sym(E)` as graded-algebra data on the base**, for a quasi-coherent module `E` on an
arbitrary scheme. The projective bundle `𝐏(E)` of Stacks Tag 01OB is `relativeProj (symAlgebra E)`,
which is `Stacks.SymGraded.schemeProjectiveBundle E _` by definition. -/
abbrev symAlgebra {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent] : SheafGradedAlgebra S :=
  Stacks.SymGraded.schemeSheafGradedAlgebra E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)

/-- `Sym(E)` is generated in degree one over its degree-zero part on every affine open of the
base, which is what makes the absolute twists on the charts of `𝐏(E)` invertible. -/
theorem adjoin_symAlgebra_eq_top {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent] :
    ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin ((symAlgebra E).grading U 0)
        (((symAlgebra E).grading U 1 : Set ((symAlgebra E).sectionRing U))) = ⊤ :=
  Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E _

/-! ### Degree-one twists of a relative `Proj` -/

variable {S : Scheme.{u}}

/-- **A degree-one twist of the relative `Proj` of `A`**: an `𝒪`-module on `Proj_S(A)` whose
restriction to the inverse image of each affine open `V` of the base is the absolute twist `𝒪(1)`
of `Proj(A(V))`, transported along the chart identification
`Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`.

This is the one property of `𝒪_{𝐏(E)}(1)` that the proof of Stacks Tag 01VN uses, and it is
available without Stacks Tag 01NR's glued graded algebra: the identification of `p⁻¹(V)` with
`Proj(A(V))` is available and twist-datum-free. -/
def IsDegreeOneTwist (A : SheafGradedAlgebra S) (M : (relativeProj A).scheme.Modules) : Prop :=
  ∀ (V : S.Opens) (hV : IsAffineOpen V),
    Nonempty
      ((Scheme.Modules.pullback
            (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).obj
          (twistingSheaf (A.grading V) 1) ≅
        (Scheme.Modules.pullback ((relativeProj A).toBase ⁻¹ᵁ V).ι).obj M)

/-- **The degree-one piece of a twist datum is a degree-one twist.** The witness is
`Stacks.Tag01VNChartBasis.chartTwistIso`, so this is the single field of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` that `IsDegreeOneTwist` retains. -/
theorem isDegreeOneTwist_piece_one {A : SheafGradedAlgebra S} (D : TwistData A) :
    IsDegreeOneTwist A (D.algebra.piece 1) :=
  fun V hV => ⟨Tag01VNChartBasis.chartTwistIso D V hV⟩

/-! ### Stacks Tag 01VM -/

/-- **Stacks Tag 01VM: relative very ampleness.** An invertible `𝒪_X`-module `L` is *very ample
relative to* `f : X ⟶ S` when there are a quasi-coherent `𝒪_S`-module `E`, an invertible
degree-one twist `M` on the projective bundle `𝐏(E) = Proj_S(Sym(E))`, and an immersion
`i : X ⟶ 𝐏(E)` over `S` with `L ≅ i^* M`.

The twist is quantified over rather than named, because `𝒪_{𝐏(E)}(1)` is not constructed in this
repository; `IsDegreeOneTwist` is the characterisation used in its place, and the module
documentation records what that costs. -/
def IsRelativelyVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (E : S.Modules) (hE : E.IsQuasicoherent),
    have := hE
    ∃ (M : (relativeProj (symAlgebra E)).scheme.Modules)
      (hM : IsInvertibleModule (relativeProj (symAlgebra E)).scheme M),
      have := hM
      IsDegreeOneTwist (symAlgebra E) M ∧
        ∃ i : X ⟶ (relativeProj (symAlgebra E)).scheme,
          IsImmersion i ∧ i ≫ (relativeProj (symAlgebra E)).toBase = f ∧
            Nonempty (L ≅ (Scheme.Modules.pullback i).obj M)

/-- **The introduction rule for relative very ampleness**, which is the form the producing
directions of Tags 01VT and 01VU meet: a quasi-coherent `E`, an invertible degree-one twist on
`𝐏(E)`, an immersion over the base and an isomorphism. -/
theorem isRelativelyVeryAmple_of_immersion {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (E : S.Modules) [hE : E.IsQuasicoherent]
    (M : (relativeProj (symAlgebra E)).scheme.Modules)
    [hM : IsInvertibleModule (relativeProj (symAlgebra E)).scheme M]
    (hdt : IsDegreeOneTwist (symAlgebra E) M) (i : X ⟶ (relativeProj (symAlgebra E)).scheme)
    (him : IsImmersion i) (hover : i ≫ (relativeProj (symAlgebra E)).toBase = f)
    (e : L ≅ (Scheme.Modules.pullback i).obj M) :
    IsRelativelyVeryAmple f L :=
  ⟨E, hE, M, hM, hdt, i, him, hover, ⟨e⟩⟩

/-! ### The comparison with the narrow predicate already in the tree -/

/-- **`Stacks.Tag01VNChartBasis.HasRelativeVeryAmpleTwist` implies relative very ampleness.**

The narrow predicate asks for a twist datum `D` and uses `D.algebra.piece 1` as the twist. That
piece is invertible by `TwistMapsInvertible.twistData_isInvertible` and is a degree-one
twist by `isDegreeOneTwist_piece_one`, so it is one of the modules the predicate below quantifies
over.

The converse is not proved and is not expected to be provable here; see the module
documentation. -/
theorem isRelativelyVeryAmple_of_hasRelativeVeryAmpleTwist {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L]
    (h : Tag01VNChartBasis.HasRelativeVeryAmpleTwist f L) :
    IsRelativelyVeryAmple f L := by
  obtain ⟨E, hE, D, i, him, hover, ⟨e⟩⟩ := h
  have := hE
  have hinv : IsInvertibleModule (relativeProj (symAlgebra E)).scheme (D.algebra.piece 1) :=
    TwistMapsInvertible.twistData_isInvertible D (adjoin_symAlgebra_eq_top E) 1
  exact ⟨E, hE, D.algebra.piece 1, hinv, isDegreeOneTwist_piece_one D, i, him, hover, ⟨e⟩⟩

/-! ### Clause (3) of Stacks Tag 01Q3 for a degree-one twist -/

/-- **Clause (3) of Stacks Tag 01Q3 for a degree-one twist on the inverse image of an affine
open, from the same clause for `𝒪(1)` on the affine chart.**

This is `Stacks.Tag01VNChartBasis.isBasisNonvanishing_preimage_of_chart` with the degree-one piece
of a twist datum replaced by an arbitrary degree-one twist. The proof is the same: the chart
identification is a scheme isomorphism, along which clause (3) transports, and the degree-one
twist condition is a module isomorphism, along which it transports too. -/
theorem isBasisNonvanishing_preimage_of_isDegreeOneTwist {A : SheafGradedAlgebra S}
    (M : (relativeProj A).scheme.Modules)
    [IsInvertibleModule (relativeProj A).scheme M] (hdt : IsDegreeOneTwist A M)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (V : S.Opens) (hV : IsAffineOpen V)
    (hbasis :
      letI := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin
        (A.grading V) (hgen V hV) 1
      Stacks.AmpleTheory.IsBasisNonvanishing (AlgebraicGeometry.Proj (A.grading V))
        (twistingSheaf (A.grading V) 1)) :
    letI : IsInvertibleModule ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
        ((modulePullback ((relativeProj A).toBase ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj M) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback
        ((relativeProj A).toBase ⁻¹ᵁ V).ι M
    Stacks.AmpleTheory.IsBasisNonvanishing ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
      ((modulePullback ((relativeProj A).toBase ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj M) := by
  have : IsInvertibleModule (AlgebraicGeometry.Proj (A.grading V))
      (twistingSheaf (A.grading V) 1) :=
    TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin
      (A.grading V) (hgen V hV) 1
  have : IsInvertibleModule ((relativeProj A).toBase ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).obj
        (twistingSheaf (A.grading V) 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback
      (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom (twistingSheaf (A.grading V) 1)
  exact Tag01VNChartBasis.isBasisNonvanishing_of_iso (hdt V hV).some
    (Tag01VNChartBasis.isBasisNonvanishing_pullback_iso
      (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV) _ hbasis)

/-! ### Stacks Tag 01VN against this predicate -/

/-- **Relative very ampleness gives the hypothesis of Stacks Tag 01VN in its basis form.** The
ambient scheme is `𝐏(E)`, the invertible module is the degree-one twist, and the basis clause on
the inverse image of each affine open of the base comes from the chart passage above, whose
absolute input is `Stacks.Tag01VNChartBasis.ProjOneBasisClause`. -/
theorem hasRelativeBasisImmersion_of_isRelativelyVeryAmple
    (hclause : Tag01VNChartBasis.ProjOneBasisClause.{u, u}) {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) :
    Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion f L := by
  obtain ⟨E, hE, M, hM, hdt, i, him, hover, ⟨e⟩⟩ := hL
  have := hE
  have := hM
  refine ⟨(relativeProj (symAlgebra E)).scheme, (relativeProj (symAlgebra E)).toBase, M, hM, i,
    him, hover, fun V hV => ?_, ⟨e⟩⟩
  exact isBasisNonvanishing_preimage_of_isDegreeOneTwist M hdt (adjoin_symAlgebra_eq_top E) V hV
    (hclause _ (adjoin_symAlgebra_eq_top E V hV))

/-- **The content of Stacks Tag 01VN against this predicate**, on
`Stacks.Tag01VNChartBasis.ProjOneBasisClause` as its only premise: a quasi-compact morphism and a
relatively very ample invertible module give a relatively ample one.

The premise is the same single one that
`Stacks.Tag01VNChartBasis.isRelativelyAmple_of_hasRelativeVeryAmpleTwist` already carried, and the
hypothesis is weaker, so this subsumes that theorem — the recovery is recorded by
`isRelativelyAmple_of_hasRelativeVeryAmpleTwist'` below. -/
theorem isRelativelyAmple_of_isRelativelyVeryAmple
    (hclause : Tag01VNChartBasis.ProjOneBasisClause.{u, u}) {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (hL : IsRelativelyVeryAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleBasisRoute.isRelativelyAmple_of_hasRelativeBasisImmersion f L hf
    (hasRelativeBasisImmersion_of_isRelativelyVeryAmple hclause f L hL)

/-- **`Stacks.Tag01VNChartBasis.isRelativelyAmple_of_hasRelativeVeryAmpleTwist` recovered**, which
is what makes the theorem above a generalisation of the formalized form of Tag 01VN's content rather
than a variant of it. -/
theorem isRelativelyAmple_of_hasRelativeVeryAmpleTwist'
    (hclause : Tag01VNChartBasis.ProjOneBasisClause.{u, u}) {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (hL : Tag01VNChartBasis.HasRelativeVeryAmpleTwist f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_isRelativelyVeryAmple hclause f L hf
    (isRelativelyVeryAmple_of_hasRelativeVeryAmpleTwist f L hL)

end Stacks.Tag01VMRelativeVeryAmple

end
