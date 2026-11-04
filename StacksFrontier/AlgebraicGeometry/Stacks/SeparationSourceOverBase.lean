module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented

/-!
# The separation axioms, absolutely and over the base (Stacks 050N)

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 050N** has eight assertions. The
first four compare, for an algebraic stack `𝒳` over `S`, the *absolute* separation axioms of
**Stacks 050D** parts (5)-(8) with the axioms over `S` of **Stacks 050D** parts (1)-(4):

* (1) `𝒳` is DM **if and only if** `𝒳` is DM over `S`;
* (2) `𝒳` is quasi-DM **if and only if** `𝒳` is quasi-DM over `S`;
* (3) if `𝒳` is separated, then `𝒳` is separated over `S`;
* (4) if `𝒳` is quasi-separated, then `𝒳` is quasi-separated over `S`.

The asymmetry is the source's: (1) and (2) are biconditionals, (3) and (4) are one-directional,
because `𝒳` separated over a base that is not itself separated need not be separated. The last
four assertions are about a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`:

* (5) if `𝒳` is DM over `S`, then `f` is DM;
* (6) if `𝒳` is quasi-DM over `S`, then `f` is quasi-DM;
* (7) if `𝒳` is separated over `S` and `Δ_{𝒴/S}` is separated, then `f` is separated;
* (8) if `𝒳` is quasi-separated over `S` and `Δ_{𝒴/S}` is quasi-separated, then `f` is
  quasi-separated.

The source's proof of the last four is one sentence: *"Parts (5), (6), (7), and (8) follow
immediately from Lemma 050M and Spaces, Definition 02X5."* That is the argument carried out here.
Being DM over `S` is being DM as a structure morphism (**Stacks 050D**, part (1)), the structure
morphism of `𝒳` is `f` followed by that of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`, an equality of 1-morphisms on the nose), so
each hypothesis on `𝒳` says that the composite `f ≫ p_𝒴` has the axiom, and the corresponding
part of **Stacks 050M** — cancellation of the second factor of a composite — gives the axiom
for `f`.

The source's proof of the first four reads `𝒳` as an algebraic stack over `Spec(ℤ)` through
**Stacks 04X6** and applies the same Lemma 050M there, along the factorisation
`𝒳 ⟶ S ⟶ Spec(ℤ)` of its structure morphism. Parts (1) and (2) are carried out in full: the
implications from the absolute axioms are proved here, their converses in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented`, and the biconditionals the source
states are assembled from both halves below. See the implementation notes for what parts (3)
and (4) still need.

## Main results

* `AlgebraicGeometry.Stack.isDMAbs_iff_isDMOver`: part (1), the biconditional `𝒳` is DM `↔` `𝒳`
  is DM over `S`.
* `AlgebraicGeometry.Stack.isQuasiDMAbs_iff_isQuasiDMOver`: part (2), the biconditional `𝒳` is
  quasi-DM `↔` `𝒳` is quasi-DM over `S`.
* `AlgebraicGeometry.Stack.isDMOver_of_isDMAbs`: the implication from the absolute axiom to the
  axiom over `S` in part (1). **Untagged**: the tag for part (1) sits on the biconditional, which
  is its covering set.
* `AlgebraicGeometry.Stack.isQuasiDMOver_of_isQuasiDMAbs`: the implication from the absolute axiom
  to the axiom over `S` in part (2). **Untagged**, for the same reason.
* `AlgebraicGeometry.Stack.isDM_of_isDMOver`: part (5).
* `AlgebraicGeometry.Stack.isQuasiDM_of_isQuasiDMOver`: part (6).
* `AlgebraicGeometry.Stack.isSeparated_of_isSeparatedOver_of_isSeparated_diagonal`: part (7).
* `AlgebraicGeometry.Stack.isQuasiSeparated_of_isQuasiSeparatedOver_of_isQuasiSeparated_diagonal`:
  part (8).

## Implementation notes

The cancellation tool the four clauses run on is
`AlgebraicGeometry.Stack.AlgebraicStacks.prop_relativeDiagonal_cancel`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation`: it cancels a condition of
Properties of Stacks, Section 04XB, across the factorisation `𝒳 ⟶ 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` of the
relative diagonal of a composite (`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp`)
from the space-level cancellations — **Stacks 06G6** for unramifiedness, **Stacks 03XN** for
local quasi-finiteness, **Stacks 03KS** for quasi-compactness and **Stacks 03KR** for
quasi-separatedness. Its four specialisations are parts (1)-(4) of **Stacks 050M**, and those
are exactly what discharge the four clauses below: part (1) gives part (5), part (2) part (6),
part (3) part (7) and part (4) part (8).

**Parts (1)-(4): the absolute axioms are defined, and the obstruction is a proof, not a
definition.** The four absolute axioms of **Stacks 050D**, parts (5)-(8), are
`AlgebraicGeometry.Stack.IsDMAbs`, `AlgebraicGeometry.Stack.IsQuasiDMAbs`,
`AlgebraicGeometry.Stack.IsSeparatedAbs` and `AlgebraicGeometry.Stack.IsQuasiSeparatedAbs`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute`, where **Stacks 04X6**
(`AlgebraicGeometry.Stack.changeBaseAlgebraicStacks`) is specialised at the terminal base as
`AlgebraicGeometry.Stack.viewOverInt`. So all four clauses are statable, and parts (1) and (2)
are proved here in both directions.

Each clause is read over the base `Spec(ℤ)`, where the structure morphism of `𝒳` factors through
the view of the stack represented by `S`: the factorisation is
`AlgebraicGeometry.Stack.comp_structureMorphism` at that base, so the four clauses are the four
clauses of **Stacks 050M**, resp. **Stacks 050K**, applied there. What each clause then needs is
to carry a condition of Stacks 04XB on a relative diagonal between the base `Spec(ℤ)` and the
base `S`, and that transfer is
`AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase`.

**One thing is still missing, and it is what keeps parts (3) and (4) from being stated.**

* *The transfer is available only at an étale-chart property* — a condition of Stacks 04XB at a
  property of morphisms of schemes read through **Stacks 03MJ**, since the one base-independence
  statement in the library is
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`. DM and
  quasi-DM are of that shape, being unramifiedness and local quasi-finiteness of the relative
  diagonal; separatedness and quasi-separatedness are **not**, being properness, resp.
  quasi-compactness and quasi-separatedness, each of which is defined by quantifying over the
  algebraic spaces over the base. So **parts (3) and (4) are not stated here**: what they need
  is the analogue of that lemma at `AlgebraicGeometry.Space.IsProper`,
  `AlgebraicGeometry.Space.IsQuasiCompact` and `AlgebraicGeometry.Space.IsQuasiSeparated`.
The converse halves of parts (1) and (2) are **proved**, not missing. They run the
composition of **Stacks 050K** rather than the cancellation of Stacks 050M, so they need the
second factor — the structure morphism over `Spec(ℤ)` of the view of the stack represented by
`S` — to be DM, resp. quasi-DM, which is the statement that `Δ_{S/ℤ}` is unramified, resp.
locally quasi-finite. That is
`AlgebraicGeometry.Stack.isDMOver_viewOverInt_schemeStack`, resp.
`AlgebraicGeometry.Stack.isQuasiDMOver_viewOverInt_schemeStack`, and the converses themselves are
`AlgebraicGeometry.Stack.isDMAbs_of_isDMOver` and
`AlgebraicGeometry.Stack.isQuasiDMAbs_of_isQuasiDMOver`, all four in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented`. The two biconditionals below are
assembled from them and from the two implications above, and they carry the tags for parts (1)
and (2).

The analogous hypothesis of the source's parts (3) and (4) — that `Δ_g` is separated, resp.
quasi-separated — is *not* among the missing facts: for a 1-morphism representable by algebraic
spaces it is **Stacks 04YQ**, parts (4) and (3), which are
`AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces` and
`AlgebraicGeometry.Stack.mono_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`. Note that
what parts (3) and (4) need of `g : S ⟶ Spec(ℤ)` is a property of its *diagonal* and never of `g`
itself; `g` is not separated for a general `S`, which is exactly why those two parts of the
source are one-directional.

The hypothesis of part (7), and of part (8), is that `Δ_{𝒴/S}` is separated, resp.
quasi-separated, *in the sense of Stacks 04XB* — the notion that applies to a 1-morphism
representable by algebraic spaces, which `Δ_{𝒴/S}` is by **Stacks 04XS** part (1). That is the
reading under which the hypothesis is the one Stacks 050H parts (3) and (2) consume, i.e. the
form in which the proof of Stacks 050M uses it.

## References

* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050N, part (1), the implication from the absolute axiom.** If an algebraic stack
`𝒳` over `S` is DM, then it is DM over `S`.

The structure morphism of `𝒳` over `Spec(ℤ)` is the view over `Spec(ℤ)` of the structure
morphism of `𝒳` over `S`, followed by the structure morphism over `Spec(ℤ)` of the view of the
stack represented by `S` — that is `AlgebraicGeometry.Stack.comp_structureMorphism` read at the
base `Spec(ℤ)`, where it needs nothing of the 1-morphism it is applied to. So part (1) of
**Stacks 050M** (`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_comp`), which cancels the
second factor of a DM composite with no hypothesis on it, gives that the view of the structure
morphism is DM; and
`AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase` carries the
unramifiedness of its relative diagonal back from the base `Spec(ℤ)` to the base `S`.

**This is one direction of a biconditional, and it carries no tag.** The source's part (1) is
"`𝒳` is DM ⟺ `𝒳` is DM over `S`"; the converse is
`AlgebraicGeometry.Stack.isDMAbs_of_isDMOver`, which additionally needs that the structure
morphism of the stack represented by `S` over `Spec(ℤ)` is DM, i.e. that `Δ_{S/ℤ}` is
unramified. The tag for part (1) is on `AlgebraicGeometry.Stack.isDMAbs_iff_isDMOver`, the
biconditional assembled from the two. -/
theorem isDMOver_of_isDMAbs (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsDMAbs.{u, w, w'} B S hS 𝒵) : IsDMOver B S hS 𝒵 := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
    (structureMorphism B S hS 𝒵), ?_⟩
  refine hasEtaleChartProperty_relativeDiagonal_of_changeBase B S _ hS
      (contains_specULiftZ B) (toIntObject B S hS) _ 𝒵.val _
      (structureMorphism B S hS 𝒵).hom ?_
  exact (AlgebraicStacks.isDM_of_comp B _ (contains_specULiftZ B)
    (Bicategory.InducedBicategory.mkHom
      (changeBaseHom B S _ hS (contains_specULiftZ B) (toIntObject B S hS)
        (structureMorphism B S hS 𝒵).hom))
    (structureMorphism B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
    (by simpa only [comp_structureMorphism] using h)).2

/-- **Stacks 050N, part (2), the implication from the absolute axiom.** If an algebraic stack
`𝒳` over `S` is quasi-DM, then it is quasi-DM over `S`.

The same argument as part (1), with part (2) of **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_comp`) in place of part (1); it too needs
no hypothesis on the second factor, and local quasi-finiteness is an étale-chart condition
(**Stacks 03XJ**, part (1)), so the same transfer applies.

**This is one direction of a biconditional, and it carries no tag**, for the reason given at
part (1); the tag for part (2) is on
`AlgebraicGeometry.Stack.isQuasiDMAbs_iff_isQuasiDMOver`. -/
theorem isQuasiDMOver_of_isQuasiDMAbs (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsQuasiDMAbs.{u, w, w'} B S hS 𝒵) : IsQuasiDMOver B S hS 𝒵 := by
  refine hasEtaleChartProperty_relativeDiagonal_of_changeBase B S _ hS
      (contains_specULiftZ B) (toIntObject B S hS) _ 𝒵.val _
      (structureMorphism B S hS 𝒵).hom ?_
  exact (AlgebraicStacks.isQuasiDM_of_comp B _ (contains_specULiftZ B)
      (Bicategory.InducedBicategory.mkHom
        (changeBaseHom B S _ hS (contains_specULiftZ B) (toIntObject B S hS)
          (structureMorphism B S hS 𝒵).hom))
      (structureMorphism B _ (contains_specULiftZ B)
        (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
      (by simpa only [comp_structureMorphism] using h))

/-- **Stacks 050N, part (1).** An algebraic stack `𝒳` over `S` is DM **if and only if** it is DM
over `S`.

The implication from the absolute axiom is `AlgebraicGeometry.Stack.isDMOver_of_isDMAbs` above,
which cancels the second factor of the factorisation `𝒳 ⟶ S ⟶ Spec(ℤ)` by part (1) of
**Stacks 050M** and carries the resulting condition on the relative diagonal back from the base
`Spec(ℤ)` to the base `S`. The converse is
`AlgebraicGeometry.Stack.isDMAbs_of_isDMOver`, which composes along the same factorisation by
part (5) of **Stacks 050L**, using that the second factor is DM
(`AlgebraicGeometry.Stack.isDMOver_viewOverInt_schemeStack`, i.e. that `Δ_{S/ℤ}` is unramified).
Neither direction carries a hypothesis the source does not have. -/
@[stacks 050N "part (1)"]
theorem isDMAbs_iff_isDMOver (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsDMAbs.{u, w, w'} B S hS 𝒵 ↔ IsDMOver B S hS 𝒵 :=
  ⟨isDMOver_of_isDMAbs.{u, w, w'} B S hS 𝒵, isDMAbs_of_isDMOver.{u, w, w'} B S hS 𝒵⟩

/-- **Stacks 050N, part (2).** An algebraic stack `𝒳` over `S` is quasi-DM **if and only if** it
is quasi-DM over `S`.

The same two halves as part (1), with local quasi-finiteness in place of unramifiedness:
`AlgebraicGeometry.Stack.isQuasiDMOver_of_isQuasiDMAbs` above runs part (2) of **Stacks 050M**,
and `AlgebraicGeometry.Stack.isQuasiDMAbs_of_isQuasiDMOver` runs part (6) of **Stacks 050L**
against `AlgebraicGeometry.Stack.isQuasiDMOver_viewOverInt_schemeStack`. Neither direction
carries a hypothesis the source does not have. -/
@[stacks 050N "part (2)"]
theorem isQuasiDMAbs_iff_isQuasiDMOver (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsQuasiDMAbs.{u, w, w'} B S hS 𝒵 ↔ IsQuasiDMOver B S hS 𝒵 :=
  ⟨isQuasiDMOver_of_isQuasiDMAbs.{u, w, w'} B S hS 𝒵,
    isQuasiDMAbs_of_isQuasiDMOver.{u, w, w'} B S hS 𝒵⟩

/-- **Stacks 050N, part (5).** If `𝒳` is DM over `S`, then every 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` is DM.

Being DM over `S` is DM-ness of the structure morphism of `𝒳` (**Stacks 050D**, part (1)), and
that structure morphism is `f` followed by the structure morphism of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`), so part (1) of **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_comp`), which cancels the second factor of a
DM composite with no hypothesis on it, gives the conclusion. -/
@[stacks 050N "part (5)"]
theorem isDM_of_isDMOver (f : 𝒳 ⟶ 𝒴) (h𝒳 : IsDMOver B S hS 𝒳) : IsDM B S hS f :=
  AlgebraicStacks.isDM_of_comp B S hS f (structureMorphism B S hS 𝒴) (by
    simpa only [comp_structureMorphism] using h𝒳)

/-- **Stacks 050N, part (6).** If `𝒳` is quasi-DM over `S`, then every 1-morphism `f : 𝒳 ⟶ 𝒴`
of algebraic stacks over `S` is quasi-DM.

The same argument as part (5), with part (2) of **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_comp`) in place of part (1); it too needs
no hypothesis on the second factor. -/
@[stacks 050N "part (6)"]
theorem isQuasiDM_of_isQuasiDMOver (f : 𝒳 ⟶ 𝒴) (h𝒳 : IsQuasiDMOver B S hS 𝒳) :
    AlgebraicStacks.IsQuasiDM B S hS f :=
  AlgebraicStacks.isQuasiDM_of_comp B S hS f (structureMorphism B S hS 𝒴) (by
    simpa only [comp_structureMorphism] using h𝒳)

/-- **Stacks 050N, part (7).** If `𝒳` is separated over `S` and the relative diagonal `Δ_{𝒴/S}`
is separated in the sense of Stacks 04XB, then every 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` is separated.

The same argument as part (5), with part (3) of **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_comp_of_isSeparated_diagonal`) in place
of part (1). That part cancels the second factor of a separated composite provided the second
factor has separated relative diagonal, and here the second factor is the structure morphism of
`𝒴`, so the proviso is exactly the hypothesis `hΔ` that the source's part (7) carries too. -/
@[stacks 050N "part (7)"]
theorem isSeparated_of_isSeparatedOver_of_isSeparated_diagonal (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsSeparatedOver B S hS 𝒳)
    (hΔ : IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒴).hom)) :
    AlgebraicStacks.IsSeparated B S hS f :=
  AlgebraicStacks.isSeparated_of_comp_of_isSeparated_diagonal B S hS f
    (structureMorphism B S hS 𝒴) (by simpa only [comp_structureMorphism] using h𝒳) hΔ

/-- **Stacks 050N, part (8).** If `𝒳` is quasi-separated over `S` and the relative diagonal
`Δ_{𝒴/S}` is quasi-separated in the sense of Stacks 04XB, then every 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` is quasi-separated.

The same argument as part (7), with part (4) of **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_comp_of_isQuasiSeparated_diagonal`)
in place of part (3); the hypothesis `hΔ` is again what that part needs of the second factor,
which here is the structure morphism of `𝒴`. -/
@[stacks 050N "part (8)"]
theorem isQuasiSeparated_of_isQuasiSeparatedOver_of_isQuasiSeparated_diagonal (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsQuasiSeparatedOver B S hS 𝒳)
    (hΔ : IsQuasiSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒴).hom)) :
    AlgebraicStacks.IsQuasiSeparated B S hS f :=
  AlgebraicStacks.isQuasiSeparated_of_comp_of_isQuasiSeparated_diagonal B S hS f
    (structureMorphism B S hS 𝒴) (by simpa only [comp_structureMorphism] using h𝒳) hΔ

end AlgebraicGeometry.Stack

end
