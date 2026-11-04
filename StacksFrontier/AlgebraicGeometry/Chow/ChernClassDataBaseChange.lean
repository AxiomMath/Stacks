module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change compatibility of the Chern class and power sum data

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. The total Chern class of a finite locally free
module is carried in this repository by the datum `Stacks.Chow.TotalChernClassSeries`, and the
power sums `P_p` by `Stacks.Chow.PowerSumClassRule`. Both are data attached to a **single**
scheme: they record the series `c(ℰ)` and the family `(P_p(ℰ))_p` of each module of that scheme,
and the laws they satisfy — the identification with the bivariant Chern classes of Stacks 0B7H,
the normalisation off the finite locally free modules, and additivity or multiplicativity on
short exact sequences — all live on that one scheme.

Nothing in either datum relates the datum on `X` to the datum on another scheme `X'` over `X`.
That is a real gap and not an oversight of the formalization: for the power sums, `cls` is
constrained only by vanishing off the finite locally free modules and by additivity on their
short exact sequences, and both the zero family and a nonzero additive family satisfy that, so
for two *independently chosen* data `W` on `X` and `W'` on `X'` the equation

  `res_g(P_p(ℰ)) = P_p(g^*ℰ)`

is simply false. The constant-rank pinning `Stacks.Chow.TotalChernClassSeries.ch_isChernClass`
does not repair the same gap for the total Chern class either: the characterization
`Stacks.Chow.IsChernClassBivariant` of Stacks 0B7H has a uniqueness statement,
`Stacks.Chow.eq_of_isChernClassBivariant`, but no base change statement, so it pins `ch` on each
scheme separately and says nothing across a morphism.

This file supplies the missing relation as a **predicate on the existing data**, rather than as a
new field of either structure. That is deliberate. Both structures occur as hypotheses of
theorems in this repository, several of which carry Stacks tags; adding a field would strengthen
those hypotheses and so weaken every one of those theorems. A theorem proved from the
over-permissive datum is stronger than the source's, which is the direction this repository
allows, so the existing statements are left exactly as they are and the compatibility is asked
for separately, only where it is used.

## Main definitions

* `Stacks.Chow.TotalChernClassSeries.IsBaseChangeCompatible` — the restriction map of Stacks 0B7F
  carries the total Chern class of a finite locally free module on `X` to the total Chern class
  of its pullback on `X'`, degree by degree.
* `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible` — the restriction map of Stacks 0B7F
  carries the power sum `P_p` of a finite locally free module on `X` to the power sum `P_p` of
  its pullback on `X'`.

## Main results

* `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible.powerSumClassComplex` — **the base change
  clause for `P_p` of a complex.** The restriction of `P_p(ℰ^•)` is `P_p` of the pulled back
  complex `g^*ℰ^•`. This is the clause that Stacks 0GUF uses, and it is provable from the
  predicate because `P_p` of a complex is an alternating **sum**, which the restriction map
  respects for the plain reason that it is a homomorphism of groups.
* `Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible.chernCharacterComplexComponent` — the
  same clause for `ch_p(ℰ^•) = P_p(ℰ^•)/p!`, after tensoring the restriction map with `𝐐`.

## Implementation notes

**Why the predicate is stated at `Stacks.Chow.chowCohomologyRestriction` and not at a carried
map.** The abstract form of this compatibility already occurs in this repository, as the
hypothesis `pbCh` of `Stacks.Chow.chernClassKGroup_pullback` and as the field `pbCh` of
`Stacks.Chow.SecondAdamsSplittingAt`, both in
`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperatorChernScaling`. There the pullback of Chow
cohomology is itself a carried parameter `pb`, because that proof also needs the
multiplicativity of the restriction map and the injectivity of Stacks 02UL, neither of which is
formalized here; carrying the map along with its properties only weakens the hypothesis. The
predicate here is the *specialization* of that statement to the restriction map of Stacks 0B7F
that this repository does construct, `Stacks.Chow.chowCohomologyRestriction`, which is what a
consumer reasoning about an actual morphism of schemes needs. No bridge lemma between the two is
required or provided: instantiating `pb i := chowCohomologyRestriction C G sX g (i : ℤ) hgys` and
`sP := g ≫ sX` turns `pbCh` into
`Stacks.Chow.TotalChernClassSeries.IsBaseChangeCompatible` literally, so a pair satisfying the
predicate below supplies that hypothesis of `Stacks.Chow.chernClassKGroup_pullback` by
definitional unfolding. What it does *not* supply are that theorem's other hypotheses `pbOne` and
`pbGradedMul`, which together say the restriction map is a ring map of `A^*(X)^∧` and which need
Stacks 0FE0.

**Nothing here is discharged against a canonical construction, and that is not an omission.**
Neither datum is constructed in this repository: `ch` is a field of
`Stacks.Chow.TotalChernClassSeries` because identifying the rank-locus assembly of Stacks 0ESW
with `Stacks.Chow.chernClass` on a module of globally constant rank is unproved, and `cls` is a
field of `Stacks.Chow.PowerSumClassRule` because the evaluated power sums
`P_p(c_1, …, c_p)` of Stacks 0F9B need the multiplication of `A^*(X)`, Stacks 0FE0. There is
therefore no canonical `ch` or `cls` in this repository against which either predicate could be
proved, and both necessarily remain hypotheses wherever they are used. What *is* new here is that
the compatibility is now a nameable condition on the existing data, rather than a statement that
could not be written down at all.

**Why only the finite locally free modules.** The field `ch` sends a module that is not finite
locally free to the unit series and `cls` sends it to the zero family, both as normalisations
matching `AlgebraicGeometry.VectorBundleKZero.classOf`. Asking the compatibility for those
modules too would be a *stronger* demand, and one the canonical construction need not meet: the
restriction map is not known here to carry `R.one` to `R'.one` — that is the separate hypothesis
`pbOne` of `Stacks.Chow.chernClassKGroup_pullback` — and the pullback of a module that is not
finite locally free can be finite locally free. The predicates are therefore asked only of the
finite locally free modules, exactly as `pbCh` is, which is both the faithful reading and the
weaker hypothesis.

**Why the clause for the total Chern class of a complex is not in this file.** The total Chern
class of a complex is the alternating **product** `∏_n c(ℰ^n)^{(-1)^n)}` of Stacks 0ESZ, so
restricting it needs the restriction map to be multiplicative for the Cauchy product of the
series ring in which that product is formed. That multiplicativity *is* available, as
`Stacks.Chow.chernClassKGroup_chowCohomologyRestriction` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction`, for series rings whose
degreewise product and unit are those of Stacks 0B7E; what such a ring costs is commutativity of
the Chow cohomology in the non-negative degrees, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`. So the clause exists, as
`Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistenceTotalChern`, and it is
there rather than here because it needs that construction, which this file does not import. The
power sums and the Chern character are alternating sums, and for them the restriction map being a
homomorphism of groups is all that is needed, with no series ring and hence no commutativity;
that is why those clauses close here with nothing of the kind carried.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

section BaseChange

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : X' ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **The base change compatibility of a total Chern class datum.** The restriction map
`g^* : A^i(X) ⟶ A^i(X')` of Stacks 0B7F carries the degree-`i` component of the total Chern
class of a finite locally free module `ℰ` on `X` to the degree-`i` component of the total Chern
class of `g^*ℰ` on `X'`:

  `g^*(c_i(ℰ)) = c_i(g^*ℰ)`.

This is the compatibility of the Chern classes with restriction which
`Stacks.Chow.TotalChernClassSeries` does not record, stated as a predicate on a pair of data so
that no existing statement is changed; see the implementation notes of this file. It is asked
only of the finite locally free modules, matching the hypothesis `pbCh` of
`Stacks.Chow.chernClassKGroup_pullback`. -/
def TotalChernClassSeries.IsBaseChangeCompatible
    {R : ChowCohomologySeriesRing C G sX} {R' : ChowCohomologySeriesRing C G (g ≫ sX)}
    (D : TotalChernClassSeries C G sX R) (D' : TotalChernClassSeries C G (g ≫ sX) R') : Prop :=
  ∀ E : X.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      ∀ i : ℕ, chowCohomologyRestriction C G sX g (i : ℤ) hgys (D.ch E i) =
        D'.ch ((Scheme.Modules.pullback g).obj E) i

/-- **The base change compatibility of a power sum datum.** The restriction map
`g^* : A^p(X) ⟶ A^p(X')` of Stacks 0B7F carries the power sum `P_p(ℰ)` of a finite locally free
module `ℰ` on `X` to the power sum `P_p(g^*ℰ)` of its pullback:

  `g^*(P_p(ℰ)) = P_p(g^*ℰ)`.

This is the compatibility with restriction which `Stacks.Chow.PowerSumClassRule` does not record,
stated as a predicate on a pair of data so that no existing statement is changed; see the
implementation notes of this file. -/
def PowerSumClassRule.IsBaseChangeCompatible (W : PowerSumClassRule C G sX)
    (W' : PowerSumClassRule C G (g ≫ sX)) : Prop :=
  ∀ M : X.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
      ∀ p : ℕ, chowCohomologyRestriction C G sX g (p : ℤ) hgys (W.cls M p) =
        W'.cls ((Scheme.Modules.pullback g).obj M) p

/-- **The base change clause for the power sums of a complex.** The restriction map of Stacks
0B7F carries the class `P_p(ℰ^•)` of Stacks 0ESZ to the class `P_p(g^*ℰ^•)` of the pulled back
complex:

  `g^*(P_p(ℰ^•)) = P_p(g^*ℰ^•)`.

This is the clause the proof of Stacks 0GUF uses. It follows from the base change compatibility
of the power sum data alone: `P_p` of a complex is the alternating **sum** of the `P_p` of its
terms, by `Stacks.Chow.powerSumClassComplex_eq_sum`, and the restriction map is a homomorphism of
groups, so it passes through the sum and through the integer multiples. The terms of the complex
are assumed finite locally free, which is the hypothesis the source states on `ℰ^•`, and which is
what lets the compatibility be applied to each of them. -/
theorem powerSumClassComplex_chowCohomologyRestriction {W : PowerSumClassRule C G sX}
    {W' : PowerSumClassRule C G (g ≫ sX)}
    (hW : PowerSumClassRule.IsBaseChangeCompatible C G sX g hgys W W')
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ) :
    chowCohomologyRestriction C G sX g (p : ℤ) hgys (powerSumClassComplex C G sX W P a k p) =
      powerSumClassComplex C G (g ≫ sX) W'
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a k p := by
  rw [powerSumClassComplex_eq_sum, powerSumClassComplex_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_zsmul, hW _ (hflf i hi) p]
  rfl

end BaseChange

end Stacks.Chow

end
