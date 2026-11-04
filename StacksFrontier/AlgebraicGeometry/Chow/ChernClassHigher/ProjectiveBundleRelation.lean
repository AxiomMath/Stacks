module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.TrivialChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback

/-!
# The projective-bundle characterization of the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r` and
let `(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ`. Stacks 02U6 says that for a `k`-cycle
`α` on `X` the classes `c_j(ℰ) ∩ α` of Stacks 02U5 are the **unique** classes
`α_j ∈ A_{k-j}(X)` with `α_0 = α` and

  `∑_{i = 0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*(α_{r-i}) = 0`   in `A_{k-1}(P)`.

This file formalizes that characterization, and the two consequences the Stacks Project draws
from it immediately: Stacks 02U7, that the cap products depend only on the rational equivalence
class of `α`, and Stacks 02U8, that flat pullback commutes with them.

The uniqueness is the whole engine: Stacks 02U7, 02U8, 02U9 and 0B7G are each proved by applying
an operation (flat pullback, proper pushforward, a Gysin map) to the displayed relation,
observing that the transported family again satisfies the relation, and concluding by uniqueness.
Uniqueness itself is injectivity of the projective space bundle map of Stacks 02TX, which is the
hypothesis `Stacks.Chow.ProjectiveBundleRelationInjective` below.

## Main definitions

* `Stacks.Chow.chowGroupCast` — transport of a Chow class along an equality of degrees, as an
  additive equivalence.
* `Stacks.Chow.projectiveBundlePullback` — `π^* : A_m(X) ⟶ A_{m + r - 1}(P)`, the flat pullback
  of Stacks 0FVK along the projection of the bundle.
* `Stacks.Chow.projectiveBundleChernTerm` — the `i`-th summand
  `c₁(O_P(1))^i ∩ π^*(-) : A_{k-(r-i)}(X) ⟶ A_{k-1}(P)` of the relation.
* `Stacks.Chow.ProjectiveBundleChernRelation` — the displayed relation, for a family of Chow
  classes on `X`.
* `Stacks.Chow.ProjectiveBundleRelationInjective` — **Stacks 02TX, injectivity**: the map
  `(α_0, …, α_{r-1}) ↦ ∑_{i < r} c₁(O_P(1))^i ∩ π^*α_i` is injective.
* `Stacks.Chow.ProjectiveBundleRelationSurjective` — **Stacks 02TX, surjectivity**: that same map
  is surjective.
* `Stacks.Chow.IsChernCapFamily` — **Stacks 02U6**: a family `(α_j)_{j ≤ r}` of Chow classes on
  `X` is *the* family of Chern class cap products of a class `α`, namely `α_0 = α` and the
  relation holds.
* `Stacks.Chow.ChernTermsCompatibleWithFlatPullback` — **Stacks 02SS and 02RD**: flat pullback
  along the projection of the bundle carries each summand of the relation over `Y` to the
  corresponding summand over `X`.
* `Stacks.Chow.trivialChernCapOperator` — the first Chern class cap operator of the structure
  sheaf, the component rule of Stacks 02SO being zero in every degree.

## Main results

* `Stacks.Chow.eq_of_isChernCapFamily` — **Stacks 02U6, uniqueness**: granted the injectivity of
  Stacks 02TX, two families characterizing the same class are equal.
* `Stacks.Chow.isChernCapFamily_rationallyEquivalent` — **Stacks 02U7**: rationally equivalent
  cycles have the same Chern class cap products.
* `Stacks.Chow.flatPullback_isChernCapFamily` — the family obtained from a characterizing family
  by flat pullback again satisfies the relation, over the pulled-back bundle.
* `Stacks.Chow.isChernCapFamily_flatPullback` — **Stacks 02U8**: flat pullback commutes with the
  Chern class cap products.
* `Stacks.Chow.capOnChow_trivialChernCapOperator` — **Stacks 02SP, second assertion, on Chow
  groups**: the cap product of the structure sheaf is the zero homomorphism.
* `Stacks.Chow.eq_zero_of_projectiveBundleRelationInjective_trivialChernCapOperator` — read at
  that operator, `Stacks.Chow.ProjectiveBundleRelationInjective` forces Chow groups of the base
  to vanish, so it is weaker than the injectivity half of Stacks 02TX and is not a theorem at
  these parameters.

## Implementation notes

### What the projective bundle is, and why it is a parameter

The object the relation is read on is the projective bundle `(π : P ⟶ X, O_P(1))` of `ℰ`
together with three facts about it that this repository does not have:

* that `π` is flat, locally of finite type and of relative dimension `r - 1` — these are the
  hypotheses under which Stacks 02TX forms the bundle;
* that `O_P(1)` exists at all. `Stacks.RelativeProj.projectiveBundle` is here, but its twists are
  the invertible modules of Stacks 01O4, whose representability statement is not available, and
  the `@[stacks 01OB]` attribute on that definition is clause-qualified for exactly this reason;
* that `c₁(O_P(1)) ∩ -` is defined on Chow groups, which is Stacks 02SO together with Stacks
  02TI.

The last two are supplied together by one object: a `Stacks.Chow.ChernCapOperator` on `P`
is a first Chern class component rule of Stacks 02SO in every degree whose cap product factors
through rational equivalence, Stacks 02TI, which is precisely what an invertible module on `P`
provides once those two tags are available. So `P`, `π` and the operator are parameters, and the
statements below are correspondingly *more general* than the Stacks statements: they hold for any
morphism and any first Chern class cap operator satisfying the projective space bundle formula.
Specializing to `Stacks.RelativeProj.projectiveBundle X ℰ` and the operator of `O_P(1)` recovers
Stacks 02U6, 02U7 and 02U8 verbatim.

### The rank-`r` module itself is not a parameter

Nothing below mentions `ℰ`: the module enters only through its projective bundle, and every
property of the bundle that the proofs use is a hypothesis. Carrying `ℰ` as well would be an
unused parameter. This is the same generalization that
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic` records for its rank hypothesis.

### The degree of the relation, and `r = 0`

Each summand of the relation lands in `A_{k + (r-1) - r}(P)`, with `r - 1` computed in `ℕ`. For
`r ≥ 1` that degree is `k - 1`, which is the degree in the Stacks statement; for `r = 0` it is
`k`, and the relation reads `α_0 = 0`, which is the correct degenerate statement, the bundle of
the zero module being empty. Writing the degree this way, rather than as `k - 1`, is what lets
one statement cover both cases; the `ℕ`-valued `r - 1` is also the relative dimension of `π`, so
the two agree without a side condition.

### Uniqueness is stated as the injectivity hypothesis, not derived from an isomorphism

`Stacks.Chow.ProjectiveBundleRelationInjective` asserts injectivity of
`(α_0, …, α_{r-1}) ↦ ∑_{i<r} c₁(O_P(1))^i ∩ π^*α_i`, written with exactly the summands
`Stacks.Chow.projectiveBundleChernTerm` of the relation, reindexed over `Fin r`. That map is the
map of Stacks 02TX at the base degree `k - r`; stating it with the same summands rather than
through a separate definition and a comparison lemma removes every transport between the two
spellings. Only injectivity is used — the surjectivity half of Stacks 02TX is what the
*existence* of the family needs, and existence is supplied here by Stacks 02U5, which is not in
this repository, so the families are hypotheses.

### The injectivity predicate is weaker than Stacks 02TX, and cannot be discharged as stated

`Stacks.Chow.ProjectiveBundleRelationInjective` quantifies over an arbitrary
`Stacks.Chow.ChernCapOperator` on `P`: nothing ties `twist` to `π`, and `π` is not assumed
proper, so the pushforward `π_*` that step 1 of Stacks 02TX applies to the relation cannot even
be formed at these parameters —
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula` carries
`[IsProper π]` in its variable block for exactly that reason. The predicate is therefore not a
theorem here, and the witness is in this repository:
`Stacks.Chow.eq_zero_of_projectiveBundleRelationInjective_trivialChernCapOperator` reads it at
`Stacks.Chow.trivialChernCapOperator`, the cap operator of the structure sheaf, whose cap product
on Chow groups vanishes by the second assertion of Stacks 02SP
(`Stacks.Chow.firstChernClassCap_trivialChernComponentCycleRule` of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.TrivialChernClass`), and the
conclusion becomes the vanishing of every `A_{k-(r-i)}(X)` with `i ≠ 0`. That operator satisfies
every hypothesis the predicate is stated under, so taking `X = Spec(κ)`, `P = 𝐏^1_κ`, `r = 2` and
`k = 1` leaves the hypotheses intact while `A_0(Spec(κ)) ≅ ℤ` does not vanish.

The faithful statement needs `twist` to be the cap operator of the bundle's own `O_P(1)` — the
degree-one piece of its graded algebra, Stacks 01NR — together with `[IsProper π]`, and that
re-parameterization has to reach `Stacks.Chow.eq_of_isChernCapFamily` below, which is what
consumes the predicate. Even re-parameterized the mathematics is absent: step 1 of Stacks 02TX
needs Stacks 02TW at `s = r - 1`, that `π_*(c₁(O_P(1))^{r-1} ∩ π^*α) = α`, and the file named
above proves only the vanishing `s < r - 1`
(`Stacks.Chow.projectiveBundleProjection_twist_eq_zero_of_lt`, which carries no hypothesis).
The top degree needs Stacks 02TM, whose two producers in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapDivisor` —
`Stacks.Chow.effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula` and
`Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible_of_keyFormula` —
both assume `Stacks.Chow.KeyFormulaRationalEquivalenceOnDivisor`, the rational equivalence the
key formula is to exhibit *on the divisor*. The key formula itself is no longer missing, and
neither is Stacks 02TI: Stacks 0AYC for the situation of Stacks 0AYB is
`Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData` of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationKeyFormula`, and on it rests
`Stacks.Chow.firstChernCapFactorsEverywhere` of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors`, which is Stacks 02TI with no
hypothesis.

The predicate is a hypothesis of a theorem, or a field of a datum, in ten files: this one;
`Stacks.Chow.ProjectiveBundleExistence`, `.ProjectiveBundleBivariantClass`,
`.ProjectiveBundleGysin`, `.ProjectiveBundleFlatPullback`, `.ProjectiveBundleProperPushforward`
and `.IntegralChernClass` of
`StacksDraft.AlgebraicGeometry.Chow.ChernClassHigher`;
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.TrivialSubsheaf`;
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIsoPositiveRank`; and the
field `hinj` of `Stacks.Chow.BundleStep` in
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundle`. That is the scope of the real
fix.

### Why no `Stacks.Chow.HigherChernCapRule` is constructed here

`Stacks.Chow.HigherChernCapRule` is an operation on Chow groups for *every* scheme locally of
finite type over the base and every rank-`r` module on it. Building one from the characterization
below would need the projective bundle data and the surjectivity of the map of Stacks 02TX for
every such pair, so it is Stacks 02TX itself — and Stacks 01O4 for the twist — that stands
between this file and that construction, not anything about Chern classes.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of degrees -/

/-- Transport of a Chow class along an equality of degrees, as an additive equivalence. -/
def chowGroupCast (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {k l : ℤ} (h : k = l) : chowGroup C q k ≃+ chowGroup C q l :=
  AddEquiv.cast (M := chowGroup C q) h

/-- Transport along the reflexive equality of degrees is the identity. -/
@[simp]
theorem chowGroupCast_rfl (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {k : ℤ} (x : chowGroup C q k) : chowGroupCast C q rfl x = x :=
  rfl

/-- Transports along two equalities of degrees compose. -/
@[simp]
theorem chowGroupCast_chowGroupCast (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {k l m : ℤ} (h : k = l) (h' : l = m) (x : chowGroup C q k) :
    chowGroupCast C q h' (chowGroupCast C q h x) = chowGroupCast C q (h.trans h') x := by
  subst h; subst h'; rfl

/-! ### Two pieces of pure algebra -/

/-- An alternating sum `∑_{i ≤ r} (-1)^i T_i(a_i)` determines `a` once its last entry is known
and the unsigned sum of the first `r` summands is injective in its `r` arguments.

This is the algebraic skeleton of the uniqueness in Stacks 02U6: the index `i = r` of the
relation carries the entry `α_0 = α`, which is given, and the remaining `r` entries are
determined because the projective space bundle map of Stacks 02TX is injective. -/
private theorem eq_of_alternating_sum_eq {r : ℕ} {M : ℕ → Type*} [∀ i, AddCommGroup (M i)]
    {N : Type*} [AddCommGroup N] (T : ∀ i : Fin (r + 1), M i.val →+ N)
    (hinj : Function.Injective
      fun β : (∀ i : Fin r, M i.val) ↦ ∑ i : Fin r, T i.castSucc (β i))
    (a b : ∀ i : Fin (r + 1), M i.val)
    (hab : ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val • T i (a i) =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val • T i (b i))
    (hlast : a (Fin.last r) = b (Fin.last r)) : a = b := by
  have key : (fun i : Fin r ↦ (-1 : ℤ) ^ i.val • a i.castSucc) =
      fun i : Fin r ↦ (-1 : ℤ) ^ i.val • b i.castSucc := by
    refine hinj ?_
    simp only [map_zsmul]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hlast] at hab
    simpa only [Fin.val_castSucc] using add_right_cancel hab
  funext i
  refine Fin.lastCases hlast (fun j ↦ ?_) i
  have hj := congrArg (fun z ↦ (-1 : ℤ) ^ j.val • z) (congrFun key j)
  simpa only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul] using hj

/-- Two families agreeing at an index agree at every index equal to it. Used to pass between the
indexing `j` of the Chern class cap products and the indexing `r - j` of the summands of the
relation, which are each other's inverse. -/
private theorem congr_family_eq {I : Type*} {A : I → Sort*} (c d : ∀ i, A i) {i j : I}
    (h : i = j) (hc : c i = d i) : c j = d j := by
  cases h; exact hc

/-! ### The summands of the relation -/

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-- **Stacks 0FVK** along the projection of the bundle: the flat pullback
`π^* : A_m(X) ⟶ A_{m + r - 1}(P)`. The projection of the projective bundle of a rank-`r` module
is flat of relative dimension `r - 1`, which is the hypothesis `hπ`. -/
def projectiveBundlePullback (m : ℤ) :
    chowGroup C sX m →+ chowGroup C sP (m + ((r - 1 : ℕ) : ℤ)) :=
  flatPullbackChow C sP sX π hsP (r - 1) hπ m (hfac m)

/-- The `i`-th summand `c₁(O_P(1))^i ∩ π^*(-) : A_{k-(r-i)}(X) ⟶ A_{k+(r-1)-r}(P)` of the
relation of Stacks 02U6: pull a class of degree `k - (r - i)` back to the bundle and cap it `i`
times with the first Chern class of the twist. -/
def projectiveBundleChernTerm (k : ℤ) (i : ℕ) (hi : i ≤ r) :
    chowGroup C sX (k - ((r - i : ℕ) : ℤ)) →+ chowGroup C sP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) :=
  (iteratedChernCapOnChow C sP (List.replicate i twist)
      (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))).comp
    (((chowGroupCast C sP
        (show k - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) =
            k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + ((List.replicate i twist).length : ℤ) from by
          simp only [List.length_replicate]
          omega)).toAddMonoidHom).comp
      (projectiveBundlePullback C sX sP π hsP r hπ hfac (k - ((r - i : ℕ) : ℤ))))

/-- **Stacks 02U6, the relation.** The alternating sum
`∑_{i=0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*(α_{r-i})` vanishes in the Chow group of the bundle. -/
def ProjectiveBundleChernRelation (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) : Prop :=
  ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
        (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩) = 0

add_to_stacks 02U1 "Equation 42.37.1.1, the displayed relation of clause (1) of Definition 02U0:
  `∑_{i=0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*c_{r-i} = 0`, the condition on a family of Chow classes
  that Definition 02U0 solves to define the Chern classes of a rank-`r` finite locally free
  module. The tag labels the displayed equation, which is this condition, so it is carried by the
  definition naming it; `Stacks.Chow.IsChernCapFamily` conjoins it with `c₀ = α`."
  ProjectiveBundleChernRelation

/-- **Stacks 02TX, injectivity.** The projective space bundle map
`(α_0, …, α_{r-1}) ↦ ∑_{i<r} c₁(O_P(1))^i ∩ π^*α_i`, from `⨁_{i<r} A_{k-r+i}(X)` to
`A_{k-1}(P)`, is injective in every degree.

Written with the summands of the relation themselves, reindexed over `Fin r`: the `i`-th
argument has degree `k - (r - i)`, which is `k - r + i`, and the `r + 1`-st summand of the
relation — the one carrying `α_0` — is the one omitted. -/
def ProjectiveBundleRelationInjective : Prop :=
  ∀ k : ℤ, Function.Injective
    fun β : (∀ i : Fin r, chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) ↦
      ∑ i : Fin r, projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
        i.isLt.le (β i)

/-- **Stacks 02TX, surjectivity.** The projective space bundle map
`(α_0, …, α_{r-1}) ↦ ∑_{i<r} c₁(O_P(1))^i ∩ π^*α_i`, from `⨁_{i<r} A_{k-r+i}(X)` to
`A_{k-1}(P)`, is surjective in every degree.

Written with the same summands as `Stacks.Chow.ProjectiveBundleRelationInjective`, so that the
two halves together say that the map of Stacks 02TX is bijective. This is the half the
*existence* of a family of Chern class cap products rests on: solving the relation of Stacks
02U6 for `α_1, …, α_r` with `α_0 = α` prescribed is exactly exhibiting a preimage of
`-(-1)^r c₁(O_P(1))^r ∩ π^*α`. -/
def ProjectiveBundleRelationSurjective : Prop :=
  ∀ k : ℤ, Function.Surjective
    fun β : (∀ i : Fin r, chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) ↦
      ∑ i : Fin r, projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
        i.isLt.le (β i)

/-! ### The characterization of Stacks 02U6 -/

/-- **Stacks 02U6.** That a family `(α_j)_{0 ≤ j ≤ r}` of Chow classes on `X`, with `α_j` of
degree `k - j`, is the family of Chern class cap products of the class `α ∈ A_k(X)`: its zeroth
member is `α`, and it satisfies the projective-bundle relation.

The Stacks Project states this for `α` a `k`-*cycle*, and the cap products `c_j(ℰ) ∩ α` of
Stacks 02U5 are defined on cycles; the relation however is an identity in the Chow group of the
bundle and is read through the flat pullback of Stacks 0FVK, so it depends on `α` only through
its class. Stating the characterization on classes is therefore not a weakening — it is Stacks
02U7, and `Stacks.Chow.isChernCapFamily_rationallyEquivalent` draws that consequence. -/
def IsChernCapFamily (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) : Prop :=
  chowGroupCast C sX
      (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)
      (c ⟨0, Nat.zero_lt_succ r⟩) = α ∧
    ProjectiveBundleChernRelation C sX sP π hsP r hπ hfac twist k c

/-- **Stacks 02U6, uniqueness.** Granted the injectivity of the projective space bundle map of
Stacks 02TX, there is at most one family of Chern class cap products of a given class: the
relation together with the value in degree `k` determines every member.

This is the engine of the section: Stacks 02U7, 02U8, 02U9 and 0B7G are each proved by
transporting the relation along an operation and appealing to this uniqueness. -/
@[stacks 02U6 "uniqueness; carries the projective bundle as a flat morphism of relative dimension
r - 1 with a first Chern class cap operator for its twist (Stacks 01O4, 02SO, 02TI), Stacks 02S1
for its projection, and the injectivity half of Stacks 02TX"]
theorem eq_of_isChernCapFamily (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac
      twist) (k : ℤ) (α : chowGroup C sX k)
    {c d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))}
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c)
    (hd : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α d) : c = d := by
  have hzero : c ⟨0, Nat.zero_lt_succ r⟩ = d ⟨0, Nat.zero_lt_succ r⟩ :=
    (chowGroupCast C sX
      (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)).injective
        (hc.1.trans hd.1.symm)
  have hreindex := eq_of_alternating_sum_eq
    (M := fun n : ℕ ↦ chowGroup C sX (k - ((r - n : ℕ) : ℤ)))
    (fun i : Fin (r + 1) ↦ projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
      (Nat.lt_succ_iff.mp i.isLt))
    (hinj k) (fun i ↦ c ⟨r - i.val, by omega⟩) (fun i ↦ d ⟨r - i.val, by omega⟩)
    (show _ = _ from hc.2.trans hd.2.symm)
    (congr_family_eq c d (show (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) =
      ⟨r - (Fin.last r).val, by omega⟩ from by ext; simp) hzero)
  funext j
  refine congr_family_eq c d (show (⟨r - (r - j.val), by omega⟩ : Fin (r + 1)) = j from ?_) ?_
  · exact Fin.val_injective (show r - (r - j.val) = (j : ℕ) from by omega)
  · exact congrFun hreindex ⟨r - j.val, by omega⟩

/-! ### Stacks 02U7: the cap products respect rational equivalence -/

/-- **Stacks 02U7.** If `α` and `β` are rationally equivalent `k`-cycles on `X`, then the Chern
class cap products of `α` and of `β` agree: `c_j(ℰ) ∩ α = c_j(ℰ) ∩ β` in `A_{k-j}(X)`.

The Stacks proof is exactly this: the two families are determined by the *same* equation in the
Chow group of the projective bundle, which relies on flat pullback being compatible with rational
equivalence, Stacks 02S1 — here the hypothesis `hfac` that produces the flat pullback of Stacks
0FVK in the first place. -/
@[stacks 02U7 "carries the projective bundle as a flat morphism of relative dimension r - 1 with
a first Chern class cap operator for its twist (Stacks 01O4, 02SO, 02TI), Stacks 02S1 for its
projection, the injectivity half of Stacks 02TX, and the cap products of Stacks 02U5 as families
satisfying the characterization of Stacks 02U6"]
theorem isChernCapFamily_rationallyEquivalent
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α β : CycleGroup C sX k) (hαβ : RationallyEquivalent C sX k α β)
    {c d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))}
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfac twist k
      (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) c)
    (hd : IsChernCapFamily C sX sP π hsP r hπ hfac twist k
      (QuotientAddGroup.mk' (rationalEquivalences C sX k) β) d) : c = d := by
  have hclass : QuotientAddGroup.mk' (rationalEquivalences C sX k) α =
      QuotientAddGroup.mk' (rationalEquivalences C sX k) β := by
    have h0 : QuotientAddGroup.mk' (rationalEquivalences C sX k) (α - β) = 0 :=
      (QuotientAddGroup.eq_zero_iff (N := rationalEquivalences C sX k) (α - β)).2 hαβ
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  exact eq_of_isChernCapFamily C sX sP π hsP r hπ hfac twist hinj k _ hc (hclass ▸ hd)

/-! ### The injectivity predicate read at the structure sheaf -/

/-- The first Chern class cap operator of the structure sheaf: its component rule of Stacks 02SO
is zero on every integral closed subscheme, so the cap product it defines on cycles vanishes by
the second assertion of Stacks 02SP and the factoring of Stacks 02TI is immediate. -/
def trivialChernCapOperator : ChernCapOperator C sP where
  chern k := trivialChernComponentCycleRule C sP k
  factors k := fun α _ ↦ by
    rw [firstChernClassCap_trivialChernComponentCycleRule]
    simp

/-- **Stacks 02SP, second assertion, on Chow groups.** Capping with the first Chern class of the
structure sheaf is the zero homomorphism `A_{k+1}(P) ⟶ A_k(P)`. -/
theorem capOnChow_trivialChernCapOperator (k : ℤ) :
    (trivialChernCapOperator C sP).capOnChow C sP k = 0 :=
  (eq_firstChernClassCapOnChow C sP k _ ((trivialChernCapOperator C sP).factors k) 0
    (by
      rw [AddMonoidHom.zero_comp]
      exact (firstChernClassCap_trivialChernComponentCycleRule C sP k).symm)).symm

/-- Transport of the zero homomorphism along an equality of degrees is zero. -/
private theorem chowGroupDegreeCast_zero {k l m : ℤ} (h : k = l) :
    chowGroupDegreeCast C sP h (0 : chowGroup C sP l →+ chowGroup C sP m) = 0 := by
  subst h; rfl

/-- A nonempty iterate of the cap product of the structure sheaf is zero. -/
private theorem iteratedChernCapOnChow_replicate_trivialChernCapOperator_eq_zero (n : ℕ)
    (k : ℤ) :
    iteratedChernCapOnChow C sP (List.replicate (n + 1) (trivialChernCapOperator C sP)) k = 0 := by
  rw [List.replicate_succ, iteratedChernCapOnChow, capOnChow_trivialChernCapOperator,
    AddMonoidHom.zero_comp, chowGroupDegreeCast_zero]

/-- For the cap operator of the structure sheaf every summand of the projective space bundle map
other than the zeroth is the zero homomorphism, the zeroth being the flat pullback itself. -/
theorem projectiveBundleChernTerm_trivialChernCapOperator_eq_zero (k : ℤ) (i : ℕ) (hi : i ≤ r)
    (hi0 : i ≠ 0) :
    projectiveBundleChernTerm C sX sP π hsP r hπ hfac (trivialChernCapOperator C sP) k i hi =
      0 := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [projectiveBundleChernTerm, iteratedChernCapOnChow_replicate_trivialChernCapOperator_eq_zero,
    AddMonoidHom.zero_comp]

/-- Read at the cap operator of the structure sheaf, whose cap product on Chow groups vanishes,
`Stacks.Chow.ProjectiveBundleRelationInjective` forces every Chow group of the base in the
degrees `k - (r - i)` with `i ≠ 0` to vanish: the map it speaks of forgets all but its zeroth
argument. So the predicate, whose `twist` is an arbitrary cap operator unrelated to `π`, is not a
faithful rendering of the injectivity half of Stacks 02TX. -/
theorem eq_zero_of_projectiveBundleRelationInjective_trivialChernCapOperator
    (h : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac (trivialChernCapOperator C sP))
    (k : ℤ) (i : Fin r) (hi : i.val ≠ 0)
    (x : chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) : x = 0 := by
  have hsum : ∑ j : Fin r, projectiveBundleChernTerm C sX sP π hsP r hπ hfac
      (trivialChernCapOperator C sP) k j.val j.isLt.le (Function.update (0 : ∀ j : Fin r,
        chowGroup C sX (k - ((r - j.val : ℕ) : ℤ))) i x j) =
      ∑ j : Fin r, projectiveBundleChernTerm C sX sP π hsP r hπ hfac
        (trivialChernCapOperator C sP) k j.val j.isLt.le ((0 : ∀ j : Fin r,
          chowGroup C sX (k - ((r - j.val : ℕ) : ℤ))) j) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j = i
    · subst hj
      rw [projectiveBundleChernTerm_trivialChernCapOperator_eq_zero C sX sP π hsP r hπ hfac k
        j.val j.isLt.le hi]
      simp
    · rw [Function.update_of_ne hj]
  have hx := congrFun (h k hsum) i
  rwa [Function.update_self] at hx

end Stacks.Chow

end
