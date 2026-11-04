module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity
public import StacksCore.Tactic.StacksAttribute

/-!
# The complex of Stacks 0GU9 and the first higher Chow group of Stacks 0GUA

Let `(S, δ)` be the base situation of chapter 42 and let `p : X ⟶ S` be locally of finite type.
Stacks 0GU9 displays the three locally finite groups

`⨁'_{δ(x) = k + 2} K₂ᴹ(κ(x)) ⟶ ⨁'_{δ(x) = k + 1} K₁ᴹ(κ(x)) ⟶ ⨁'_{δ(x) = k} K₀ᴹ(κ(x))`

and asserts that they form a complex; Stacks 0GUA then *defines* the first higher Chow group
`CH^M_k(X, 1)` to be the homology of that complex in the middle. This file proves the assertion
and makes the definition.

The two differentials are already built: the tame-symbol differential
`Stacks.Chow.pointwiseMilnorBoundary` of Stacks 0GU9 and the divisor differential
`Stacks.Chow.pointwiseDivisorDifferential` of Stacks 0GU3. What is proved here is that their
composite vanishes.

## The argument

`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall` reduces the
vanishing to one point `x` of relative dimension `k + 2` and one point `y` of relative dimension
`k` at a time: it is enough that the contributions of the pairs `(x, x')` sum to zero. When `x`
does not specialize to `y` every contribution vanishes. In the remaining case the index
translation `Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_finsum_intermediatePoint` reads
the sum over the points `x'` of relative dimension `k + 1` as a sum over the intermediate points
of `W = closure {x}`, the correspondence
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` reads that as a sum over the height-one primes
of `𝒪_{W, y}`, the summand identity
`Stacks.Chow.pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder` identifies each term with
the corresponding term of the local algebraic reciprocity, and
`AlgebraicGeometry.sum_localMilnorBoundaryOrder_eq_zero` sets that sum to zero.

## The first higher Chow group

Stacks 0GUA writes `CH^M_k(X, 1) = H_1` of the complex. Here the homology in the middle is taken
in its elementary form: the kernel of the divisor differential modulo the image of the
tame-symbol differential, the second being contained in the first exactly by the vanishing of
the composite. `Stacks.Chow.pointwiseMilnorShortComplex` records the same data as a
`CategoryTheory.ShortComplex` of abelian groups, whose `zero` field is the vanishing proved here.

## What is carried

No further input is assumed. Everything carries `[LocallyOfFiniteType p]`, the standing
hypothesis of chapter 42, and the universal catenarity and local Noetherianness of the base,
which are part of `Stacks.Chow.ChowSituation`.

**The localization property of Stacks 0GUA is not formalized here**, but elsewhere. The tag
asserts, for an open `U ⊆ X` with reduced closed complement `Y`, a degreewise split short exact
sequence of the three chain groups compatible with both differentials, and deduces a six-term
exact sequence by the snake lemma. The three split short exact sequences are
`Stacks.Chow.milnorChainLocalization_shortExact_degrees` in
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/MilnorChainLocalization.lean`, and the
six-term exact sequence they yield is `Stacks.Chow.milnorChowLocalization_exact` in
`StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/MilnorChowLocalizationSequence.lean`.

## Main definitions

* `Stacks.Chow.pointwiseMilnorShortComplex` — the complex of Stacks 0GU9, as a short complex of
  abelian groups.
* `Stacks.Chow.milnorChowCycleGroup`, `Stacks.Chow.milnorChowBoundarySubgroup` — the cycles and
  the boundaries in the middle degree.
* `Stacks.Chow.milnorChowGroupOne` — **`CH^M_k(X, 1)`**, the homology of the complex in the
  middle.
* `Stacks.Chow.milnorChowClassOne` — the class of a cycle in `CH^M_k(X, 1)`.

## Main results

* `Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_zero` — the contribution of a single point
  of relative dimension `k + 2` to the composite vanishes.
* `Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary` — **the complex of
  Stacks 0GU9**: the composite of the two differentials is the zero homomorphism.
* `Stacks.Chow.range_pointwiseMilnorBoundary_le` — the boundaries are cycles.
* `Stacks.Chow.milnorChowClassOne_surjective`,
  `Stacks.Chow.milnorChowClassOne_eq_zero_iff` — the class map presents `CH^M_k(X, 1)`.

## References

* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The composite of the two differentials -/

/-- **The contribution of a single point of relative dimension `k + 2` vanishes.** Fix a chain
`ξ`, a point `y` of relative dimension `k` and a point `x` of relative dimension `k + 2`. The
contributions of the pairs `(x, x')`, summed over the points `x'` of relative dimension `k + 1`,
give zero.

If `x` does not specialize to `y` this is the empty case
`Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_zero_of_not_specializes`. In the remaining
case the local ring of `W = closure {x}` at `y` is two-dimensional, the sum is re-indexed first
by the intermediate points of `W` and then by the height-one primes of that local ring, each
term is
identified with a term of the local algebraic reciprocity of Stacks 0EAX by
`Stacks.Chow.pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder`, and that reciprocity sets
the sum to zero. -/
theorem finsum_pointClosureOrdBoundaryTerm_eq_zero (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (y : pointsOfDimension C p k) (x : pointsOfDimension C p (k + 2)) :
    (∑ᶠ x' : pointsOfDimension C p (k + 1),
      pointClosureOrdBoundaryTerm C p k ξ y.1 x x') = 0 := by
  by_cases hxy : (x.1 : X) ⤳ (y.1 : X)
  swap
  · exact finsum_pointClosureOrdBoundaryTerm_eq_zero_of_not_specializes C p k ξ x hxy
  have : IsLocallyNoetherian (integralComponentAt (x.1 : X)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt (x.1 : X)).subschemeι ≫ p)
  have hdim2 : ringKrullDim ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy))) = 2 :=
    ringKrullDim_pointClosureStalk_eq_two_of_relativeDimension_sub_eq_two C p hxy
      (by rw [(mem_pointsOfDimension C p).mp x.2, (mem_pointsOfDimension C p).mp y.2]; ring)
  refine (finsum_pointClosureOrdBoundaryTerm_eq_finsum_intermediatePoint C p k ξ x y hxy).trans ?_
  refine Eq.trans (finsum_comp_equiv (heightOnePrimeEquivIntermediatePoint hdim2)
    (f := fun z ↦ pointClosureOrdBoundaryTerm C p k ξ y.1 x
      (intermediatePointOfDimension C p ((mem_pointsOfDimension C p).mp x.2)
        (specializes_iff_mem_closure.mp hxy) z))).symm ?_
  exact (finsum_congr fun q ↦
    pointClosureOrdBoundaryTerm_eq_localMilnorBoundaryOrder C p k ξ x y hxy hdim2 q).trans
    (sum_localMilnorBoundaryOrder_eq_zero hdim2 _)

/-- **Stacks 0GU9.** The three locally finite direct sums of Milnor K-groups of the tag form a
complex: the tame-symbol differential followed by the divisor differential of Stacks 0GU3 is the
zero homomorphism.

This is the assertion of the tag. By
`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall` it suffices to
check it one point of relative dimension `k + 2` and one point of relative dimension `k` at a
time, which is `Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_zero`. -/
@[stacks 0GU9 "the complex of the tag: the composite of the tame-symbol differential of the tag \
with the divisor differential of Stacks 0GU3 is the zero homomorphism, so the three locally \
finite direct sums of Stacks 0GU2 -- the degree-two, degree-one and degree-zero Milnor K-groups \
of the residue fields at the points of relative dimension k + 2, k + 1 and k -- form a complex",
  stacks 0EAY "the remark's closing sentence: the composition of the two displayed arrows is \
zero when i = 1 and j is arbitrary. The remark says this follows from Lemma 0EAX, and the proof \
here does run through 0EAX's content: it reduces to \
AlgebraicGeometry.sum_localMilnorBoundaryOrder_eq_zero at the two-dimensional local ring \
𝒪_{closure {x}, y}, which reduces to AlgebraicGeometry.sum_ord_localTameSymbol_eq_zero -- the \
declaration registered for 0EAX, the vanishing of the sum of ord_{A/𝔮}(∂_{A_𝔮}(f, g)) over the \
height-one primes. The remark's preceding sentence, that it is not clear the composition is zero \
in general, is not a claim; for excellent X the remark cites [Kato-Milnor-K], and that citation \
is not formalized"]
theorem pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary (k : ℤ) :
    (pointwiseDivisorDifferential C p k).comp (pointwiseMilnorBoundary C p k) = 0 :=
  pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall C p k
    fun ξ y x ↦ finsum_pointClosureOrdBoundaryTerm_eq_zero C p k ξ y x

/-- The divisor differential kills every tame-symbol boundary. -/
theorem pointwiseDivisorDifferential_pointwiseMilnorBoundary (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) :
    pointwiseDivisorDifferential C p k (pointwiseMilnorBoundary C p k ξ) = 0 :=
  DFunLike.congr_fun (pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary C p k) ξ

/-! ### The complex as a short complex of abelian groups -/

/-- **Stacks 0GU9.** The complex of the tag, packaged as a short complex of abelian groups: the
degree-two Milnor K-chains at the points of relative dimension `k + 2`, the degree-one chains at
the points of relative dimension `k + 1` and the degree-zero chains at the points of relative
dimension `k`, with the tame-symbol differential and the divisor differential of Stacks 0GU3.
Its `zero` field is
`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary`. -/
@[stacks 0GU9 "the complex of the tag, assembled as a short complex of abelian groups out of the \
three locally finite direct sums of Stacks 0GU2 and the two differentials, the vanishing of \
whose composite is its defining property"]
def pointwiseMilnorShortComplex (k : ℤ) : ShortComplex AddCommGrpCat.{u} where
  X₁ := AddCommGrpCat.of (PointwiseKTwoGroup C p k)
  X₂ := AddCommGrpCat.of (PointwiseKOneGroup C p k)
  X₃ := AddCommGrpCat.of (PointwiseCycleGroup C p k)
  f := AddCommGrpCat.ofHom (pointwiseMilnorBoundary C p k)
  g := AddCommGrpCat.ofHom (pointwiseDivisorDifferential C p k)
  zero :=
    AddCommGrpCat.hom_ext (pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary C p k)

/-! ### The first higher Chow group -/

/-- The cycles in the middle degree of the complex of Stacks 0GU9: the degree-one Milnor
K-chains killed by the divisor differential of Stacks 0GU3. -/
def milnorChowCycleGroup (k : ℤ) : AddSubgroup (PointwiseKOneGroup C p k) :=
  (pointwiseDivisorDifferential C p k).ker

/-- **The boundaries are cycles.** This is the vanishing of the composite of the two
differentials, read as an inclusion of subgroups. -/
theorem range_pointwiseMilnorBoundary_le (k : ℤ) :
    (pointwiseMilnorBoundary C p k).range ≤ milnorChowCycleGroup C p k := by
  rintro a ⟨ξ, rfl⟩
  exact pointwiseDivisorDifferential_pointwiseMilnorBoundary C p k ξ

/-- The boundaries in the middle degree, as a subgroup of the cycles: the image of the
tame-symbol differential, which lands in the cycles by
`Stacks.Chow.range_pointwiseMilnorBoundary_le`. -/
def milnorChowBoundarySubgroup (k : ℤ) : AddSubgroup (milnorChowCycleGroup C p k) :=
  (pointwiseMilnorBoundary C p k).range.addSubgroupOf (milnorChowCycleGroup C p k)

/-- **Stacks 0GUA.** The first higher Chow group `CH^M_k(X, 1)` of the tag: the homology in the
middle of the complex of Stacks 0GU9, that is, the degree-one Milnor K-chains killed by the
divisor differential of Stacks 0GU3 modulo those coming from a degree-two Milnor K-chain under
the tame-symbol differential. The superscript of the tag distinguishes this group from the higher
Chow groups of the literature. -/
@[stacks 0GUA "the definition of the tag: the first higher Chow group CH^M_k(X, 1) is the \
homology in the middle of the complex of Stacks 0GU9, formed as the degree-one Milnor K-chains \
killed by the divisor differential of Stacks 0GU3 modulo the image of the tame-symbol \
differential of Stacks 0GU9, the latter lying in the former because that composite is the zero \
homomorphism; the localization property of the tag, namely the degreewise split short exact \
sequences attached to an open subscheme with reduced closed complement together with the \
six-term exact sequence the snake lemma yields from them, is not proved here but in \
Stacks.Chow.milnorChainLocalization_shortExact_degrees and \
Stacks.Chow.milnorChowLocalization_exact"]
def milnorChowGroupOne (k : ℤ) : Type u :=
  milnorChowCycleGroup C p k ⧸ milnorChowBoundarySubgroup C p k

/-- `CH^M_k(X, 1)` is an abelian group, as a quotient of abelian groups. -/
instance (k : ℤ) : AddCommGroup (milnorChowGroupOne C p k) :=
  inferInstanceAs (AddCommGroup (milnorChowCycleGroup C p k ⧸ milnorChowBoundarySubgroup C p k))

/-- The class in `CH^M_k(X, 1)` of a degree-one Milnor K-chain killed by the divisor
differential. -/
def milnorChowClassOne (k : ℤ) : milnorChowCycleGroup C p k →+ milnorChowGroupOne C p k :=
  QuotientAddGroup.mk' (milnorChowBoundarySubgroup C p k)

/-- Every class in `CH^M_k(X, 1)` is the class of a cycle. -/
theorem milnorChowClassOne_surjective (k : ℤ) :
    Function.Surjective (milnorChowClassOne C p k) :=
  QuotientAddGroup.mk'_surjective _

/-- A cycle has class zero in `CH^M_k(X, 1)` exactly when it is the tame-symbol boundary of a
degree-two Milnor K-chain. -/
theorem milnorChowClassOne_eq_zero_iff (k : ℤ) (a : milnorChowCycleGroup C p k) :
    milnorChowClassOne C p k a = 0 ↔
      ∃ ξ : PointwiseKTwoGroup C p k, pointwiseMilnorBoundary C p k ξ = a.1 :=
  QuotientAddGroup.eq_zero_iff a

end Stacks.Chow

end
