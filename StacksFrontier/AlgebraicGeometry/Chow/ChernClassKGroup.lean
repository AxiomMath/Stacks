module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern class map on the Grothendieck group of vector bundles

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. Stacks 0FEL records the following construction. The
total Chern class of a finite locally free module is multiplicative in short exact sequences by
the Whitney sum formula, Stacks 02UI, so sending the generator `[ℰ]` of `K_0(Vect(X))` to

  `c(ℰ) = 1 + c_1(ℰ) + c_2(ℰ) + …`

and extending multiplicatively defines a map

  `c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`.

The target is the **product** over all `i ≥ 0`, not the direct sum: `−[ℰ]` has to go to the
formal inverse `c(ℰ)^{-1}`, whose degree-`i` component is given by the recursion

  `c(ℰ)^{-1}_0 = 1`,  `c(ℰ)^{-1}_{n+1} = − ∑_{i + j = n} c_{i+1}(ℰ) · c(ℰ)^{-1}_j`,

and nothing bounds the degrees in which that is nonzero. This file constructs the map, the
product, the multiplication on it and the formal inverse.

## Main definitions

* `Stacks.Chow.chowCohomologySeries` — the target `∏_{i ≥ 0} A^i(X)` of the Chern class map: a
  family `(a_0, a_1, a_2, …)` with `a_i ∈ A^i(X)` and **no** condition on its support.
* `Stacks.Chow.GradedChowProductRule`, `Stacks.Chow.chowSeriesMul` — a degreewise product
  `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` and the Cauchy product of two series it defines.
* `Stacks.Chow.ChowCohomologySeriesRing` — the ring `A^*(X)^∧ = ∏_{i ≥ 0} A^i(X)` of Stacks 0FE0
  as a datum: a degreewise product, a unit series, and the laws. See the implementation notes for
  why it is a parameter.
* `Stacks.Chow.gradedFormalInverse` — the formal inverse of a series with constant term `u`, by
  the recursion above, for a bare degreewise product: neither the laws of the series ring nor its
  unit series are needed to write it down, and only a left unit law for `u` is needed to make it
  invert.
* `Stacks.Chow.ChowCohomologySeriesRing.formalInverse` — that inverse at the degreewise product
  of a series ring and the constant term of its unit series.
* `Stacks.Chow.ChowCohomologySeriesRing.UnitalSeries` — the series with constant term `1`, a
  commutative **group** under the Cauchy product.
* `Stacks.Chow.GradedTotalChernClassSeries` — the total Chern class as a datum, for a bare
  degreewise product and unit series: the series `c(ℰ)` of each module, its identification with
  the bivariant Chern classes of Stacks 0B7H, and the Whitney sum formula of Stacks 02UI in the
  form `c(ℰ) = c(ℰ_1) c(ℰ_2)`. Only the product and the unit of a series ring are used, never its
  laws.
* `Stacks.Chow.TotalChernClassSeries` — that datum at the product and unit of a
  `Stacks.Chow.ChowCohomologySeriesRing`.
* `Stacks.Chow.chernClassKGroupHom`, `Stacks.Chow.chernClassKGroup` — **Stacks 0FEL**, the map
  `c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`, first as a homomorphism into the group of unital series
  written additively and then as the map of the source.

## Main results

* `Stacks.Chow.chowSeriesMul_gradedFormalInverse`,
  `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesMul_formalInverse` — the recursion really does
  invert: `a · a^{-1} = 1` for every series with constant term `1`.
* `Stacks.Chow.chernClassKGroupHom_classOf`, `Stacks.Chow.chernClassKGroup_classOf` —
  `c([ℰ]) = c(ℰ)`, the value on a generator, for the homomorphism and for the map.
* `Stacks.Chow.chernClassKGroup_add` — `c(α + β) = c(α) c(β)`: the map is multiplicative, which
  is what "extending multiplicatively" means and what Stacks 02UI makes possible.
* `Stacks.Chow.chernClassKGroup_neg_classOf` — **the remark's last clause**: `−[ℰ]` goes to the
  formal inverse `c(ℰ)^{-1}`, and `c(ℰ) · c(−[ℰ]) = 1`.

## Implementation notes

### Why the ring and the Chern classes are parameters

Two of the three ingredients of the remark are not in this repository.

The ring structure on `A^*(X)` is composition of bivariant classes, Stacks 0FE0. The composite of
two bivariant classes **is** constructed, as `Stacks.Chow.bivariantComposite` in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class`, and it satisfies the composition
formula of Stacks 0FE0 by `Stacks.Chow.isBivariantClassComposition_bivariantComposite`. It carries
neither descent condition: Stacks 02S1 is supplied there by `Stacks.Chow.flatPullbackDescends` and
Stacks 02S2 by `Stacks.Chow.properPushforwardDescends`. It does still carry the two Gysin-system
clauses of Stacks 02TA, which are properties of the chosen Gysin system `G` and are open: `G` is a
parameter of the whole development, an arbitrary one does not satisfy them, and nothing here
constructs the Gysin map of Stacks 02TO for which they hold. What is missing for the ring is the
step from that
composite to a degreewise product `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` and the laws the Cauchy product
obeys. So the degreewise product, the unit series and the three laws
the Cauchy product obeys — associativity, commutativity and the unit law — are collected in
`Stacks.Chow.ChowCohomologySeriesRing` and carried as a parameter. Every one of its fields is a
property of the real ring `A^*(X)^∧`; what is *not* assumed is anything about Chern classes, and
the Cauchy product itself is constructed here, from the degreewise product, rather than carried.

The Chern classes `c_j(ℰ) ∈ A^j(X)` are Stacks 0B7H, which is also characterized but not
constructed in this repository: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`, where the cap products of Stacks
0B7G enter as the parameter `Stacks.Chow.HigherChernCapRule`. So the series `c(ℰ)` is a field of
`Stacks.Chow.TotalChernClassSeries`; it is pinned down rather than left free, because that
structure also carries, for a module of rank `r`, the assertion that the degree-`j` component of
`c(ℰ)` satisfies the characterization `Stacks.Chow.IsChernClassBivariant` of Stacks 0B7H, and by
`Stacks.Chow.eq_of_isChernClassBivariant` that determines it uniquely.

### Where Stacks 02UI enters, and in what form

Well-definedness of `c` — that it factors through the relations defining `K_0(Vect(X))` — is
exactly the Whitney sum formula of Stacks 02UI, and it is a **hypothesis** here, the field
`ch_shortExact`, in the source's own product form `c(ℰ) = c(ℰ_1) c(ℰ_2)`.

It is not derived from the repository's Stacks 02UI,
`Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.ShortExactSequence`, because that is a different
statement: it is the relation read *componentwise on Chow groups*, between cap products
`c_m(ℰ) ∩ α = ∑_{i+j=m} c_i(ℰ_1) ∩ (c_j(ℰ_2) ∩ α)`, and it carries three inputs of its own.
Deducing the product form from it would need the bivariant Chern classes themselves (Stacks
0B7H), the composition product (Stacks 0FE0) and the compatibility of the cap operation of a
composite with the two cap operations — the step that turns a convolution of cap products into a
Cauchy product of classes. The first two are available: the Chern classes as
`Stacks.Chow.chernClass`, relative to the cap products of Stacks 0B7G, and the composite of two
classes as `Stacks.Chow.bivariantComposite`. The degreewise product assembled from the composite,
the laws it obeys and the cap-compatibility step are not, so the product form is not deduced here and
the relation is assumed in the form the construction consumes.

### The degrees carry their own proofs

A degreewise product has to land in `A^{i+j}(X)`, and `(i + j) + k` and `i + (j + k)` are the
same natural number but not the same term, so writing the laws naively needs transports between
the groups. They are avoided throughout by giving the product an explicit target degree together
with a proof that it is the sum: `Stacks.Chow.GradedChowProductRule` takes `i`, `j`, `n` and a
proof of `i + j = n`. Every equation below is then an equation inside one group `A^n(X)`, and
since proofs of a `Prop` are definitionally equal, no transport is ever needed.

For the same reason the Cauchy product and the recursion defining the formal inverse are indexed
by `Finset.antidiagonal`, whose membership *is* the equation `p.1 + p.2 = n`.

### The map on `K_0`, and why it is a group homomorphism to a multiplicative group

`K_0(Vect(X))` is written additively, the target multiplicatively, so `c` is built as an additive
homomorphism into `Additive` of the group of unital series. The group structure is what makes the
remark's last clause automatic: `c(−α) = c(α)^{-1}` is `map_neg`. The inverse itself is not
chosen out of an existence statement — it is
`Stacks.Chow.ChowCohomologySeriesRing.formalInverse`, defined by the recursion of the module
docstring, and `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesMul_formalInverse` proves it is an
inverse.

Finally, `K_0(Vect(X))` is here
`AlgebraicGeometry.VectorBundleKZero`, whose `classOf` is defined on *every* sheaf of modules and
vanishes off the finite locally free ones; so the Chern class datum is required to take the unit
series on a module that is not finite locally free, which is the same normalisation and is not a
mathematical assumption.

## References

* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-! ### The target of the Chern class map -/

/-- **The target of Stacks 0FEL.** The product `∏_{i ≥ 0} A^i(X)` of the nonnegative-degree Chow
cohomology groups of a scheme `X` locally of finite type over the base: a family
`(a_0, a_1, a_2, …)` with `a_i ∈ A^i(X)`, subject to **no** condition on its support.

The product and not the direct sum, and not the completion `A^*(X)^∧` of Stacks 0FE0 either: the
formal inverse of a total Chern class has a component in every degree in general, and that is the
reason the source writes an infinite product. -/
@[stacks 0FEL "the target: the product over i >= 0 of the Chow cohomology groups A^i(X), with \
  A^i(X) the group Stacks.Chow.chowCohomologyComponent of Stacks 0B7E"]
abbrev chowCohomologySeries : Type (u + 1) :=
  ∀ i : ℕ, chowCohomologyComponent C G sX (i : ℤ)

/-- A degreewise product on Chow cohomology: a map `A^i(X) × A^j(X) ⟶ A^n(X)` for every `i`, `j`
and `n` with `i + j = n`. The target degree is an argument carrying its own proof, so that no
transport between `A^{(i+j)+k}(X)` and `A^{i+(j+k)}(X)` is ever needed. -/
abbrev GradedChowProductRule : Type (u + 1) :=
  ∀ i j n : ℕ, i + j = n →
    chowCohomologyComponent C G sX (i : ℤ) → chowCohomologyComponent C G sX (j : ℤ) →
      chowCohomologyComponent C G sX (n : ℤ)

variable {C G sX}

/-- The term of the Cauchy product of two series indexed by a pair `p` of degrees: the product of
the coefficients in degrees `p.1` and `p.2` when `p` lies on the antidiagonal of `n`, and `0`
otherwise. -/
def chowSeriesTerm (gm : GradedChowProductRule C G sX) (a b : chowCohomologySeries C G sX)
    (n : ℕ) (p : ℕ × ℕ) : chowCohomologyComponent C G sX (n : ℤ) :=
  if h : p.1 + p.2 = n then gm p.1 p.2 n h (a p.1) (b p.2) else 0

/-- The value of `Stacks.Chow.chowSeriesTerm` on the antidiagonal. -/
theorem chowSeriesTerm_of_add (gm : GradedChowProductRule C G sX)
    (a b : chowCohomologySeries C G sX) {n i j : ℕ} (h : i + j = n) :
    chowSeriesTerm gm a b n (i, j) = gm i j n h (a i) (b j) := by
  rw [chowSeriesTerm]
  split
  · rfl
  · next hc => exact absurd h hc

/-- **The Cauchy product of two series of Chow cohomology classes.** Its degree-`n` coefficient is
`∑_{i + j = n} a_i b_j`. This is the multiplication of the ring `A^*(X)^∧` of Stacks 0FE0, read on
the product `∏_{i ≥ 0} A^i(X)`. -/
def chowSeriesMul (gm : GradedChowProductRule C G sX) (a b : chowCohomologySeries C G sX) :
    chowCohomologySeries C G sX :=
  fun n => ∑ p ∈ Finset.antidiagonal n, chowSeriesTerm gm a b n p

/-! ### The formal inverse of a series, for a bare degreewise product

The formal inverse needs neither the laws of `Stacks.Chow.ChowCohomologySeriesRing` nor its unit
series: a degreewise product and a class `u ∈ A^0(X)` to use as the constant term are enough to
write the recursion down, and a left unit law for `u` is enough to make it invert. The inverse of
`Stacks.Chow.ChowCohomologySeriesRing.formalInverse` is this one at `R.gradedMul` and `R.one 0`;
stating it here is what lets the *commutative* series of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries`, which has no such structure
available, use the same inverse rather than a second copy of the recursion. -/

/-- **The formal inverse of a series with constant term `u`**, for a bare degreewise product.
Its coefficients are given by the recursion

  `b_0 = u`,  `b_{n+1} = − ∑_{i + j = n} a_{i+1} b_j`,

which is the unique solution of `a b = 1` when `a_0 = u` is a left unit; see
`Stacks.Chow.chowSeriesMul_gradedFormalInverse`. Nothing bounds the degrees in which it is
nonzero, which is the reason the target of Stacks 0FEL is a product and not a direct sum. -/
def gradedFormalInverse (gm : GradedChowProductRule C G sX)
    (u : chowCohomologyComponent C G sX (0 : ℤ)) (a : chowCohomologySeries C G sX) :
    ∀ n : ℕ, chowCohomologyComponent C G sX (n : ℤ)
  | 0 => u
  | (n + 1) => -∑ p ∈ Finset.antidiagonal n,
      (if h : p.1 + p.2 = n then
        gm (p.1 + 1) p.2 (n + 1) (by omega) (a (p.1 + 1)) (gradedFormalInverse gm u a p.2)
      else 0)

/-- The constant term of the formal inverse is the chosen class `u`. -/
theorem gradedFormalInverse_zero (gm : GradedChowProductRule C G sX)
    (u : chowCohomologyComponent C G sX (0 : ℤ)) (a : chowCohomologySeries C G sX) :
    gradedFormalInverse gm u a 0 = u := by rw [gradedFormalInverse]

/-- **The recursion defining the formal inverse.** -/
theorem gradedFormalInverse_succ (gm : GradedChowProductRule C G sX)
    (u : chowCohomologyComponent C G sX (0 : ℤ)) (a : chowCohomologySeries C G sX) (n : ℕ) :
    gradedFormalInverse gm u a (n + 1) = -∑ p ∈ Finset.antidiagonal n,
      (if h : p.1 + p.2 = n then
        gm (p.1 + 1) p.2 (n + 1) (by omega) (a (p.1 + 1)) (gradedFormalInverse gm u a p.2)
      else 0) := by rw [gradedFormalInverse]

/-- **The formal inverse inverts.** Let `one` be a series concentrated in degree `0` whose
constant term is a left unit for the degreewise product. For a series `a` with `a 0 = one 0` the
Cauchy product of `a` with `Stacks.Chow.gradedFormalInverse` is `one`. -/
theorem chowSeriesMul_gradedFormalInverse {gm : GradedChowProductRule C G sX}
    (one : chowCohomologySeries C G sX) (hsucc : ∀ n : ℕ, one (n + 1) = 0)
    (hunit : ∀ (n : ℕ) (x : chowCohomologyComponent C G sX (n : ℤ)),
      gm 0 n n (Nat.zero_add n) (one 0) x = x)
    (a : chowCohomologySeries C G sX) (ha : a 0 = one 0) :
    chowSeriesMul gm a (gradedFormalInverse gm (one 0) a) = one := by
  funext n
  cases n with
  | zero =>
      rw [chowSeriesMul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        chowSeriesTerm_of_add gm a (gradedFormalInverse gm (one 0) a) (show 0 + 0 = 0 from rfl),
        ha, gradedFormalInverse_zero]
      exact hunit 0 (one 0)
  | succ m =>
      rw [chowSeriesMul, Finset.Nat.sum_antidiagonal_succ,
        chowSeriesTerm_of_add gm a (gradedFormalInverse gm (one 0) a) (Nat.zero_add (m + 1)), ha,
        hunit (m + 1) (gradedFormalInverse gm (one 0) a (m + 1)),
        gradedFormalInverse_succ gm (one 0) a m, hsucc m, neg_add_eq_zero]
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hmem
      rw [Finset.mem_antidiagonal] at hmem
      rw [dite_eq_left hmem, chowSeriesTerm_of_add gm a (gradedFormalInverse gm (one 0) a)
        (show i + 1 + j = m + 1 by omega)]

/-! ### The ring of series -/

/-- **The ring `A^*(X)^∧ = ∏_{i ≥ 0} A^i(X)` of Stacks 0FE0, as a datum.** A degreewise product
on the Chow cohomology of `X`, a unit series, and the laws: the degreewise product is additive in
each variable, the unit series is concentrated in degree `0`, and the Cauchy product it defines is
associative, commutative and has the unit series as a unit.

Every field is a property of the ring structure that Stacks 0FE0 puts on the bivariant classes of
`X`, namely composition of bivariant classes. The composite of two classes is constructed in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class`, but nothing assembles a
degreewise product or the laws below out of it; so, being data, they are a parameter rather than
something quantified over. -/
structure ChowCohomologySeriesRing (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] where
  /-- The degreewise product `A^i(X) × A^j(X) ⟶ A^{i+j}(X)`. -/
  gradedMul : GradedChowProductRule C G sX
  /-- The unit series `1 ∈ ∏_{i ≥ 0} A^i(X)`. -/
  one : chowCohomologySeries C G sX
  /-- The unit series is concentrated in degree `0`. -/
  one_apply_succ : ∀ n : ℕ, one (n + 1) = 0
  /-- The degreewise product is additive in its first variable. -/
  gradedMul_add_left : ∀ (i j n : ℕ) (h : i + j = n)
    (x x' : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)),
    gradedMul i j n h (x + x') y = gradedMul i j n h x y + gradedMul i j n h x' y
  /-- The degreewise product is additive in its second variable. -/
  gradedMul_add_right : ∀ (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y y' : chowCohomologyComponent C G sX (j : ℤ)),
    gradedMul i j n h x (y + y') = gradedMul i j n h x y + gradedMul i j n h x y'
  /-- The Cauchy product is associative. -/
  mul_assoc : ∀ a b c : chowCohomologySeries C G sX,
    chowSeriesMul gradedMul (chowSeriesMul gradedMul a b) c =
      chowSeriesMul gradedMul a (chowSeriesMul gradedMul b c)
  /-- The Cauchy product is commutative. -/
  mul_comm : ∀ a b : chowCohomologySeries C G sX,
    chowSeriesMul gradedMul a b = chowSeriesMul gradedMul b a
  /-- The unit series is a unit for the Cauchy product. -/
  one_mul : ∀ a : chowCohomologySeries C G sX, chowSeriesMul gradedMul one a = a

namespace ChowCohomologySeriesRing

variable (R : ChowCohomologySeriesRing C G sX)

/-- The degreewise product of `0` with anything is `0`. -/
theorem gradedMul_zero_left (i j n : ℕ) (h : i + j = n)
    (y : chowCohomologyComponent C G sX (j : ℤ)) : R.gradedMul i j n h 0 y = 0 := by
  have h0 := R.gradedMul_add_left i j n h 0 0 y
  rw [add_zero] at h0
  simpa using h0.symm

/-- A term of the Cauchy product with the unit series on the left vanishes unless the first degree
is `0`. -/
theorem chowSeriesTerm_one_left_eq_zero (a : chowCohomologySeries C G sX) (n i j : ℕ)
    (hi : i ≠ 0) : chowSeriesTerm R.gradedMul R.one a n (i, j) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [chowSeriesTerm]
  split
  · rw [R.one_apply_succ k, R.gradedMul_zero_left]
  · rfl

/-- **The constant term of the unit series is a unit for the degreewise product.** This is the
normalisation `c_0 = 1` in the form the construction uses it. -/
theorem gradedMul_one_apply_zero (n : ℕ) (x : chowCohomologyComponent C G sX (n : ℤ)) :
    R.gradedMul 0 n n (Nat.zero_add n) (R.one 0) x = x := by
  classical
  have h := congrFun (R.one_mul (Function.update (0 : chowCohomologySeries C G sX) n x)) n
  rw [chowSeriesMul] at h
  rw [Finset.sum_eq_single_of_mem (0, n) (Finset.mem_antidiagonal.mpr (Nat.zero_add n))] at h
  · rw [chowSeriesTerm, dite_eq_left (Nat.zero_add n)] at h
    simpa using h
  · rintro ⟨i, j⟩ hmem hne
    refine R.chowSeriesTerm_one_left_eq_zero _ _ i j ?_
    rintro rfl
    rw [Finset.mem_antidiagonal] at hmem
    simp only [Nat.zero_add] at hmem
    subst hmem
    exact hne rfl

/-! ### The formal inverse -/

/-- **The formal inverse of a series with constant term `1`.** Its coefficients are given by the
recursion

  `b_0 = 1`,  `b_{n+1} = − ∑_{i + j = n} a_{i+1} b_j`,

which is the unique solution of `a b = 1` when `a_0 = 1`; see
`Stacks.Chow.ChowCohomologySeriesRing.chowSeriesMul_formalInverse`. Nothing bounds the degrees in
which it is nonzero, which is why the target of Stacks 0FEL is a product and not a direct sum. -/
def formalInverse (R : ChowCohomologySeriesRing C G sX) (a : chowCohomologySeries C G sX) :
    ∀ n : ℕ, chowCohomologyComponent C G sX (n : ℤ)
  | 0 => R.one 0
  | (n + 1) => -∑ p ∈ Finset.antidiagonal n,
      (if h : p.1 + p.2 = n then
        R.gradedMul (p.1 + 1) p.2 (n + 1) (by omega) (a (p.1 + 1)) (formalInverse R a p.2)
      else 0)

/-- The constant term of the formal inverse is the constant term of the unit series. -/
theorem formalInverse_zero (a : chowCohomologySeries C G sX) :
    R.formalInverse a 0 = R.one 0 := by rw [formalInverse]

/-- **The recursion defining the formal inverse.** -/
theorem formalInverse_succ (a : chowCohomologySeries C G sX) (n : ℕ) :
    R.formalInverse a (n + 1) = -∑ p ∈ Finset.antidiagonal n,
      (if h : p.1 + p.2 = n then
        R.gradedMul (p.1 + 1) p.2 (n + 1) (by omega) (a (p.1 + 1)) (R.formalInverse a p.2)
      else 0) := by rw [formalInverse]

/-- The formal inverse of a series ring is the bare formal inverse at its product and unit. -/
private theorem formalInverse_eq_gradedFormalInverse (a : chowCohomologySeries C G sX) :
    R.formalInverse a = gradedFormalInverse R.gradedMul (R.one 0) a := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [formalInverse_zero, gradedFormalInverse_zero]
    | succ m =>
      rw [formalInverse_succ, gradedFormalInverse_succ]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun p hp => ?_)
      rw [ih p.2 (by have := Finset.mem_antidiagonal.1 hp; omega)]

/-- **The formal inverse inverts.** For a series `a` whose constant term is that of the unit
series, the Cauchy product of `a` with `Stacks.Chow.ChowCohomologySeriesRing.formalInverse` is the
unit series. -/
theorem chowSeriesMul_formalInverse (a : chowCohomologySeries C G sX) (ha : a 0 = R.one 0) :
    chowSeriesMul R.gradedMul a (R.formalInverse a) = R.one := by
  rw [formalInverse_eq_gradedFormalInverse]
  exact chowSeriesMul_gradedFormalInverse R.one R.one_apply_succ R.gradedMul_one_apply_zero a ha

/-! ### The group of unital series -/

/-- **The series with constant term `1`.** Under the Cauchy product these form a commutative
*group*, the formal inverse providing the inverse; the Chern class of a vector bundle is one of
them, and that is what lets the Chern class map be extended multiplicatively to `K_0(Vect(X))`. -/
abbrev UnitalSeries (R : ChowCohomologySeriesRing C G sX) : Type (u + 1) :=
  {a : chowCohomologySeries C G sX // a 0 = R.one 0}

/-- The unital series form a commutative group under the Cauchy product, with the formal inverse
as inverse. -/
instance unitalSeriesCommGroup : CommGroup (UnitalSeries R) where
  mul a b := ⟨chowSeriesMul R.gradedMul a.1 b.1, by
    rw [chowSeriesMul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      chowSeriesTerm_of_add R.gradedMul a.1 b.1 (show 0 + 0 = 0 from rfl), a.2, b.2]
    exact R.gradedMul_one_apply_zero 0 (R.one 0)⟩
  one := ⟨R.one, rfl⟩
  inv a := ⟨R.formalInverse a.1, R.formalInverse_zero a.1⟩
  mul_assoc a b c := Subtype.ext (R.mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (R.one_mul a.1)
  mul_one a := Subtype.ext ((R.mul_comm _ _).trans (R.one_mul a.1))
  inv_mul_cancel a := Subtype.ext ((R.mul_comm _ _).trans (R.chowSeriesMul_formalInverse a.1 a.2))
  mul_comm a b := Subtype.ext (R.mul_comm a.1 b.1)

/-- The underlying series of a product of unital series is their Cauchy product. -/
@[simp] theorem UnitalSeries.val_mul (a b : UnitalSeries R) :
    (a * b).1 = chowSeriesMul R.gradedMul a.1 b.1 := rfl

/-- The underlying series of the unit is the unit series `R.one`. -/
@[simp] theorem UnitalSeries.val_one : (1 : UnitalSeries R).1 = R.one := rfl

/-- The underlying series of an inverse is the formal inverse of the underlying series. -/
@[simp] theorem UnitalSeries.val_inv (a : UnitalSeries R) :
    (a⁻¹).1 = R.formalInverse a.1 := rfl

end ChowCohomologySeriesRing

/-! ### The total Chern class as a datum -/

open ChowCohomologySeriesRing

/-- **The total Chern class, as a datum.** For each sheaf of modules `ℰ` on `X` a series
`c(ℰ) ∈ ∏_{i ≥ 0} A^i(X)` with constant term `1`, such that:

* for a module of rank `r`, its degree-`j` component satisfies the characterization of Stacks
  0B7H, so that it **is** the `j`-th bivariant Chern class `c_j(ℰ)` — the characterization
  determines the class, by `Stacks.Chow.eq_of_isChernClassBivariant`;
* a module that is not finite locally free gets the unit series, the normalisation
  `AlgebraicGeometry.VectorBundleKZero.classOf` uses for the same modules;
* **Stacks 02UI**, the Whitney sum formula: a short exact sequence of finite locally free modules
  `0 ⟶ ℰ_1 ⟶ ℰ_2 ⟶ ℰ_3 ⟶ 0` gives `c(ℰ_2) = c(ℰ_1) c(ℰ_3)` for the Cauchy product.

Which fields are irreducible, and which are not.

`cap` is irreducible here: nothing in this repository constructs a
`Stacks.Chow.HigherChernCapRule`. It is Stacks 0B7G, built in the source from the cap product on
cycles of Stacks 02U5 and its invariance under rational equivalence, Stacks 02U7; reaching those
needs the projective bundle formula of Stacks 02TX, hence Stacks 02TM and the key formula of
Stacks 0AYC, and the twists of Stacks 01O4. None of them is formalized here, and the source proves
each itself rather than citing it, so none may be assumed instead.

`ch` and `ch_isChernClass` are not irreducible given `cap`. On a module of constant rank `r` the
series is `Stacks.Chow.chernClassSeriesOfRank`: its components satisfy the characterization, by
`Stacks.Chow.isChernClassBivariant_chernClassSeriesOfRank`, and it is the only series that does,
by `Stacks.Chow.chernClassSeriesOfRank_eq`. On a module of non-constant rank the classes are the
rank-locus assembly of Stacks 0ESW, `Stacks.Chow.chernClassArbitraryRank`, whose family of
constant-rank classes is `Stacks.Chow.rankLocusChernClass`. What stands between those and a
definition of `ch` on every module is the identification of that assembly with
`Stacks.Chow.chernClass` on a module of globally constant rank — the case `X = X_r` of the
decomposition — which is not proved here; until it is, `ch` stays a field.

`ch_apply_zero` is irreducible for a smaller reason: `R.one 0` is unconstrained, the only
condition on the unit series being `one_apply_succ`, and `c_0 = 1` is a normalisation of the cap
products, Stacks 02U0, that `cap` does not carry. The degree-`0` identity class exists, as
`Stacks.Chow.bivariantIdentityClass` of Stacks 0FBS, but under a Gysin naturality hypothesis for
the identity cap rule that nothing here discharges.

`ch_shortExact` is Stacks 02UI and is irreducible here: the repository's own 02UI,
`Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, is the relation read componentwise on Chow
groups between cap products and carries three inputs of its own; the series-level product form
needs the ring structure of Stacks 0FE0 and the cap-compatibility step, as above. -/
structure GradedTotalChernClassSeries (C : ChowSituation.{u}) (G : GysinSystem C)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (gm : GradedChowProductRule C G sX) (one : chowCohomologySeries C G sX) where
  /-- The Chern cap products of Stacks 0B7G, in every rank. -/
  cap : ∀ r : ℕ, HigherChernCapRule C r
  /-- The total Chern class `c(ℰ) = 1 + c_1(ℰ) + c_2(ℰ) + …` of a sheaf of modules. -/
  ch : X.Modules → chowCohomologySeries C G sX
  /-- The constant term of the total Chern class is `1`; this is `c_0 = 1`, Stacks 02U0. -/
  ch_apply_zero : ∀ E : X.Modules, ch E 0 = one 0
  /-- The degree-`j` component of the total Chern class of a module of rank `r` is the `j`-th
  bivariant Chern class of Stacks 0B7H. -/
  ch_isChernClass : ∀ (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r) (j : Fin (r + 1)),
    IsChernClassBivariant C sX E r G (cap r) hrank j (ch E (j : ℕ))
  /-- A module that is not finite locally free gets the unit series. -/
  ch_eq_one_of_not_isFiniteLocallyFree : ∀ E : X.Modules,
    ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      ch E = one
  /-- **Stacks 02UI, the Whitney sum formula.** A short exact sequence of finite locally free
  modules `0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` gives `c(E₂) = c(E₁) c(E₃)`. -/
  ch_shortExact : ∀ {E₁ E₂ E₃ : X.Modules} (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (w : f ≫ g = 0),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₁ →
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₂ →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₃ →
          Mono f → Epi g → (CategoryTheory.ShortComplex.mk f g w).Exact →
            ch E₂ = chowSeriesMul gm (ch E₁) (ch E₃)

/-- **The total Chern class, as a datum.** For each sheaf of modules `ℰ` on `X` a series
`c(ℰ) ∈ ∏_{i ≥ 0} A^i(X)` with constant term `1`, such that:

* for a module of rank `r`, its degree-`j` component satisfies the characterization of Stacks
  0B7H, so that it **is** the `j`-th bivariant Chern class `c_j(ℰ)` — the characterization
  determines the class, by `Stacks.Chow.eq_of_isChernClassBivariant`;
* a module that is not finite locally free gets the unit series, the normalisation
  `AlgebraicGeometry.VectorBundleKZero.classOf` uses for the same modules;
* **Stacks 02UI**, the Whitney sum formula: a short exact sequence of finite locally free modules
  `0 ⟶ ℰ_1 ⟶ ℰ_2 ⟶ ℰ_3 ⟶ 0` gives `c(ℰ_2) = c(ℰ_1) c(ℰ_3)` for the Cauchy product.

Which fields are irreducible, and which are not.

`cap` is irreducible here: nothing in this repository constructs a
`Stacks.Chow.HigherChernCapRule`. It is Stacks 0B7G, built in the source from the cap product on
cycles of Stacks 02U5 and its invariance under rational equivalence, Stacks 02U7; reaching those
needs the projective bundle formula of Stacks 02TX, hence Stacks 02TM and the key formula of
Stacks 0AYC, and the twists of Stacks 01O4. None of them is formalized here, and the source proves
each itself rather than citing it, so none may be assumed instead.

`ch` and `ch_isChernClass` are not irreducible given `cap`. On a module of constant rank `r` the
series is `Stacks.Chow.chernClassSeriesOfRank`: its components satisfy the characterization, by
`Stacks.Chow.isChernClassBivariant_chernClassSeriesOfRank`, and it is the only series that does,
by `Stacks.Chow.chernClassSeriesOfRank_eq`. On a module of non-constant rank the classes are the
rank-locus assembly of Stacks 0ESW, `Stacks.Chow.chernClassArbitraryRank`, whose family of
constant-rank classes is `Stacks.Chow.rankLocusChernClass`. What stands between those and a
definition of `ch` on every module is the identification of that assembly with
`Stacks.Chow.chernClass` on a module of globally constant rank — the case `X = X_r` of the
decomposition — which is not proved here; until it is, `ch` stays a field.

`ch_apply_zero` is irreducible for a smaller reason: `R.one 0` is unconstrained, the only
condition on the unit series being `one_apply_succ`, and `c_0 = 1` is a normalisation of the cap
products, Stacks 02U0, that `cap` does not carry. The degree-`0` identity class exists, as
`Stacks.Chow.bivariantIdentityClass` of Stacks 0FBS, but under a Gysin naturality hypothesis for
the identity cap rule that nothing here discharges.

`ch_shortExact` is Stacks 02UI and is irreducible here: the repository's own 02UI,
`Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, is the relation read componentwise on Chow
groups between cap products and carries three inputs of its own; the series-level product form
needs the ring structure of Stacks 0FE0 and the cap-compatibility step, as above. -/
structure TotalChernClassSeries (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (R : ChowCohomologySeriesRing C G sX) where
  /-- The Chern cap products of Stacks 0B7G, in every rank. -/
  cap : ∀ r : ℕ, HigherChernCapRule C r
  /-- The total Chern class `c(ℰ) = 1 + c_1(ℰ) + c_2(ℰ) + …` of a sheaf of modules. -/
  ch : X.Modules → chowCohomologySeries C G sX
  /-- The constant term of the total Chern class is `1`; this is `c_0 = 1`, Stacks 02U0. -/
  ch_apply_zero : ∀ E : X.Modules, ch E 0 = R.one 0
  /-- The degree-`j` component of the total Chern class of a module of rank `r` is the `j`-th
  bivariant Chern class of Stacks 0B7H. -/
  ch_isChernClass : ∀ (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r) (j : Fin (r + 1)),
    IsChernClassBivariant C sX E r G (cap r) hrank j (ch E (j : ℕ))
  /-- A module that is not finite locally free gets the unit series. -/
  ch_eq_one_of_not_isFiniteLocallyFree : ∀ E : X.Modules,
    ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      ch E = R.one
  /-- **Stacks 02UI, the Whitney sum formula.** A short exact sequence of finite locally free
  modules `0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` gives `c(E₂) = c(E₁) c(E₃)`. -/
  ch_shortExact : ∀ {E₁ E₂ E₃ : X.Modules} (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (w : f ≫ g = 0),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₁ →
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₂ →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₃ →
          Mono f → Epi g → (CategoryTheory.ShortComplex.mk f g w).Exact →
            ch E₂ = chowSeriesMul R.gradedMul (ch E₁) (ch E₃)

/-- A total Chern class datum for a series ring is one for its degreewise product and unit
series. -/
def TotalChernClassSeries.toGraded {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {R : ChowCohomologySeriesRing C G sX}
    (D : TotalChernClassSeries C G sX R) : GradedTotalChernClassSeries C G sX R.gradedMul R.one :=
  ⟨D.cap, D.ch, D.ch_apply_zero, D.ch_isChernClass, D.ch_eq_one_of_not_isFiniteLocallyFree,
    D.ch_shortExact⟩

/-- A total Chern class datum for the degreewise product and unit series of a series ring is one
for the series ring. -/
def GradedTotalChernClassSeries.toTotal {C : ChowSituation.{u}} {G : GysinSystem C}
    {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {R : ChowCohomologySeriesRing C G sX}
    (D : GradedTotalChernClassSeries C G sX R.gradedMul R.one) : TotalChernClassSeries C G sX R :=
  ⟨D.cap, D.ch, D.ch_apply_zero, D.ch_isChernClass, D.ch_eq_one_of_not_isFiniteLocallyFree,
    D.ch_shortExact⟩

/-! ### The Chern class map on `K_0(Vect(X))` -/

variable {R : ChowCohomologySeriesRing C G sX}

/-- **Stacks 0FEL, as a homomorphism of groups.** The Chern class map
`c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`, read as a homomorphism from `K_0(Vect(X))` to the group of
series with constant term `1` written additively. The universal property of `K_0(Vect(X))` applies
because the Whitney sum formula makes `ℰ ↦ c(ℰ)` additive on short exact sequences once the target
is written additively; that is the well-definedness the source gets from Stacks 02UI. -/
def chernClassKGroupHom (D : TotalChernClassSeries C G sX R) :
    AlgebraicGeometry.VectorBundleKZero X →+ Additive (UnitalSeries R) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom
    (fun E => Additive.ofMul (⟨D.ch E, D.ch_apply_zero E⟩ : UnitalSeries R))
    (fun E hE => by
      refine congrArg Additive.ofMul (Subtype.ext ?_)
      exact D.ch_eq_one_of_not_isFiniteLocallyFree E hE)
    (fun f g w h₁ h₂ h₃ _ _ hex => by
      rw [← ofMul_mul]
      refine congrArg Additive.ofMul (Subtype.ext ?_)
      exact D.ch_shortExact f g w h₁ h₂ h₃ inferInstance inferInstance hex)

/-- The Chern class map of Stacks 0FEL on the class of a module is the total Chern class of that
module, read in the group of series with constant term `1`. -/
theorem chernClassKGroupHom_classOf (D : TotalChernClassSeries C G sX R) (E : X.Modules) :
    chernClassKGroupHom D (AlgebraicGeometry.VectorBundleKZero.classOf X E) =
      Additive.ofMul (⟨D.ch E, D.ch_apply_zero E⟩ : UnitalSeries R) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf _ _ _ E

/-- **Stacks 0FEL.** The Chern class map

  `c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`,

sending the generator `[ℰ]` to `c(ℰ) = 1 + c_1(ℰ) + c_2(ℰ) + …` and extended multiplicatively;
so `−[ℰ]` goes to the formal inverse `c(ℰ)^{-1}`, which is why the target is the infinite product.
It is well defined by the Whitney sum formula of Stacks 02UI. -/
@[stacks 0FEL "the map c : K_0(Vect(X)) -> prod_{i >= 0} A^i(X) itself, with K_0(Vect(X)) the \
  Grothendieck group AlgebraicGeometry.VectorBundleKZero of Stacks 0FDK and A^i(X) the Chow \
  cohomology Stacks.Chow.chowCohomologyComponent of Stacks 0B7E. CARRIED, as the two fields of \
  the parameters R and D: (1) the ring structure of A^*(X)^∧, Stacks 0FE0 -- composition of \
  bivariant classes, whose composite StacksDraft.AlgebraicGeometry.Chow.BivariantComposition \
  .Class constructs as Stacks.Chow.bivariantComposite, though nothing here assembles the ring \
  out of it -- namely a degreewise product A^i x A^j -> A^{i+j}, additive in each variable, a \
  unit series, and associativity, commutativity and the unit law for the Cauchy product it \
  defines; (2) the total Chern class series c(E) of each module; Stacks 0B7H is constructed \
  here, as Stacks.Chow.chernClass, but relative to the Chern cap products of Stacks 0B7G \
  that the characterization is read against (the parameter Stacks.Chow.HigherChernCapRule), \
  which rest on Stacks 02U5 and 02U7 and are not formalized here; and \
  (3) the Whitney sum formula c(E_2) = c(E_1) c(E_3) of Stacks 02UI in the source's product \
  form, which is the well-definedness. The repository's Stacks 02UI, \
  Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact, is the relation read componentwise on Chow \
  groups between cap products and does not give the product form: that deduction needs the \
  bivariant Chern classes of Stacks 0B7H, the composition product of Stacks 0FE0 and the \
  compatibility of the cap operation of a composite with the two cap operations; the first two \
  are available, the degreewise product built from the composite and the last are not. NOT \
  carried, and constructed here: the product prod_{i >= 0} A^i(X), the Cauchy \
  product on it, the formal inverse of a series with constant term 1 and the proof that it \
  inverts, the group of such series, and the map c with the three properties below"]
def chernClassKGroup (D : TotalChernClassSeries C G sX R) :
    AlgebraicGeometry.VectorBundleKZero X → chowCohomologySeries C G sX :=
  fun α => (Additive.toMul (chernClassKGroupHom D α) : UnitalSeries R).1

/-- The Chern class map sends the generator `[ℰ]` to the total Chern class `c(ℰ)`. -/
theorem chernClassKGroup_classOf (D : TotalChernClassSeries C G sX R) (E : X.Modules) :
    chernClassKGroup D (AlgebraicGeometry.VectorBundleKZero.classOf X E) = D.ch E := by
  rw [chernClassKGroup, chernClassKGroupHom,
    AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf]
  rfl

/-- **The Chern class map is multiplicative**, which is what "extending multiplicatively" means:
the sum in `K_0(Vect(X))` goes to the Cauchy product of series. This is the content Stacks 02UI
supplies. -/
@[stacks 0FEL "the multiplicativity -- extending multiplicatively -- of the map, which is its \
  well-definedness on K_0(Vect(X)); the Whitney sum formula of Stacks 02UI is carried, see the \
  attribute on Stacks.Chow.chernClassKGroup"]
theorem chernClassKGroup_add (D : TotalChernClassSeries C G sX R)
    (α β : AlgebraicGeometry.VectorBundleKZero X) :
    chernClassKGroup D (α + β) =
      chowSeriesMul R.gradedMul (chernClassKGroup D α) (chernClassKGroup D β) := by
  rw [chernClassKGroup, map_add, toMul_add]
  rfl

/-- The Chern class map sends `0` to the unit series. -/
theorem chernClassKGroup_zero (D : TotalChernClassSeries C G sX R) :
    chernClassKGroup D 0 = R.one := by
  rw [chernClassKGroup, map_zero]
  rfl

/-- **The Chern class map sends a negative to the formal inverse.** -/
theorem chernClassKGroup_neg (D : TotalChernClassSeries C G sX R)
    (α : AlgebraicGeometry.VectorBundleKZero X) :
    chernClassKGroup D (-α) = R.formalInverse (chernClassKGroup D α) := by
  rw [chernClassKGroup, map_neg, toMul_neg]
  rfl

/-- **Stacks 0FEL, the last clause of the remark.** `−[ℰ]` is sent to the formal inverse
`c(ℰ)^{-1}`: its coefficients are given by the recursion of
`Stacks.Chow.ChowCohomologySeriesRing.formalInverse_succ`, which is not supported in finitely many
degrees in general, and the Cauchy product of `c([ℰ])` with it is the unit series. This is why the
target of the map is the infinite product `∏_{i ≥ 0} A^i(X)` rather than a finite sum. -/
@[stacks 0FEL "the clause that -[E] is sent to the formal inverse c(E)^{-1}, which is why the \
  target is an infinite product; the formal inverse is constructed here by the recursion \
  Stacks.Chow.ChowCohomologySeriesRing.formalInverse_succ and is not carried"]
theorem chernClassKGroup_neg_classOf (D : TotalChernClassSeries C G sX R) (E : X.Modules) :
    chernClassKGroup D (-AlgebraicGeometry.VectorBundleKZero.classOf X E) =
        R.formalInverse (D.ch E) ∧
      chowSeriesMul R.gradedMul (D.ch E)
        (chernClassKGroup D (-AlgebraicGeometry.VectorBundleKZero.classOf X E)) = R.one := by
  have h : chernClassKGroup D (-AlgebraicGeometry.VectorBundleKZero.classOf X E) =
      R.formalInverse (D.ch E) := by
    rw [chernClassKGroup_neg, chernClassKGroup_classOf]
  refine ⟨h, ?_⟩
  rw [h]
  exact R.chowSeriesMul_formalInverse (D.ch E) (D.ch_apply_zero E)

end Stacks.Chow

end
