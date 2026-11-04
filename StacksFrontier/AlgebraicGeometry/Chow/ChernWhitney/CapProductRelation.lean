module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.BinomialInversion
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# The Whitney relation for an invertible subsheaf, componentwise on Chow groups

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 and let

  `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules with `ℒ` invertible, `ℰ` of rank
`r + 1` and `ℱ` of rank `r`. [Stacks, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH) is the
Whitney relation `c(ℰ) = c(ℒ) · c(ℱ)` between the total Chern classes. This file states and
proves that relation **componentwise, as an identity between cap products on Chow groups**:

  `c_{i+1}(ℰ) ∩ α = c_{i+1}(ℱ) ∩ α + c₁(ℒ) ∩ (c_i(ℱ) ∩ α)`.

## Why componentwise, and not as a product of total classes

The product form cannot be written in this repository. `Stacks.Chow.IsTotalChernClass` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass` takes values in
`Stacks.Chow.nonhomogeneousBivariantGroup`, a direct sum of bivariant groups carrying no
`Mul`, `Monoid` or `Ring` instance; there is no `totalChernClass` *function* at all, only the
predicate together with `Stacks.Chow.bivariantFormalSum`, which receives the homogeneous classes
as an argument; and the composition that would supply the multiplication is unproved, blocked on
Stacks 0B6Y and through it Stacks 02OR, as
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic` records.

Expanding `c(ℒ) = 1 + c₁(ℒ)` and comparing coefficients turns the product form into exactly the
relation above, which needs no multiplication: only the cap products of Stacks 02U5 and the
descended first Chern class cap product of Stacks 02TI, which compose because the first lands in
a Chow group and the second is defined on one. This is also the reduction the source proof
performs itself, so nothing is lost.

## What is carried, and why

The proof of Stacks 02UH twists the sequence by `ℒ^{⊗ -1}`, so that its subsheaf becomes the
structure sheaf and Stacks 02UG identifies the Chern classes of the twisted middle and quotient
terms; reading the twist formula of Stacks 02UD on both terms then produces two binomial
transforms, at `r + 1` and at `r`, that agree. That agreement is carried here as the hypothesis
`hbinom` of `Stacks.Chow.chernClassCapExt_succ_eq_add_firstChernCap`, stated with the binomial
transform of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.BinomialInversion` along the
graded endomorphism `Stacks.Chow.inverseFirstChernCapStep`. Neither Stacks 02UD nor Stacks 02UG
is proved in this repository — both are stated here without proof — so the
agreement of the transforms is an input and is named as such in the `@[stacks 02UH]` clause.

Inverting the transform is then the entire remaining content, and it is pure algebra; it is
proved in the file named above, for a family of abelian groups with a degree-raising additive
endomorphism, which is what the cap products form.

Three further inputs are explicit parameters, each of them already carried that way by the
declarations this file composes:

* `chernE` and `chernF`, the component data of Stacks 02U0, which
  `Stacks.Chow.chernClassCap` takes as an explicit argument because Stacks 02U0 and the
  projective bundle formula beneath it are not in this repository;
* `hfac`, the assertion of Stacks 02TI that the first Chern class cap product of the invertible
  subsheaf factors through rational equivalence, which
  `Stacks.Chow.firstChernClassCapOnChow` takes as an explicit argument, and which is
  *equivalent* to the existence of the descended operation by
  `Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff`.

## Main definitions

* `Stacks.Chow.chernClassCapExt` — the cap product of Stacks 02U5 indexed by a natural number
  and extended by zero above the rank, so that the relation can be read at every index without
  `Fin` coercions.
* `Stacks.Chow.firstChernCapStep` — `c₁(L) ∩ -` as a map `A_{n-i}(X) ⟶ A_{n-(i+1)}(X)`, and
  `Stacks.Chow.inverseFirstChernCapStep` its negative, which by Stacks 02SQ is
  `c₁(L^{⊗ -1}) ∩ -`.
* `Stacks.Chow.chernCapFamily` — the graded sequence `j ↦ c_j(ℰ) ∩ α`.

## Main results

* `Stacks.Chow.chernClassCapExt_succ_eq_add_firstChernCap` — **Stacks 02UH**, componentwise.

## References

* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The cap product of Stacks 02U5, indexed by a natural number -/

/-- **Stacks 02U5, extended by zero.** Intersection with the `i`-th Chern class of a finite
locally free module of rank `r`, as a homomorphism `Z_n(X) ⟶ A_{n-i}(X)` indexed by a natural
number `i`: it is the cap product of `Stacks.Chow.chernClassCap` for `i ≤ r` and zero above the
rank, which is the standard convention and the one the Whitney relation needs in order to be
stated at `i = r + 1` for the quotient.

Indexing by a natural number rather than by `Fin (r + 1)` is what makes the relation below free
of `Fin.castSucc` crossings between the two ranks `r + 1` and `r`. -/
def chernClassCapExt (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (E : X.Modules) (r : ℕ) (hrank : PullbackPreservesRank E r)
    (chern : ChernClassCycleRule C r) (i : ℕ) :
    CycleGroup C p n →+ chowGroup C p (n - (i : ℤ)) :=
  if h : i ≤ r then chernClassCap C p E r hrank n ⟨i, Nat.lt_succ_of_le h⟩ chern else 0

/-- Up to the rank, the extended cap product is the cap product of Stacks 02U5. -/
theorem chernClassCapExt_of_le (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (E : X.Modules) (r : ℕ) (hrank : PullbackPreservesRank E r)
    (chern : ChernClassCycleRule C r) (i : ℕ) (h : i ≤ r) :
    chernClassCapExt C p n E r hrank chern i =
      chernClassCap C p E r hrank n ⟨i, Nat.lt_succ_of_le h⟩ chern :=
  dite_eq_left h

/-- Above the rank the extended cap product is zero. -/
theorem chernClassCapExt_of_gt (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (E : X.Modules) (r : ℕ) (hrank : PullbackPreservesRank E r)
    (chern : ChernClassCycleRule C r) (i : ℕ) (h : ¬ i ≤ r) :
    chernClassCapExt C p n E r hrank chern i = 0 :=
  dite_eq_right h

/-- The graded sequence of cap products of a fixed cycle: `j ↦ c_j(E) ∩ α`, an element of
`A_{n-j}(X)` in each degree `j`. -/
def chernCapFamily (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (E : X.Modules) (r : ℕ) (hrank : PullbackPreservesRank E r)
    (chern : ChernClassCycleRule C r) (α : CycleGroup C p n) :
    ∀ j : ℕ, chowGroup C p (n - (j : ℤ)) :=
  fun j => chernClassCapExt C p n E r hrank chern j α

/-! ### The first Chern class cap product as a graded endomorphism -/

/-- **Stacks 02TI for an invertible module, in every degree.** The assertion that the first Chern
class cap product of `L` factors through rational equivalence in every degree, which is what
`Stacks.Chow.firstChernClassCapOnChow` needs in order to be formed in every degree at once.

By `Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff` this is equivalent to
the existence of the descended operations, so carrying it is not a weakening. -/
abbrev InvertibleChernCapDescends (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Prop :=
  ∀ m : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C p m
    (firstChernComponentCycleRule C p m L)

/-- **Stacks 02SO and 02TI.** Intersection with the first Chern class of an invertible module,
read as a map `A_{n-i}(X) ⟶ A_{n-(i+1)}(X)` between the Chow groups a cap product of degree `i`
and of degree `i + 1` land in. This is the degree-raising endomorphism along which the binomial
transform of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.BinomialInversion` is taken. -/
def firstChernCapStep (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfac : InvertibleChernCapDescends C p L) (i : ℕ) :
    chowGroup C p (n - (i : ℤ)) →+ chowGroup C p (n - ((i + 1 : ℕ) : ℤ)) :=
  chowGroupDegreeCast C p (show n - (i : ℤ) = n - ((i + 1 : ℕ) : ℤ) + 1 by omega)
    (firstChernClassCapOnChow C p (n - ((i + 1 : ℕ) : ℤ))
      (firstChernComponentCycleRule C p (n - ((i + 1 : ℕ) : ℤ)) L) (hfac _))

/-- The negative of `Stacks.Chow.firstChernCapStep`.

By [Stacks, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ) this is intersection with
`c₁(L^{⊗ -1})`, which is the element the proof of Stacks 02UH takes binomial transforms along:
the sequence is twisted by the inverse of its invertible subsheaf. The tensor inverse of an
invertible module is not available in this repository in proved form, so this
operator is *defined* as the negative, and the identification with `c₁(L^{⊗ -1}) ∩ -` is part of
what the hypothesis of the Whitney relation below carries. -/
def inverseFirstChernCapStep (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (n : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfac : InvertibleChernCapDescends C p L) (i : ℕ) :
    chowGroup C p (n - (i : ℤ)) →+ chowGroup C p (n - ((i + 1 : ℕ) : ℤ)) :=
  -firstChernCapStep C p n L hfac i

/-! ### The Whitney relation -/

/-- **Stacks 02UH, componentwise on cap products.** For a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of finite locally free modules with `S.X₁` invertible, `S.X₂` of
rank `r + 1` and `S.X₃` of rank `r`, and for every `n`-cycle `α`,

  `c_{i+1}(S.X₂) ∩ α = c_{i+1}(S.X₃) ∩ α + c₁(S.X₁) ∩ (c_i(S.X₃) ∩ α)`

in `A_{n-i-1}(X)`, for every `i ≤ r`. Summing over `i` and expanding `c(S.X₁) = 1 + c₁(S.X₁)`
this is the relation `c(S.X₂) = c(S.X₁) · c(S.X₃)` of the source; see the module documentation
for why the product form cannot be written here.

The hypothesis `hbinom` is the input: the equality of the binomial transform of the Chern cap
products of `S.X₂` at `r + 1` with that of `S.X₃` at `r`, along `c₁` of the inverse of the
invertible subsheaf. That equality is what Stacks 02UD gives for the twists of `S.X₂` and `S.X₃`
by `S.X₁^{⊗ -1}` once Stacks 02UG has identified the two twisted sheaves' Chern classes, and
neither of those tags is proved in this repository. -/
@[stacks 02UH "CORRECTION OF FORM: the source states c(E) = c(L)c(F) in the bivariant ring \
  A^*(X). That product is not stated here, and cannot be: this development has no ring \
  structure on bivariant classes and no total Chern class, because Chern classes are built as \
  operations CycleGroup C p k -> chowGroup C p (k - j) on X's own cycles (Stacks 02U5) rather \
  than as bivariant classes over all Y -> X -- the source's formulation needs proper pushforward \
  on Chow groups, Stacks 0GU8, which this repository does not have. What is proved instead is \
  the componentwise identity c_{i+1}(E) = c_{i+1}(F) + c₁(L)c_i(F) that the source's own proof \
  reduces the product to, for every n and every cycle alpha in CycleGroup C p n. \
  Carried: hbinom (the equality of binomial transforms that Stacks 02UD at the twists by the \
  inverse of the invertible subsheaf gives once Stacks 02UG is applied to them), the Stacks \
  02U0 data chernE and chernF, and Stacks 02TI for c₁ of the subsheaf as hfac"]
theorem chernClassCapExt_succ_eq_add_firstChernCap (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ) (S : ShortComplex X.Modules)
    (_hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property S.X₁]
    (r : ℕ) (hrankE : PullbackPreservesRank S.X₂ (r + 1))
    (hrankF : PullbackPreservesRank S.X₃ r) (chernE : ChernClassCycleRule C (r + 1))
    (chernF : ChernClassCycleRule C r) (hfac : InvertibleChernCapDescends C p S.X₁)
    (α : CycleGroup C p n) (i : ℕ) (hi : i + 1 ≤ r + 1)
    (hbinom : ∀ m ≤ r + 1,
      binomialTransform (inverseFirstChernCapStep C p n S.X₁ hfac) (r + 1)
          (chernCapFamily C p n S.X₂ (r + 1) hrankE chernE α) m =
        binomialTransform (inverseFirstChernCapStep C p n S.X₁ hfac) r
          (chernCapFamily C p n S.X₃ r hrankF chernF α) m) :
    chernClassCapExt C p n S.X₂ (r + 1) hrankE chernE (i + 1) α =
      chernClassCapExt C p n S.X₃ r hrankF chernF (i + 1) α +
        firstChernCapStep C p n S.X₁ hfac i
          (chernClassCapExt C p n S.X₃ r hrankF chernF i α) := by
  have h := eq_sub_of_binomialTransform_eq (inverseFirstChernCapStep C p n S.X₁ hfac)
    (chernCapFamily C p n S.X₂ (r + 1) hrankE chernE α)
    (chernCapFamily C p n S.X₃ r hrankF chernF α) r i hi hbinom
  simp only [chernCapFamily] at h
  rw [h]
  simp only [inverseFirstChernCapStep, AddMonoidHom.neg_apply, sub_neg_eq_add]

end Stacks.Chow


end
