module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of a module containing the structure sheaf as a subbundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let

  `0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0`

be a short exact sequence of finite locally free `O_X`-modules, with `ℰ` of rank `r` and `ℱ` of
rank `r - 1`. [Stacks, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG) asserts

  `c_r(ℰ) = 0`  and  `c_j(ℰ) = c_j(ℱ)` for `j = 0, …, r - 1`,

as an identity in `A^*(X)`. This file states and proves that identity **on cap products**: for
every degree `k` and every class `α ∈ A_k(X)`,

  `c_r(ℰ) ∩ α = 0`  and  `c_j(ℰ) ∩ α = c_j(ℱ) ∩ α` in `A_{k-j}(X)`.

## Why on cap products, and not in `A^*(X)`

The source's `A^*(X)` is not available in this repository, and neither is anything that would let
an identity be asserted in it:

* `Stacks.Chow.nonhomogeneousBivariantGroup` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass`, the graded group
  `⊕_p A^p(X ⟶ X)`, carries no `Mul`, no `Monoid` and no `Ring` instance, and the composition
  that would supply one is unproved, blocked on Stacks 0B6Y and through it Stacks 02OR, as
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic` records;
* there is no total Chern class *function*: `Stacks.Chow.IsTotalChernClass` is a predicate on an
  element of that group, and `Stacks.Chow.bivariantFormalSum` receives the homogeneous classes as
  an argument.

The Chern classes themselves are present only as the cap products of Stacks 02U5 and 02U6, so a
per-degree identity between those operators is the strongest form the statement can take here.
Nothing of Stacks 02UG is lost in the passage: the source's two conclusions are each an identity
between homogeneous components, and a homogeneous bivariant class on `X ⟶ X` is determined by its
cap products, so the statements below say what the source says, degree by degree, on every class
of every degree.

## The inputs of the two theorems

The proof is the proof of the source. Write the ranks as `r + 2` and `r + 1`. Let
`(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ` and `(ϖ : Q ⟶ X, O_Q(1))` that of `ℱ`. The
surjection `ℰ ⟶ ℱ` gives a closed immersion `ι : Q ⟶ P` over `X`; the section of `O_P(1)`
corresponding to `1 ∈ Γ(X, O_X)` vanishes exactly along `Q`, so `Q` is an effective Cartier
divisor on `P` with `O_P(Q) ≅ O_P(1)`, and therefore
`c₁(O_P(1)) ∩ π^*β = ι_*(ϖ^*β)` by Stacks 02TR. Combining that with Stacks 02SU — proper
pushforward commutes with the first Chern class cap — turns the `i`-th summand of the relation
of Stacks 02U6 over `Q` into the `(i+1)`-st summand of the relation over `P`. That single
identity, summand by summand, is the hypothesis
`Stacks.Chow.ChernTermsCompatibleWithTrivialSubbundle`: neither Stacks 02TR nor the instance of
Stacks 02SU needed here is available for the Chow groups and the unrelated first Chern class cap
operators occurring here, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward`, whose
hypothesis `Stacks.Chow.ChernTermsCompatibleWithPushforward` this one is the index-shifted
analogue of.

Everything else is proved: the family of `ℱ` extended by zero in the top degree satisfies the
relation over `P` and has `α` in degree `k`, so the uniqueness of Stacks 02U6 identifies it with
the family of `ℰ`, and its top member is zero while its lower members are those of `ℱ`.

As in the two files named above, the projective bundles, their twists and the injectivity half of
Stacks 02TX are parameters, because Stacks 02TX and the representability of the twists (Stacks
01O4) are not in this repository. Of Stacks 02TX only injectivity enters, and only over `P`.

That a flat pullback factors through rational equivalence, Stacks 02S1, is **not** a parameter of
the two theorems of Stacks 02UG below: for an arbitrary flat morphism of relative dimension `r`
it is the theorem `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and both
theorems supply it from there for `π` and for `ϖ`. The intermediate declarations of this file
still take it as an argument, because they are stated for an arbitrary such datum.

### The short exact sequence, and where it acts

`ℰ`, `ℱ`, the sequence, its exactness, the ranks `r + 2` and `r + 1`, and the identification of
its subsheaf with `O_X` are explicit hypotheses of the two theorems of Stacks 02UG below, named
`_S`, `_hexact`, `_hunit` and the two rank instances. They are not used in the proofs: in the
source they serve exactly to produce the closed immersion `ι` and the vanishing of the section of
`O_P(1)`, which is to say exactly to produce `ι` and
`Stacks.Chow.ChernTermsCompatibleWithTrivialSubbundle`, and those are arguments here. Keeping
them is what makes the statements statements *about a short exact sequence with trivial
subsheaf*, rather than about an arbitrary pair of bundles with a proper morphism between them.

### The source's rank `r = 1` is excluded

The ranks are written `r + 2` and `r + 1`, so the source's rank is at least `2`. The degenerate
case `r = 1` — where `ℱ` has rank `0`, hence is zero, and `ℰ ≅ O_X` — cannot be stated in the
spelling of `Stacks.Chow.projectiveBundleChernTerm`, whose summands land in degree
`k + (r - 1) - r` with `r - 1` computed in `ℕ`: for a rank-`0` quotient that degree is `k`, not
`k - 1`, so the summands over `Q` and over `P` live in degrees that differ by one and no
pushforward relates them. The projective bundle of a rank-`0` module is empty, which is where the
degeneration comes from. This is a restriction of the source's generality and is named in the
`@[stacks 02UG]` clauses.

## Main definitions

* `Stacks.Chow.chernFamilyExtendByZero` — a family `(α_j)_{j ≤ r+1}` of Chow classes on `X`,
  extended by `0` in degree `r + 2`.
* `Stacks.Chow.ChernTermsCompatibleWithTrivialSubbundle` — **Stacks 02TR and 02SU, assembled**:
  proper pushforward along `ι : Q ⟶ P` carries the `i`-th summand of the relation of Stacks 02U6
  over `Q` to the `(i+1)`-st summand over `P`.

## Main results

* `Stacks.Chow.projectiveBundleChernRelation_chernFamilyExtendByZero` — the extension by zero of
  a family satisfying the relation over `Q` satisfies the relation over `P`.
* `Stacks.Chow.isChernCapFamily_chernFamilyExtendByZero` — the same for the characterization of
  Stacks 02U6.
* `Stacks.Chow.eq_chernFamilyExtendByZero` — the family of `ℰ` is the family of `ℱ` extended by
  zero.
* `Stacks.Chow.chernCap_top_eq_zero` — **Stacks 02UG**, the vanishing `c_r(ℰ) ∩ α = 0`.
* `Stacks.Chow.chernCap_castSucc_eq` — **Stacks 02UG**, the agreement
  `c_j(ℰ) ∩ α = c_j(ℱ) ∩ α` for `j ≤ r - 1`.

## References

* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Evaluating a family at indices equal by arithmetic -/

/-- Transport of the value of a family of Chow classes along an equality of indices. The relation
of Stacks 02U6 indexes its summands by `i` and the family by `r - i`, and the index shift of this
file turns `r + 2 - (i + 1)` into `r + 1 - i`; those are equal by arithmetic on `ℕ` and not as
terms, so some transport is unavoidable. -/
private theorem chowGroupCast_family_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {I : Type*} (deg : I → ℤ)
    (b : ∀ i : I, chowGroup C sX (deg i)) {i j : I} (h : i = j) :
    b j = chowGroupCast C sX (congrArg deg h) (b i) := by
  subst h
  rfl

/-! ### The two bundles and the compatibility of their relations -/

variable (C : ChowSituation.{u}) {X P Q : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (ϖ : Q ⟶ X) [LocallyOfFiniteType ϖ] [Flat ϖ] (hsQ : ϖ ≫ sX = sQ)
  (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r + 2 - 1))
  (hϖ : AlgebraicGeometry.RelativeDimension ϖ (r + 1 - 1))
  (hfacP : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r + 2 - 1) hπ k)
  (hfacQ : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sQ sX ϖ hsQ (r + 1 - 1) hϖ k)
  (twistP : ChernCapOperator C sP) (twistQ : ChernCapOperator C sQ)
  (ι : Q ⟶ P) [IsProper ι] (hι : ι ≫ sP = sQ)

/-- A family `(α_j)_{0 ≤ j ≤ r+1}` of Chow classes on `X`, with `α_j` of degree `k - j`, read as
a family indexed by `0 ≤ j ≤ r + 2` by setting its top member to zero.

This is the family the source produces: the Chern classes of the rank-`r+2` module `ℰ` are those
of the rank-`r+1` quotient `ℱ` below the top degree, and zero in the top degree. -/
def chernFamilyExtendByZero (k : ℤ) (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (j : Fin (r + 3)) : chowGroup C sX (k - (j : ℤ)) :=
  Fin.lastCases (motive := fun j : Fin (r + 3) => chowGroup C sX (k - (j : ℤ))) 0 e j

/-- Below the top degree the extended family is the given one. -/
theorem chernFamilyExtendByZero_castSucc (k : ℤ)
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ))) (j : Fin (r + 2)) :
    chernFamilyExtendByZero C sX r k e j.castSucc = e j :=
  Fin.lastCases_castSucc (motive := fun j : Fin (r + 3) => chowGroup C sX (k - (j : ℤ))) j

/-- In the top degree the extended family is zero. -/
theorem chernFamilyExtendByZero_last (k : ℤ)
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ))) :
    chernFamilyExtendByZero C sX r k e (Fin.last (r + 2)) = 0 :=
  Fin.lastCases_last (motive := fun j : Fin (r + 3) => chowGroup C sX (k - (j : ℤ)))

/-- Below the top degree the extended family is the given one, up to transport along an equality
of indices. -/
private theorem chernFamilyExtendByZero_eq_chowGroupCast (k : ℤ)
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ))) (j : Fin (r + 2)) (m : Fin (r + 3))
    (h : j.castSucc = m) :
    chernFamilyExtendByZero C sX r k e m =
      chowGroupCast C sX (congrArg (fun j : Fin (r + 3) => k - (j : ℤ)) h) (e j) := by
  rw [chowGroupCast_family_eq C sX (fun j : Fin (r + 3) => k - (j : ℤ))
    (chernFamilyExtendByZero C sX r k e) h, chernFamilyExtendByZero_castSucc]

/-- **Stacks 02TR and 02SU, assembled.** Proper pushforward along the closed immersion
`ι : Q ⟶ P` of the projective bundle of the quotient into the projective bundle of the middle
term carries the `i`-th summand `c₁(O_Q(1))^i ∩ ϖ^*(-)` of the relation of Stacks 02U6 over `Q`
to the `(i+1)`-st summand `c₁(O_P(1))^{i+1} ∩ π^*(-)` of the relation over `P`.

The content is `c₁(O_P(1)) ∩ π^*β = ι_*(ϖ^*β)`, which is Stacks 02TR applied to the effective
Cartier divisor `Q ⊂ P` cut out by the section of `O_P(1)` coming from `1 ∈ Γ(X, O_X)`, followed
by `i` applications of Stacks 02SU; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.TrivialSubsheaf`. The two transports along
`Stacks.Chow.chowGroupCast` pass between the two spellings `r + 1 - i` and `r + 2 - (i + 1)` of
the source degree and between the two spellings `k + (r+1-1) - (r+1)` and `k + (r+2-1) - (r+2)`
of the target degree. -/
def ChernTermsCompatibleWithTrivialSubbundle : Prop :=
  ∀ (k : ℤ) (i : ℕ) (hi : i ≤ r + 1) (x : chowGroup C sX (k - ((r + 1 - i : ℕ) : ℤ))),
    projectiveBundleChernTerm C sX sP π hsP (r + 2) hπ hfacP twistP k (i + 1) (by omega)
        (chowGroupCast C sX
          (show k - ((r + 1 - i : ℕ) : ℤ) = k - ((r + 2 - (i + 1) : ℕ) : ℤ) from by omega) x) =
      chowGroupCast C sP
          (show k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) =
              k + ((r + 2 - 1 : ℕ) : ℤ) - ((r + 2 : ℕ) : ℤ) from by omega)
        (properChowPushforward C sQ sP ι hι (k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sQ sP ι hι
            (k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ)))
          (projectiveBundleChernTerm C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k i hi x))

/-! ### The relation over the bundle of the middle term -/

/-- The extension by zero of a family satisfying the projective-bundle relation over `Q`
satisfies the projective-bundle relation over `P`.

This is the computation of the source: the summand of index `0` of the relation over `P` consumes
the top member of the family, which is zero, and the remaining summands are, by the compatibility
of Stacks 02TR and 02SU, the proper pushforward of the summands of the relation over `Q`, with
the sign shifted by one. -/
theorem projectiveBundleChernRelation_chernFamilyExtendByZero
    (hcompat : ChernTermsCompatibleWithTrivialSubbundle C sX sP sQ π hsP ϖ hsQ r hπ hϖ hfacP
      hfacQ twistP twistQ ι hι) (k : ℤ)
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (he : ProjectiveBundleChernRelation C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k e) :
    ProjectiveBundleChernRelation C sX sP π hsP (r + 2) hπ hfacP twistP k
      (chernFamilyExtendByZero C sX r k e) := by
  have hQ : ∑ i : Fin (r + 2), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k i.val
        (Nat.lt_succ_iff.mp i.isLt) (e ⟨r + 1 - i.val, by omega⟩) = 0 := he
  change ∑ i : Fin (r + 3), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sP π hsP (r + 2) hπ hfacP twistP k i.val
        (Nat.lt_succ_iff.mp i.isLt)
        (chernFamilyExtendByZero C sX r k e ⟨r + 2 - i.val, by omega⟩) = 0
  have hhead : (-1 : ℤ) ^ ((0 : Fin (r + 3)) : ℕ) •
      projectiveBundleChernTerm C sX sP π hsP (r + 2) hπ hfacP twistP k
          ((0 : Fin (r + 3)) : ℕ) (Nat.lt_succ_iff.mp (0 : Fin (r + 3)).isLt)
          (chernFamilyExtendByZero C sX r k e
            ⟨r + 2 - ((0 : Fin (r + 3)) : ℕ), by omega⟩) = 0 := by
    rw [chowGroupCast_family_eq C sX (fun j : Fin (r + 3) => k - (j : ℤ))
      (chernFamilyExtendByZero C sX r k e)
      (show Fin.last (r + 2) =
          (⟨r + 2 - ((0 : Fin (r + 3)) : ℕ), by omega⟩ : Fin (r + 3)) from
        Fin.val_injective (by simp)),
      chernFamilyExtendByZero_last C sX r k e]
    simp only [map_zero, smul_zero]
  have htail : ∀ i : Fin (r + 2), (-1 : ℤ) ^ (i.val + 1) •
      projectiveBundleChernTerm C sX sP π hsP (r + 2) hπ hfacP twistP k (i.val + 1) (by omega)
          (chernFamilyExtendByZero C sX r k e ⟨r + 2 - (i.val + 1), by omega⟩) =
        - (chowGroupCast C sP
            (show k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) =
                k + ((r + 2 - 1 : ℕ) : ℤ) - ((r + 2 : ℕ) : ℤ) from by omega)
          (properChowPushforward C sQ sP ι hι (k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ))
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sQ sP ι hι
              (k + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ)))
            ((-1 : ℤ) ^ i.val •
              projectiveBundleChernTerm C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k i.val
                (Nat.lt_succ_iff.mp i.isLt) (e ⟨r + 1 - i.val, by omega⟩)))) := by
    intro i
    rw [map_zsmul, map_zsmul, chernFamilyExtendByZero_eq_chowGroupCast C sX r k e
      ⟨r + 1 - i.val, by omega⟩ ⟨r + 2 - (i.val + 1), by omega⟩ (Fin.val_injective (by simp)),
      hcompat k i.val (Nat.lt_succ_iff.mp i.isLt) (e ⟨r + 1 - i.val, by omega⟩),
      show ((-1 : ℤ) ^ (i.val + 1)) = -((-1 : ℤ) ^ i.val) from by ring, neg_smul]
  rw [Fin.sum_univ_succ, hhead, zero_add]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => htail i) ?_
  rw [Finset.sum_neg_distrib, ← map_sum, ← map_sum, hQ, map_zero, map_zero, neg_zero]

/-- The extension by zero of a family characterizing the Chern class cap products of `α` for the
quotient characterizes the Chern class cap products of `α` for the middle term. -/
theorem isChernCapFamily_chernFamilyExtendByZero
    (hcompat : ChernTermsCompatibleWithTrivialSubbundle C sX sP sQ π hsP ϖ hsQ r hπ hϖ hfacP
      hfacQ twistP twistQ ι hι) (k : ℤ) (α : chowGroup C sX k)
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (he : IsChernCapFamily C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k α e) :
    IsChernCapFamily C sX sP π hsP (r + 2) hπ hfacP twistP k α
      (chernFamilyExtendByZero C sX r k e) := by
  refine ⟨?_, projectiveBundleChernRelation_chernFamilyExtendByZero C sX sP sQ π hsP ϖ hsQ r hπ
    hϖ hfacP hfacQ twistP twistQ ι hι hcompat k e he.2⟩
  rw [chernFamilyExtendByZero_eq_chowGroupCast C sX r k e ⟨0, Nat.zero_lt_succ (r + 1)⟩
    ⟨0, Nat.zero_lt_succ (r + 2)⟩ (Fin.val_injective rfl), chowGroupCast_chowGroupCast]
  exact he.1

/-- The family of Chern class cap products of the middle term is the family of the quotient
extended by zero: the uniqueness of Stacks 02U6 applied to the two families over `P`. -/
theorem eq_chernFamilyExtendByZero
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP (r + 2) hπ hfacP twistP)
    (hcompat : ChernTermsCompatibleWithTrivialSubbundle C sX sP sQ π hsP ϖ hsQ r hπ hϖ hfacP
      hfacQ twistP twistQ ι hι) (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 3), chowGroup C sX (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP (r + 2) hπ hfacP twistP k α c)
    (he : IsChernCapFamily C sX sQ ϖ hsQ (r + 1) hϖ hfacQ twistQ k α e) :
    c = chernFamilyExtendByZero C sX r k e :=
  eq_of_isChernCapFamily C sX sP π hsP (r + 2) hπ hfacP twistP hinj k α hc
    (isChernCapFamily_chernFamilyExtendByZero C sX sP sQ π hsP ϖ hsQ r hπ hϖ hfacP hfacQ twistP
      twistQ ι hι hcompat k α e he)

/-! ### Stacks 02UG -/

/-- **Stacks 02UG, the vanishing of the top Chern class, on cap products.** Let

  `0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0`

be a short exact sequence of finite locally free modules on `X` with `ℰ` of rank `r + 2` and `ℱ`
of rank `r + 1`. Then for every `k` and every class `α ∈ A_k(X)`,

  `c_{r+2}(ℰ) ∩ α = 0`  in  `A_{k-r-2}(X)`.

The cap products are the members of families satisfying the characterization of Stacks 02U6,
which is how they exist in this repository at all: `hc` and `he` are those families for `ℰ` and
for `ℱ`. The proof is the proof of the source: the family of `ℱ` extended by zero satisfies the
relation over the bundle of `ℰ`, by Stacks 02TR and 02SU, and the uniqueness of Stacks 02U6
identifies it with the family of `ℰ`, whose top member is therefore zero.

Stacks 02S1 for the two projections is supplied from
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` and is not an argument. The
projective bundles themselves, their twists `O_P(1)` and `O_Q(1)`, the closed immersion `ι`, the
injectivity half of Stacks 02TX over `P` and the summandwise form `hcompat` of Stacks 02TR and
02SU are arguments, because Stacks 02TX and the representability of the twists (Stacks 01O4) are
not in this repository; see the module documentation. -/
@[stacks 02UG "the vanishing c_{r+2}(E) cap alpha = 0, stated degreewise on the cap products of \
  02U5 rather than in A^*(X), which has no multiplication here; ranks r + 2 and r + 1, so the \
  source's r = 1 is excluded; bundles, twists, iota, 02TX injectivity and 02TR+02SU are inputs"]
theorem chernCap_top_eq_zero
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP (r + 2) hπ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      twistP)
    (hcompat : ChernTermsCompatibleWithTrivialSubbundle C sX sP sQ π hsP ϖ hsQ r hπ hϖ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
      twistP twistQ ι hι)
    (_S : ShortComplex X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} _S.X₂ (r + 2)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} _S.X₃ (r + 1)]
    (_hunit : _S.X₁ ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (_hexact : _S.ShortExact) (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 3), chowGroup C sX (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP (r + 2) hπ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      twistP k α c)
    (he : IsChernCapFamily C sX sQ ϖ hsQ (r + 1) hϖ
      (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
      twistQ k α e) :
    c (Fin.last (r + 2)) = 0 := by
  rw [eq_chernFamilyExtendByZero C sX sP sQ π hsP ϖ hsQ r hπ hϖ
    (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
    (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
    twistP twistQ ι hι hinj hcompat k α c e hc he]
  exact chernFamilyExtendByZero_last C sX r k e

/-- **Stacks 02UG, the agreement of the lower Chern classes, on cap products.** Let

  `0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0`

be a short exact sequence of finite locally free modules on `X` with `ℰ` of rank `r + 2` and `ℱ`
of rank `r + 1`. Then for every `k`, every class `α ∈ A_k(X)` and every `j ≤ r + 1`,

  `c_j(ℰ) ∩ α = c_j(ℱ) ∩ α`  in  `A_{k-j}(X)`.

As for the vanishing above, the cap products are the members of families satisfying the
characterization of Stacks 02U6, and the proof is the uniqueness of that characterization applied
to the family of `ℱ` extended by zero. The inputs are the ones listed at
`Stacks.Chow.chernCap_top_eq_zero`, Stacks 02S1 for the two projections again being supplied from
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`. -/
@[stacks 02UG "the agreement c_j(E) cap alpha = c_j(F) cap alpha for j <= r + 1, stated \
  degreewise on the cap products of 02U5 rather than in A^*(X), which has no multiplication \
  here; ranks r + 2 and r + 1; bundles, twists, iota, 02TX and 02TR+02SU are inputs"]
theorem chernCap_castSucc_eq
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP (r + 2) hπ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      twistP)
    (hcompat : ChernTermsCompatibleWithTrivialSubbundle C sX sP sQ π hsP ϖ hsQ r hπ hϖ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
      twistP twistQ ι hι)
    (_S : ShortComplex X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} _S.X₂ (r + 2)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} _S.X₃ (r + 1)]
    (_hunit : _S.X₁ ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (_hexact : _S.ShortExact) (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 3), chowGroup C sX (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 2), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP (r + 2) hπ
      (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
      twistP k α c)
    (he : IsChernCapFamily C sX sQ ϖ hsQ (r + 1) hϖ
      (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
      twistQ k α e) (j : Fin (r + 2)) :
    c j.castSucc = e j := by
  rw [eq_chernFamilyExtendByZero C sX sP sQ π hsP ϖ hsQ r hπ hϖ
    (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r + 2 - 1) hπ)
    (flatPullbackFactorsThroughRationalEquivalence_general C sQ sX ϖ hsQ (r + 1 - 1) hϖ)
    twistP twistQ ι hι hinj hcompat k α c e hc he]
  exact chernFamilyExtendByZero_castSucc C sX r k e j

end Stacks.Chow

end
