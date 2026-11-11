module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective-bundle step of Stacks 02UG, on cap-product families

[Stacks, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG) asserts, for a short exact
sequence `0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0` of finite locally free `O_X`-modules of ranks `r` and `r - 1` on
`X` locally of finite type over the base, that `c_r(ℰ) = 0` and `c_j(ℰ) = c_j(ℱ)` for
`j = 0, …, r - 1` in `A^*(X)`. **This file does not formalize that lemma.** Stacks 02UG is stated
and proved, unconditionally and in `A^*(X)`, as
`Stacks.Chow.chernClass_eq_of_shortExact_of_iso_unit` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.InvertibleSubsheaf`, which carries the tag; its
cap-product form is `Stacks.Chow.GenuineChern.chernCap_eq_of_shortExact_of_iso_unit` in
`StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible`.

What this file proves is the formal, index-shifting step of the source's proof, for abstract
projective-bundle data. Let `π : P ⟶ X` and `ϖ : Q ⟶ X` be flat of relative dimensions `r + 1`
and `r`, with arbitrary first Chern class cap operators standing for `O_P(1)` and `O_Q(1)`, and let
`ι : Q ⟶ P` be proper. If proper pushforward along `ι` carries the `i`-th summand of the relation
of Stacks 02U6 over `Q` to the `(i+1)`-st summand over `P` (the hypothesis
`Stacks.Chow.ChernTermsCompatibleWithTrivialSubbundle`, which in the source is supplied by
Stacks 02TR and 02SU for the projective bundles of `ℰ` and `ℱ`), and the relation over `P` has
unique solutions (the injectivity half of Stacks 02TX, a hypothesis), then any family satisfying
the relation over `Q`, extended by zero in the top degree, is the family over `P`.

None of `P`, `Q`, `π`, `ϖ`, the twists, `ι` or the families is tied to a short exact sequence,
and the geometric content of Stacks 02UG (the closed immersion of projective bundles, Stacks 02TR,
02SU and 02TX) is carried by the hypotheses. The two final theorems also take a short exact
sequence `0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0` with ranks `r + 2` and `r + 1` as arguments `_S`, `_hunit`,
`_hexact` and two rank instances, but these are not used and are not related to the other data.
Those theorems are therefore conditional structural lemmas, not statements of Stacks 02UG, and
carry no `@[stacks]` registration.

Stacks 02S1 (that a flat pullback factors through rational equivalence) is supplied for `π` and
`ϖ` by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` in the final two
theorems; the intermediate declarations take it as an argument.

## Main definitions

* `Stacks.Chow.chernFamilyExtendByZero` — a family `(α_j)_{j ≤ r+1}` of Chow classes on `X`,
  extended by `0` in degree `r + 2`.
* `Stacks.Chow.ChernTermsCompatibleWithTrivialSubbundle` — the summandwise identity that
  Stacks 02TR and 02SU give in the source: proper pushforward along `ι : Q ⟶ P` carries the
  `i`-th summand of the relation of Stacks 02U6 over `Q` to the `(i+1)`-st summand over `P`.

## Main results

* `Stacks.Chow.projectiveBundleChernRelation_chernFamilyExtendByZero` — the extension by zero of
  a family satisfying the relation over `Q` satisfies the relation over `P`.
* `Stacks.Chow.isChernCapFamily_chernFamilyExtendByZero` — the same for the characterization of
  Stacks 02U6.
* `Stacks.Chow.eq_chernFamilyExtendByZero` — under injectivity over `P`, the family over `P` is
  the family over `Q` extended by zero.
* `Stacks.Chow.chernCap_top_eq_zero`, `Stacks.Chow.chernCap_castSucc_eq` — the top member of the
  family over `P` vanishes and its lower members are those of the family over `Q`, under the
  hypotheses above.

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

/-! ### The conclusions of the index-shifting step -/

/-- **The top member of the family over `P` vanishes.** Given flat `π : P ⟶ X` and
`ϖ : Q ⟶ X` of relative dimensions `r + 1` and `r`, first Chern class cap operators `twistP` and
`twistQ`, a proper `ι : Q ⟶ P` satisfying `ChernTermsCompatibleWithTrivialSubbundle`, and
injectivity `hinj` of the relation over `P`: if `c` and `e` satisfy the characterization of
Stacks 02U6 for `α ∈ A_k(X)` over `P` and over `Q`, then `c_{r+2} = 0`.

This is the formal step of the source's proof of Stacks 02UG, not Stacks 02UG itself: the
arguments `_S`, `_hunit`, `_hexact` and the two rank instances describe a short exact sequence
`0 ⟶ O_X ⟶ ℰ ⟶ ℱ ⟶ 0` but are unused and unrelated to `P`, `Q`, the twists, `ι`, `c` and `e`,
and the geometric inputs (Stacks 02TR, 02SU, 02TX) are hypotheses. Stacks 02UG is
`Stacks.Chow.chernClass_eq_of_shortExact_of_iso_unit`. -/
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

/-- **The lower members of the family over `P` are those over `Q`.** Under the hypotheses of
`Stacks.Chow.chernCap_top_eq_zero`, `c_j = e_j` for every `j ≤ r + 1`.

As for `Stacks.Chow.chernCap_top_eq_zero`, this is the formal step of the source's proof of
Stacks 02UG, not Stacks 02UG itself: the short exact sequence arguments are unused and unrelated
to the other data, and the geometric inputs are hypotheses. Stacks 02UG is
`Stacks.Chow.chernClass_eq_of_shortExact_of_iso_unit`. -/
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
