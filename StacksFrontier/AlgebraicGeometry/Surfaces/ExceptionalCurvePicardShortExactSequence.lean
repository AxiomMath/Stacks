module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ContractionPicardDescent

/-!
# The Picard short exact sequence of the contraction of an exceptional curve

Let `b : X ⟶ X'` be the contraction of an exceptional curve of the first kind `E ⊆ X`, cut out by
the ideal sheaf `D` and presented as the projective line by an isomorphism `e : 𝐏¹_k ≅ E` carrying
the normal sheaf of `E` in `X` to the twist `𝒪(-1)`. Then

`0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0`

is a short exact sequence, whose first map is pullback along `b` and whose second sends an
invertible class `ℒ` to its degree on `E`; and it is split by `n ↦ 𝒪_X(-nE)`.

This file states that sequence as a single theorem, with every clause spelled out: pullback along
`b` is injective; a class of `X` has degree zero on `E` exactly when it is pulled back along `b`;
the degree map is onto `ℤ`; the degree of `𝒪_X(-nE)` on `E` is `n`, so `n ↦ 𝒪_X(-nE)` is a
section of the degree map; and the degree of `𝒪_X(E)` on `E` is `-1`.

The degree used is the integer-valued one: `Pic(𝐏¹_k) = ℤ` under the identification carrying `m`
to the class of `𝒪(m)`, so the degree map takes no parameter.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.picardShortExactSequence_of_isContraction` — **the
  short exact sequence `0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0` of the contraction of an exceptional curve
  of the first kind, with its splitting**, all of its clauses in one statement.

## References

* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)
  (b : X ⟶ X')

/-- **Stacks Project, Tag 0C5L: the Picard short exact sequence of the contraction of an
exceptional curve of the first kind, together with its splitting.** Let `b : X ⟶ X'` contract the
exceptional curve of the first kind `E ⊆ X` cut out by the ideal sheaf `D` and presented as
`𝐏¹_k` by the isomorphism `e`. Then

`0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0`

is exact, and split by `n ↦ 𝒪_X(-nE)`; the first map is pullback along `b` and the second is the
degree on `E`. The five clauses below are, in order:

* exactness at `Pic(X')`: pullback along `b` is injective;
* exactness at `Pic(X)`, both inclusions at once: a class of `X` has degree zero on `E` if and
  only if it is pulled back along `b`;
* exactness at `ℤ`: the degree on `E` is onto `ℤ`;
* the splitting: `𝒪_X(-nE)` has degree `n` on `E`, so `n ↦ 𝒪_X(-nE)` is a section of the degree
  map;
* the normalization of the degree: `𝒪_X(E)` has degree `-1` on `E`.

Being an effective Cartier divisor is the first clause of the hypothesis that `D` cuts out an
exceptional curve of the first kind, so nothing is assumed here beyond the contraction and the
curve it contracts. -/
@[stacks 0C5L "the short exact sequence 0 → Pic(X') → Pic(X) → Z → 0 of the contraction of an \
exceptional curve of the first kind, in one statement with every clause written out: pullback \
along b is injective, a class has degree zero on the exceptional curve iff it is pulled back \
along b, the degree is surjective onto Z, the splitting n ↦ O_X(-nE) is a section of the degree, \
and O_X(E) has degree -1"]
public theorem picardShortExactSequence_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom b) ∧
      (∀ L : Stacks.Picard.ofScheme X, D.exceptionalDegree k e L = 0 ↔
        ∃ L' : Stacks.Picard.ofScheme X', Stacks.Picard.schemePullbackClassHom b L' = L) ∧
      Function.Surjective (D.exceptionalDegree k e) ∧
      (∀ n : ℤ, D.exceptionalDegree k e (negativeExceptionalMultipleHom D n) = n) ∧
      D.exceptionalDegree k e (Stacks.Divisors.picardClass D) = -1 := by
  refine ⟨injective_schemePullbackClassHom_of_isContraction (D := D) (b := b) (hb := hb),
    fun L => ⟨fun hL => contractionPicardExactness_of_isContraction
      (D := D) (k := k) (e := e) (b := b) (hb := hb) L hL, ?_⟩,
    exceptionalDegree_surjective (D := D) (k := k) (e := e) (hE := hE),
    exceptionalDegree_negativeExceptionalMultiple (D := D) (k := k) (e := e) (hE := hE),
    exceptionalDegree_picardClass (D := D) (k := k) (e := e) (hE := hE)⟩
  rintro ⟨L', rfl⟩
  exact exceptionalDegree_schemePullbackClassHom (D := D) (k := k) (e := e) (b := b) (hb := hb) L'

end Scheme.IdealSheafData

end AlgebraicGeometry

end
