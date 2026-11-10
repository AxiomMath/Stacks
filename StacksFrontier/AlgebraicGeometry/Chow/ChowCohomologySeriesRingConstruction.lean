module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperatorChernScaling
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup

/-!
# The series ring of Chow cohomology, built from the product of Stacks 0B7E

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. `Stacks.Chow.ChowCohomologySeriesRing` is the datum out of which
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` builds the group `∏_{i ≥ 0} A^i(X)` of
Stacks 0FEL, the formal inverse, and hence the Chern class map on `K_0(Vect(X))`. It is a
*parameter* of every theorem there, and nothing in this repository supplies one. This file
supplies the content of that datum from the graded ring `A^*(X)` of Stacks 0B7E, whose product is
`Stacks.Chow.chowCohomologyRingMul`, and isolates exactly what is still missing.

## What is built

* `Stacks.Chow.chowCohomologyDegreeCast` — the transport `A^p(X) ≃+ A^q(X)` along `p = q`, which
  is what turns the `ℤ`-graded product of Stacks 0B7E into the `ℕ`-indexed product rule
  `Stacks.Chow.GradedChowProductRule` whose target degree is an argument.
* `Stacks.Chow.GradedChowProductRule.IsAddLeft`, `IsAddRight`, `IsAssoc`, `IsComm` — the four laws
  of a degreewise product, named so that each can be established once for the product of Stacks
  0B7E and then fed to the structure.
* `Stacks.Chow.chowSeriesMul_assoc_of_isAssoc` — associativity of the Cauchy product of
  `Stacks.Chow.chowSeriesMul` from associativity of the degreewise product. This is the only
  combinatorial step: both iterated products are the sum over `{(i, j, k) : i + j + k = n}`, and
  the reindexing is the bijection `((i + j, k), (i, j)) ↦ ((i, j + k), (j, k))`.
* `Stacks.Chow.chowSeriesMul_comm_of_isComm`, `Stacks.Chow.chowSeriesMul_one_left_of`,
  `Stacks.Chow.chowSeriesMul_one_right_of` — the remaining laws of the Cauchy product from the
  corresponding laws of the degreewise product.
* `Stacks.Chow.chowCohomologyGradedProductRule`, `Stacks.Chow.chowCohomologySeriesOne` — the
  product rule and the unit series of Stacks 0B7E: composition of bivariant classes read in
  `ℕ`-degrees, and the identity class `1 ∈ A^0(X)`. Their four laws are
  `Stacks.Chow.chowCohomologyGradedProductRule_isAddLeft`, `_isAddRight`, `_isAssoc` and
  `_one_mul`, `_mul_one`.
* `Stacks.Chow.chowCohomologySeriesRingOfGradedComm` and
  `Stacks.Chow.chowCohomologySeriesRingOfInvertible` — **the construction**: a term of
  `Stacks.Chow.ChowCohomologySeriesRing` whose degreewise product is the product of Stacks 0B7E,
  carrying one hypothesis and no other. This is the first term of that structure built anywhere
  in this repository; every theorem of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` and of the modules downstream of it takes
  one as a parameter, and until now nothing supplied one.

* `Stacks.Chow.chowCohomologyRestriction_chowCohomologyGradedProductRule`,
  `Stacks.Chow.chowCohomologyRestriction_chowCohomologySeriesOne`,
  `Stacks.Chow.chowCohomologyRestriction_chowSeriesMul` — what the construction buys: the
  restriction map of Stacks 0B7F respects the degreewise product, the unit series and hence the
  Cauchy product of the series ring. The module doc of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative` records that its
  multiplicativity was stated for the product of Stacks 0B7E and *not* identified with
  `Stacks.Chow.ChowCohomologySeriesRing.gradedMul` of Stacks 0FEL; these are that identification
  cashed in.
* `Stacks.Chow.chernClassKGroup_chowCohomologyRestriction` — the consequence: the Chern class map
  of Stacks 0FEL commutes with restriction, with three of the six hypotheses of
  `Stacks.Chow.chernClassKGroup_pullback` discharged and only the comparison of the two
  total-Chern-class data left.

## What is still missing, exactly

The one hypothesis is commutativity of the degreewise product,
`Stacks.Chow.GradedChowProductRule.IsComm`. It is not a convenience that could be weakened away:
`Stacks.Chow.ChowCohomologySeriesRing.gradedMul_comm_of_mul_comm` derives it *from* the
commutativity field of the structure, by evaluating that field on the two series supported in a
single degree. The two directions together are
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`:

  a `Stacks.Chow.ChowCohomologySeriesRing` whose product is the one of Stacks 0B7E exists
  **if and only if** `a · b = b · a` for all `a ∈ A^i(X)` and `b ∈ A^j(X)`, the degrees `i`
  and `j` ranging over `ℕ`.

That last restriction is not a detail. `A^*(X)` is graded by `ℤ`, so the right-hand side is
*less* than commutativity of the ring `A^*(X)`, and the two must not be conflated where a
centrality statement is at stake; they are separated, and their different effects on the
centrality clause of Stacks 0FAC proved, in
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity`.

So the gap between Stacks 0B7E and Stacks 0FEL is exactly that assertion, and nothing else.
`A^*(X)` is the ring of bivariant classes of `𝟙 X` under composition, for which the source
asserts no commutativity. `Stacks.Chow.chernClassBivariant_mem_center` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ChernClassCentral`, Stacks 02UA, gives
`a · b = b · a` only when one of the two factors is a Chern class, which is strictly weaker than
the quantification over all of `A^i(X) × A^j(X)` above.

Weakening the structure is not an alternative either. Its commutativity field feeds
`Stacks.Chow.ChowCohomologySeriesRing.unitalSeriesCommGroup`, and three of that instance's uses —
`mul_one`, `inv_mul_cancel` and the `CommGroup` field `mul_comm` — are the only uses of the field
in `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup`. The first two need only a right unit
and a right inverse, which the Cauchy product has: `Stacks.Chow.chowSeriesMul_one_right_of` and
`Stacks.Chow.ChowCohomologySeriesRing.chowSeriesMul_formalInverse`. The third is irreducible,
because `Stacks.Chow.chernClassKGroupHom` is built by
`AlgebraicGeometry.VectorBundleKZero.liftAddHom`, whose target carries `[AddCommGroup]`, and
`Stacks.Chow.totalChernClassComplex_eq_prod` is a `Finset.prod`, which carries `[CommMonoid]`.
A non-commutative sibling of the structure would therefore have no consumer.

What *is* an alternative is to shrink the components rather than to weaken the laws. Restricted to
the classes that are **central** in `A^*(X)` — where `a · b = b · a` holds by the definition of
the centre and not by hypothesis — the same Cauchy product, the same unit series and the same
formal inverse make a commutative ring and a commutative group with no hypothesis at all:
`Stacks.Chow.centralChowSeriesCommRing` and `Stacks.Chow.CentralUnitalSeries` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries`, which share every law proved
below. That is the subobject Stacks 02UA and Remark 0ESW put the Chern classes in, and it is
where the total Chern class of a complex and the centrality clause of Stacks 0FAC (1) for it are
constructed, in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CentralTotalChernClass`. So the assertion
above is the gap between Stacks 0B7E and Stacks 0FEL *as stated over all of `A^i(X)`*, not a gap
in the source's own construction.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

-- `Finset.antidiagonal` is ambiguous once `Mathlib.Data.Finset.MulAntidiagonal` is imported: the
-- additive form of `Finset.mulAntidiagonal` carries the name too. The antidiagonal meant here is
-- the one of `Finset.HasAntidiagonal`.
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX]

/-! ### Transport between components of equal degree -/

/-- The transport `A^p(X) ≃+ A^q(X)` along an equality `p = q` of degrees. The components of
`Stacks.Chow.chowCohomology` are a family of groups indexed by `ℤ`, and the product of Stacks
0B7E lands in the degree `p + q`; `Stacks.Chow.GradedChowProductRule` instead takes the target
degree as an argument together with a proof that it is the sum, so that no transport is needed
downstream. This is the transport that makes the translation. -/
def chowCohomologyDegreeCast {p q : ℤ} (h : p = q) :
    chowCohomologyComponent C G sX p ≃+ chowCohomologyComponent C G sX q where
  toFun := cast (congrArg (chowCohomologyComponent C G sX) h)
  invFun := cast (congrArg (chowCohomologyComponent C G sX) h.symm)
  left_inv _ := by subst h; rfl
  right_inv _ := by subst h; rfl
  map_add' _ _ := by subst h; rfl

/-- Transporting a class between components of equal degree does not change it. -/
theorem chowCohomologyDegreeCast_heq {p q : ℤ} (h : p = q)
    (x : chowCohomologyComponent C G sX p) :
    chowCohomologyDegreeCast (G := G) (sX := sX) h x ≍ x := by subst h; rfl

/-- A transported class is a given one exactly when the two agree heterogeneously. -/
theorem chowCohomologyDegreeCast_eq_iff_heq {p q : ℤ} (h : p = q)
    (x : chowCohomologyComponent C G sX p) (y : chowCohomologyComponent C G sX q) :
    chowCohomologyDegreeCast (G := G) (sX := sX) h x = y ↔ x ≍ y :=
  ⟨fun hx => hx ▸ (chowCohomologyDegreeCast_heq h x).symm,
    fun hx => eq_of_heq ((chowCohomologyDegreeCast_heq h x).trans hx)⟩

/-- A transported class is a given one when the two agree heterogeneously. -/
theorem chowCohomologyDegreeCast_eq_of_heq {p q : ℤ} (h : p = q)
    {x : chowCohomologyComponent C G sX p} {y : chowCohomologyComponent C G sX q} (hxy : x ≍ y) :
    chowCohomologyDegreeCast (G := G) (sX := sX) h x = y :=
  (chowCohomologyDegreeCast_eq_iff_heq h x y).2 hxy

/-! ### The laws of a degreewise product

The three laws of `Stacks.Chow.GradedChowProductRule` that the Cauchy product of
`Stacks.Chow.chowSeriesMul` needs, named so that they can be established once for the product of
Stacks 0B7E and then fed to the structures of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup`. -/

namespace GradedChowProductRule

/-- A degreewise product is additive in its first variable. -/
def IsAddLeft (gm : GradedChowProductRule C G sX) : Prop :=
  ∀ (i j n : ℕ) (h : i + j = n) (x x' : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)),
    gm i j n h (x + x') y = gm i j n h x y + gm i j n h x' y

/-- A degreewise product is additive in its second variable. -/
def IsAddRight (gm : GradedChowProductRule C G sX) : Prop :=
  ∀ (i j n : ℕ) (h : i + j = n) (x : chowCohomologyComponent C G sX (i : ℤ))
    (y y' : chowCohomologyComponent C G sX (j : ℤ)),
    gm i j n h x (y + y') = gm i j n h x y + gm i j n h x y'

/-- A degreewise product is associative. The three intermediate degrees `ij`, `jk` and `n` carry
their own proofs, so that neither side needs a transport. -/
def IsAssoc (gm : GradedChowProductRule C G sX) : Prop :=
  ∀ (i j k ij jk n : ℕ) (hij : i + j = ij) (hjk : j + k = jk) (h₁ : ij + k = n) (h₂ : i + jk = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ))
    (z : chowCohomologyComponent C G sX (k : ℤ)),
    gm ij k n h₁ (gm i j ij hij x y) z = gm i jk n h₂ x (gm j k jk hjk y z)

/-- A degreewise product is commutative: `a · b = b · a` for `a ∈ A^i(X)` and `b ∈ A^j(X)`. -/
def IsComm (gm : GradedChowProductRule C G sX) : Prop :=
  ∀ (i j n : ℕ) (h : i + j = n) (h' : j + i = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ)),
    gm i j n h x y = gm j i n h' y x

/-- The degreewise product with a fixed second factor, as a homomorphism of groups. -/
def leftHom {gm : GradedChowProductRule C G sX} (hl : IsAddLeft gm) (i j n : ℕ) (h : i + j = n)
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    chowCohomologyComponent C G sX (i : ℤ) →+ chowCohomologyComponent C G sX (n : ℤ) :=
  AddMonoidHom.mk' (fun x => gm i j n h x y) fun x x' => hl i j n h x x' y

@[simp] theorem leftHom_apply {gm : GradedChowProductRule C G sX} (hl : IsAddLeft gm)
    (i j n : ℕ) (h : i + j = n) (y : chowCohomologyComponent C G sX (j : ℤ))
    (x : chowCohomologyComponent C G sX (i : ℤ)) : leftHom hl i j n h y x = gm i j n h x y := rfl

/-- The degreewise product with a fixed first factor, as a homomorphism of groups. -/
def rightHom {gm : GradedChowProductRule C G sX} (hr : IsAddRight gm) (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) :
    chowCohomologyComponent C G sX (j : ℤ) →+ chowCohomologyComponent C G sX (n : ℤ) :=
  AddMonoidHom.mk' (fun y => gm i j n h x y) fun y y' => hr i j n h x y y'

@[simp] theorem rightHom_apply {gm : GradedChowProductRule C G sX} (hr : IsAddRight gm)
    (i j n : ℕ) (h : i + j = n) (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) : rightHom hr i j n h x y = gm i j n h x y := rfl

/-- An additive degreewise product kills `0` in its first variable. -/
theorem IsAddLeft.zero_left {gm : GradedChowProductRule C G sX} (hl : IsAddLeft gm)
    (i j n : ℕ) (h : i + j = n) (y : chowCohomologyComponent C G sX (j : ℤ)) :
    gm i j n h 0 y = 0 := (leftHom hl i j n h y).map_zero

/-- An additive degreewise product kills `0` in its second variable. -/
theorem IsAddRight.zero_right {gm : GradedChowProductRule C G sX} (hr : IsAddRight gm)
    (i j n : ℕ) (h : i + j = n) (x : chowCohomologyComponent C G sX (i : ℤ)) :
    gm i j n h x 0 = 0 := (rightHom hr i j n h x).map_zero

end GradedChowProductRule

/-! ### Additivity of the Cauchy product

The Cauchy product of `Stacks.Chow.chowSeriesMul` is additive in each variable, and kills `0`,
as soon as the degreewise product is additive in the corresponding variable; no other law is
involved. `Stacks.Chow.chowSeriesMul_add_right`, `Stacks.Chow.chowSeriesMul_add_left`,
`Stacks.Chow.chowSeriesMul_zero_left` and `Stacks.Chow.chowSeriesMul_zero_right` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerChernProduct` are these
read at the degreewise product of a `Stacks.Chow.ChowCohomologySeriesRing`. -/

/-- A term of the Cauchy product with `0` on the left vanishes. -/
theorem chowSeriesTerm_zero_left_of {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (a : chowCohomologySeries C G sX) (n : ℕ)
    (p : ℕ × ℕ) : chowSeriesTerm gm 0 a n p = 0 := by
  rw [chowSeriesTerm]
  split
  · exact hl.zero_left _ _ _ _ _
  · rfl

/-- A term of the Cauchy product with `0` on the right vanishes. -/
theorem chowSeriesTerm_zero_right_of {gm : GradedChowProductRule C G sX}
    (hr : GradedChowProductRule.IsAddRight gm) (a : chowCohomologySeries C G sX) (n : ℕ)
    (p : ℕ × ℕ) : chowSeriesTerm gm a 0 n p = 0 := by
  rw [chowSeriesTerm]
  split
  · exact hr.zero_right _ _ _ _ _
  · rfl

/-- The Cauchy product with `0` on the left is `0`. -/
theorem chowSeriesMul_zero_left_of {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (a : chowCohomologySeries C G sX) :
    chowSeriesMul gm 0 a = 0 := by
  funext n
  exact Finset.sum_eq_zero fun p _ => chowSeriesTerm_zero_left_of hl a n p

/-- The Cauchy product with `0` on the right is `0`. -/
theorem chowSeriesMul_zero_right_of {gm : GradedChowProductRule C G sX}
    (hr : GradedChowProductRule.IsAddRight gm) (a : chowCohomologySeries C G sX) :
    chowSeriesMul gm a 0 = 0 := by
  funext n
  exact Finset.sum_eq_zero fun p _ => chowSeriesTerm_zero_right_of hr a n p

/-- **The Cauchy product is additive in its second variable** as soon as the degreewise product
is. -/
theorem chowSeriesMul_add_right_of {gm : GradedChowProductRule C G sX}
    (hr : GradedChowProductRule.IsAddRight gm) (a b c : chowCohomologySeries C G sX) :
    chowSeriesMul gm a (b + c) = chowSeriesMul gm a b + chowSeriesMul gm a c := by
  funext n
  rw [chowSeriesMul, Pi.add_apply, chowSeriesMul, chowSeriesMul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [chowSeriesTerm, chowSeriesTerm, chowSeriesTerm]
  split
  · exact hr _ _ _ _ _ _ _
  · rw [add_zero]

/-- **The Cauchy product is additive in its first variable** as soon as the degreewise product
is. -/
theorem chowSeriesMul_add_left_of {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (a b c : chowCohomologySeries C G sX) :
    chowSeriesMul gm (a + b) c = chowSeriesMul gm a c + chowSeriesMul gm b c := by
  funext n
  rw [chowSeriesMul, Pi.add_apply, chowSeriesMul, chowSeriesMul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [chowSeriesTerm, chowSeriesTerm, chowSeriesTerm]
  split
  · exact hl _ _ _ _ _ _ _
  · rw [add_zero]

/-! ### Associativity of the Cauchy product -/

/-- Expanding a term of the Cauchy product whose left factor is itself a Cauchy product: the
degree-`n` term at `p` is the sum over the antidiagonal of `p.1`. -/
theorem chowSeriesTerm_chowSeriesMul_left {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (a b c : chowCohomologySeries C G sX) (n : ℕ)
    (p : ℕ × ℕ) :
    chowSeriesTerm gm (chowSeriesMul gm a b) c n p
      = ∑ q ∈ antidiagonal p.1,
          (if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (chowSeriesTerm gm a b p.1 q) (c p.2) else 0) := by
  by_cases h : p.1 + p.2 = n
  · rw [chowSeriesTerm, dite_eq_left h, chowSeriesMul,
      show gm p.1 p.2 n h (∑ q ∈ antidiagonal p.1, chowSeriesTerm gm a b p.1 q) (c p.2)
          = ∑ q ∈ antidiagonal p.1, gm p.1 p.2 n h (chowSeriesTerm gm a b p.1 q) (c p.2)
        from map_sum (GradedChowProductRule.leftHom hl p.1 p.2 n h (c p.2)) _ _]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [dite_eq_left h]
  · rw [chowSeriesTerm, dite_eq_right h]
    exact (Finset.sum_eq_zero fun q _ => dite_eq_right h).symm

/-- Expanding a term of the Cauchy product whose right factor is itself a Cauchy product: the
degree-`n` term at `p` is the sum over the antidiagonal of `p.2`. -/
theorem chowSeriesTerm_chowSeriesMul_right {gm : GradedChowProductRule C G sX}
    (hr : GradedChowProductRule.IsAddRight gm) (a b c : chowCohomologySeries C G sX) (n : ℕ)
    (p : ℕ × ℕ) :
    chowSeriesTerm gm a (chowSeriesMul gm b c) n p
      = ∑ q ∈ antidiagonal p.2,
          (if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (a p.1) (chowSeriesTerm gm b c p.2 q) else 0) := by
  by_cases h : p.1 + p.2 = n
  · rw [chowSeriesTerm, dite_eq_left h, chowSeriesMul,
      show gm p.1 p.2 n h (a p.1) (∑ q ∈ antidiagonal p.2, chowSeriesTerm gm b c p.2 q)
          = ∑ q ∈ antidiagonal p.2, gm p.1 p.2 n h (a p.1) (chowSeriesTerm gm b c p.2 q)
        from map_sum (GradedChowProductRule.rightHom hr p.1 p.2 n h (a p.1)) _ _]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [dite_eq_left h]
  · rw [chowSeriesTerm, dite_eq_right h]
    exact (Finset.sum_eq_zero fun q _ => dite_eq_right h).symm

/-- **The Cauchy product of `Stacks.Chow.chowSeriesMul` is associative** as soon as the degreewise
product is additive in each variable and associative. Both iterated products are the sum over
`{(i, j, k) : i + j + k = n}` of `a_i b_j c_k`; the reindexing is the bijection
`((i + j, k), (i, j)) ↦ ((i, j + k), (j, k))` between the two ways of parenthesizing. -/
theorem chowSeriesMul_assoc_of_isAssoc {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (hr : GradedChowProductRule.IsAddRight gm)
    (ha : GradedChowProductRule.IsAssoc gm) (a b c : chowCohomologySeries C G sX) :
    chowSeriesMul gm (chowSeriesMul gm a b) c = chowSeriesMul gm a (chowSeriesMul gm b c) := by
  funext n
  calc chowSeriesMul gm (chowSeriesMul gm a b) c n
      = ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.1,
          (if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (chowSeriesTerm gm a b p.1 q) (c p.2) else 0) := by
        rw [chowSeriesMul]
        exact Finset.sum_congr rfl fun p _ => chowSeriesTerm_chowSeriesMul_left hl a b c n p
    _ = ∑ x ∈ (antidiagonal n).sigma fun p => antidiagonal p.1,
          (if h : x.1.1 + x.1.2 = n then
            gm x.1.1 x.1.2 n h (chowSeriesTerm gm a b x.1.1 x.2) (c x.1.2) else 0) :=
        Finset.sum_sigma' (antidiagonal n) (fun p => antidiagonal p.1)
          (fun p q => if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (chowSeriesTerm gm a b p.1 q) (c p.2) else 0)
    _ = ∑ x ∈ (antidiagonal n).sigma fun p => antidiagonal p.2,
          (if h : x.1.1 + x.1.2 = n then
            gm x.1.1 x.1.2 n h (a x.1.1) (chowSeriesTerm gm b c x.1.2 x.2) else 0) := by
        refine Finset.sum_nbij' (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
          (fun y => ⟨(y.1.1 + y.2.1, y.2.2), (y.1.1, y.2.1)⟩) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨⟨m, k⟩, ⟨u, v⟩⟩ hx
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal] at hx
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal]
          dsimp only at hx ⊢
          exact ⟨by omega, rfl⟩
        · rintro ⟨⟨u, t⟩, ⟨v, k⟩⟩ hy
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal] at hy
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal]
          dsimp only at hy ⊢
          exact ⟨by omega, rfl⟩
        · rintro ⟨⟨m, k⟩, ⟨u, v⟩⟩ hx
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal] at hx
          dsimp only at hx ⊢
          obtain ⟨-, h₂⟩ := hx
          subst h₂
          rfl
        · rintro ⟨⟨u, t⟩, ⟨v, k⟩⟩ hy
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal] at hy
          dsimp only at hy ⊢
          obtain ⟨-, h₂⟩ := hy
          subst h₂
          rfl
        · rintro ⟨⟨m, k⟩, ⟨u, v⟩⟩ hx
          rw [Finset.mem_sigma, mem_antidiagonal, mem_antidiagonal] at hx
          dsimp only at hx ⊢
          obtain ⟨h₁, h₂⟩ := hx
          have h₃ : u + (v + k) = n := by omega
          rw [dite_eq_left h₁, dite_eq_left h₃, chowSeriesTerm_of_add gm a b h₂,
            chowSeriesTerm_of_add gm b c (show v + k = v + k from rfl)]
          exact ha u v k m (v + k) n h₂ rfl h₁ h₃ (a u) (b v) (c k)
    _ = ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2,
          (if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (a p.1) (chowSeriesTerm gm b c p.2 q) else 0) :=
        (Finset.sum_sigma' (antidiagonal n) (fun p => antidiagonal p.2)
          (fun p q => if h : p.1 + p.2 = n then
            gm p.1 p.2 n h (a p.1) (chowSeriesTerm gm b c p.2 q) else 0)).symm
    _ = chowSeriesMul gm a (chowSeriesMul gm b c) n := by
        rw [chowSeriesMul]
        exact (Finset.sum_congr rfl fun p _ =>
          chowSeriesTerm_chowSeriesMul_right hr a b c n p).symm

/-- A coefficient of the Cauchy product is a single term when all other terms vanish. -/
private theorem chowSeriesMul_apply_of_forall_ne {gm : GradedChowProductRule C G sX}
    (a b : chowCohomologySeries C G sX) {i j n : ℕ} (h : i + j = n)
    (hz : ∀ (s t : ℕ) (hst : s + t = n), s ≠ i → gm s t n hst (a s) (b t) = 0) :
    chowSeriesMul gm a b n = gm i j n h (a i) (b j) := by
  rw [chowSeriesMul, Finset.sum_eq_single_of_mem (i, j) (mem_antidiagonal.mpr h),
    chowSeriesTerm_of_add gm a b h]
  rintro ⟨s, t⟩ hmem hne
  rw [mem_antidiagonal] at hmem
  dsimp only at hmem
  rw [chowSeriesTerm_of_add gm a b hmem]
  exact hz s t hmem fun hs => hne (Prod.ext hs (by omega))

/-! ### Commutativity of the Cauchy product -/

/-- **Two series whose coefficients commute with each other have commuting Cauchy products.** The
reindexing is the flip of the antidiagonal, and the hypothesis is needed only at the coefficients
of the two series given, not at every pair of classes: that is what lets the central series of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries` commute with no hypothesis on
`A^*(X)` at all. `Stacks.Chow.chowSeriesMul_comm_of_isComm` is this at a degreewise product that
is commutative outright. -/
theorem chowSeriesMul_comm_of_forall_comm {gm : GradedChowProductRule C G sX}
    (a b : chowCohomologySeries C G sX)
    (hc : ∀ (i j n : ℕ) (h : i + j = n) (h' : j + i = n),
      gm i j n h (a i) (b j) = gm j i n h' (b j) (a i)) :
    chowSeriesMul gm a b = chowSeriesMul gm b a := by
  funext n
  rw [chowSeriesMul, chowSeriesMul]
  refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_antidiagonal] at hp
    rw [mem_antidiagonal]
    omega
  · intro p hp
    rw [mem_antidiagonal] at hp
    rw [mem_antidiagonal]
    omega
  · exact fun p _ => rfl
  · exact fun p _ => rfl
  · rintro ⟨u, v⟩ hp
    rw [mem_antidiagonal] at hp
    rw [chowSeriesTerm_of_add gm a b hp,
      chowSeriesTerm_of_add gm b a (show v + u = n by omega)]
    exact hc u v n hp (by omega)

/-- **The Cauchy product is commutative as soon as the degreewise product is.** The reindexing is
the flip of the antidiagonal. -/
theorem chowSeriesMul_comm_of_isComm {gm : GradedChowProductRule C G sX}
    (hc : GradedChowProductRule.IsComm gm) (a b : chowCohomologySeries C G sX) :
    chowSeriesMul gm a b = chowSeriesMul gm b a :=
  chowSeriesMul_comm_of_forall_comm a b fun i j n h h' => hc i j n h h' (a i) (b j)

/-- **The commutativity field of `Stacks.Chow.ChowCohomologySeriesRing` is equivalent to
commutativity of the degreewise product in every pair of non-negative degrees.** Evaluating it on
the two series supported in a single degree returns `a · b = b · a` for `a ∈ A^i(X)`, `b ∈ A^j(X)`
with `i`, `j` in `ℕ`.

So that field is not a normalisation that could be weakened away: it demands that the product of
Stacks 0B7E — composition of bivariant classes — be commutative in every pair of non-negative
degrees, which the source does not assert. It does *not* say that the whole ring `A^*(X)` is
commutative, that ring being graded by `ℤ`; the difference is the subject of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity`. Stacks 02UA,
`Stacks.Chow.chernClassBivariant_mem_center`, gives commutativity only when one factor is a Chern
class. -/
theorem ChowCohomologySeriesRing.gradedMul_comm_of_mul_comm (R : ChowCohomologySeriesRing C G sX) :
    GradedChowProductRule.IsComm R.gradedMul := by
  classical
  intro i j n h h' x y
  have hsingle : ∀ (u v m : ℕ) (hm : u + v = m)
      (p : chowCohomologyComponent C G sX (u : ℤ)) (q : chowCohomologyComponent C G sX (v : ℤ)),
      chowSeriesMul R.gradedMul (Function.update (0 : chowCohomologySeries C G sX) u p)
          (Function.update (0 : chowCohomologySeries C G sX) v q) m
        = R.gradedMul u v m hm p q := by
    intro u v m hm p q
    refine (chowSeriesMul_apply_of_forall_ne _ _ hm fun s t hst hs => ?_).trans ?_
    · rw [Function.update_of_ne hs, Pi.zero_apply]
      exact R.gradedMul_zero_left _ _ _ _ _
    · rw [Function.update_self, Function.update_self]
  have key := congrFun (R.mul_comm (Function.update (0 : chowCohomologySeries C G sX) i x)
    (Function.update (0 : chowCohomologySeries C G sX) j y)) n
  rw [hsingle i j n h x y, hsingle j i n h' y x] at key
  exact key

/-! ### The unit laws of the Cauchy product -/

/-- The unit series is a left unit for the Cauchy product as soon as it is concentrated in degree
`0` and its constant term is a left unit for the degreewise product. -/
theorem chowSeriesMul_one_left_of {gm : GradedChowProductRule C G sX}
    (hl : GradedChowProductRule.IsAddLeft gm) (one : chowCohomologySeries C G sX)
    (hsucc : ∀ n : ℕ, one (n + 1) = 0)
    (hunit : ∀ (n : ℕ) (x : chowCohomologyComponent C G sX (n : ℤ)),
      gm 0 n n (Nat.zero_add n) (one 0) x = x)
    (a : chowCohomologySeries C G sX) : chowSeriesMul gm one a = a := by
  funext n
  refine (chowSeriesMul_apply_of_forall_ne (gm := gm) one a (Nat.zero_add n)
    fun s t hst hs => ?_).trans (hunit n (a n))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  rw [hsucc k]
  exact hl.zero_left _ _ _ _ _

/-- The unit series is a right unit for the Cauchy product as soon as it is concentrated in degree
`0` and its constant term is a right unit for the degreewise product. -/
theorem chowSeriesMul_one_right_of {gm : GradedChowProductRule C G sX}
    (hr : GradedChowProductRule.IsAddRight gm) (one : chowCohomologySeries C G sX)
    (hsucc : ∀ n : ℕ, one (n + 1) = 0)
    (hunit : ∀ (n : ℕ) (x : chowCohomologyComponent C G sX (n : ℤ)),
      gm n 0 n (Nat.add_zero n) x (one 0) = x)
    (a : chowCohomologySeries C G sX) : chowSeriesMul gm a one = a := by
  funext n
  refine (chowSeriesMul_apply_of_forall_ne (gm := gm) a one (Nat.add_zero n)
    fun s t hst hs => ?_).trans (hunit n (a n))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  rw [hsucc k]
  exact hr.zero_right _ _ _ _ _

/-! ### The degreewise product of Stacks 0B7E -/

section OfMul

variable (hiso : G.IsNaturalUnderInverseIso)

/-- Transporting the first factor of the product of Stacks 0B7E between components of equal
degree does not change the product. -/
theorem chowCohomologyMul_degreeCast_left {p p' q : ℤ} (h : p = p')
    (x : chowCohomologyComponent C G sX p) (y : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso (chowCohomologyDegreeCast h x) y
      ≍ chowCohomologyRingMul C G sX hiso x y := by subst h; rfl

/-- Transporting the second factor of the product of Stacks 0B7E between components of equal
degree does not change the product. -/
theorem chowCohomologyMul_degreeCast_right {p q q' : ℤ} (h : q = q')
    (x : chowCohomologyComponent C G sX p) (y : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso x (chowCohomologyDegreeCast h y)
      ≍ chowCohomologyRingMul C G sX hiso x y := by subst h; rfl

/-- **The product of Stacks 0B7E, as a degreewise product rule.** The class `a · b ∈ A^n(X)` of
`a ∈ A^i(X)` and `b ∈ A^j(X)` for `i + j = n`: the product
`Stacks.Chow.chowCohomologyRingMul`, which is composition of bivariant classes, transported from the
degree `i + j` computed in `ℤ` to the degree `n` the rule is asked for. -/
def chowCohomologyGradedProductRule (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ)) :
    chowCohomologyComponent C G sX (n : ℤ) :=
  chowCohomologyDegreeCast (show (i : ℤ) + (j : ℤ) = (n : ℤ) by omega)
    (chowCohomologyRingMul C G sX hiso x y)

/-- The degreewise product rule of Stacks 0B7E is the product of Stacks 0B7E, the transport of the
degree removed. -/
theorem chowCohomologyGradedProductRule_heq (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ)) :
    chowCohomologyGradedProductRule hiso i j n h x y ≍ chowCohomologyRingMul C G sX hiso x y :=
  chowCohomologyDegreeCast_heq _ _

/-- **Stacks 0B7E, one distributive law**, for the degreewise product rule. -/
theorem chowCohomologyGradedProductRule_isAddLeft :
    GradedChowProductRule.IsAddLeft (chowCohomologyGradedProductRule (sX := sX) hiso) := by
  intro i j n h x x' y
  simp only [chowCohomologyGradedProductRule]
  rw [chowCohomologyAdd_mul, map_add]

/-- **Stacks 0B7E, the other distributive law**, for the degreewise product rule. -/
theorem chowCohomologyGradedProductRule_isAddRight :
    GradedChowProductRule.IsAddRight (chowCohomologyGradedProductRule (sX := sX) hiso) := by
  intro i j n h x y y'
  simp only [chowCohomologyGradedProductRule]
  rw [chowCohomologyMul_add, map_add]

/-- **Stacks 0B7E, associativity**, for the degreewise product rule. The heterogeneous
associativity of `Stacks.Chow.chowCohomologyMul_assoc` becomes an equality once both sides are
read in the degree the rule names. -/
theorem chowCohomologyGradedProductRule_isAssoc :
    GradedChowProductRule.IsAssoc (chowCohomologyGradedProductRule (sX := sX) hiso) := by
  intro i j k ij jk n hij hjk h₁ h₂ x y z
  have e₁ : chowCohomologyRingMul C G sX hiso
        (chowCohomologyGradedProductRule hiso i j ij hij x y) z
      ≍ chowCohomologyRingMul C G sX hiso (chowCohomologyRingMul C G sX hiso x y) z :=
    chowCohomologyMul_degreeCast_left hiso _ _ _
  have e₂ := chowCohomologyMul_assoc C G sX hiso x y z
  have e₃ : chowCohomologyRingMul C G sX hiso x
        (chowCohomologyGradedProductRule hiso j k jk hjk y z)
      ≍ chowCohomologyRingMul C G sX hiso x (chowCohomologyRingMul C G sX hiso y z) :=
    chowCohomologyMul_degreeCast_right hiso _ _ _
  have e₄ : chowCohomologyGradedProductRule hiso i jk n h₂ x
        (chowCohomologyGradedProductRule hiso j k jk hjk y z)
      ≍ chowCohomologyRingMul C G sX hiso x
        (chowCohomologyGradedProductRule hiso j k jk hjk y z) :=
    chowCohomologyGradedProductRule_heq hiso _ _ _ _ _ _
  exact chowCohomologyDegreeCast_eq_of_heq _ (e₁.trans (e₂.trans (e₃.symm.trans e₄.symm)))

/-- **The unit series.** The series whose constant term is the class `1 ∈ A^0(X)` of Stacks 0B7E
and whose other components vanish. -/
def chowCohomologySeriesOne : chowCohomologySeries C G sX
  | 0 => chowCohomologyUnit C G sX hiso
  | (_ + 1) => 0

/-- **Stacks 0B7E, the unit law `1 · a = a`**, for the degreewise product rule. -/
theorem chowCohomologyGradedProductRule_one_mul (n : ℕ)
    (x : chowCohomologyComponent C G sX (n : ℤ)) :
    chowCohomologyGradedProductRule hiso 0 n n (Nat.zero_add n)
        (chowCohomologySeriesOne hiso 0) x = x :=
  chowCohomologyDegreeCast_eq_of_heq _ (chowCohomologyUnit_mul C G sX hiso x)

/-- **Stacks 0B7E, the unit law `a · 1 = a`**, for the degreewise product rule. -/
theorem chowCohomologyGradedProductRule_mul_one (n : ℕ)
    (x : chowCohomologyComponent C G sX (n : ℤ)) :
    chowCohomologyGradedProductRule hiso n 0 n (Nat.add_zero n) x
        (chowCohomologySeriesOne hiso 0) = x :=
  chowCohomologyDegreeCast_eq_of_heq _ (chowCohomologyMul_unit C G sX hiso x)

/-! ### The series ring, and the one thing it still needs -/

/-- **The datum of Stacks 0FEL for the product of Stacks 0B7E.** Every field of
`Stacks.Chow.ChowCohomologySeriesRing` is discharged from the ring `A^*(X)` of Stacks 0B7E — the
degreewise product is composition of bivariant classes, the unit series is the identity class
`1 ∈ A^0(X)`, the two distributive laws are those of Stacks 0B7E, associativity of the Cauchy
product is `Stacks.Chow.chowSeriesMul_assoc_of_isAssoc` applied to associativity of composition,
and the unit law is `Stacks.Chow.chowCohomologyUnit_mul` — except commutativity of the Cauchy
product, which is carried here as the hypothesis `hc` and is exactly commutativity of composition
of bivariant classes in every pair of degrees.

This is the first term of `Stacks.Chow.ChowCohomologySeriesRing` constructed in this repository;
every theorem of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` and of the modules
downstream of it takes one as a parameter, and until now nothing supplied one. -/
def chowCohomologySeriesRingOfGradedComm
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso)) :
    ChowCohomologySeriesRing C G sX where
  gradedMul := chowCohomologyGradedProductRule hiso
  one := chowCohomologySeriesOne hiso
  one_apply_succ _ := rfl
  gradedMul_add_left := chowCohomologyGradedProductRule_isAddLeft hiso
  gradedMul_add_right := chowCohomologyGradedProductRule_isAddRight hiso
  mul_assoc := chowSeriesMul_assoc_of_isAssoc (chowCohomologyGradedProductRule_isAddLeft hiso)
    (chowCohomologyGradedProductRule_isAddRight hiso)
    (chowCohomologyGradedProductRule_isAssoc hiso)
  mul_comm := chowSeriesMul_comm_of_isComm hc
  one_mul := chowSeriesMul_one_left_of (chowCohomologyGradedProductRule_isAddLeft hiso)
    (chowCohomologySeriesOne hiso) (fun _ => rfl)
    (chowCohomologyGradedProductRule_one_mul hiso)

@[simp] theorem chowCohomologySeriesRingOfGradedComm_gradedMul
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso)) :
    (chowCohomologySeriesRingOfGradedComm hiso hc).gradedMul
      = chowCohomologyGradedProductRule hiso := rfl

@[simp] theorem chowCohomologySeriesRingOfGradedComm_one
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso)) :
    (chowCohomologySeriesRingOfGradedComm hiso hc).one = chowCohomologySeriesOne hiso := rfl

/-- **The obstruction, exactly.** A `Stacks.Chow.ChowCohomologySeriesRing` whose degreewise
product is the product of Stacks 0B7E exists if and only if that product is commutative in every
pair of **non-negative** degrees. Everything else the structure asks for is a law of the ring
`A^*(X)` and is discharged above; commutativity is not, and it cannot be weakened away, because
the commutativity field of the structure *implies* it.

The ring `A^*(X)` of Stacks 0B7E is the bivariant classes of `𝟙 X` under composition, and the
source asserts no commutativity for it. `Stacks.Chow.chernClassBivariant_mem_center`, Stacks
02UA, gives `a · b = b · a` only when one of the two factors is a Chern class; that is strictly
weaker than the right-hand side here, which quantifies over all of `A^i(X) × A^j(X)` for `i`, `j`
in `ℕ`. In the other direction the right-hand side is itself strictly weaker than commutativity
of the ring `A^*(X)`, which is graded by `ℤ`; the two are separated in
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity`, where it matters
because only the stronger one makes the centrality clause of Stacks 0FAC vacuous. -/
theorem nonempty_chowCohomologySeriesRing_iff_isComm :
    (∃ R : ChowCohomologySeriesRing C G sX,
        R.gradedMul = chowCohomologyGradedProductRule hiso)
      ↔ GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso) :=
  ⟨fun ⟨R, hR⟩ => hR ▸ R.gradedMul_comm_of_mul_comm,
    fun hc => ⟨chowCohomologySeriesRingOfGradedComm hiso hc, rfl⟩⟩

/-! ### Restriction is multiplicative for the constructed series ring

This is where the construction pays. `Stacks.Chow.chowCohomologyRestriction_chowCohomologyRingMul`
and
`Stacks.Chow.chowCohomologyRestriction_unit` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative` say that the
restriction map of Stacks 0B7F respects the product and the unit of Stacks 0B7E. The module doc of
that file records that its multiplication is *not* identified with
`Stacks.Chow.ChowCohomologySeriesRing.gradedMul` of Stacks 0FEL anywhere in this repository;
`Stacks.Chow.chowCohomologySeriesRingOfGradedComm` is that identification, and the two theorems
below are its consequence: the restriction map satisfies, degreewise, exactly the hypotheses
`pbGradedMul` and `pbOne` that `Stacks.Chow.chernClassKGroup_pullback` and
`Stacks.Chow.SecondAdamsSplittingAt` carry. -/

section Restriction

variable (C) (G) (sX) {X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- Restriction commutes with the transport between components of equal degree. -/
theorem chowCohomologyRestriction_degreeCast {p q : ℤ} (h : p = q)
    (z : chowCohomologyComponent C G sX p) :
    chowCohomologyRestriction C G sX f q hgys (chowCohomologyDegreeCast h z)
      = chowCohomologyDegreeCast h (chowCohomologyRestriction C G sX f p hgys z) := by
  subst h; rfl

variable (hiso : G.IsNaturalUnderInverseIso)

/-- **The hypothesis `pbGradedMul`, discharged.** The restriction map of Stacks 0B7F respects the
degreewise product of the series ring built from Stacks 0B7E. Its content is
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyRingMul`, the multiplicativity of Stacks 0B7F;
the degreewise
product rule differs from the product of Stacks 0B7E only by the transport of the degree, and
restriction commutes with that. -/
theorem chowCohomologyRestriction_chowCohomologyGradedProductRule (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    chowCohomologyRestriction C G sX f (n : ℤ) hgys
        (chowCohomologyGradedProductRule hiso i j n h x y)
      = chowCohomologyGradedProductRule hiso i j n h
          (chowCohomologyRestriction C G sX f (i : ℤ) hgys x)
          (chowCohomologyRestriction C G sX f (j : ℤ) hgys y) := by
  simp only [chowCohomologyGradedProductRule]
  rw [chowCohomologyRestriction_degreeCast, chowCohomologyRestriction_chowCohomologyRingMul]

/-- **The hypothesis `pbOne`, discharged in every degree.** The restriction map of Stacks 0B7F
takes the unit series of the series ring built from Stacks 0B7E to the unit series. In degree `0`
this is `Stacks.Chow.chowCohomologyRestriction_unit`; in the higher degrees both sides are `0`. -/
theorem chowCohomologyRestriction_chowCohomologySeriesOne (i : ℕ) :
    chowCohomologyRestriction C G sX f (i : ℤ) hgys (chowCohomologySeriesOne hiso i)
      = chowCohomologySeriesOne (sX := f ≫ sX) hiso i := by
  cases i with
  | zero => exact chowCohomologyRestriction_unit C G sX f hgys hiso
  | succ k => exact map_zero _

/-- **The restriction map is a homomorphism for the Cauchy product of Stacks 0FEL built from
Stacks 0B7E.** The Cauchy products correspond degreewise, which is the statement that the
degree-`n` coefficient of `res(a · b)` is `∑_{i + j = n} res(a_i) res(b_j)`.

No commutativity is involved: the proof is
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyGradedProductRule` term by term, which
carries no hypothesis, so the statement is made at the degreewise product itself rather than at
the `Stacks.Chow.ChowCohomologySeriesRing` built from it — whose existence, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`, would be commutativity of `A^*(X)` in
every pair of non-negative degrees. That ring's product is this one, so nothing is lost. -/
theorem chowCohomologyRestriction_chowSeriesMul
    (a b : chowCohomologySeries C G sX) (n : ℕ) :
    chowCohomologyRestriction C G sX f (n : ℤ) hgys
        (chowSeriesMul (chowCohomologyGradedProductRule hiso) a b n)
      = chowSeriesMul (chowCohomologyGradedProductRule (sX := f ≫ sX) hiso)
          (fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys (a i))
          (fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys (b i)) n := by
  rw [chowSeriesMul, chowSeriesMul, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [chowSeriesTerm_of_add _ a b hp, chowSeriesTerm_of_add _ _ _ hp]
  exact chowCohomologyRestriction_chowCohomologyGradedProductRule C G sX f hgys hiso
    p.1 p.2 n hp (a p.1) (b p.2)

/-- **The restriction map is a homomorphism for the formal inverse of Stacks 0FEL.** The inverse
of `Stacks.Chow.gradedFormalInverse` is built by a recursion out of the degreewise product, sums
and negation, and the restriction map of Stacks 0B7F respects all three; so it carries the formal
inverse of a series to the formal inverse of its restriction, with no hypothesis.

Together with `Stacks.Chow.chowCohomologyRestriction_chowSeriesMul` and
`Stacks.Chow.chowCohomologyRestriction_chowCohomologySeriesOne` this says that restriction is a
homomorphism of the *groups* of unital series of Stacks 0FEL, which is what comparing total Chern
classes across a base change asks for. -/
theorem chowCohomologyRestriction_gradedFormalInverse
    (u : chowCohomologyComponent C G sX (0 : ℤ)) (a : chowCohomologySeries C G sX) (n : ℕ) :
    chowCohomologyRestriction C G sX f (n : ℤ) hgys
        (gradedFormalInverse (chowCohomologyGradedProductRule hiso) u a n)
      = gradedFormalInverse (chowCohomologyGradedProductRule (sX := f ≫ sX) hiso)
          (chowCohomologyRestriction C G sX f (0 : ℤ) hgys u)
          (fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys (a i)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
        rw [gradedFormalInverse_zero, gradedFormalInverse_zero]
        rfl
    | succ m =>
        rw [gradedFormalInverse_succ, gradedFormalInverse_succ, map_neg, map_sum]
        refine congrArg Neg.neg (Finset.sum_congr rfl fun p hp => ?_)
        rw [mem_antidiagonal] at hp
        rw [dite_eq_left hp, dite_eq_left hp,
          chowCohomologyRestriction_chowCohomologyGradedProductRule C G sX f hgys hiso,
          ih p.2 (by omega)]

/-! ### The Chern class map of Stacks 0FEL restricts

With the series rings of both schemes built from Stacks 0B7E, the first three hypotheses of
`Stacks.Chow.chernClassKGroup_pullback` are theorems rather than data. What is left is the
comparison of the two total-Chern-class data, and that only.

The two series rings are kept abstract and pinned by the two equations
`R.gradedMul = chowCohomologyGradedProductRule hiso` and
`R.one = chowCohomologySeriesOne hiso` rather than being the term
`Stacks.Chow.chowCohomologySeriesRingOfGradedComm` builds. That is not a weakening: by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` a series ring satisfying the first
equation exists exactly when the one that construction builds does, and any series ring
satisfying the two equations is one it could have built. -/

/-- **The Chern class map of Stacks 0FEL commutes with the restriction map of Stacks 0B7F**, for
any series rings whose degreewise product and unit are those of Stacks 0B7E — which, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`, are the only series rings on that
product there can be. Of the six hypotheses `Stacks.Chow.chernClassKGroup_pullback` carries, three
are discharged here: the pullback is the restriction map of Stacks 0B7F, which is a degreewise
homomorphism by construction, respects the degreewise product by
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyGradedProductRule` and the unit series by
`Stacks.Chow.chowCohomologyRestriction_chowCohomologySeriesOne`.

The three that remain are about the total Chern class itself and not about the multiplication: a
map `pK` on `K_0(Vect)`, its compatibility `pKClassOf` with the classes of modules, and `pbCh`,
the base change compatibility of the two total-Chern-class data, which is
`Stacks.Chow.TotalChernClassSeries.IsBaseChangeCompatible` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange` and which
`Stacks.Chow.chowCohomologyRestriction_ch_eq` establishes for a module of globally constant rank
`r` in the degrees `j ≤ r` only. So `pbCh` is the whole remaining obstruction to the Chern class
map restricting, and it is not an obstruction about the multiplication. -/
theorem chernClassKGroup_chowCohomologyRestriction
    {R : ChowCohomologySeriesRing C G sX} {R' : ChowCohomologySeriesRing C G (f ≫ sX)}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hmul' : R'.gradedMul = chowCohomologyGradedProductRule (sX := f ≫ sX) hiso)
    (hone : R.one = chowCohomologySeriesOne hiso)
    (hone' : R'.one = chowCohomologySeriesOne (sX := f ≫ sX) hiso)
    {D : TotalChernClassSeries C G sX R} {D' : TotalChernClassSeries C G (f ≫ sX) R'}
    (pK : AlgebraicGeometry.VectorBundleKZero X →+* AlgebraicGeometry.VectorBundleKZero X')
    (pbCh : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        ∀ i : ℕ, chowCohomologyRestriction C G sX f (i : ℤ) hgys (D.ch E i)
          = D'.ch ((Scheme.Modules.pullback f).obj E) i)
    (pKClassOf : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        pK (AlgebraicGeometry.VectorBundleKZero.classOf X E)
          = AlgebraicGeometry.VectorBundleKZero.classOf X'
            ((Scheme.Modules.pullback f).obj E))
    (β : AlgebraicGeometry.VectorBundleKZero X) (i : ℕ) :
    chowCohomologyRestriction C G sX f (i : ℤ) hgys (chernClassKGroup D β i)
      = chernClassKGroup D' (pK β) i :=
  chernClassKGroup_pullback (fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys)
    (fun i => by
      rw [hone, hone']
      exact chowCohomologyRestriction_chowCohomologySeriesOne C G sX f hgys hiso i)
    (fun i j n h x y => by
      rw [hmul, hmul']
      exact chowCohomologyRestriction_chowCohomologyGradedProductRule C G sX f hgys hiso
        i j n h x y)
    pK pbCh pKClassOf β i

end Restriction

end OfMul

/-! ### The Gysin system of the genuine first Chern class rule -/

section OfInvertible


/-- **The datum of Stacks 0FEL for the Gysin system this repository constructs**, with no
hypothesis on that system: the isomorphism case of Stacks 02TA is discharged for it by
`Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso`, exactly as for
`Stacks.Chow.chowCohomologyRingOfInvertible`. The remaining hypothesis is commutativity of
composition of bivariant classes, and nothing else. -/
def chowCohomologySeriesRingOfInvertible
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX)
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C))) :
    ChowCohomologySeriesRing C (gysinSystemOfInvertible C) sX :=
  chowCohomologySeriesRingOfGradedComm
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) hc

end OfInvertible

end Stacks.Chow

end
