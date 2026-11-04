module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction

/-!
# The centre of `A^*(X)` under commutativity of the Chow cohomology ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. Stacks 02UA and Stacks 0FAC (1) assert that Chern
classes lie in the **centre** of the ring `A^*(X)` of Stacks 0B7E, and the source's own warning
after Stacks 0B7E is that it is *not clear* that `A^*(X)` is commutative — the centrality
assertions are informative precisely because of that.

This file measures what happens to such an assertion when commutativity is *assumed*, which is
what a formalization of the total Chern class in the series ring of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction` would have to assume:
by `Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`, a
`Stacks.Chow.ChowCohomologySeriesRing` whose degreewise product is the product of Stacks 0B7E
exists if and only if `Stacks.Chow.GradedChowProductRule.IsComm` holds for that product.

## Main results

* `Stacks.Chow.chowCohomologyCenter_eq_top_of_mul_comm` — if the ring `A^*(X)` is commutative
  then its centre is the whole ring.
* `Stacks.Chow.chowCohomologyMul_comm_of_heq_comm` — degreewise commutativity of the product of
  Stacks 0B7E, in *every* pair of degrees of `ℤ`, gives commutativity of the ring `A^*(X)`.
* `Stacks.Chow.forall_mem_center_of_heq_comm` — **the vacuity.** Under that hypothesis every
  member of an *arbitrary* family of classes `c p ∈ A^p(X)` lies in the centre of `A^*(X)`, with
  no hypothesis whatsoever relating the family to any sheaf, complex or object of the derived
  category. So the conclusion of the centrality clause of Stacks 02UA and of Stacks 0FAC (1) is,
  under commutativity, independent of the data it is asserted of.
* `Stacks.Chow.chowCohomologyMul_heq_comm_of_isComm` — the commutativity that the series ring
  provides, `Stacks.Chow.GradedChowProductRule.IsComm`, is degreewise commutativity of the
  product of Stacks 0B7E in the **non-negative** degrees, and in those only.
* `Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg` — consequently a class of `A^p(X)` with
  `p ≥ 0` is central as soon as it commutes with the classes of the **negative** degrees: under
  `Stacks.Chow.GradedChowProductRule.IsComm` the negative degrees are the entire residue of the
  centrality assertion.

## What this says about registering the total Chern class reading of Stacks 0FAC (1)

The ring `A^*(X)` of Stacks 0B7E is graded by `ℤ`, as `Stacks.Chow.chowCohomology` is: a
bivariant class of Stacks 0B76 has a degree `p ∈ ℤ`, and nothing in the source or in this
repository makes `A^p(X)` vanish for `p < 0`. The two results above therefore separate two
hypotheses that are easily conflated:

* commutativity of `A^*(X)` as a ring, equivalently degreewise commutativity in every pair of
  degrees of `ℤ`. Under it the centrality clause is **vacuous**, by
  `Stacks.Chow.forall_mem_center_of_heq_comm`: it holds of every family of classes. A
  registration of Stacks 0FAC (1) carrying this hypothesis would claim the tag by a triviality.
* `Stacks.Chow.GradedChowProductRule.IsComm`, which is what a series ring built on the product of
  Stacks 0B7E carries. It quantifies over degrees in `ℕ`, so it is strictly less than the first
  and does **not** make the clause vacuous; by
  `Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg` what it leaves open is exactly the
  commutation with the negative degrees, about which neither the source nor this repository says
  anything. A registration of Stacks 0FAC (1) carrying this hypothesis would be a registration of
  an unproved statement.

So neither hypothesis supports a registration of the total Chern class reading of the clause,
and for different reasons. What does support one is to stop assuming anything about `A^*(X)` and
to form the total Chern class in the **centre**, where the Cauchy product is commutative by the
definition of the centre:
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries` builds that ring, with no
hypothesis, and the total Chern class reading of the clause is registered on it in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CentralTotalChernClass`. The power sum
reading, which needs no series ring at all, is registered in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Centrality`.

Neither result makes the two measurements below idle: they are what rules out the registrations
that *would* have been made on the carried series ring, and
`Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg` is still the exact statement of what such a
ring leaves open in the negative degrees.

Nothing here carries a `@[stacks]` attribute: the statements are measurements of a hypothesis,
not conclusions of a tag.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso)

/-! ### Commutativity of `A^*(X)` makes its centre the whole ring -/

/-- **If the ring `A^*(X)` of Stacks 0B7E is commutative then its centre is all of it.** The
centrality assertions of Stacks 02UA and Stacks 0FAC (1) are therefore empty under that
hypothesis; the source's warning after Stacks 0B7E, that commutativity of `A^*(X)` is not clear,
is what gives them content. -/
theorem chowCohomologyCenter_eq_top_of_mul_comm
    (hcomm : ∀ x y : chowCohomology C G sX,
      letI := chowCohomologyRing C G sX hiso
      x * y = y * x) :
    letI := chowCohomologyRing C G sX hiso
    Subring.center (chowCohomology C G sX) = ⊤ := by
  let := chowCohomologyRing C G sX hiso
  exact (Subring.eq_top_iff' _).2 fun x => Subring.mem_center_iff.2 fun y => hcomm y x

/-- Heterogeneously equal classes in equal degrees have equal images in `A^*(X)`. -/
private theorem of_eq_of_heq {i i' : ℤ} (h : i = i') {u : chowCohomologyComponent C G sX i}
    {v : chowCohomologyComponent C G sX i'} (huv : u ≍ v) :
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) i u
      = DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) i' v := by
  cases h
  exact congrArg _ (eq_of_heq huv)

/-- **Degreewise commutativity of the product of Stacks 0B7E in every pair of degrees of `ℤ`
gives commutativity of the ring `A^*(X)`.** The products of two classes of degrees `p` and `q`
taken in the two orders lie in `A^{p+q}(X)` and `A^{q+p}(X)`, the same integer presented by two
terms, so the hypothesis is heterogeneous; the ring is the direct sum over `ℤ` of its components,
in which multiplication of two homogeneous elements is
`Stacks.Chow.chowCohomologyRingMul` by `DirectSum.of_mul_of`, and an arbitrary element is a finite
sum
of homogeneous ones. -/
theorem chowCohomologyMul_comm_of_heq_comm
    (hcomm : ∀ (p q : ℤ) (x : chowCohomologyComponent C G sX p)
      (y : chowCohomologyComponent C G sX q),
      chowCohomologyRingMul C G sX hiso x y ≍ chowCohomologyRingMul C G sX hiso y x)
    (x y : chowCohomology C G sX) :
    letI := chowCohomologyRing C G sX hiso
    x * y = y * x := by
  let gring : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C G sX q :=
    chowCohomologyGRing C G sX hiso
  let := chowCohomologyRing C G sX hiso
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => rw [zero_mul, mul_zero]
    | of q b =>
      rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
      exact of_eq_of_heq C G sX (add_comm _ _) (hcomm p q a b)
    | add y y' hy hy' => rw [mul_add, add_mul, hy, hy']
  | add x x' hx hx' => rw [add_mul, mul_add, hx, hx']

/-- **The centrality clause, under commutativity of `A^*(X)`, for an arbitrary family of
classes.** Let `c` assign to every `p ≥ 0` a class `c p ∈ A^p(X)`. If the product of Stacks 0B7E
is degreewise commutative in every pair of degrees of `ℤ` then every `c p` lies in the centre of
`A^*(X)` — with no hypothesis relating `c` to a sheaf, to a complex, or to an object of the
derived category.

This is the vacuity of the total Chern class reading of Stacks 0FAC (1) in the one form in which
this repository could state it: the conclusion of the clause follows from the commutativity that
the series ring of Stacks 0FEL requires, for data satisfying no defining property at all. -/
theorem forall_mem_center_of_heq_comm
    (hcomm : ∀ (p q : ℤ) (x : chowCohomologyComponent C G sX p)
      (y : chowCohomologyComponent C G sX q),
      chowCohomologyRingMul C G sX hiso x y ≍ chowCohomologyRingMul C G sX hiso y x)
    (c : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ)) (p : ℕ) :
    letI := chowCohomologyRing C G sX hiso
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (p : ℤ) (c p) ∈
      Subring.center (chowCohomology C G sX) := by
  let := chowCohomologyRing C G sX hiso
  rw [chowCohomologyCenter_eq_top_of_mul_comm C G sX hiso
    (chowCohomologyMul_comm_of_heq_comm C G sX hiso hcomm)]
  exact Subring.mem_top _

/-! ### What the series ring's commutativity does and does not give -/

/-- **The commutativity carried by a series ring built on the product of Stacks 0B7E is
degreewise commutativity in the non-negative degrees.** `Stacks.Chow.GradedChowProductRule.IsComm`
quantifies over degrees in `ℕ`, and on those it is exactly commutativity of
`Stacks.Chow.chowCohomologyRingMul`, the transport of the degree removed. -/
theorem chowCohomologyMul_heq_comm_of_isComm
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso))
    (i j : ℕ) (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    chowCohomologyRingMul C G sX hiso x y ≍ chowCohomologyRingMul C G sX hiso y x :=
  ((chowCohomologyGradedProductRule_heq hiso i j (i + j) rfl x y).symm.trans
    (heq_of_eq (hc i j (i + j) rfl (Nat.add_comm j i) x y))).trans
      (chowCohomologyGradedProductRule_heq hiso j i (i + j) (Nat.add_comm j i) y x)

/-- **Under the commutativity carried by the series ring, the negative degrees are the entire
residue of the centrality assertion.** Let `a ∈ A^p(X)` with `p ≥ 0`. If the product of Stacks
0B7E satisfies `Stacks.Chow.GradedChowProductRule.IsComm` — equivalently, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`, if a
`Stacks.Chow.ChowCohomologySeriesRing` on that product exists — and if `a` commutes with the
classes of every negative degree, then `a` is central in `A^*(X)`.

So that hypothesis does not make the centrality clause of Stacks 0FAC (1) vacuous: `A^*(X)` is
graded by `ℤ` and nothing in the source or here makes `A^q(X)` vanish for `q < 0`. What it leaves
to prove is the commutation with those degrees alone, which the source does not address. -/
theorem mem_center_of_isComm_of_heq_comm_neg
    (hc : GradedChowProductRule.IsComm (chowCohomologyGradedProductRule (sX := sX) hiso))
    {p : ℕ} (a : chowCohomologyComponent C G sX (p : ℤ))
    (hneg : ∀ q : ℤ, q < 0 → ∀ b : chowCohomologyComponent C G sX q,
      chowCohomologyRingMul C G sX hiso b a ≍ chowCohomologyRingMul C G sX hiso a b) :
    letI := chowCohomologyRing C G sX hiso
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (p : ℤ) a ∈
      Subring.center (chowCohomology C G sX) := by
  let gring : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C G sX q :=
    chowCohomologyGRing C G sX hiso
  let := chowCohomologyRing C G sX hiso
  rw [Subring.mem_center_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | of q b =>
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    refine of_eq_of_heq C G sX (add_comm _ _) ?_
    rcases lt_or_ge q 0 with hq | hq
    · exact hneg q hq b
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact chowCohomologyMul_heq_comm_of_isComm C G sX hiso hc m p b a
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

end Stacks.Chow

end
