module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction

/-!
# The series ring of the centre of the Chow cohomology ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. The source **declines** to assert that the ring
`A^*(X)` of Stacks 0B7E is commutative — the warning after that tag reads "it is not clear that
the `ℤ`-algebra structure on `A^*(X)` is commutative, but we will see that Chern classes live in
its center" — and what it uses in place of commutativity is Stacks 02UA: the Chern classes
generate a commutative, indeed central, subalgebra, which is the reading Remark 0ESW makes
explicit when it forms the total Chern class `c(ℰ)` in `A^*(X)^∧`.

This file builds the series ring **in that centre**. Its elements are the series
`(a_0, a_1, a_2, …)` with `a_i ∈ A^i(X)` each of whose components is central in `A^*(X)`, and
under the Cauchy product of `Stacks.Chow.chowSeriesMul` they form a **commutative ring with no
hypothesis at all**: two central classes commute with each other by the definition of the centre,
and that is the whole of the commutativity the Cauchy product needs.

## Why this is not `Stacks.Chow.ChowCohomologySeriesRing`

`Stacks.Chow.ChowCohomologySeriesRing` has the *whole* of `A^i(X)` in each degree, and its
commutativity field is therefore commutativity of `A^*(X)` in every pair of non-negative degrees:
by `Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` such a ring exists on the product of
Stacks 0B7E if and only if that holds. Every theorem carrying one carries that hypothesis, which
the source does not make. Restricting the components to the centre removes it — not by weakening
the structure, but by naming the subobject in which the source works.

## What is reused, and what is new

Nothing of the series machinery is duplicated. The Cauchy product is
`Stacks.Chow.chowSeriesMul` at the degreewise product `Stacks.Chow.chowCohomologyGradedProductRule`
of Stacks 0B7E, the unit series is `Stacks.Chow.chowCohomologySeriesOne`, the inverse is
`Stacks.Chow.gradedFormalInverse`, and the laws are the hypothesis-free theorems already proved
for them: `Stacks.Chow.chowSeriesMul_assoc_of_isAssoc`, `Stacks.Chow.chowSeriesMul_one_left_of`,
`Stacks.Chow.chowSeriesMul_one_right_of`, `Stacks.Chow.chowSeriesMul_add_left_of`,
`Stacks.Chow.chowSeriesMul_add_right_of` and `Stacks.Chow.chowSeriesMul_gradedFormalInverse`. The
only new ingredient is commutativity, and it comes from
`Stacks.Chow.chowSeriesMul_comm_of_forall_comm`, which asks for commutation at the coefficients of
the two series given rather than at every pair of classes.

## Main definitions

* `Stacks.Chow.IsCentralComponent` — a class `a ∈ A^p(X)` is central in the ring `A^*(X)`. This is
  the conclusion of Stacks 02UA clause (1),
  `Stacks.Chow.chernClassBivariant_mem_center`, verbatim: that theorem is a proof of this
  predicate for `c_j(ℰ)` with no bridge in between.
* `Stacks.Chow.IsCentralSeries` — every component of a series is central.
* `Stacks.Chow.centralChowSeriesSubgroup` — the central series, as an additive subgroup of
  `∏_{i ≥ 0} A^i(X)`.
* `Stacks.Chow.centralChowSeriesCommRing` — **the construction**: the central series are a
  **commutative ring** under the pointwise sum and the Cauchy product of Stacks 0FE0, with no
  hypothesis on `A^*(X)`.
* `Stacks.Chow.CentralUnitalSeries` — the central series with constant term `1`, a commutative
  **group** under the Cauchy product, with `Stacks.Chow.gradedFormalInverse` for the inverse. This
  is what a Chern class map on `K_0(Vect(X))` needs as a target, and it is the object the total
  Chern class of Remark 0ESW lives in.

## Main results

* `Stacks.Chow.isCentralComponent_iff_heq_comm` — a class is central exactly when it commutes with
  every homogeneous class, the transport of the degree removed. This is how centrality is used.
* `Stacks.Chow.chowSeriesMul_comm_of_isCentralComponent` — **the point**: the Cauchy product of a
  series with central components commutes with every series.
* `Stacks.Chow.isCentralComponent_of_restriction_of_injective` — centrality is *reflected* by a
  degreewise injective restriction map of Stacks 0B7F. This is the degreewise form of
  `Stacks.Chow.mem_center_of_chowCohomologyTotalRestriction_mem_center`.

## Which degrees are covered

The centre is taken in the ring `A^*(X)`, which is graded by `ℤ`: a central class commutes with
the classes of **every** degree, the negative ones included. So the commutativity of the ring
below is not the `ℕ`-indexed one of `Stacks.Chow.GradedChowProductRule.IsComm`, and
`Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg` — the observation that a series ring leaves the
negative degrees of the centrality assertion open — does not apply to it. The series themselves
are indexed by `ℕ`, as the product of Stacks 0FEL is; it is the commutation that is asked in all
of `ℤ`.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

-- `Finset.antidiagonal` is ambiguous once `Mathlib.Data.Finset.MulAntidiagonal` is imported: the
-- additive form of `Finset.mulAntidiagonal` carries the name too. The antidiagonal meant here is
-- the one of `Finset.HasAntidiagonal`.
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso)

/-! ### Homogeneous classes in the direct sum -/

/-- **Two classes of equal degrees have the same image in `A^*(X)` exactly when they agree
heterogeneously.** The components of `Stacks.Chow.chowCohomology` are indexed by `ℤ` and a product
of two classes lands in a degree presented as a sum, so comparisons of products inside the direct
sum are comparisons of degrees as well as of classes; this is what trades the one for the
other. -/
theorem chowCohomologyOf_eq_iff_heq {p q : ℤ} (h : p = q)
    (a : chowCohomologyComponent C G sX p) (b : chowCohomologyComponent C G sX q) :
    DirectSum.of (fun r : ℤ ↦ chowCohomologyComponent C G sX r) p a
        = DirectSum.of (fun r : ℤ ↦ chowCohomologyComponent C G sX r) q b ↔ a ≍ b := by
  cases h
  exact ⟨fun hab => heq_of_eq (DirectSum.of_injective _ hab),
    fun hab => congrArg _ (eq_of_heq hab)⟩

/-! ### Central classes -/

/-- **A class of `A^p(X)` is central in the ring `A^*(X)` of Stacks 0B7E.** This is the conclusion
of Stacks 02UA clause (1) as `Stacks.Chow.chernClassBivariant_mem_center` states it: a membership
in `Subring.center` of the image of the class under `DirectSum.of`. The ring structure of Stacks
0B7E is an `@[instance_reducible] def` and not an `instance`, which is why it is supplied by
hand. -/
def IsCentralComponent {p : ℤ} (a : chowCohomologyComponent C G sX p) : Prop :=
  letI : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) p a ∈
    Subring.center (chowCohomology C G sX)

/-- **A class is central exactly when it commutes with every homogeneous class.** The two products
`a · b` and `b · a` of a class of degree `p` and a class of degree `q` lie in `A^{p+q}(X)` and
`A^{q+p}(X)`, the same integer presented by two terms, so the commutation is heterogeneous; in the
direct sum both are elements of one type and no transport appears. An arbitrary element of
`A^*(X)` is a finite sum of homogeneous ones, which is why commuting with those is enough. -/
theorem isCentralComponent_iff_heq_comm {p : ℤ} (a : chowCohomologyComponent C G sX p) :
    IsCentralComponent C G sX hiso a ↔
      ∀ (q : ℤ) (b : chowCohomologyComponent C G sX q),
        chowCohomologyRingMul C G sX hiso a b ≍ chowCohomologyRingMul C G sX hiso b a := by
  let gring : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C G sX q :=
    chowCohomologyGRing C G sX hiso
  let : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  have key : IsCentralComponent C G sX hiso a ↔
      ∀ x : chowCohomology C G sX,
        x * DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) p a
          = DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) p a * x :=
    Subring.mem_center_iff
  rw [key]
  constructor
  · intro ha q b
    have h := ha (DirectSum.of (fun r : ℤ ↦ chowCohomologyComponent C G sX r) q b)
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of] at h
    exact ((chowCohomologyOf_eq_iff_heq C G sX (add_comm q p) _ _).1 h).symm
  · intro hcomm x
    induction x using DirectSum.induction_on with
    | zero => rw [zero_mul, mul_zero]
    | of q b =>
        rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
        exact (chowCohomologyOf_eq_iff_heq C G sX (add_comm q p) _ _).2 (hcomm q b).symm
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]

/-- The classes of `A^p(X)` that are central, as an additive subgroup. -/
private def centralComponentAddSubgroup (p : ℤ) :
    AddSubgroup (chowCohomologyComponent C G sX p) :=
  letI : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  (Subring.center (chowCohomology C G sX)).toAddSubgroup.comap
    (DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) p)

/-- The zero class of any degree is central. -/
theorem isCentralComponent_zero {p : ℤ} :
    IsCentralComponent C G sX hiso (0 : chowCohomologyComponent C G sX p) :=
  (centralComponentAddSubgroup C G sX hiso p).zero_mem

/-- **The unit `1 ∈ A^0(X)` of Stacks 0B7E is central.** It operates as the identity on the Chow
group of every test scheme, so both products with it are the class itself. -/
theorem isCentralComponent_chowCohomologyUnit :
    IsCentralComponent C G sX hiso (chowCohomologyUnit C G sX hiso) :=
  (isCentralComponent_iff_heq_comm C G sX hiso _).2 fun _ b =>
    (chowCohomologyUnit_mul C G sX hiso b).trans (chowCohomologyMul_unit C G sX hiso b).symm

section Closure

variable {C G sX hiso}

/-- A sum of central classes is central. -/
theorem isCentralComponent_add {p : ℤ} {a b : chowCohomologyComponent C G sX p}
    (ha : IsCentralComponent C G sX hiso a) (hb : IsCentralComponent C G sX hiso b) :
    IsCentralComponent C G sX hiso (a + b) :=
  (centralComponentAddSubgroup C G sX hiso p).add_mem ha hb

/-- The negative of a central class is central. -/
theorem isCentralComponent_neg {p : ℤ} {a : chowCohomologyComponent C G sX p}
    (ha : IsCentralComponent C G sX hiso a) : IsCentralComponent C G sX hiso (-a) :=
  (centralComponentAddSubgroup C G sX hiso p).neg_mem ha

/-- A finite sum of central classes is central. -/
theorem isCentralComponent_sum {α : Type*} {p : ℤ} (s : Finset α)
    (f : α → chowCohomologyComponent C G sX p)
    (hf : ∀ i ∈ s, IsCentralComponent C G sX hiso (f i)) :
    IsCentralComponent C G sX hiso (∑ i ∈ s, f i) :=
  (centralComponentAddSubgroup C G sX hiso p).sum_mem hf

/-- **The product of two central classes is central**: the centre of a ring is closed under
multiplication, and the product of Stacks 0B7E is the multiplication of two homogeneous elements
of the direct sum. -/
theorem isCentralComponent_mul {p q : ℤ} {a : chowCohomologyComponent C G sX p}
    {b : chowCohomologyComponent C G sX q} (ha : IsCentralComponent C G sX hiso a)
    (hb : IsCentralComponent C G sX hiso b) :
    IsCentralComponent C G sX hiso (chowCohomologyRingMul C G sX hiso a b) := by
  let gring : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C G sX q :=
    chowCohomologyGRing C G sX hiso
  let : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  have h : DirectSum.of (fun r : ℤ ↦ chowCohomologyComponent C G sX r) p a
        * DirectSum.of (fun r : ℤ ↦ chowCohomologyComponent C G sX r) q b ∈
      Subring.center (chowCohomology C G sX) := Subring.mul_mem _ ha hb
  rwa [DirectSum.of_mul_of] at h

/-- Transporting a central class between components of equal degree keeps it central. -/
theorem isCentralComponent_degreeCast {p q : ℤ} (h : p = q)
    {a : chowCohomologyComponent C G sX p} (ha : IsCentralComponent C G sX hiso a) :
    IsCentralComponent C G sX hiso (chowCohomologyDegreeCast h a) := by
  subst h
  exact ha

/-- **The degreewise product of Stacks 0B7E takes central classes to central classes.** It is the
product of Stacks 0B7E followed by the transport of the degree, and both preserve centrality. -/
theorem isCentralComponent_chowCohomologyGradedProductRule {i j n : ℕ} (h : i + j = n)
    {x : chowCohomologyComponent C G sX (i : ℤ)} {y : chowCohomologyComponent C G sX (j : ℤ)}
    (hx : IsCentralComponent C G sX hiso x) (hy : IsCentralComponent C G sX hiso y) :
    IsCentralComponent C G sX hiso (chowCohomologyGradedProductRule hiso i j n h x y) := by
  simp only [chowCohomologyGradedProductRule]
  exact isCentralComponent_degreeCast _ (isCentralComponent_mul hx hy)

end Closure

/-! ### Commutativity of the Cauchy product in the centre -/

/-- **The Cauchy product of a series with central components commutes with every series.** This is
the whole content of the construction: `Stacks.Chow.chowSeriesMul_comm_of_forall_comm` asks for
commutation at the coefficients of the two series given, and centrality of the coefficients of one
of them supplies it in every pair of degrees. No hypothesis on `A^*(X)` is involved. -/
theorem chowSeriesMul_comm_of_isCentralComponent (a b : chowCohomologySeries C G sX)
    (ha : ∀ i : ℕ, IsCentralComponent C G sX hiso (a i)) :
    chowSeriesMul (chowCohomologyGradedProductRule hiso) a b
      = chowSeriesMul (chowCohomologyGradedProductRule hiso) b a := by
  refine chowSeriesMul_comm_of_forall_comm a b fun i j n h h' => ?_
  simp only [chowCohomologyGradedProductRule]
  refine chowCohomologyDegreeCast_eq_of_heq _ ?_
  exact ((isCentralComponent_iff_heq_comm C G sX hiso (a i)).1 (ha i) (j : ℤ) (b j)).trans
    (chowCohomologyDegreeCast_heq _ _).symm

/-! ### Central series -/

/-- **A series of Chow cohomology classes all of whose components are central** in the ring
`A^*(X)` of Stacks 0B7E. -/
def IsCentralSeries (a : chowCohomologySeries C G sX) : Prop :=
  ∀ i : ℕ, IsCentralComponent C G sX hiso (a i)

/-- **The unit series of Stacks 0B7E is central.** Its constant term is the unit `1 ∈ A^0(X)` and
its other components vanish. -/
theorem isCentralSeries_chowCohomologySeriesOne :
    IsCentralSeries C G sX hiso (chowCohomologySeriesOne hiso) := by
  intro i
  cases i with
  | zero => exact isCentralComponent_chowCohomologyUnit C G sX hiso
  | succ k => exact isCentralComponent_zero C G sX hiso

/-- **The Cauchy product of two central series is central.** Each coefficient of the product is a
finite sum of degreewise products of central classes. -/
theorem isCentralSeries_chowSeriesMul {a b : chowCohomologySeries C G sX}
    (ha : IsCentralSeries C G sX hiso a) (hb : IsCentralSeries C G sX hiso b) :
    IsCentralSeries C G sX hiso (chowSeriesMul (chowCohomologyGradedProductRule hiso) a b) := by
  intro n
  rw [chowSeriesMul]
  refine isCentralComponent_sum _ _ fun p _ => ?_
  rw [chowSeriesTerm]
  split
  · exact isCentralComponent_chowCohomologyGradedProductRule _ (ha p.1) (hb p.2)
  · exact isCentralComponent_zero C G sX hiso

/-- **The formal inverse of a central series is central.** The recursion of
`Stacks.Chow.gradedFormalInverse` builds each coefficient out of the coefficients of the series and
the lower coefficients of the inverse, so the centre, being closed under the degreewise product,
sums and negation, swallows all of them. -/
theorem isCentralSeries_gradedFormalInverse {a : chowCohomologySeries C G sX}
    (ha : IsCentralSeries C G sX hiso a) :
    IsCentralSeries C G sX hiso
      (gradedFormalInverse (chowCohomologyGradedProductRule hiso)
        (chowCohomologyUnit C G sX hiso) a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
        rw [gradedFormalInverse_zero]
        exact isCentralComponent_chowCohomologyUnit C G sX hiso
    | succ m =>
        rw [gradedFormalInverse_succ]
        refine isCentralComponent_neg (isCentralComponent_sum _ _ fun p hp => ?_)
        rw [mem_antidiagonal] at hp
        rw [dif_pos hp]
        exact isCentralComponent_chowCohomologyGradedProductRule _ (ha (p.1 + 1))
          (ih p.2 (by omega))

/-! ### The series ring of the centre -/

/-- **The central series, as an additive subgroup of `∏_{i ≥ 0} A^i(X)`.** The centre of a ring is
an additive subgroup, degreewise. -/
def centralChowSeriesSubgroup : AddSubgroup (chowCohomologySeries C G sX) where
  carrier := {a | IsCentralSeries C G sX hiso a}
  add_mem' ha hb i := isCentralComponent_add (ha i) (hb i)
  zero_mem' _ := isCentralComponent_zero C G sX hiso
  neg_mem' ha i := isCentralComponent_neg (ha i)

/-- Membership of the subgroup of central series is centrality of every component. -/
theorem mem_centralChowSeriesSubgroup_iff (a : chowCohomologySeries C G sX) :
    a ∈ centralChowSeriesSubgroup C G sX hiso ↔ IsCentralSeries C G sX hiso a := Iff.rfl

/-- **The series ring in the centre of `A^*(X)`, and it is commutative.** The series
`(a_0, a_1, a_2, …)` with `a_i ∈ A^i(X)` central in the ring `A^*(X)` of Stacks 0B7E form a
commutative ring under the pointwise sum and the Cauchy product of Stacks 0FE0 — with **no
hypothesis** on `A^*(X)`, whose commutativity the source declines to assert.

Every law but commutativity is one of the hypothesis-free theorems about the product of Stacks
0B7E: associativity of the Cauchy product is `Stacks.Chow.chowSeriesMul_assoc_of_isAssoc` applied
to associativity of composition of bivariant classes, the distributive laws are
`Stacks.Chow.chowSeriesMul_add_left_of` and `Stacks.Chow.chowSeriesMul_add_right_of` applied to
the two distributive laws of Stacks 0B7E, and the unit laws are
`Stacks.Chow.chowSeriesMul_one_left_of` and `Stacks.Chow.chowSeriesMul_one_right_of` applied to
the unit `1 ∈ A^0(X)`. Commutativity is
`Stacks.Chow.chowSeriesMul_comm_of_isCentralComponent`, and it is where the restriction to the
centre is used. Contrast `Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`: the same
construction over the whole of each `A^i(X)` exists only under commutativity of `A^*(X)` in every
pair of non-negative degrees. -/
instance centralChowSeriesCommRing : CommRing (centralChowSeriesSubgroup C G sX hiso) :=
  { (inferInstance : AddCommGroup (centralChowSeriesSubgroup C G sX hiso)) with
    mul := fun a b => ⟨chowSeriesMul (chowCohomologyGradedProductRule hiso) a.1 b.1,
      isCentralSeries_chowSeriesMul C G sX hiso a.2 b.2⟩
    one := ⟨chowCohomologySeriesOne hiso, isCentralSeries_chowCohomologySeriesOne C G sX hiso⟩
    mul_assoc := fun a b c => Subtype.ext (chowSeriesMul_assoc_of_isAssoc
      (chowCohomologyGradedProductRule_isAddLeft hiso)
      (chowCohomologyGradedProductRule_isAddRight hiso)
      (chowCohomologyGradedProductRule_isAssoc hiso) a.1 b.1 c.1)
    mul_comm := fun a b =>
      Subtype.ext (chowSeriesMul_comm_of_isCentralComponent C G sX hiso a.1 b.1 a.2)
    one_mul := fun a => Subtype.ext (chowSeriesMul_one_left_of
      (chowCohomologyGradedProductRule_isAddLeft hiso) (chowCohomologySeriesOne hiso)
      (fun _ => rfl) (chowCohomologyGradedProductRule_one_mul hiso) a.1)
    mul_one := fun a => Subtype.ext (chowSeriesMul_one_right_of
      (chowCohomologyGradedProductRule_isAddRight hiso) (chowCohomologySeriesOne hiso)
      (fun _ => rfl) (chowCohomologyGradedProductRule_mul_one hiso) a.1)
    zero_mul := fun a => Subtype.ext
      (chowSeriesMul_zero_left_of (chowCohomologyGradedProductRule_isAddLeft hiso) a.1)
    mul_zero := fun a => Subtype.ext
      (chowSeriesMul_zero_right_of (chowCohomologyGradedProductRule_isAddRight hiso) a.1)
    left_distrib := fun a b c => Subtype.ext
      (chowSeriesMul_add_right_of (chowCohomologyGradedProductRule_isAddRight hiso) a.1 b.1 c.1)
    right_distrib := fun a b c => Subtype.ext
      (chowSeriesMul_add_left_of (chowCohomologyGradedProductRule_isAddLeft hiso) a.1 b.1 c.1) }

@[simp] theorem centralChowSeries_val_mul (a b : centralChowSeriesSubgroup C G sX hiso) :
    (a * b).1 = chowSeriesMul (chowCohomologyGradedProductRule hiso) a.1 b.1 := rfl

@[simp] theorem centralChowSeries_val_one :
    (1 : centralChowSeriesSubgroup C G sX hiso).1 = chowCohomologySeriesOne hiso := rfl

/-! ### The group of central series with constant term `1` -/

/-- **The central series with constant term `1`.** Under the Cauchy product of Stacks 0FE0 these
form a commutative **group**, the formal inverse `Stacks.Chow.gradedFormalInverse` providing the
inverse — with no hypothesis on `A^*(X)`. The total Chern class of a module is one of them by
Stacks 02UA, and that is what lets the Chern class map of Stacks 0FEL be extended
multiplicatively to `K_0(Vect(X))` without assuming `A^*(X)` commutative. -/
structure CentralUnitalSeries where
  /-- The underlying series `(a_0, a_1, a_2, …)` with `a_i ∈ A^i(X)`. -/
  val : chowCohomologySeries C G sX
  /-- Every component is central in the ring `A^*(X)` of Stacks 0B7E. -/
  central : IsCentralSeries C G sX hiso val
  /-- The constant term is the unit `1 ∈ A^0(X)` of Stacks 0B7E. -/
  val_apply_zero : val 0 = chowCohomologyUnit C G sX hiso

namespace CentralUnitalSeries

variable {C G sX hiso}

/-- Two central unital series with the same underlying series are equal. -/
@[ext] theorem ext {a b : CentralUnitalSeries C G sX hiso} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  subst h
  rfl

/-- **The central unital series are a commutative group under the Cauchy product**, with no
hypothesis on `A^*(X)`. The product and the unit are those of
`Stacks.Chow.centralChowSeriesCommRing`, which preserve a constant term of `1`, and the inverse is
`Stacks.Chow.gradedFormalInverse`, whose recursion needs exactly that constant term; it stays
central by `Stacks.Chow.isCentralSeries_gradedFormalInverse`. Commutativity is again
`Stacks.Chow.chowSeriesMul_comm_of_isCentralComponent`, and it is the only law using the
restriction to the centre. -/
instance : CommGroup (CentralUnitalSeries C G sX hiso) where
  mul a b :=
    { val := chowSeriesMul (chowCohomologyGradedProductRule hiso) a.val b.val
      central := isCentralSeries_chowSeriesMul C G sX hiso a.central b.central
      val_apply_zero := by
        rw [chowSeriesMul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
          chowSeriesTerm_of_add (chowCohomologyGradedProductRule hiso) a.val b.val
            (show 0 + 0 = 0 from rfl), a.val_apply_zero, b.val_apply_zero]
        exact chowCohomologyGradedProductRule_one_mul hiso 0 (chowCohomologyUnit C G sX hiso) }
  one :=
    { val := chowCohomologySeriesOne hiso
      central := isCentralSeries_chowCohomologySeriesOne C G sX hiso
      val_apply_zero := rfl }
  inv a :=
    { val := gradedFormalInverse (chowCohomologyGradedProductRule hiso)
        (chowCohomologyUnit C G sX hiso) a.val
      central := isCentralSeries_gradedFormalInverse C G sX hiso a.central
      val_apply_zero := gradedFormalInverse_zero _ _ _ }
  mul_assoc a b c := ext (chowSeriesMul_assoc_of_isAssoc
    (chowCohomologyGradedProductRule_isAddLeft hiso)
    (chowCohomologyGradedProductRule_isAddRight hiso)
    (chowCohomologyGradedProductRule_isAssoc hiso) a.val b.val c.val)
  mul_comm a b := ext (chowSeriesMul_comm_of_isCentralComponent C G sX hiso a.val b.val a.central)
  one_mul a := ext (chowSeriesMul_one_left_of
    (chowCohomologyGradedProductRule_isAddLeft hiso) (chowCohomologySeriesOne hiso)
    (fun _ => rfl) (chowCohomologyGradedProductRule_one_mul hiso) a.val)
  mul_one a := ext (chowSeriesMul_one_right_of
    (chowCohomologyGradedProductRule_isAddRight hiso) (chowCohomologySeriesOne hiso)
    (fun _ => rfl) (chowCohomologyGradedProductRule_mul_one hiso) a.val)
  inv_mul_cancel a := ext
    ((chowSeriesMul_comm_of_isCentralComponent C G sX hiso _ a.val
        (isCentralSeries_gradedFormalInverse C G sX hiso a.central)).trans
      (chowSeriesMul_gradedFormalInverse (chowCohomologySeriesOne hiso) (fun _ => rfl)
        (chowCohomologyGradedProductRule_one_mul hiso) a.val a.val_apply_zero))

@[simp] theorem val_mul (a b : CentralUnitalSeries C G sX hiso) :
    (a * b).val = chowSeriesMul (chowCohomologyGradedProductRule hiso) a.val b.val := rfl

@[simp] theorem val_one :
    (1 : CentralUnitalSeries C G sX hiso).val = chowCohomologySeriesOne hiso := rfl

@[simp] theorem val_inv (a : CentralUnitalSeries C G sX hiso) :
    (a⁻¹).val = gradedFormalInverse (chowCohomologyGradedProductRule hiso)
      (chowCohomologyUnit C G sX hiso) a.val := rfl

/-- **A central unital series is a unital series of any series ring built on the product of Stacks
0B7E, and the inclusion is multiplicative.** So the commutative group above is a subgroup of
`Stacks.Chow.ChowCohomologySeriesRing.UnitalSeries` whenever the latter exists — which, by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`, is exactly when `A^*(X)` is
commutative in every pair of non-negative degrees. The point of the group above is that it exists
when that one does not. -/
def toUnitalSeries {R : ChowCohomologySeriesRing C G sX}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hone : R.one = chowCohomologySeriesOne hiso) :
    CentralUnitalSeries C G sX hiso →* ChowCohomologySeriesRing.UnitalSeries R :=
  MonoidHom.mk' (fun a => ⟨a.val, by rw [hone]; exact a.val_apply_zero⟩)
    fun a b => Subtype.ext (by
      change chowSeriesMul (chowCohomologyGradedProductRule hiso) a.val b.val
        = chowSeriesMul R.gradedMul a.val b.val
      rw [hmul])

@[simp] theorem toUnitalSeries_val {R : ChowCohomologySeriesRing C G sX}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hone : R.one = chowCohomologySeriesOne hiso) (a : CentralUnitalSeries C G sX hiso) :
    (toUnitalSeries hmul hone a).1 = a.val := rfl

end CentralUnitalSeries

/-! ### Centrality is reflected by an injective restriction map -/

section Restriction

variable {X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Centrality is reflected by a degreewise injective restriction map of Stacks 0B7F.** If the
restriction of a class `a ∈ A^p(X)` to `X'` is central in `A^*(X')` then `a` is central in
`A^*(X)`: the restriction map is multiplicative, by Stacks 0B7F, so it carries both products of
`a` with a class `b` to the two products of their restrictions, which agree.

This is the degreewise form of
`Stacks.Chow.mem_center_of_chowCohomologyTotalRestriction_mem_center`, stated on the components
rather than on the graded ring because that is the shape in which the coefficients of a series are
given. Along an envelope the injectivity is automatic, by
`Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope`. -/
theorem isCentralComponent_of_restriction_of_injective
    (hinj : ∀ q : ℤ, Function.Injective (chowCohomologyRestriction C G sX f q hgys))
    {p : ℤ} (a : chowCohomologyComponent C G sX p)
    (ha : IsCentralComponent C G (f ≫ sX) hiso
      (chowCohomologyRestriction C G sX f p hgys a)) :
    IsCentralComponent C G sX hiso a := by
  rw [isCentralComponent_iff_heq_comm] at ha ⊢
  intro q b
  have key : chowCohomologyDegreeCast (show q + p = p + q from add_comm q p)
      (chowCohomologyRingMul C G sX hiso b a) = chowCohomologyRingMul C G sX hiso a b := by
    refine hinj (p + q) ?_
    rw [chowCohomologyRestriction_degreeCast, chowCohomologyRestriction_chowCohomologyRingMul,
      chowCohomologyRestriction_chowCohomologyRingMul]
    exact chowCohomologyDegreeCast_eq_of_heq _
      (ha q (chowCohomologyRestriction C G sX f q hgys b)).symm
  exact ((chowCohomologyDegreeCast_eq_iff_heq _ _ _).1 key).symm

/-! ### Restriction as a homomorphism of the central series groups

The restriction map of Stacks 0B7F need **not** take central classes to central classes: it is a
ring map `A^*(X) ⟶ A^*(X')`, and a ring map carries the centre into the centre only when it is
surjective. So there is no homomorphism from the central unital series of `X` to those of `X'`.
What there is, and what suffices, is a homomorphism on the subgroup of those whose restriction
*does* land in the centre — a condition that the total Chern classes satisfy for the reason the
source gives, namely Stacks 02UA on `X'`. -/

/-- **The central unital series whose restriction is again central.** A subgroup: the unit series
restricts to the unit series, and restriction respects the Cauchy product and the formal inverse
by `Stacks.Chow.chowCohomologyRestriction_chowSeriesMul` and
`Stacks.Chow.chowCohomologyRestriction_gradedFormalInverse`, while the central series of `X'` are
closed under both. -/
def centralUnitalSeriesRestrictionSubgroup :
    Subgroup (CentralUnitalSeries C G sX hiso) where
  carrier := {a | IsCentralSeries C G (f ≫ sX) hiso
    fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys (a.val i)}
  one_mem' i := by
    change IsCentralComponent C G (f ≫ sX) hiso (chowCohomologyRestriction C G sX f (i : ℤ) hgys
      (chowCohomologySeriesOne hiso i))
    rw [chowCohomologyRestriction_chowCohomologySeriesOne]
    exact isCentralSeries_chowCohomologySeriesOne C G (f ≫ sX) hiso i
  mul_mem' {a b} ha hb i := by
    change IsCentralComponent C G (f ≫ sX) hiso (chowCohomologyRestriction C G sX f (i : ℤ) hgys
      (chowSeriesMul (chowCohomologyGradedProductRule hiso) a.val b.val i))
    rw [chowCohomologyRestriction_chowSeriesMul]
    exact isCentralSeries_chowSeriesMul C G (f ≫ sX) hiso ha hb i
  inv_mem' {a} ha i := by
    change IsCentralComponent C G (f ≫ sX) hiso (chowCohomologyRestriction C G sX f (i : ℤ) hgys
      (gradedFormalInverse (chowCohomologyGradedProductRule hiso)
        (chowCohomologyUnit C G sX hiso) a.val i))
    rw [chowCohomologyRestriction_gradedFormalInverse, chowCohomologyRestriction_unit]
    exact isCentralSeries_gradedFormalInverse C G (f ≫ sX) hiso ha i

/-- **Restriction of Chow cohomology is a homomorphism of the central series groups**, on the
subgroup where it lands in the centre. The unit series goes to the unit series and the Cauchy
products correspond, both with no hypothesis on `A^*(X)` or on `A^*(X')`. -/
def centralUnitalSeriesRestrictionHom :
    centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys →*
      CentralUnitalSeries C G (f ≫ sX) hiso :=
  MonoidHom.mk'
    (fun a =>
      { val := fun i => chowCohomologyRestriction C G sX f (i : ℤ) hgys (a.1.val i)
        central := a.2
        val_apply_zero := by
          rw [a.1.val_apply_zero]
          exact chowCohomologyRestriction_unit C G sX f hgys hiso })
    fun a b => CentralUnitalSeries.ext (funext fun i =>
      chowCohomologyRestriction_chowSeriesMul C G sX f hgys hiso a.1.val b.1.val i)

@[simp] theorem centralUnitalSeriesRestrictionHom_val
    (a : centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys) (i : ℕ) :
    (centralUnitalSeriesRestrictionHom C G sX hiso f hgys a).val i
      = chowCohomologyRestriction C G sX f (i : ℤ) hgys (a.1.val i) := rfl

end Restriction

end Stacks.Chow

end
