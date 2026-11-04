module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-! # The monomial basis of a graded divided power polynomial algebra

Let `A` be a graded divided power polynomial algebra over a coefficient algebra `P`, presented as
in `DividedPowers.TateResolution.GradedDividedPowerPolynomial` as the directed union of the
finite stages obtained by adjoining homogeneous variables of positive degree. This file exhibits
each homogeneous piece `Aᵢ n` as a free `P`-module on the divided power monomials of degree `n`,
and deduces that `Aᵢ n` is free, respectively module finite, over the ground ring whenever `P`
is. That freeness is the input to the `free` field of
`DividedPowers.TateResolution.Resolution`, and the basis itself is what lets the Tor groups of
Tag 09PQ be read off the homogeneous pieces.

A monomial is described by an exponent vector `ν` on the variables, finitely supported, whose
exponent at a variable of odd degree is at most `1` — a variable of odd degree has square zero,
so no higher power of it survives. Its *weight* is `∑ j, ν j * deg j`, which is the degree of the
corresponding product of divided powers. The associated element of `A` is the product of the
`ν j`-th divided power of each variable in the support, taken in the order of a chosen linear
order on the variables; for a variable of odd degree the `k`-th divided power is just the `k`-th
power.

## Main definitions

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.Variable` — the index type of all
  variables, with `varDegree` their degrees.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.IsAdmissible` and `weight` — the
  constraint on an exponent vector and its total degree.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.monomialSet` and `Monomials` — the
  exponent vectors of the monomials of a given degree, and their index type.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.variablePower` and `monomial` — the
  divided powers of a single variable and the monomial attached to an exponent vector.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.stage` and `stageGrade` — a finite
  variable stage of the presentation and its homogeneous pieces.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.monomialSumMap` — the expansion of a
  finitely supported family of coefficients against the monomials.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.gradeEquiv` — the monomial basis: the
  degree-`n` piece as a free module on the degree-`n` monomials over the coefficient algebra.

## Main results

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.monomial_mem_grade` — a monomial is
  homogeneous of degree its weight.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.finite_monomials` — there are only
  finitely many monomials of each degree when every variable set is finite.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.odd_decomposition` and
  `even_decomposition` — adjoining one variable to a finite stage splits its homogeneous pieces,
  in two summands in odd degree and in one summand per divided power in even degree.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.stageGrade_le_repSubmodule` and
  `eq_zero_of_monomialSumMap_eq_zero` — the monomials in the variables of a finite stage span its
  homogeneous pieces and are linearly independent over the coefficient algebra.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.exists_monomialSumMap_eq` and
  `eq_zero_of_monomialSumMap_eq_zero_of_mem_monomialSet` — the same two statements for the whole
  algebra, obtained from the stages by passing to the directed union.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.gradeExpansion_bijective` — the
  statement that `gradeEquiv` is well defined.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.free_grade` and `finite_grade` — each
  homogeneous piece is free, respectively module finite, over the ground ring.

## Implementation notes

The order used to form a monomial is an arbitrary linear order on the variables, taken as an
instance argument. Different orders change a monomial by a sign only, so the statements that do
not mention a monomial — freeness and module finiteness of the homogeneous pieces — take no order
argument and choose one internally, by well-ordering the variables.

The two one-variable decompositions are the only results that use the `successor` field of the
presentation. They are stated for an arbitrary finite set `T` of variables together with the
hypothesis that its members are the new variable and those of `S`, rather than for
`insert j S`, so that they apply whichever `DecidableEq` instance the ambient context supplies;
the field itself is stated with a classical one.

Linear independence is recorded as the statement that a vanishing combination has vanishing
coefficients, over the index type of *all* exponent vectors rather than over the subtype of those
of a given degree, since the inductive step on the variables changes both the degree and the
variable set. The subtype appears only in `gradeEquiv`, where
`Finsupp.supportedEquivFinsupp` converts between the two.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

namespace GradedDividedPowerPolynomial

noncomputable section

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}

/-- The index type of all the variables of a graded divided power polynomial algebra: a variable
is an index of `G.indices n` for some `n`, and then has degree `n + 1`. -/
public abbrev Variable (G : GradedDividedPowerPolynomial Aᵢ γ ι) : Type w :=
  Σ n : ℕ, G.indices n

/-- The degree of a variable. Every variable has positive degree. -/
public def varDegree (G : GradedDividedPowerPolynomial Aᵢ γ ι) (j : G.Variable) : ℕ :=
  j.1 + 1

/-- Every variable has positive degree. -/
public theorem varDegree_pos (G : GradedDividedPowerPolynomial Aᵢ γ ι) (j : G.Variable) :
    0 < G.varDegree j :=
  Nat.succ_pos _

/-- A variable is homogeneous of its degree. -/
public theorem generator_mem_grade (G : GradedDividedPowerPolynomial Aᵢ γ ι) (j : G.Variable) :
    G.generator j ∈ Aᵢ (G.varDegree j) :=
  G.generator_mem j

/-- A variable of even degree lies in the positive even part, where the divided powers live. -/
public theorem generator_mem_positiveEvenPart (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {j : G.Variable} (hj : Even (G.varDegree j)) :
    G.generator j ∈ positiveEvenPart Aᵢ := by
  obtain ⟨k, hk⟩ := hj
  have hk' : G.varDegree j = 2 * k := by omega
  refine mem_positiveEvenPart_of_mem_grade Aᵢ (d := k) ?_ ?_
  · have := G.varDegree_pos j
    omega
  · rw [← hk']
    exact G.generator_mem_grade j

/-- An exponent vector is *admissible* when its exponent at every variable of odd degree is at
most one: an odd-degree variable has square zero, so no higher power of it survives. -/
public def IsAdmissible (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (ν : G.Variable →₀ ℕ) : Prop :=
  ∀ j : G.Variable, Odd (G.varDegree j) → ν j ≤ 1

/-- The weight of an exponent vector: the degree of the monomial it describes. -/
public def weight (G : GradedDividedPowerPolynomial Aᵢ γ ι) (ν : G.Variable →₀ ℕ) : ℕ :=
  ν.sum fun j k ↦ k * G.varDegree j

/-- The zero exponent vector has weight zero. -/
@[simp]
public theorem weight_zero (G : GradedDividedPowerPolynomial Aᵢ γ ι) :
    G.weight 0 = 0 := by
  simp [weight]

/-- The zero exponent vector is admissible. -/
public theorem isAdmissible_zero (G : GradedDividedPowerPolynomial Aᵢ γ ι) :
    G.IsAdmissible 0 :=
  fun _ _ ↦ by simp

/-- Erasing a variable from an exponent vector preserves admissibility. -/
public theorem IsAdmissible.erase {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} (hν : G.IsAdmissible ν)
    (j : G.Variable) : G.IsAdmissible (ν.erase j) := by
  intro i hi
  by_cases h : i = j
  · subst h; simp
  · rw [Finsupp.erase_ne h]; exact hν i hi

/-- Splitting off the exponent at one variable from the weight. -/
public theorem weight_erase {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    (ν : G.Variable →₀ ℕ) (j : G.Variable) :
    G.weight ν = ν j * G.varDegree j + G.weight (ν.erase j) := by
  simpa [weight] using
    (Finsupp.add_sum_erase' ν j (fun i k ↦ k * G.varDegree i) (fun _ ↦ by simp)).symm

/-- The exponent at any variable is bounded by the weight. -/
public theorem le_weight {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    (ν : G.Variable →₀ ℕ) (j : G.Variable) :
    ν j * G.varDegree j ≤ G.weight ν := by
  rw [weight_erase ν j]
  omega

/-- A variable in the support of an exponent vector has degree at most the weight. -/
public theorem varDegree_le_weight {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} {j : G.Variable} (hj : j ∈ ν.support) :
    G.varDegree j ≤ G.weight ν := by
  calc G.varDegree j = 1 * G.varDegree j := (one_mul _).symm
    _ ≤ ν j * G.varDegree j :=
      Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj))
    _ ≤ G.weight ν := le_weight ν j

/-- The exponent vectors of the monomials of degree `n`: the admissible ones of weight `n`. -/
public def monomialSet (G : GradedDividedPowerPolynomial Aᵢ γ ι) (n : ℕ) :
    Set (G.Variable →₀ ℕ) :=
  {ν : G.Variable →₀ ℕ | G.IsAdmissible ν ∧ G.weight ν = n}

/-- Membership in the exponent set of the degree-`n` monomials. -/
@[simp]
public theorem mem_monomialSet {G : GradedDividedPowerPolynomial Aᵢ γ ι} {n : ℕ}
    {ν : G.Variable →₀ ℕ} :
    ν ∈ G.monomialSet n ↔ G.IsAdmissible ν ∧ G.weight ν = n := Iff.rfl

/-- The index type of the monomials of degree `n`: the admissible exponent vectors of weight
`n`. -/
public def Monomials (G : GradedDividedPowerPolynomial Aᵢ γ ι) (n : ℕ) : Type w :=
  ↥(G.monomialSet n)

/-- A monomial of degree `n` is in particular an exponent vector. -/
instance (G : GradedDividedPowerPolynomial Aᵢ γ ι) (n : ℕ) :
    CoeHead (G.Monomials n) (G.Variable →₀ ℕ) :=
  ⟨Subtype.val⟩

/-- Monomials of a given degree are determined by their exponent vector. -/
@[ext]
public theorem Monomials.ext {G : GradedDividedPowerPolynomial Aᵢ γ ι} {n : ℕ}
    {ν μ : G.Monomials n} (h : (ν : G.Variable →₀ ℕ) = (μ : G.Variable →₀ ℕ)) : ν = μ :=
  Subtype.ext h

/-- An exponent vector of weight `n` vanishes at every variable of degree greater than `n`. -/
public theorem apply_eq_zero_of_weight_lt {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} {j : G.Variable} (hj : G.weight ν < G.varDegree j) : ν j = 0 := by
  by_contra h
  exact absurd (varDegree_le_weight (Finsupp.mem_support_iff.2 h)) (by omega)

/-- There are only finitely many monomials of each degree when every variable set is finite.
This is the finiteness assertion of Tag 09PN. -/
public theorem finite_monomials (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [∀ i : ℕ, Finite (G.indices i)] (n : ℕ) : Finite (G.Monomials n) := by
  classical
  refine Finite.of_injective
    (β := (Σ i : Fin n, G.indices (i : ℕ)) → Fin (n + 1))
    (fun ν j ↦ ⟨(ν : G.Variable →₀ ℕ) ⟨(j.1 : ℕ), j.2⟩, ?_⟩) ?_
  · have hb := le_weight (ν : G.Variable →₀ ℕ) (⟨(j.1 : ℕ), j.2⟩ : G.Variable)
    rw [ν.2.2] at hb
    have h1 : (ν : G.Variable →₀ ℕ) ⟨(j.1 : ℕ), j.2⟩ * 1 ≤
        (ν : G.Variable →₀ ℕ) ⟨(j.1 : ℕ), j.2⟩ * G.varDegree ⟨(j.1 : ℕ), j.2⟩ :=
      Nat.mul_le_mul_left _ (G.varDegree_pos _)
    omega
  · intro ν μ h
    refine Monomials.ext (Finsupp.ext fun j ↦ ?_)
    by_cases hj : (j.1 : ℕ) < n
    · exact congrArg (fun x : Fin (n + 1) ↦ (x : ℕ))
        (congrFun h (⟨⟨j.1, hj⟩, j.2⟩ : Σ i : Fin n, G.indices (i : ℕ)))
    · have hd : n < G.varDegree j := by simp only [varDegree]; omega
      rw [apply_eq_zero_of_weight_lt (ν := (ν : G.Variable →₀ ℕ)) (by rw [ν.2.2]; exact hd),
        apply_eq_zero_of_weight_lt (ν := (μ : G.Variable →₀ ℕ)) (by rw [μ.2.2]; exact hd)]

/-- The `k`-th divided power of a variable: its `k`-th power when the variable has odd degree,
and the `k`-th divided power of the ambient structure when it has even degree. The two cases
agree with the source's description of the variables adjoined by the two kinds of extension. -/
public def variablePower (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (j : G.Variable) (k : ℕ) : A :=
  if Odd (G.varDegree j) then G.generator j ^ k else γ.dpow k (G.generator j)

/-- The zeroth divided power of a variable is one. -/
@[simp]
public theorem variablePower_zero (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (j : G.Variable) : G.variablePower j 0 = 1 := by
  rw [variablePower]
  split_ifs with h
  · exact pow_zero _
  · exact γ.dpow_zero (G.generator_mem_positiveEvenPart (Nat.not_odd_iff_even.1 h))

/-- The first divided power of a variable is the variable itself. -/
@[simp]
public theorem variablePower_one (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (j : G.Variable) : G.variablePower j 1 = G.generator j := by
  rw [variablePower]
  split_ifs with h
  · exact pow_one _
  · exact γ.dpow_one (G.generator_mem_positiveEvenPart (Nat.not_odd_iff_even.1 h))

/-- A divided power of a variable is homogeneous, of the degree of the variable times the
exponent, provided the exponent is admissible for that variable. -/
public theorem variablePower_mem_grade (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (j : G.Variable) (k : ℕ) (hk : Odd (G.varDegree j) → k ≤ 1) :
    G.variablePower j k ∈ Aᵢ (k * G.varDegree j) := by
  rw [variablePower]
  split_ifs with h
  · have hk1 : k ≤ 1 := hk h
    interval_cases k
    · simpa using SetLike.one_mem_graded Aᵢ
    · simpa using G.generator_mem_grade j
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [γ.dpow_zero (G.generator_mem_positiveEvenPart (Nat.not_odd_iff_even.1 h))]
      simpa using SetLike.one_mem_graded Aᵢ
    · obtain ⟨d, hd⟩ := Nat.not_odd_iff_even.1 h
      have hd' : G.varDegree j = 2 * d := by omega
      have := γ.dpow_mem_grade (n := k) (d := d) (x := G.generator j) (by omega)
        (G.generator_mem_positiveEvenPart (Nat.not_odd_iff_even.1 h))
        (by rw [← hd']; exact G.generator_mem_grade j)
      rw [show 2 * k * d = k * G.varDegree j by rw [hd']; ring] at this
      exact this

/-- The monomial attached to an exponent vector: the product of the divided powers of the
variables in its support, multiplied in the order of the chosen linear order. -/
public def monomial (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable]
    (ν : G.Variable →₀ ℕ) : A :=
  ((ν.support.sort).map fun j ↦ G.variablePower j (ν j)).prod

/-- The monomial attached to the zero exponent vector is one. -/
@[simp]
public theorem monomial_zero (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] : G.monomial 0 = 1 := by
  simp [monomial]

/-- Splitting the smallest variable of its support off a monomial. -/
public theorem monomial_erase {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] (ν : G.Variable →₀ ℕ) (j : G.Variable)
    (hlt : ∀ x ∈ ν.support, x ≠ j → j < x) :
    G.monomial ν = G.variablePower j (ν j) * G.monomial (ν.erase j) := by
  classical
  by_cases hj : j ∈ ν.support
  · have hne : j ∉ ν.support.erase j := Finset.notMem_erase _ _
    have hle : ∀ b ∈ ν.support.erase j, j ≤ b := fun b hb ↦
      le_of_lt (hlt b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb))
    have hsort : (ν.support).sort = j :: ((ν.erase j).support).sort := by
      rw [Finsupp.support_erase, ← Finset.sort_insert _ hle hne, Finset.insert_erase hj]
    rw [monomial, monomial, hsort, List.map_cons, List.prod_cons]
    congr 1
    refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
    have hi' : i ∈ (ν.erase j).support := (Finset.mem_sort _).1 hi
    rw [Finsupp.support_erase] at hi'
    rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hi')]
  · rw [Finsupp.notMem_support_iff.1 hj, Finsupp.erase_of_notMem_support hj,
      variablePower_zero, one_mul]

/-- A monomial is homogeneous of degree the weight of its exponent vector. -/
public theorem monomial_mem_grade {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {ν : G.Variable →₀ ℕ} (hν : G.IsAdmissible ν) :
    G.monomial ν ∈ Aᵢ (G.weight ν) := by
  classical
  suffices h : ∀ (c : ℕ) (μ : G.Variable →₀ ℕ), μ.support.card ≤ c → G.IsAdmissible μ →
      G.monomial μ ∈ Aᵢ (G.weight μ) from h ν.support.card ν le_rfl hν
  intro c
  induction c with
  | zero =>
    intro μ hc _
    rw [Finsupp.support_eq_empty.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 hc))]
    simpa using SetLike.one_mem_graded Aᵢ
  | succ c ih =>
    intro μ hc hμ
    rcases μ.support.eq_empty_or_nonempty with he | hne
    · rw [Finsupp.support_eq_empty.1 he]
      simpa using SetLike.one_mem_graded Aᵢ
    · set j := μ.support.min' hne with hjdef
      have hjmem : j ∈ μ.support := Finset.min'_mem _ hne
      have hlt : ∀ x ∈ μ.support, x ≠ j → j < x := fun x hx hxj ↦
        lt_of_le_of_ne (Finset.min'_le _ _ hx) (Ne.symm hxj)
      have hcard : (μ.erase j).support.card ≤ c := by
        rw [Finsupp.support_erase]
        have := Finset.card_erase_of_mem hjmem
        omega
      rw [monomial_erase μ j hlt, weight_erase μ j]
      exact SetLike.GradedMul.mul_mem
        (G.variablePower_mem_grade j (μ j) (hμ j))
        (ih _ hcard (hμ.erase j))

/-! ### Finite stages and their homogeneous pieces -/

/-- The finite stage of the presentation on a finite set `S` of variables: the subring generated
by the coefficients and by the variables of `S` together with all their divided powers. -/
public abbrev stage (G : GradedDividedPowerPolynomial Aᵢ γ ι) (S : Finset G.Variable) :
    Subring A :=
  finiteVariableStage γ ι G.generator S

/-- The coefficients lie in every stage. -/
public theorem coeff_mem_stage (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (S : Finset G.Variable) (p : P) : ι p ∈ G.stage S :=
  Subring.subset_closure (Or.inl ⟨p, rfl⟩)

/-- Every stage contains the image of the ground ring, so it is a submodule. -/
public theorem smul_mem_stage (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (S : Finset G.Variable) (r : R) {x : A} (hx : x ∈ G.stage S) : r • x ∈ G.stage S := by
  rw [Algebra.smul_def, ← ι.commutes r]
  exact mul_mem (G.coeff_mem_stage S _) hx

/-- The divided powers of a variable of `S` lie in the stage on `S`. -/
public theorem variablePower_mem_stage (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {S : Finset G.Variable} {j : G.Variable} (hj : j ∈ S) (k : ℕ) :
    G.variablePower j k ∈ G.stage S := by
  rw [variablePower]
  split_ifs
  · have hg : G.generator j ∈ G.stage S :=
      Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)
    exact pow_mem hg k
  · exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨k, rfl⟩⟩)

/-- The stages increase with the set of variables. -/
public theorem stage_mono (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {S T : Finset G.Variable} (h : S ⊆ T) : G.stage S ≤ G.stage T :=
  Subring.closure_le.2 fun x hx ↦ by
    rcases hx with hx | ⟨j, hjS, hj⟩
    · exact Subring.subset_closure (Or.inl hx)
    · exact Subring.subset_closure (Or.inr ⟨j, h hjS, hj⟩)

/-- Only the coefficients lie in the stage on no variables. -/
public theorem mem_stage_empty_iff (G : GradedDividedPowerPolynomial Aᵢ γ ι) {x : A} :
    x ∈ G.stage (∅ : Finset G.Variable) ↔ ∃ p : P, ι p = x := by
  refine ⟨fun hx ↦ ?_, fun ⟨p, hp⟩ ↦ hp ▸ G.coeff_mem_stage _ p⟩
  have hle : G.stage (∅ : Finset G.Variable) ≤ ι.range.toSubring := by
    refine Subring.closure_le.2 fun y hy ↦ ?_
    rcases hy with hy | ⟨j, hj, -⟩
    · exact Subalgebra.mem_toSubring.2 ((AlgHom.mem_range ι).2 hy)
    · simp at hj
  exact (AlgHom.mem_range ι).1 (Subalgebra.mem_toSubring.1 (hle hx))

/-- A monomial in the variables of `S` lies in the stage on `S`. -/
public theorem monomial_mem_stage {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {ν : G.Variable →₀ ℕ} {S : Finset G.Variable}
    (h : ν.support ⊆ S) : G.monomial ν ∈ G.stage S := by
  refine list_prod_mem fun x hx ↦ ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact G.variablePower_mem_stage (h ((Finset.mem_sort _).1 hi)) _

/-- The degree-`n` homogeneous piece of the finite stage on `S`. -/
public def stageGrade (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (S : Finset G.Variable) (n : ℕ) : Submodule R A where
  carrier := {x : A | x ∈ Aᵢ n ∧ x ∈ G.stage S}
  zero_mem' := ⟨Submodule.zero_mem _, Subring.zero_mem _⟩
  add_mem' hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, Subring.add_mem _ hx.2 hy.2⟩
  smul_mem' r _ hx := ⟨Submodule.smul_mem _ r hx.1, G.smul_mem_stage S r hx.2⟩

/-- Membership in the degree-`n` piece of a stage is homogeneity together with membership in
the stage. -/
@[simp]
public theorem mem_stageGrade {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {S : Finset G.Variable} {n : ℕ} {x : A} :
    x ∈ G.stageGrade S n ↔ x ∈ Aᵢ n ∧ x ∈ G.stage S := Iff.rfl

/-- The homogeneous pieces of the stages increase with the set of variables. -/
public theorem stageGrade_mono (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {S T : Finset G.Variable} (h : S ⊆ T) (n : ℕ) :
    G.stageGrade S n ≤ G.stageGrade T n :=
  fun _ hx ↦ ⟨hx.1, G.stage_mono h hx.2⟩

/-! ### The monomial expansion map -/

/-- The `P`-linear combination of the monomials with the prescribed coefficients, written with
the coefficient on the right of its monomial. -/
public def monomialSumMap (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable] :
    ((G.Variable →₀ ℕ) →₀ P) →ₗ[R] A :=
  Finsupp.lsum R fun ν ↦ (LinearMap.mulLeft R (G.monomial ν)).comp ι.toLinearMap

/-- The expansion map is the sum of the monomials against their coefficients. -/
public theorem monomialSumMap_apply (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (c : (G.Variable →₀ ℕ) →₀ P) :
    G.monomialSumMap c = c.sum fun ν p ↦ G.monomial ν * ι p :=
  Finsupp.lsum_apply R _ c

/-- A single coefficient expands to the corresponding monomial with that coefficient. -/
@[simp]
public theorem monomialSumMap_single (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (ν : G.Variable →₀ ℕ) (p : P) :
    G.monomialSumMap (Finsupp.single ν p) = G.monomial ν * ι p := by
  rw [monomialSumMap_apply, Finsupp.sum_single_index (by simp)]

/-- An exponent vector contributing to the degree-`n` piece of the stage on `S`: admissible, of
weight `n`, and supported in `S`. -/
public def IsStageExponent (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (S : Finset G.Variable) (n : ℕ) (ν : G.Variable →₀ ℕ) : Prop :=
  G.IsAdmissible ν ∧ G.weight ν = n ∧ ν.support ⊆ S

/-- A stage exponent for `S` is a stage exponent for any larger set of variables. -/
public theorem IsStageExponent.mono {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {S T : Finset G.Variable} {n : ℕ} {ν : G.Variable →₀ ℕ}
    (h : G.IsStageExponent S n ν) (hST : S ⊆ T) : G.IsStageExponent T n ν :=
  ⟨h.1, h.2.1, h.2.2.trans hST⟩

/-- The submodule of elements of degree `n` that are `P`-combinations of the degree-`n` monomials
in the variables of `S`. -/
public def repSubmodule (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable]
    (S : Finset G.Variable) (n : ℕ) : Submodule R A :=
  Submodule.map G.monomialSumMap (Finsupp.supported P R {ν | G.IsStageExponent S n ν})

/-- Membership in the monomial span, unfolded as the existence of a coefficient family. -/
public theorem mem_repSubmodule_iff {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {S : Finset G.Variable} {n : ℕ} {x : A} :
    x ∈ G.repSubmodule S n ↔ ∃ c : (G.Variable →₀ ℕ) →₀ P,
      (∀ ν ∈ c.support, G.IsStageExponent S n ν) ∧ G.monomialSumMap c = x := by
  refine ⟨fun ⟨c, hc, hx⟩ ↦ ⟨c, fun ν hν ↦ (Finsupp.mem_supported R c).1 hc hν, hx⟩,
    fun ⟨c, hc, hx⟩ ↦ ⟨c, (Finsupp.mem_supported R c).2 fun ν hν ↦ hc ν hν, hx⟩⟩

/-- A single monomial with a coefficient is a `P`-combination of monomials. -/
public theorem monomial_mul_mem_repSubmodule {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {S : Finset G.Variable} {n : ℕ} {ν : G.Variable →₀ ℕ}
    (hν : G.IsStageExponent S n ν) (p : P) :
    G.monomial ν * ι p ∈ G.repSubmodule S n :=
  mem_repSubmodule_iff.2 ⟨Finsupp.single ν p, fun μ hμ ↦ by
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hμ)]; exact hν, by simp⟩

/-- An admissible monomial of weight `n` times a coefficient is homogeneous of degree `n`. -/
private theorem monomial_mul_coeff_mem_grade {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {ν : G.Variable →₀ ℕ} {n : ℕ} (hν : G.IsAdmissible ν)
    (hw : G.weight ν = n) (p : P) : G.monomial ν * ι p ∈ Aᵢ n := by
  have h0 : G.monomial ν * ι p ∈ Aᵢ (G.weight ν + 0) :=
    SetLike.GradedMul.mul_mem (monomial_mem_grade hν) (G.coefficient_mem _)
  rwa [hw, Nat.add_zero] at h0

/-- A `P`-combination of the degree-`n` monomials in the variables of `S` is a homogeneous
element of degree `n` of the stage on `S`. -/
public theorem repSubmodule_le_stageGrade {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] (S : Finset G.Variable) (n : ℕ) :
    G.repSubmodule S n ≤ G.stageGrade S n := by
  rintro x ⟨c, hc, rfl⟩
  rw [monomialSumMap_apply]
  refine Submodule.sum_mem _ fun ν hν ↦ ?_
  have h := (Finsupp.mem_supported R c).1 hc hν
  exact ⟨monomial_mul_coeff_mem_grade h.1 h.2.1 _,
    mul_mem (monomial_mem_stage h.2.2) (G.coeff_mem_stage S _)⟩

/-- The combinations of monomials in a smaller set of variables are among those for a larger
set. -/
public theorem repSubmodule_mono {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {S T : Finset G.Variable} (hST : S ⊆ T) (n : ℕ) :
    G.repSubmodule S n ≤ G.repSubmodule T n := by
  rintro x ⟨c, hc, rfl⟩
  exact mem_repSubmodule_iff.2
    ⟨c, fun ν hν ↦ ((Finsupp.mem_supported R c).1 hc hν).mono hST, rfl⟩

/-- In odd degree the divided powers of a variable are its ordinary powers. -/
public theorem variablePower_of_odd (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {j : G.Variable} (hj : Odd (G.varDegree j)) (k : ℕ) :
    G.variablePower j k = G.generator j ^ k := by
  rw [variablePower]
  split_ifs
  · rfl

/-- In even degree the divided powers of a variable are those of the ambient structure. -/
public theorem variablePower_of_even (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    {j : G.Variable} (hj : Even (G.varDegree j)) (k : ℕ) :
    G.variablePower j k = γ.dpow k (G.generator j) := by
  rw [variablePower]
  split_ifs with h
  · exact absurd hj (Nat.not_even_iff_odd.2 h)
  · rfl

/-! ### Adjoining one variable

The two results below are the only places where the `successor` field of the presentation is
used. They say that adjoining one more variable to a finite stage decomposes the homogeneous
pieces of the larger stage as a direct sum over the exponent of the new variable: two summands
when the new variable has odd degree, since its square vanishes, and one summand for each
divided power when it has even degree.
-/

/-- A stage on `T`, whose members are `j` and those of `S`, is the stage on `insert j S`. -/
private theorem mem_finiteVariableStage_insert {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {S T : Finset G.Variable} {j : G.Variable} (hT : ∀ a : G.Variable, a ∈ T ↔ a = j ∨ a ∈ S)
    {x : A} (hx : x ∈ G.stage T) : x ∈ finiteVariableStage γ ι G.generator
      (@insert _ _ (@Finset.instInsert _ (Classical.decEq G.Variable)) j S) := by
  let := Classical.decEq G.Variable
  have : T = insert j S := by ext a; rw [hT a, Finset.mem_insert]
  exact this ▸ hx

/-- Adjoining a variable `j` of odd degree to the stage on `S`: every homogeneous element of the
larger stage is uniquely a coefficient plus a coefficient times the new variable. -/
public theorem odd_decomposition {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {S : Finset G.Variable} {j : G.Variable} (hj : j ∉ S) (hodd : Odd (G.varDegree j))
    {T : Finset G.Variable} (hT : ∀ a : G.Variable, a ∈ T ↔ a = j ∨ a ∈ S) :
    (∀ (n : ℕ) (x : A), x ∈ G.stageGrade T n → ∃ b₀ b₁ : A,
        b₀ ∈ G.stageGrade S n ∧ b₁ ∈ G.stageGrade S (n - G.varDegree j) ∧
        (G.varDegree j ≤ n ∨ b₁ = 0) ∧ x = b₀ + b₁ * G.generator j) ∧
      (∀ b₀ b₁ : A, b₀ ∈ G.stage S → b₁ ∈ G.stage S →
        b₀ + b₁ * G.generator j = 0 → b₀ = 0 ∧ b₁ = 0) := by
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, hdp, hoddc, hevenc⟩ := G.successor S j hj
  obtain ⟨e, he_incl, he_gen, he_grade, he_dpow⟩ := hoddc hodd
  have hSi : ∀ (m : ℕ) (b : ↥(G.stage S)), b ∈ Sᵢ m ↔ (b : A) ∈ Aᵢ m := by
    intro m b
    rw [← he_incl b, ← he_grade m (OddVariableExtension.inclusion Sᵢ (j.1 + 1) b),
      OddVariableExtension.mem_grade_iff]
    refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ h.1⟩
    rw [show (OddVariableExtension.inclusion Sᵢ (j.1 + 1) b).snd = (0 : ↥(G.stage S)) from rfl]
    split_ifs <;> simp
  have hvd : G.varDegree j = j.1 + 1 := rfl
  constructor
  · intro n x hx
    have hxT := mem_finiteVariableStage_insert hT hx.2
    set y : OddVariableExtension Sᵢ (j.1 + 1) := e.symm ⟨x, hxT⟩ with hydef
    have hey : (e y : A) = x := by rw [hydef, e.apply_symm_apply]
    have hygr := (OddVariableExtension.mem_grade_iff Sᵢ (j.1 + 1) n y).1
      ((he_grade n y).2 (by rw [hey]; exact hx.1))
    obtain ⟨u, v, hy, hu, hv⟩ : ∃ u v : ↥(G.stage S),
        (OddVariableExtension.inclusion Sᵢ (j.1 + 1) u
          + OddVariableExtension.inclusion Sᵢ (j.1 + 1) v
            * OddVariableExtension.generator Sᵢ (j.1 + 1) = y)
        ∧ u ∈ Sᵢ n ∧ v ∈ (if j.1 + 1 ≤ n then Sᵢ (n - (j.1 + 1)) else ⊥) :=
      ⟨y.fst, y.snd,
        OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator Sᵢ (j.1 + 1) y,
        hygr.1, hygr.2⟩
    have hsplit : x = (u : A) + (v : A) * G.generator j := by
      rw [← hey, ← hy, map_add, map_mul]
      push_cast
      rw [he_incl u, he_incl v, he_gen]
    by_cases hdn : j.1 + 1 ≤ n
    · have hv' : v ∈ Sᵢ (n - (j.1 + 1)) := by simpa [hdn] using hv
      exact ⟨_, _, ⟨(hSi n u).1 hu, u.2⟩, ⟨by rw [hvd]; exact (hSi _ _).1 hv', v.2⟩,
        Or.inl (by rw [hvd]; exact hdn), hsplit⟩
    · have hv' : v = 0 := (Submodule.mem_bot R).1 (by simpa [hdn] using hv)
      refine ⟨_, _, ⟨(hSi n u).1 hu, u.2⟩, ?_, Or.inr ?_, hsplit⟩
      · rw [hv']
        exact ⟨by simp, by simp⟩
      · rw [hv']; simp
  · have key : ∀ u v : ↥(G.stage S),
        (u : A) + (v : A) * G.generator j = 0 → u = 0 ∧ v = 0 := by
      intro u v huv
      set y : OddVariableExtension Sᵢ (j.1 + 1) :=
        OddVariableExtension.inclusion Sᵢ (j.1 + 1) u
          + OddVariableExtension.inclusion Sᵢ (j.1 + 1) v
            * OddVariableExtension.generator Sᵢ (j.1 + 1) with hydef
      have hzero : (e y : A) = 0 := by
        rw [hydef, map_add, map_mul]
        push_cast
        rw [he_incl u, he_incl v, he_gen]
        exact huv
      have hy0 : y = 0 :=
        e.injective ((Subtype.ext (by simpa using hzero) : e y = 0).trans (map_zero e).symm)
      have hcoef : OddVariableExtension.coefficients Sᵢ (j.1 + 1) y = (u, v) := by
        rw [hydef]; simp
      rw [hy0, map_zero, Prod.ext_iff] at hcoef
      exact ⟨hcoef.1.symm, hcoef.2.symm⟩
    intro b₀ b₁ h₀ h₁ h
    obtain ⟨h1, h2⟩ := key ⟨b₀, h₀⟩ ⟨b₁, h₁⟩ h
    exact ⟨by simpa using congrArg (fun w : ↥(G.stage S) ↦ (w : A)) h1,
      by simpa using congrArg (fun w : ↥(G.stage S) ↦ (w : A)) h2⟩

/-- Adjoining a variable `j` of even degree to the stage on `S`: every homogeneous element of
the larger stage is uniquely a finite sum of divided powers of the new variable with
coefficients from the stage on `S`. -/
public theorem even_decomposition {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {S : Finset G.Variable} {j : G.Variable} (hj : j ∉ S) (heven : Even (G.varDegree j))
    {T : Finset G.Variable} (hT : ∀ a : G.Variable, a ∈ T ↔ a = j ∨ a ∈ S) :
    (∀ (n : ℕ) (x : A), x ∈ G.stageGrade T n → ∃ (K : Finset ℕ) (b : ℕ → A),
        (∀ k ∈ K, k * G.varDegree j ≤ n) ∧
        (∀ k ∈ K, b k ∈ G.stageGrade S (n - k * G.varDegree j)) ∧
        x = ∑ k ∈ K, G.variablePower j k * b k) ∧
      (∀ (K : Finset ℕ) (b : ℕ → A), (∀ k, b k ∈ G.stage S) →
        ∑ k ∈ K, G.variablePower j k * b k = 0 → ∀ k ∈ K, b k = 0) := by
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, hdp, hoddc, hevenc⟩ := G.successor S j hj
  let _ : Algebra R ↥(G.stage S) := aS
  let _ : GradedAlgebra Sᵢ := gS
  let _ : IsStrictlyGradedComm Sᵢ := cS
  have _ : Fact (Even (j.1 + 1)) := ⟨heven⟩
  obtain ⟨e, he_coeff, he_gen, he_grade, he_dpow⟩ := hevenc heven
  have hdpos : 0 < j.1 + 1 := Nat.succ_pos _
  have hvd : G.varDegree j = j.1 + 1 := rfl
  have hSi : ∀ (m : ℕ) (b : ↥(G.stage S)), b ∈ Sᵢ m ↔ (b : A) ∈ Aᵢ m := by
    intro m b
    rw [← he_coeff b, ← he_grade m (EvenVariableAlgebra.coeffEmbedding b)]
    exact (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff Sᵢ (j.1 + 1) m b).symm
  have hmem1 : EvenVariableAlgebra.monomial (1 : ℕ) (1 : ↥(G.stage S)) ∈
      positiveEvenPart (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) := by
    obtain ⟨q, hq⟩ := heven
    have hq' : j.1 + 1 = 2 * q := by simp only [varDegree] at hq; omega
    refine mem_positiveEvenPart_of_mem_grade _ (d := q) (by omega) ?_
    rw [← hq']
    simpa using EvenVariableAlgebra.monomial_one_mem_grade Sᵢ (j.1 + 1) 1
  have hmono : ∀ k : ℕ, ((e (EvenVariableAlgebra.monomial k (1 : ↥(G.stage S)))) : A) =
      G.variablePower j k := by
    intro k
    have h := he_dpow k _ hmem1
    rw [he_gen, dpow_monomial_one (j.1 + 1) hdpos δS k 1 Nat.one_pos] at h
    rw [show dividedPowerMonomialCoefficient k 1 = 1 by
      simp [dividedPowerMonomialCoefficient,
        Nat.div_self k.factorial_pos]] at h
    simp only [Nat.mul_one, one_smul] at h
    rw [G.variablePower_of_even heven k]
    exact h.symm
  have hmonoc : ∀ (k : ℕ) (c : ↥(G.stage S)),
      ((e (EvenVariableAlgebra.monomial k c)) : A) = G.variablePower j k * (c : A) := by
    intro k c
    have hfac : EvenVariableAlgebra.monomial k c =
        EvenVariableAlgebra.monomial k (1 : ↥(G.stage S))
          * EvenVariableAlgebra.coeffEmbedding c := by
      rw [EvenVariableAlgebra.coeffEmbedding_apply, EvenVariableAlgebra.monomial_mul_monomial]
      simp
    rw [hfac, map_mul]
    push_cast
    rw [hmono k, he_coeff c]
  constructor
  · intro n x hx
    have hxT := mem_finiteVariableStage_insert hT hx.2
    set y : EvenVariableAlgebra ↥(G.stage S) := e.symm ⟨x, hxT⟩ with hydef
    have hey : (e y : A) = x := by rw [hydef, e.apply_symm_apply]
    have hygr := (EvenVariableAlgebra.mem_grade_iff Sᵢ (j.1 + 1) n y).1
      ((he_grade n y).2 (by rw [hey]; exact hx.1))
    have hsupp : ∀ k ∈ y.coeff.support, k * (j.1 + 1) ≤ n := by
      intro k hk
      by_contra hc
      exact Finsupp.mem_support_iff.1 hk ((Submodule.mem_bot R).1 (by simpa [hc] using hygr k))
    refine ⟨y.coeff.support, fun k ↦ ((y.coeff k : ↥(G.stage S)) : A), ?_, ?_, ?_⟩
    · intro k hk; rw [hvd]; exact hsupp k hk
    · intro k hk
      refine ⟨?_, (y.coeff k).2⟩
      rw [hvd]
      exact (hSi _ _).1 (by simpa [hsupp k hk] using hygr k)
    · have hy : y = ∑ k ∈ y.coeff.support, EvenVariableAlgebra.monomial k (y.coeff k) :=
        (EvenVariableAlgebra.sum_monomial y).symm
      calc x = (e y : A) := hey.symm
        _ = (e (∑ k ∈ y.coeff.support, EvenVariableAlgebra.monomial k (y.coeff k)) : A) := by
              rw [← hy]
        _ = ∑ k ∈ y.coeff.support, ((e (EvenVariableAlgebra.monomial k (y.coeff k))) : A) := by
              rw [map_sum, AddSubmonoidClass.coe_finsetSum]
        _ = ∑ k ∈ y.coeff.support, G.variablePower j k * ((y.coeff k : ↥(G.stage S)) : A) :=
              Finset.sum_congr rfl fun k _ ↦ hmonoc k (y.coeff k)
  · intro K b hb hsum k hk
    set y : EvenVariableAlgebra ↥(G.stage S) :=
      ∑ i ∈ K, EvenVariableAlgebra.monomial i (⟨b i, hb i⟩ : ↥(G.stage S)) with hydef
    have hzero : (e y : A) = 0 := by
      rw [hydef, map_sum, AddSubmonoidClass.coe_finsetSum, ← hsum]
      exact Finset.sum_congr rfl fun i _ ↦ hmonoc i _
    have hy0 : y = 0 :=
      e.injective ((Subtype.ext (by simpa using hzero) : e y = 0).trans (map_zero e).symm)
    have hcoeffsum : y.coeff =
        ∑ i ∈ K, Finsupp.single i (⟨b i, hb i⟩ : ↥(G.stage S)) := by
      show (show EvenVariableAlgebra ↥(G.stage S) →+ (ℕ →₀ ↥(G.stage S)) from
        { toFun := EvenVariableAlgebra.coeff
          map_zero' := EvenVariableAlgebra.coeff_zero
          map_add' := EvenVariableAlgebra.coeff_add }) y = _
      rw [hydef, map_sum]
      rfl
    have hck : y.coeff k = (⟨b k, hb k⟩ : ↥(G.stage S)) := by
      rw [hcoeffsum, Finset.sum_apply']
      refine (Finset.sum_eq_single_of_mem k hk fun i _ hik ↦ ?_).trans Finsupp.single_eq_same
      exact Finsupp.single_eq_of_ne' (M := ↥(G.stage S)) hik
    rw [hy0] at hck
    have hbk : (⟨b k, hb k⟩ : ↥(G.stage S)) = 0 := by
      rw [← hck]; simp
    simpa using congrArg (fun w : ↥(G.stage S) ↦ (w : A)) hbk

/-! ### The monomial span of a stage -/

/-- Erasing the smallest variable from an exponent vector that was obtained by adjoining it. -/
public theorem erase_add_single {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} {j : G.Variable} (hj : ν j = 0) (k : ℕ) :
    (ν + Finsupp.single j k).erase j = ν := by
  refine Finsupp.ext fun i ↦ ?_
  by_cases h : i = j
  · subst h; simp [hj]
  · rw [Finsupp.erase_ne h]
    simp [Finsupp.single_eq_of_ne h]

/-- The weight of an exponent vector after adjoining a new variable. -/
public theorem weight_add_single {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} {j : G.Variable} (hj : ν j = 0) (k : ℕ) :
    G.weight (ν + Finsupp.single j k) = G.weight ν + k * G.varDegree j := by
  rw [weight_erase (ν + Finsupp.single j k) j, erase_add_single hj k]
  simp [hj, Nat.add_comm]

/-- Adjoining a new variable preserves admissibility, provided its exponent is admissible. -/
public theorem IsAdmissible.add_single {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    {ν : G.Variable →₀ ℕ} (hν : G.IsAdmissible ν) {j : G.Variable} (hj : ν j = 0) {k : ℕ}
    (hk : Odd (G.varDegree j) → k ≤ 1) : G.IsAdmissible (ν + Finsupp.single j k) := by
  intro i hi
  by_cases h : i = j
  · subst h; simpa [hj] using hk hi
  · simpa [Finsupp.single_eq_of_ne h] using hν i hi

/-- Multiplying a monomial by a divided power of a variable smaller than its support adjoins
that variable to the exponent vector. -/
public theorem variablePower_mul_monomial {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {j : G.Variable} {ν : G.Variable →₀ ℕ}
    (hν : ∀ x ∈ ν.support, j < x) (k : ℕ) :
    G.variablePower j k * G.monomial ν = G.monomial (ν + Finsupp.single j k) := by
  have hj : ν j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ absurd (hν j h) (lt_irrefl j)
  have hlt : ∀ x ∈ (ν + Finsupp.single j k).support, x ≠ j → j < x := by
    intro x hx hxj
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hν x h
    · exact absurd (Finset.mem_singleton.1 (Finsupp.support_single_subset h)) hxj
  rw [monomial_erase (ν + Finsupp.single j k) j hlt, erase_add_single hj k]
  simp [hj]

/-- A divided power of a variable smaller than `S` times a combination of monomials in `S` is a
combination of monomials in the enlarged variable set. -/
public theorem variablePower_mul_mem_repSubmodule {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {S : Finset G.Variable} {j : G.Variable}
    (hmin : ∀ x ∈ S, j < x) {T : Finset G.Variable}
    (hT : ∀ a : G.Variable, a ∈ T ↔ a = j ∨ a ∈ S) (k n : ℕ)
    (hk : Odd (G.varDegree j) → k ≤ 1) {b : A} (hb : b ∈ G.repSubmodule S n) :
    G.variablePower j k * b ∈ G.repSubmodule T (n + k * G.varDegree j) := by
  obtain ⟨c, hc, rfl⟩ := mem_repSubmodule_iff.1 hb
  have hinj : Function.Injective fun ν : G.Variable →₀ ℕ ↦ ν + Finsupp.single j k :=
    fun _ _ h ↦ by simpa using h
  have hsupp : ∀ ν ∈ c.support, ∀ x ∈ ν.support, j < x := fun ν hν x hx ↦
    hmin x ((hc ν hν).2.2 hx)
  have hzero : ∀ ν ∈ c.support, ν j = 0 := fun ν hν ↦
    Finsupp.notMem_support_iff.1 fun h ↦ absurd (hsupp ν hν j h) (lt_irrefl j)
  refine mem_repSubmodule_iff.2
    ⟨Finsupp.mapDomain (fun ν ↦ ν + Finsupp.single j k) c, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hμ)
    refine ⟨(hc ν hν).1.add_single (hzero ν hν) hk, ?_, ?_⟩
    · rw [weight_add_single (hzero ν hν) k, (hc ν hν).2.1]
    · intro x hx
      rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
      · exact (hT x).2 (Or.inr ((hc ν hν).2.2 h))
      · exact (hT x).2 (Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h)))
  · rw [monomialSumMap_apply, Finsupp.sum_mapDomain_index_inj hinj, monomialSumMap_apply,
      Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν hν ↦ ?_
    rw [← mul_assoc, variablePower_mul_monomial (hsupp ν hν) k]

/-- Every homogeneous element of a finite stage is a `P`-combination of the monomials in the
variables of that stage. -/
public theorem stageGrade_le_repSubmodule {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] (S : Finset G.Variable) :
    ∀ n : ℕ, G.stageGrade S n ≤ G.repSubmodule S n := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro n x hx
    obtain ⟨p, rfl⟩ := G.mem_stage_empty_iff.1 hx.2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h := G.monomial_mul_mem_repSubmodule
        (S := (∅ : Finset G.Variable)) (n := 0) (ν := 0)
        ⟨G.isAdmissible_zero, G.weight_zero, by simp⟩ p
      rwa [monomial_zero, one_mul] at h
    · have hz : ι p = 0 := by
        by_contra hne
        exact absurd (DirectSum.degree_eq_of_mem_mem Aᵢ hx.1 (G.coefficient_mem p) hne) (by omega)
      rw [hz]
      exact Submodule.zero_mem _
  | insert j S hmin ih =>
    intro n x hx
    have hj : j ∉ S := fun h ↦ absurd (hmin j h) (lt_irrefl j)
    have hT : ∀ a : G.Variable, a ∈ insert j S ↔ a = j ∨ a ∈ S := fun _ ↦ Finset.mem_insert
    rcases Nat.even_or_odd (G.varDegree j) with heven | hodd
    · obtain ⟨K, b, hKle, hKmem, rfl⟩ := (even_decomposition hj heven hT).1 n x hx
      refine Submodule.sum_mem _ fun k hk ↦ ?_
      have h := variablePower_mul_mem_repSubmodule hmin hT k (n - k * G.varDegree j)
        (fun ho ↦ absurd heven (Nat.not_even_iff_odd.2 ho)) (ih _ (hKmem k hk))
      rwa [Nat.sub_add_cancel (hKle k hk)] at h
    · obtain ⟨b₀, b₁, h₀, h₁, hcase, rfl⟩ := (odd_decomposition hj hodd hT).1 n x hx
      refine Submodule.add_mem _ (repSubmodule_mono (Finset.subset_insert j S) n (ih n h₀)) ?_
      rcases hcase with hle | hb₁
      · have hcomm : b₁ * G.generator j =
            ((-1 : R) ^ ((n - G.varDegree j) * G.varDegree j)) •
              (G.generator j * b₁) :=
          IsStrictlyGradedComm.graded_comm h₁.1 (G.generator_mem_grade j)
        rw [hcomm]
        refine Submodule.smul_mem _ _ ?_
        have h := variablePower_mul_mem_repSubmodule hmin hT 1 (n - G.varDegree j)
          (fun _ ↦ le_rfl) (ih _ h₁)
        rw [G.variablePower_one, Nat.one_mul, Nat.sub_add_cancel hle] at h
        exact h
      · rw [hb₁, zero_mul]
        exact Submodule.zero_mem _

/-! ### Linear independence of the monomials over a stage -/

/-- The coefficients of the monomials with a prescribed exponent at one variable, reindexed by
the exponent vectors with that variable erased. -/
private def sliceCoeff {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    (c : (G.Variable →₀ ℕ) →₀ P) (j : G.Variable) (k : ℕ) : (G.Variable →₀ ℕ) →₀ P :=
  Finsupp.mapDomain (fun ν ↦ ν.erase j) (c.filter fun ν ↦ ν j = k)

/-- A monomial combination expanded over one slice of the exponents at a single variable. -/
private theorem monomialSumMap_sliceCoeff {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] (c : (G.Variable →₀ ℕ) →₀ P) (j : G.Variable) (k : ℕ) :
    G.monomialSumMap (sliceCoeff c j k) =
      ∑ ν ∈ c.support.filter fun ν ↦ ν j = k, G.monomial (ν.erase j) * ι (c ν) := by
  rw [monomialSumMap_apply, sliceCoeff,
    Finsupp.sum_mapDomain_index (by simp) (by simp [mul_add]), Finsupp.sum,
    Finsupp.support_filter]
  refine Finset.sum_congr rfl fun ν hν ↦ ?_
  rw [Finsupp.filter_apply_pos (fun μ : G.Variable →₀ ℕ ↦ μ j = k) c
    (Finset.mem_filter.1 hν).2]

/-- A slice at an exponent not occurring in the coefficients vanishes. -/
private theorem sliceCoeff_eq_zero {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    (c : (G.Variable →₀ ℕ) →₀ P) (j : G.Variable) {k : ℕ}
    (hk : k ∉ c.support.image fun ν ↦ ν j) : sliceCoeff c j k = 0 := by
  have hf : (c.filter fun ν ↦ ν j = k) = 0 := by
    refine Finsupp.ext fun ν ↦ ?_
    by_cases h : ν j = k
    · rw [Finsupp.filter_apply_pos (fun μ : G.Variable →₀ ℕ ↦ μ j = k) c h]
      by_contra hne
      exact hk (Finset.mem_image.2 ⟨ν, Finsupp.mem_support_iff.2 hne, h⟩)
    · rw [Finsupp.filter_apply_neg (fun μ : G.Variable →₀ ℕ ↦ μ j = k) c h]; rfl
  rw [sliceCoeff, hf, Finsupp.mapDomain_zero]

/-- The monomials of a given degree in the variables of a finite stage are linearly independent
over the coefficient algebra. -/
public theorem eq_zero_of_monomialSumMap_eq_zero {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] (S : Finset G.Variable) :
    ∀ (n : ℕ) (c : (G.Variable →₀ ℕ) →₀ P),
      (∀ ν ∈ c.support, G.IsStageExponent S n ν) → G.monomialSumMap c = 0 → c = 0 := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro n c hc h0
    have hsub : c.support ⊆ {0} := fun ν hν ↦ Finset.mem_singleton.2
      (Finsupp.support_eq_empty.1 (Finset.subset_empty.1 (hc ν hν).2.2))
    have hval : G.monomialSumMap c = ι (c 0) := by
      rw [monomialSumMap_apply, Finsupp.sum_of_support_subset c hsub _ (by simp)]
      simp
    have hc0 : c 0 = 0 := G.coefficient_injective (by rw [← hval, h0, map_zero])
    refine Finsupp.ext fun ν ↦ ?_
    by_cases hν : ν ∈ c.support
    · rw [Finset.mem_singleton.1 (hsub hν)]; exact hc0
    · exact Finsupp.notMem_support_iff.1 hν
  | insert j S hmin ih =>
    intro n c hc h0
    have hj : j ∉ S := fun h ↦ absurd (hmin j h) (lt_irrefl j)
    have hT : ∀ a : G.Variable, a ∈ insert j S ↔ a = j ∨ a ∈ S := fun _ ↦ Finset.mem_insert
    have hsliceExp : ∀ (k : ℕ) (μ : G.Variable →₀ ℕ), μ ∈ (sliceCoeff c j k).support →
        G.IsStageExponent S (n - k * G.varDegree j) μ := by
      intro k μ hμ
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hμ)
      rw [Finsupp.support_filter, Finset.mem_filter] at hν
      obtain ⟨hνc, hνk⟩ := hν
      refine ⟨(hc ν hνc).1.erase j, ?_, ?_⟩
      · have hw := weight_erase ν j
        rw [(hc ν hνc).2.1, hνk] at hw
        rw [hw, Nat.add_sub_cancel_left]
      · intro x hx
        rw [Finsupp.support_erase] at hx
        rcases (hT x).1 ((hc ν hνc).2.2 (Finset.mem_of_mem_erase hx)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hx)
        · exact h
    have hBgrade : ∀ k : ℕ, G.monomialSumMap (sliceCoeff c j k) ∈
        G.stageGrade S (n - k * G.varDegree j) := fun k ↦
      repSubmodule_le_stageGrade S (n - k * G.varDegree j)
        (mem_repSubmodule_iff.2 ⟨sliceCoeff c j k, hsliceExp k, rfl⟩)
    have hdecomp : G.monomialSumMap c =
        ∑ k ∈ c.support.image (fun ν ↦ ν j),
          G.variablePower j k * G.monomialSumMap (sliceCoeff c j k) := by
      rw [monomialSumMap_apply, Finsupp.sum,
        ← Finset.sum_fiberwise_of_maps_to (g := fun ν : G.Variable →₀ ℕ ↦ ν j)
          (fun ν hν ↦ Finset.mem_image_of_mem _ hν)]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [monomialSumMap_sliceCoeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν hν ↦ ?_
      obtain ⟨hνc, hνk⟩ := Finset.mem_filter.1 hν
      have hlt : ∀ x ∈ ν.support, x ≠ j → j < x := by
        intro x hx hxj
        rcases (hT x).1 ((hc ν hνc).2.2 hx) with h | h
        · exact absurd h hxj
        · exact hmin x h
      rw [← mul_assoc, ← hνk, ← monomial_erase ν j hlt]
    have hBzero : ∀ k : ℕ, G.monomialSumMap (sliceCoeff c j k) = 0 := by
      have hout : ∀ k : ℕ, k ∉ c.support.image (fun ν ↦ ν j) →
          G.monomialSumMap (sliceCoeff c j k) = 0 := fun k hk ↦ by
        rw [sliceCoeff_eq_zero c j hk, map_zero]
      rcases Nat.even_or_odd (G.varDegree j) with heven | hodd
      · have hall := (even_decomposition hj heven hT).2
          (c.support.image fun ν ↦ ν j)
          (fun k ↦ G.monomialSumMap (sliceCoeff c j k)) (fun k ↦ (hBgrade k).2)
          (by rw [← hdecomp]; exact h0)
        intro k
        by_cases hk : k ∈ c.support.image fun ν ↦ ν j
        · exact hall k hk
        · exact hout k hk
      · have hK : c.support.image (fun ν ↦ ν j) ⊆ ({0, 1} : Finset ℕ) := by
          intro k hk
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hk
          have := (hc ν hν).1 j hodd
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have hpair : G.monomialSumMap (sliceCoeff c j 0)
            + G.generator j * G.monomialSumMap (sliceCoeff c j 1) = 0 := by
          rw [← h0, hdecomp, Finset.sum_subset hK (fun k _ hk ↦ by rw [hout k hk, mul_zero]),
            Finset.sum_pair (by norm_num)]
          rw [G.variablePower_zero, G.variablePower_one, one_mul]
        have hsgn := IsStrictlyGradedComm.graded_comm (R := R) (G.generator_mem_grade j)
          ((hBgrade 1).1)
        rw [hsgn, ← smul_mul_assoc] at hpair
        obtain ⟨hz0, hz1⟩ := (odd_decomposition hj hodd hT).2 _ _ (hBgrade 0).2
          (G.smul_mem_stage S _ (hBgrade 1).2) hpair
        have hz1' : G.monomialSumMap (sliceCoeff c j 1) = 0 := by
          have h2 : ((-1 : R) ^ (G.varDegree j * (n - 1 * G.varDegree j))) •
              (((-1 : R) ^ (G.varDegree j * (n - 1 * G.varDegree j))) •
                G.monomialSumMap (sliceCoeff c j 1)) = 0 := by
            rw [hz1, smul_zero]
          rwa [smul_smul, ← pow_add, ← Nat.two_mul, pow_mul, neg_one_sq, one_pow,
            one_smul] at h2
        intro k
        by_cases hk : k ∈ c.support.image fun ν ↦ ν j
        · rcases Finset.mem_insert.1 (hK hk) with rfl | hk1
          · exact hz0
          · rw [Finset.mem_singleton.1 hk1]; exact hz1'
        · exact hout k hk
    refine Finsupp.ext fun ν ↦ ?_
    by_cases hν : ν ∈ c.support
    · have hsl : sliceCoeff c j (ν j) = 0 :=
        ih _ _ (hsliceExp (ν j)) (hBzero (ν j))
      have hinj : Set.InjOn (fun μ : G.Variable →₀ ℕ ↦ μ.erase j)
          {μ : G.Variable →₀ ℕ | μ j = ν j} := by
        intro μ₁ h₁ μ₂ h₂ h
        refine Finsupp.ext fun i ↦ ?_
        by_cases hi : i = j
        · subst hi; rw [h₁, h₂]
        · have h' : Finsupp.erase j μ₁ = Finsupp.erase j μ₂ := h
          calc μ₁ i = (Finsupp.erase j μ₁) i := (Finsupp.erase_ne hi).symm
            _ = (Finsupp.erase j μ₂) i := by rw [h']
            _ = μ₂ i := Finsupp.erase_ne hi
      have hsupp : ↑(c.filter fun μ ↦ μ j = ν j).support ⊆
          {μ : G.Variable →₀ ℕ | μ j = ν j} := by
        rw [Finsupp.support_filter]
        intro μ hμ
        exact (Finset.mem_filter.1 hμ).2
      have happ := Finsupp.mapDomain_apply' {μ : G.Variable →₀ ℕ | μ j = ν j}
        (c.filter fun μ ↦ μ j = ν j) hsupp hinj (a := ν) rfl
      rw [← sliceCoeff, hsl] at happ
      rw [← Finsupp.filter_apply_pos (fun μ : G.Variable →₀ ℕ ↦ μ j = ν j) c rfl,
        ← happ]
      rfl
    · exact Finsupp.notMem_support_iff.1 hν

/-! ### The monomial basis of a homogeneous piece -/

/-- A `P`-combination of the degree-`n` monomials is homogeneous of degree `n`. -/
public theorem monomialSumMap_mem_grade {G : GradedDividedPowerPolynomial Aᵢ γ ι}
    [LinearOrder G.Variable] {n : ℕ} {c : (G.Variable →₀ ℕ) →₀ P}
    (hc : ∀ ν ∈ c.support, ν ∈ G.monomialSet n) : G.monomialSumMap c ∈ Aᵢ n := by
  rw [monomialSumMap_apply]
  exact Submodule.sum_mem _ fun ν hν ↦
    monomial_mul_coeff_mem_grade (hc ν hν).1 (hc ν hν).2 _

/-- Every homogeneous element of degree `n` is a `P`-combination of the monomials of degree
`n`. -/
public theorem exists_monomialSumMap_eq (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (n : ℕ) {x : A} (hx : x ∈ Aᵢ n) :
    ∃ c : (G.Variable →₀ ℕ) →₀ P,
      (∀ ν ∈ c.support, ν ∈ G.monomialSet n) ∧ G.monomialSumMap c = x := by
  obtain ⟨S, hS⟩ := G.finite_support x
  obtain ⟨c, hc, hcx⟩ := mem_repSubmodule_iff.1 (stageGrade_le_repSubmodule S n ⟨hx, hS⟩)
  exact ⟨c, fun ν hν ↦ ⟨(hc ν hν).1, (hc ν hν).2.1⟩, hcx⟩

/-- The monomials of degree `n` are linearly independent over the coefficient algebra. -/
public theorem eq_zero_of_monomialSumMap_eq_zero_of_mem_monomialSet
    (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable] (n : ℕ)
    (c : (G.Variable →₀ ℕ) →₀ P) (hc : ∀ ν ∈ c.support, ν ∈ G.monomialSet n)
    (h0 : G.monomialSumMap c = 0) : c = 0 := by
  classical
  refine eq_zero_of_monomialSumMap_eq_zero (c.support.biUnion fun ν ↦ ν.support) n c
    (fun ν hν ↦ ?_) h0
  exact ⟨(hc ν hν).1, (hc ν hν).2, fun x hx ↦ Finset.mem_biUnion.2 ⟨ν, hν, hx⟩⟩

/-- The coefficient families supported on the monomials of degree `n`. -/
public def monomialCoeff (G : GradedDividedPowerPolynomial Aᵢ γ ι) (n : ℕ) :
    Submodule R ((G.Variable →₀ ℕ) →₀ P) :=
  Finsupp.supported P R (G.monomialSet n)

/-- Expanding a coefficient family supported on the degree-`n` monomials into the degree-`n`
homogeneous piece. -/
public def gradeExpansion (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable]
    (n : ℕ) : ↥(G.monomialCoeff n) →ₗ[R] ↥(Aᵢ n) :=
  LinearMap.codRestrict (Aᵢ n) (G.monomialSumMap.comp (G.monomialCoeff n).subtype)
    fun c ↦ monomialSumMap_mem_grade fun _ hν ↦
      (Finsupp.mem_supported R (c : (G.Variable →₀ ℕ) →₀ P)).1 c.2 hν

/-- The expansion into a homogeneous piece is the ambient monomial expansion. -/
@[simp]
public theorem coe_gradeExpansion (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (n : ℕ) (c : ↥(G.monomialCoeff n)) :
    (G.gradeExpansion n c : A) = G.monomialSumMap (c : (G.Variable →₀ ℕ) →₀ P) := rfl

/-- The expansion map is bijective: the monomials of degree `n` form a basis of the degree-`n`
homogeneous piece over the coefficient algebra. -/
public theorem gradeExpansion_bijective (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (n : ℕ) : Function.Bijective (G.gradeExpansion n) := by
  refine ⟨fun c₁ c₂ h ↦ Subtype.ext (sub_eq_zero.1 ?_), fun x ↦ ?_⟩
  · refine G.eq_zero_of_monomialSumMap_eq_zero_of_mem_monomialSet n _ (fun ν hν ↦ ?_) ?_
    · rcases Finset.mem_union.1 (Finsupp.support_sub hν) with h' | h'
      · exact (Finsupp.mem_supported R _).1 c₁.2 h'
      · exact (Finsupp.mem_supported R _).1 c₂.2 h'
    · rw [map_sub, ← coe_gradeExpansion, ← coe_gradeExpansion, h, sub_self]
  · obtain ⟨c, hc, hcx⟩ := G.exists_monomialSumMap_eq n x.2
    exact ⟨⟨c, (Finsupp.mem_supported R c).2 fun ν hν ↦ hc ν hν⟩, Subtype.ext hcx⟩

/-- **The graded monomial basis.** The degree-`n` homogeneous piece of a graded divided power
polynomial algebra is free over its degree-zero coefficient algebra `P`, with basis the
divided power monomials of degree `n`. -/
public def gradeEquiv (G : GradedDividedPowerPolynomial Aᵢ γ ι) [LinearOrder G.Variable]
    (n : ℕ) : (G.Monomials n →₀ P) ≃ₗ[R] ↥(Aᵢ n) :=
  (Finsupp.supportedEquivFinsupp (M := P) (R := R) (G.monomialSet n)).symm.trans
    (LinearEquiv.ofBijective (G.gradeExpansion n) (G.gradeExpansion_bijective n))

/-- Each homogeneous piece is free over the ground ring as soon as the coefficient algebra is.
This is the `free` field of a Tate resolution, Tag 09PN. -/
@[stacks 09PN "freeness of the homogeneous pieces"]
public theorem free_grade (G : GradedDividedPowerPolynomial Aᵢ γ ι) [Module.Free R P] (n : ℕ) :
    Module.Free R ↥(Aᵢ n) := by
  let _ : LinearOrder G.Variable := IsWellOrder.linearOrder WellOrderingRel
  exact Module.Free.of_equiv (G.gradeEquiv n)

/-- Each homogeneous piece is module finite over the ground ring as soon as the coefficient
algebra is and there are only finitely many variables in each degree: there are then only
finitely many monomials of each degree. -/
@[stacks 09PN "finiteness of the homogeneous pieces"]
public theorem finite_grade (G : GradedDividedPowerPolynomial Aᵢ γ ι) [Module.Finite R P]
    [∀ i : ℕ, Finite (G.indices i)] (n : ℕ) : Module.Finite R ↥(Aᵢ n) := by
  let _ : LinearOrder G.Variable := IsWellOrder.linearOrder WellOrderingRel
  have : Finite (G.Monomials n) := G.finite_monomials n
  exact Module.Finite.equiv (G.gradeEquiv n)

end

end GradedDividedPowerPolynomial

end DividedPowers.TateResolution

end
