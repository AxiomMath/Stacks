module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedBasis
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDerivation

/-! # Finite generation of the cycles over the coefficient algebra

`StacksFrontier/RingTheory/DividedPowers/TateResolution/GradedBasis.lean` exhibits each homogeneous
piece of a graded divided power polynomial algebra as a free module on the divided power monomials
of that degree over the coefficient algebra `P`, and deduces
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.finite_grade`: the piece is module
finite over the **ground ring** `R` as soon as `P` is and the variables are finite in each degree.

That is not the finiteness Tate's construction needs. In Tag 09PN the coefficient algebra is a
polynomial ring `R[x₁, …, x_k]`, which is never module finite over `R`, so `finite_grade` does not
apply; what is true, and what the construction uses, is that each homogeneous piece is finitely
generated over `P` itself. This file proves that, and draws the consequence that makes the
*finiteness* half of Tag 09PN possible at all: over a Noetherian coefficient algebra the
degree-`n` cycles are finitely generated, so the variables of degree `n + 1` may be indexed by a
**finite** family of cycles rather than by all of them, which is what the existence half of
Tag 09PN does.

The last result of the file is the acyclicity statement that replaces the existence half's
"every cycle is prescribed". If the variables of degree `n + 1` kill a family `v` of degree-`n`
cycles, then every `P`-combination of the `v j` is a boundary — the boundary of the corresponding
combination of the variables, which is homogeneous of degree `n + 1` because the coefficients lie
in degree zero. Together with the finite generation above, a finite family of variables therefore
kills *all* the cycles of a degree.

## Main definitions

* `DividedPowers.TateResolution.coefficientGrade` — a homogeneous piece, as a module over a
  coefficient algebra sitting in degree zero.
* `DividedPowers.TateResolution.coefficientCycles` — the cycles of a homogeneous piece, as a
  module over that coefficient algebra.

## Main results

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade` — each
  homogeneous piece is finitely generated over the coefficient algebra when the variables are
  finite in each degree.
* `DividedPowers.TateResolution.fg_coefficientCycles` and
  `DividedPowers.TateResolution.exists_finite_spanning_cycles` — over a Noetherian coefficient
  algebra the degree-`n` cycles are finitely generated, exhibited as a finite family of cycles
  that every cycle is a combination of.
* `DividedPowers.TateResolution.exists_boundary_of_coefficient_combination` — a combination of
  the cycles killed by the variables of degree `n + 1` is the boundary of a homogeneous element
  of degree `n + 1`.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.coefficientGradeEquiv`,
  `DividedPowers.TateResolution.GradedDividedPowerPolynomial.free_coefficientGrade` and
  `DividedPowers.TateResolution.GradedDividedPowerPolynomial.finite_coefficientGrade` — the
  monomial basis over the coefficient algebra: each homogeneous piece is *free* over `P`, and
  module finite over `P` when the variables are finite in each degree.

### No `@[stacks 0BZ9]`

Tag 0BZ9 asks for the conclusion of Tag 09PN — a Tate resolution with finitely many generators
in each degree — under the hypothesis that `R → S` is a pseudo-coherent ring map rather than that
`R` is Noetherian and `R → S` of finite type, and its proof has two inputs: that `S` is a
pseudo-coherent module over the polynomial ring `R[x₁, …, x_n]` of the presentation, and that
each homogeneous piece `A(m)ᵢ` of a stage is a **finite free** `R[x₁, …, x_n]`-module. The second
input is what `free_coefficientGrade` and `finite_coefficientGrade` supply, which is why they are
here; `fg_coefficientGrade` gives only finite generation, and
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.free_grade` gives freeness over the
ground ring `R`, on infinitely many basis elements, so neither of those is the clause 0BZ9 uses.

Nothing in this file claims Tag 0BZ9. The tag's own statement — the existence of the degreewise
finite resolution under pseudo-coherence — is not proved anywhere in the tree; replacing
Noetherianness by pseudo-coherence in
`DividedPowers.TateResolution.hasFiniteSpanningCycles_finiteTateStage` additionally needs the
degree-`m` cycles of a stage to be finite over `P`, which no longer follows from "a submodule of
a finitely generated module" and has to come from Stacks 064Y and 064S applied to the augmented
complex of the stage.

## Implementation notes

The module structure over the coefficient algebra is taken as an instance argument `Algebra P A`
together with the hypothesis that its structure morphism is the coefficient morphism `ι` of the
presentation. It is not built from `ι` here: a `def` producing an `Algebra P A` would have to be
registered as an instance at every use site, and the one use site — the tower of Tag 09PN — has
the coefficient morphism in hand and can supply `ι.toRingHom.toAlgebra'` together with the
centrality of degree zero. Note that the coefficient algebra is required to be commutative, which
the polynomial ring of Tag 09PN is, while the graded algebra itself is only graded-commutative;
the image of `P` is central because it lies in degree zero.

Scalars are written on the left throughout, while the monomial expansion of `GradedBasis.lean`
puts its coefficients on the right. The two agree: a coefficient is homogeneous of degree zero,
so strict graded commutativity makes it commute with everything, with no sign.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0BZ9](https://stacks.math.columbia.edu/tag/0BZ9)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section Grade

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]

/-- **A homogeneous piece, as a module over a coefficient algebra sitting in degree zero.** The
degree-`n` piece is an `R`-submodule by definition; it is closed under multiplication by the
coefficient algebra because the coefficients are homogeneous of degree zero. -/
public def coefficientGrade (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    Submodule P A where
  carrier := Aᵢ n
  zero_mem' := Submodule.zero_mem _
  add_mem' hx hy := Submodule.add_mem _ hx hy
  smul_mem' p x hx := by
    rw [Algebra.smul_def]
    simpa using SetLike.GradedMul.mul_mem (h0 p) hx

/-- Membership in the degree-`n` piece over the coefficient algebra is homogeneity of degree
`n`. -/
@[simp]
public theorem mem_coefficientGrade {h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0} {n : ℕ} {x : A} :
    x ∈ coefficientGrade Aᵢ h0 n ↔ x ∈ Aᵢ n := Iff.rfl

end Grade

section Commute

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [IsStrictlyGradedComm Aᵢ]

/-- A coefficient commutes with every homogeneous element: it is itself homogeneous of degree
zero, so strict graded commutativity carries no sign. -/
public theorem coefficient_commute (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) {m : ℕ} (p : P)
    {x : A} (hx : x ∈ Aᵢ m) : x * algebraMap P A p = p • x := by
  rw [Algebra.smul_def]
  simpa using (IsStrictlyGradedComm.graded_comm (R := R) (h0 p) hx).symm

end Commute

section CoefficientAlgebra

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R P] [Algebra R A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]

/-- **An element of degree zero is central.** It commutes with a homogeneous element with no
sign, strict graded commutativity contributing `(-1) ^ 0`, and every element is a finite sum of
homogeneous ones. -/
public theorem commute_of_mem_grade_zero {a : A} (ha : a ∈ Aᵢ 0) (x : A) : a * x = x * a := by
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Aᵢ x
  rw [hs, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simpa using IsStrictlyGradedComm.graded_comm (R := R) ha (gradedPart_mem Aᵢ x m)

/-- **A coefficient morphism landing in degree zero makes its target an algebra over its
source**, the image being central. This is the algebra structure under which the homogeneous
pieces are modules over the coefficient algebra; it is a `def` rather than an instance because it
depends on the hypothesis `h0`, and is meant to be used with `letI`. -/
@[instance_reducible]
public def coefficientAlgebra (ι : P →ₐ[R] A) (h0 : ∀ p : P, ι p ∈ Aᵢ 0) : Algebra P A :=
  ι.toRingHom.toAlgebra' fun p x => commute_of_mem_grade_zero Aᵢ (h0 p) x

/-- The structure morphism of that algebra structure is the coefficient morphism, so the
hypothesis `hι` of the results below is discharged by `rfl`. -/
public theorem algebraMap_coefficientAlgebra (ι : P →ₐ[R] A) (h0 : ∀ p : P, ι p ∈ Aᵢ 0) :
    @algebraMap P A _ _ (coefficientAlgebra Aᵢ ι h0) = ι.toRingHom := rfl

end CoefficientAlgebra

section Differential

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d]

/-- The differential is linear over a coefficient algebra sitting in degree zero: the Leibniz rule
applied to a coefficient has one term killed by the differential's vanishing in degree zero, and
the sign of the surviving term is `(-1) ^ 0`. -/
public theorem map_coefficient_smul (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) {m : ℕ} (p : P)
    {x : A} (hx : x ∈ Aᵢ m) : d (p • x) = p • d x := by
  rw [Algebra.smul_def, Algebra.smul_def,
    IsDifferentialGradedAlgebra.leibniz (𝒜 := Aᵢ) (d := d) (h0 p) hx,
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := Aᵢ) (d := d) (h0 p)]
  simp

/-- **The degree-`n` cycles, as a module over a coefficient algebra sitting in degree zero.** -/
public def coefficientCycles (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    Submodule P A where
  carrier := {x : A | x ∈ Aᵢ n ∧ d x = 0}
  zero_mem' := ⟨Submodule.zero_mem _, map_zero d⟩
  add_mem' hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, by rw [map_add, hx.2, hy.2, add_zero]⟩
  smul_mem' p x hx :=
    ⟨(coefficientGrade Aᵢ h0 n).smul_mem p hx.1, by
      rw [map_coefficient_smul Aᵢ d h0 p hx.1, hx.2, smul_zero]⟩

/-- Membership in the degree-`n` cycles over the coefficient algebra. -/
@[simp]
public theorem mem_coefficientCycles {h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0} {n : ℕ} {x : A} :
    x ∈ coefficientCycles Aᵢ d h0 n ↔ x ∈ Aᵢ n ∧ d x = 0 := Iff.rfl

/-- The cycles of a degree sit inside that degree. -/
public theorem coefficientCycles_le_coefficientGrade
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    coefficientCycles Aᵢ d h0 n ≤ coefficientGrade Aᵢ h0 n :=
  fun _ hx => hx.1

/-- **A combination of the cycles killed by the variables of degree `n + 1` is a boundary.** The
boundary of the corresponding combination of the variables is it, by linearity of the differential
over the coefficients, and that combination is homogeneous of degree `n + 1` because the
coefficients are homogeneous of degree zero.

So a family of variables whose prescribed cycles *span* the cycles of a degree kills all of them.
This is what makes a degreewise finite Tate tower acyclic; the existence half of Tag 09PN instead
prescribes every cycle individually, which costs it degreewise finiteness. -/
@[stacks 09PN "a spanning family of variables kills every cycle of its degree"]
public theorem exists_boundary_of_coefficient_combination
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) {J : Type*} (v T : J → A) (n : ℕ)
    (hT : ∀ j : J, T j ∈ Aᵢ (n + 1)) (hdT : ∀ j : J, d (T j) = v j)
    (s : Finset J) (c : J → P) :
    ∃ b : A, b ∈ Aᵢ (n + 1) ∧ d b = ∑ j ∈ s, c j • v j := by
  refine ⟨∑ j ∈ s, c j • T j,
    Submodule.sum_mem _ fun j _ => (coefficientGrade Aᵢ h0 (n + 1)).smul_mem (c j) (hT j), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_coefficient_smul Aᵢ d h0 (c j) (hT j), hdT j]

end Differential

section Noetherian

variable {P : Type v} {A : Type w} [CommRing P] [Ring A] [Algebra P A]

/-- A submodule of a finitely generated module over a Noetherian ring is finitely generated. -/
public theorem fg_of_le_of_fg [IsNoetherianRing P] {M N : Submodule P A} (hM : M.FG)
    (hNM : N ≤ M) : N.FG :=
  hM.of_le hNM

end Noetherian

section Presentation

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R P] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}

namespace GradedDividedPowerPolynomial

/-- A monomial of degree `n` times a coefficient on the right is the coefficient scalar multiple. -/
private theorem monomial_mul_eq_smul (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) {n : ℕ} {ν : G.Variable →₀ ℕ}
    (hν : G.monomial ν ∈ Aᵢ n) (p : P) : G.monomial ν * ι p = p • G.monomial ν := by
  rw [← hι, coefficient_commute Aᵢ h0 p hν]

/-- **Each homogeneous piece is finitely generated over the coefficient algebra** as soon as the
variables are finite in each degree: there are then only finitely many divided power monomials of
each degree, and they span that degree over the coefficients.

This is the coefficient-algebra analogue of
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.finite_grade`, and it is the form the
finiteness half of Tag 09PN needs: there the coefficient algebra is a polynomial ring over the
ground ring, hence not module finite over it, so `finite_grade` says nothing. -/
@[stacks 09PN "finite generation of the homogeneous pieces over the coefficients"]
public theorem fg_coefficientGrade (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [∀ i : ℕ, Finite (G.indices i)] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    (coefficientGrade Aᵢ h0 n).FG := by
  classical
  let _ : LinearOrder G.Variable := IsWellOrder.linearOrder WellOrderingRel
  have hmono : ∀ ν ∈ G.monomialSet n, G.monomial ν ∈ Aᵢ n := fun ν hν =>
    hν.2 ▸ monomial_mem_grade (G := G) hν.1
  refine Submodule.fg_def.2 ⟨G.monomial '' G.monomialSet n,
    (Set.finite_coe_iff.1 (G.finite_monomials n)).image _, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
  · rintro x ⟨ν, hν, rfl⟩
    exact hmono ν hν
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := G.exists_monomialSumMap_eq n hx
    rw [← hcx, monomialSumMap_apply]
    refine Submodule.sum_mem _ fun ν hν => ?_
    change G.monomial ν * ι (c ν) ∈ Submodule.span P (G.monomial '' G.monomialSet n)
    rw [G.monomial_mul_eq_smul Aᵢ h0 hι (hmono ν (hc ν hν))]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_image_of_mem _ (hc ν hν)))

end GradedDividedPowerPolynomial

variable (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra Aᵢ d]

/-- **The degree-`n` cycles are finitely generated over the coefficient algebra** when that
algebra is Noetherian and the variables are finite in each degree: the cycles are a submodule of
the degree-`n` piece, which is finitely generated. -/
public theorem fg_coefficientCycles (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [∀ i : ℕ, Finite (G.indices i)] [IsNoetherianRing P]
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    (coefficientCycles Aᵢ d h0 n).FG :=
  fg_of_le_of_fg (G.fg_coefficientGrade Aᵢ h0 hι n)
    (coefficientCycles_le_coefficientGrade Aᵢ d h0 n)

/-- **A finite family of degree-`n` cycles that every degree-`n` cycle is a combination of.**

This is what lets the variables of degree `n + 1` of Tate's tower be finite in number: the
existence half of Tag 09PN adjoins one variable for *every* cycle of degree `n`, which makes
acyclicity free of a homology computation but makes the resolution infinite in each degree. Over a
Noetherian coefficient algebra a finite family suffices, by
`DividedPowers.TateResolution.exists_boundary_of_coefficient_combination`. -/
@[stacks 09PN "a finite generating family of the cycles of a degree"]
public theorem exists_finite_spanning_cycles (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [∀ i : ℕ, Finite (G.indices i)] [IsNoetherianRing P]
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    ∃ s : Finset A, (∀ y ∈ s, y ∈ Aᵢ n ∧ d y = 0) ∧
      ∀ x : A, x ∈ Aᵢ n → d x = 0 → ∃ c : A → P, ∑ y ∈ s, c y • y = x := by
  obtain ⟨s, hs⟩ := fg_coefficientCycles Aᵢ d G h0 hι n
  refine ⟨s, fun y hy => hs.le (Submodule.subset_span hy), fun x hx hdx => ?_⟩
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1
    (hs.ge (show x ∈ coefficientCycles Aᵢ d h0 n from ⟨hx, hdx⟩))
  exact ⟨c, hc⟩

end Presentation

section CoefficientBasis

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R P] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}

namespace GradedDividedPowerPolynomial

/-- A monomial of degree `n`, as an element of the degree-`n` piece viewed as a module over the
coefficient algebra. -/
public def coefficientMonomial (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ)
    (ν : G.Monomials n) : ↥(coefficientGrade Aᵢ h0 n) :=
  ⟨G.monomial ν, by
    have h := monomial_mem_grade (G := G) (mem_monomialSet.1 ν.2).1
    rwa [(mem_monomialSet.1 ν.2).2] at h⟩

/-- The underlying element of a monomial of the degree-`n` piece is that monomial. -/
@[simp]
public theorem coe_coefficientMonomial (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ)
    (ν : G.Monomials n) : (G.coefficientMonomial Aᵢ h0 n ν : A) = G.monomial ν := rfl

/-- **The expansion of a coefficient family against the degree-`n` monomials**, as a map of
modules over the coefficient algebra. This is the monomial expansion of `GradedBasis.lean` with
its coefficients moved to the left, where they are scalars. -/
public noncomputable def coefficientExpansion (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (n : ℕ) :
    (G.Monomials n →₀ P) →ₗ[P] ↥(coefficientGrade Aᵢ h0 n) :=
  Finsupp.lsum P fun ν => LinearMap.toSpanSingleton P _ (G.coefficientMonomial Aᵢ h0 n ν)

omit [Algebra P A] in
/-- Every exponent vector in the support of a family pushed forward from the degree-`n` monomials
is the exponent vector of a degree-`n` monomial. -/
public theorem mem_monomialSet_of_mem_support_mapDomain
    {G : GradedDividedPowerPolynomial Aᵢ γ ι} {n : ℕ} (c : G.Monomials n →₀ P)
    {ν : G.Variable →₀ ℕ}
    (hν : ν ∈ (Finsupp.mapDomain (Subtype.val : G.Monomials n → G.Variable →₀ ℕ) c).support) :
    ν ∈ G.monomialSet n := by
  classical
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hν)
  exact μ.2

omit [Algebra P A] in
/-- **A family of coefficients on the degree-`n` monomials, pushed forward and restricted back,
is itself again.** The pushforward is zero away from the degree-`n` monomials, and a family
supported on them loses nothing under restriction. -/
public theorem mapDomain_subtypeDomain_monomialSet
    {G : GradedDividedPowerPolynomial Aᵢ γ ι} {n : ℕ} (c : (G.Variable →₀ ℕ) →₀ P)
    (hc : ∀ ν ∈ c.support, ν ∈ G.monomialSet n) :
    Finsupp.mapDomain (Subtype.val : G.Monomials n → G.Variable →₀ ℕ)
      (Finsupp.subtypeDomain (· ∈ G.monomialSet n) c : G.Monomials n →₀ P) = c := by
  classical
  refine Finsupp.ext fun ν => ?_
  by_cases hν : ν ∈ G.monomialSet n
  · have h := Finsupp.mapDomain_apply_of_injective (M := P)
      (f := (Subtype.val : G.Monomials n → G.Variable →₀ ℕ)) Subtype.val_injective
      (Finsupp.subtypeDomain (· ∈ G.monomialSet n) c : G.Monomials n →₀ P) ⟨ν, hν⟩
    exact h.trans (Finsupp.subtypeDomain_apply (p := (· ∈ G.monomialSet n)) (a := ⟨ν, hν⟩))
  · have hrange : ν ∉ Set.range (Subtype.val : G.Monomials n → G.Variable →₀ ℕ) := by
      rintro ⟨μ, rfl⟩
      exact hν μ.2
    rw [Finsupp.mapDomain_of_notMem_range _ _ hrange]
    exact (Finsupp.notMem_support_iff.1 fun hmem => hν (hc ν hmem)).symm

/-- **The coefficient expansion is the monomial expansion.** Moving a coefficient from the right
of its monomial to the left changes nothing: a coefficient is homogeneous of degree zero, so it
commutes with the monomial with no Koszul sign. -/
public theorem coe_coefficientExpansion (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) (c : G.Monomials n →₀ P) :
    (G.coefficientExpansion Aᵢ h0 n c : A) =
      G.monomialSumMap (Finsupp.mapDomain (Subtype.val : G.Monomials n → G.Variable →₀ ℕ) c) := by
  classical
  have hsum : G.monomialSumMap
      (Finsupp.mapDomain (Subtype.val : G.Monomials n → G.Variable →₀ ℕ) c) =
      c.sum fun ν p => G.monomial (ν : G.Variable →₀ ℕ) * ι p := by
    rw [monomialSumMap_apply]
    exact Finsupp.sum_mapDomain_index_inj Subtype.val_injective
  rw [hsum]
  simp only [coefficientExpansion, Finsupp.lsum_apply, Finsupp.sum,
    AddSubmonoidClass.coe_finsetSum, LinearMap.toSpanSingleton_apply, SetLike.val_smul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hmem : G.monomial (ν : G.Variable →₀ ℕ) ∈ Aᵢ n :=
    (G.coefficientMonomial Aᵢ h0 n ν).2
  rw [coe_coefficientMonomial, G.monomial_mul_eq_smul Aᵢ h0 hι hmem]

/-- **The degree-`n` monomials are a basis of the degree-`n` piece over the coefficient
algebra**: the coefficient expansion is bijective. Injectivity is the linear independence of the
monomials and surjectivity is that they span, both from `GradedBasis.lean`. -/
public theorem coefficientExpansion_bijective (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    Function.Bijective (G.coefficientExpansion Aᵢ h0 n) := by
  classical
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hzero : G.monomialSumMap
        (Finsupp.mapDomain (Subtype.val : G.Monomials n → G.Variable →₀ ℕ) c) = 0 := by
      rw [← G.coe_coefficientExpansion Aᵢ h0 hι n c, hc, ZeroMemClass.coe_zero]
    have h := G.eq_zero_of_monomialSumMap_eq_zero_of_mem_monomialSet n _
      (fun ν hν => mem_monomialSet_of_mem_support_mapDomain Aᵢ c hν) hzero
    exact Finsupp.mapDomain_injective (f := (Subtype.val : G.Monomials n → G.Variable →₀ ℕ))
      Subtype.val_injective (h.trans (Finsupp.mapDomain_zero
        (f := (Subtype.val : G.Monomials n → G.Variable →₀ ℕ)) (M := P)).symm)
  · intro y
    obtain ⟨c, hc, hcy⟩ := G.exists_monomialSumMap_eq n y.2
    refine ⟨(Finsupp.subtypeDomain (· ∈ G.monomialSet n) c : G.Monomials n →₀ P),
      Subtype.ext ?_⟩
    refine (G.coe_coefficientExpansion Aᵢ h0 hι n _).trans ?_
    rw [mapDomain_subtypeDomain_monomialSet Aᵢ (G := G) (n := n) c hc]
    exact hcy

/-- **The monomial basis over the coefficient algebra.** The degree-`n` homogeneous piece of a
graded divided power polynomial algebra is free over its degree-zero coefficient algebra `P`,
with basis the divided power monomials of degree `n`.

This is the coefficient-algebra form of
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.gradeEquiv`, which states the same
basis `R`-linearly. -/
public noncomputable def coefficientGradeEquiv (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [LinearOrder G.Variable] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    (G.Monomials n →₀ P) ≃ₗ[P] ↥(coefficientGrade Aᵢ h0 n) :=
  LinearEquiv.ofBijective (G.coefficientExpansion Aᵢ h0 n)
    (G.coefficientExpansion_bijective Aᵢ h0 hι n)

/-- **Each homogeneous piece is free over the coefficient algebra**, on the divided power
monomials of its degree.

This is the companion of
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade`: that gives
finite generation over `P`, this gives freeness over `P`. Neither follows from
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.free_grade`, which is freeness over
the ground ring `R` on infinitely many basis elements. -/
public theorem free_coefficientGrade (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    Module.Free P ↥(coefficientGrade Aᵢ h0 n) := by
  let _ : LinearOrder G.Variable := IsWellOrder.linearOrder WellOrderingRel
  exact Module.Free.of_equiv (G.coefficientGradeEquiv Aᵢ h0 hι n)

/-- **Each homogeneous piece is module finite over the coefficient algebra** when there are only
finitely many variables in each degree: there are then only finitely many monomials of each
degree. This is
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.fg_coefficientGrade` in the
`Module.Finite` spelling, which is the one the finiteness criteria for complexes ask for. -/
public theorem finite_coefficientGrade (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    [∀ i : ℕ, Finite (G.indices i)] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)
    (hι : ∀ p : P, algebraMap P A p = ι p) (n : ℕ) :
    Module.Finite P ↥(coefficientGrade Aᵢ h0 n) :=
  Module.Finite.iff_fg.2 (G.fg_coefficientGrade Aᵢ h0 hι n)

end GradedDividedPowerPolynomial

end CoefficientBasis

end DividedPowers.TateResolution

end
