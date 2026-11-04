module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradeOne
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.NoetherianCycles

/-! # The degree-one piece over the coefficient algebra

The variables of a graded divided power polynomial algebra sit in positive degree and a product
of two of them, or a divided power of one of them, already has degree two, so the degree-one piece
is spanned by the variables of degree one — with coefficients, which is to say over the
coefficient algebra `P` sitting in degree zero.

`DividedPowers.TateResolution.grade_one_le_span` says this with the coefficients written out: the
degree-one piece lies in the `R`-span of the coefficients together with their multiples of the
degree-one variables. That span also contains the coefficients themselves, which are of degree
zero, so it is not yet a statement about the degree-one piece as a `P`-module. Splitting an
element of degree one along that span and comparing homogeneous components removes the degree-zero
summand, and what is left is a `P`-combination of the degree-one variables alone.

The consequence used downstream is the one about the differential: the boundary of an element of
degree one is a `P`-combination of the boundaries of the degree-one variables. In Tate's tower
those boundaries are the prescribed generators of the kernel of the presentation, so this is what
identifies the degree-zero boundaries with that kernel.

## Main definitions

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.degreeOneVariableSet` — the variables
  of degree one.

## Main results

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.coefficientGrade_one_le_span` — the
  degree-one piece is spanned over the coefficient algebra by the degree-one variables.
* `DividedPowers.TateResolution.GradedDividedPowerPolynomial.differential_mem_span_image` — the
  boundary of an element of degree one is a combination, with coefficients in the coefficient
  algebra, of the boundaries of the degree-one variables.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0BZ9](https://stacks.math.columbia.edu/tag/0BZ9)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

namespace GradedDividedPowerPolynomial

section CoefficientGradeOne

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Algebra R P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ} {ι : P →ₐ[R] A}

/-- **The variables of degree one** of a graded divided power polynomial algebra: those indexed in
the family of index `0`, whose prescribed degree is `0 + 1`. -/
public def degreeOneVariableSet (G : GradedDividedPowerPolynomial Aᵢ γ ι) : Set A :=
  {x : A | ∃ j : Σ n : ℕ, G.indices n, j.1 = 0 ∧ x = G.generator j}

omit [Algebra P A] in
/-- A variable indexed in the family of index `0` is one of the degree-one variables. -/
public theorem generator_mem_degreeOneVariableSet (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (j : Σ n : ℕ, G.indices n) (hj : j.1 = 0) :
    G.generator j ∈ G.degreeOneVariableSet Aᵢ := ⟨j, hj, rfl⟩

/-- The degree-one variables span a submodule of the degree-one piece: each of them is homogeneous
of degree one, and the degree-one piece is stable under the coefficients. -/
public theorem span_degreeOneVariableSet_le (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) :
    Submodule.span P (G.degreeOneVariableSet Aᵢ) ≤ coefficientGrade Aᵢ h0 1 := by
  rw [Submodule.span_le]
  rintro y ⟨j, hj, rfl⟩
  have hmem := G.generator_mem j
  rw [hj] at hmem
  exact hmem

/-- **The degree-one piece is spanned over the coefficient algebra by the degree-one variables.**

`DividedPowers.TateResolution.grade_one_le_span` writes an element of degree one as an `R`-sum of
coefficients and of coefficient multiples of the degree-one variables. The first group lies in
degree zero and the second in degree one, so the degree-zero summand of such an expression of a
homogeneous element of degree one vanishes. -/
public theorem coefficientGrade_one_le_span (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (hι : ∀ p : P, algebraMap P A p = ι p) :
    coefficientGrade Aᵢ h0 1 ≤ Submodule.span P (G.degreeOneVariableSet Aᵢ) := by
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r => by
    rw [hι]; exact (ι.commutes r).symm
  intro x hx
  have hx1 : x ∈ Aᵢ 1 := hx
  have hsub : Submodule.span R (gradeOneGenerators G) ≤
      LinearMap.range ι.toLinearMap ⊔
        (Submodule.span P (G.degreeOneVariableSet Aᵢ)).restrictScalars R := by
    rw [Submodule.span_le]
    rintro y (⟨p, rfl⟩ | ⟨p, j, hj, rfl⟩)
    · exact Submodule.mem_sup_left ⟨p, rfl⟩
    · refine Submodule.mem_sup_right ?_
      have hsmul : ι p * G.generator j = p • G.generator j := by
        rw [Algebra.smul_def, hι]
      rw [hsmul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (G.generator_mem_degreeOneVariableSet Aᵢ j hj))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hsub (grade_one_le_span G hx1))
  obtain ⟨p, hp⟩ := hy
  have hy0 : y ∈ Aᵢ 0 := hp ▸ G.coefficient_mem p
  have hz1 : z ∈ Aᵢ 1 := G.span_degreeOneVariableSet_le Aᵢ h0 hz
  have hy1 : y ∈ Aᵢ 1 := by
    have hsub' : y = x - z := by rw [← hyz]; exact (add_sub_cancel_right y z).symm
    rw [hsub']
    exact Submodule.sub_mem _ hx1 hz1
  have hyzero : y = 0 := by
    by_contra hne
    exact absurd (DirectSum.degree_eq_of_mem_mem Aᵢ hy0 hy1 hne) (by omega)
  rw [← hyz, hyzero, zero_add]
  exact hz

/-- **The boundary of an element of degree one is a combination of the boundaries of the
degree-one variables**, with coefficients in the coefficient algebra.

The element is such a combination of the degree-one variables themselves, by
`DividedPowers.TateResolution.GradedDividedPowerPolynomial.coefficientGrade_one_le_span`, and the
differential is linear over the coefficients on homogeneous elements. -/
public theorem differential_mem_span_image (G : GradedDividedPowerPolynomial Aᵢ γ ι)
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra Aᵢ d]
    (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0) (hι : ∀ p : P, algebraMap P A p = ι p)
    {x : A} (hx : x ∈ Aᵢ 1) :
    d x ∈ Submodule.span P (d '' G.degreeOneVariableSet Aᵢ) := by
  have key : ∀ y ∈ Submodule.span P (G.degreeOneVariableSet Aᵢ),
      y ∈ Aᵢ 1 ∧ d y ∈ Submodule.span P (d '' G.degreeOneVariableSet Aᵢ) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        exact ⟨G.span_degreeOneVariableSet_le Aᵢ h0 (Submodule.subset_span hz),
          Submodule.subset_span ⟨z, hz, rfl⟩⟩
    | zero => exact ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | add z₁ z₂ _ _ ih₁ ih₂ =>
        exact ⟨Submodule.add_mem _ ih₁.1 ih₂.1, by
          rw [map_add]; exact Submodule.add_mem _ ih₁.2 ih₂.2⟩
    | smul p z _ ih =>
        refine ⟨(coefficientGrade Aᵢ h0 1).smul_mem p ih.1, ?_⟩
        rw [map_coefficient_smul Aᵢ d h0 p ih.1]
        exact Submodule.smul_mem _ _ ih.2
  exact (key x (G.coefficientGrade_one_le_span Aᵢ h0 hι hx)).2

end CoefficientGradeOne

end GradedDividedPowerPolynomial

end DividedPowers.TateResolution

end
