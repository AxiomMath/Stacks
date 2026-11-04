module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.MixedDegreePolynomial

/-!
# Existence of the graded divided-power polynomial algebra on prescribed variables

Let `R` be a commutative ring, let `P` be a commutative `R`-algebra and let `indices n` be, for
each `n : ℕ`, a set of names for the variables to be adjoined in degree `n + 1`. This file
constructs a strictly graded-commutative nonnegatively graded `R`-algebra `A` with divided
powers on its positive even part, together with an injective algebra map `P → A` onto its
degree-zero part, which is the graded divided-power polynomial algebra over `P` on one
homogeneous variable of degree `n + 1` for each element of `indices n`: an exterior variable in
odd degree and a divided-power variable in even degree, as in Tags 09PH and 09PI.

This is the object the construction of a Tate resolution rests on — Tag 09PN's "`A` is a graded
divided power polynomial algebra over `R`", built out of `A_0 = P` by "successively adjoining a
set of variables `T` in each degree `> 0`". The mapping property of such an algebra is already
available as
`DividedPowers.TateResolution.existsUnique_restrictedStageGradedDividedPowerPolynomial_map`;
what is proved here is that one exists over any prescribed degree-zero algebra with any
prescribed variables.

## Main results

* `DividedPowers.TateResolution.exists_gradedDividedPowerPolynomial` — the existence statement.
  The algebra, its grading, its strict graded commutativity, its divided powers, the coefficient
  map and the `RestrictedStageGradedDividedPowerPolynomial` structure all come out of the
  existential, and the structure's variable index types are literally the prescribed ones.

## Implementation notes

The whole content is supplied by the set-variable construction of Tag 0F4I in the form in which
`SetVariableExtension.Construction` proves it, namely with the degree of each variable given by
a function `deg : J → ℕ` rather than by a constant. Taking `J := Σ n : ℕ, indices n` and
`deg j := j.1 + 1` adjoins all the variables of all the degrees in one step, so no colimit over
degrees has to be formed here and the identification of each successor stage with a one-variable
extension — the `successor` field, which is what the mapping property is proved from — is
exactly the one that construction already provides. Stacks builds the same algebra as the
colimit of the tower `A(0) → A(1) → ⋯`, each step adjoining the variables of one degree; the two
descriptions agree because adjoining a set of variables is the directed union of its finite
stages either way, and a finite stage involves finitely many degrees.

The degree-zero algebra `P` enters as the graded algebra with divided powers concentrated in
degree `0` of `DegreeZeroCore`, namely `degreeZeroGrade` with `degreeZeroDividedPowers`,
which is Tag 09PN's "`A(0)_0 = A(0)` and `A(0)_d = 0` for `d ≠ 0`. Thus `d = 0` and `γ_n`,
`n > 0`, is zero as well." Nothing here depends on which of the two possible encodings of that
grading is used — it is an input to Tag 0F4I's construction and appears in no statement below
— so the instances `DegreeZeroCore` already provides are taken rather than a second copy.

The index types must live in the universe `max u v w` of the constructed algebra, because the
`indices` field of `RestrictedStageGradedDividedPowerPolynomial` does: the variables are
elements of the algebra, so nothing is lost, and in the intended application the variables of
degree `n + 1` are named by elements of the algebra itself. Universe arguments may therefore
have to be supplied explicitly at a call site, since `max u v w` does not determine `w`.

The `successor` field of `RestrictedStageGradedDividedPowerPolynomial` quantifies over a finite
set `U` whose members are `j` and the members of `S`, rather than over `insert j S`, so that
the structure needs no `DecidableEq` on the index type; the two are reconciled here by
`Finset.ext`, with the classical instance that Tag 0F4I's statement uses.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- A graded divided-power polynomial algebra exists over any prescribed commutative degree-zero
algebra `P`, with one homogeneous variable of degree `n + 1` for each element of `indices n`.
Its mapping property is `existsUnique_restrictedStageGradedDividedPowerPolynomial_map`. -/
@[stacks 09PN "graded divided power polynomial algebra over a prescribed degree-zero algebra"]
public theorem exists_gradedDividedPowerPolynomial {R : Type u} [CommRing R] (P : Type v)
    [CommRing P] [Algebra R P] (indices : ℕ → Type (max u v w)) :
    ∃ (A : Type (max u v w)) (ringA : Ring A),
      letI : Ring A := ringA
      ∃ algebraA : Algebra R A,
        letI : Algebra R A := algebraA
        ∃ (Aᵢ : ℕ → Submodule R A) (gradedA : GradedAlgebra Aᵢ),
          letI : GradedAlgebra Aᵢ := gradedA
          ∃ strictA : IsStrictlyGradedComm Aᵢ,
            letI : IsStrictlyGradedComm Aᵢ := strictA
            ∃ (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
              (h : RestrictedStageGradedDividedPowerPolynomial Aᵢ γ ι), h.indices = indices := by
  let : DecidableEq (Σ n : ℕ, indices n) := Classical.decEq _
  obtain ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ι, T, hinj, hgrade, -, hTmem,
      hsupport, hsucc, -⟩ :=
    exists_setVariableDividedPowerExtension.{u, v, max u v w, 0} (degreeZeroGrade R P)
      (degreeZeroDividedPowers R P) (Σ n : ℕ, indices n) (fun j => j.1 + 1)
      (fun j => Nat.succ_pos j.1)
  let : Ring C := ringC
  let : Algebra R C := algebraC
  let : GradedAlgebra Cᵢ := gradedC
  let : IsStrictlyGradedComm Cᵢ := strictC
  exact ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ι,
    { indices := indices
      generator := T
      generator_mem := hTmem
      coefficient_mem := fun p => hgrade 0 p (mem_degreeZeroGrade_zero R P p)
      coefficient_injective := hinj
      finite_support := hsupport
      successor := by
        intro S U j hjS hU
        have hUeq : U = insert j S :=
          Finset.ext fun k => (hU k).trans Finset.mem_insert.symm
        subst hUeq
        exact hsucc S j hjS }, rfl⟩

/-- The graded divided-power polynomial algebra over `P` on one homogeneous variable of degree
`n + 1` for each element of `indices n`, with its mapping property: an algebra map on `P`
landing in degree zero together with a homogeneous value of the right degree for each variable
extends uniquely to a map of graded algebras with divided powers. The target may live in a
universe independent of `P` and of the variables. -/
public theorem exists_gradedDividedPowerPolynomial_universalProperty {R : Type u} [CommRing R]
    (P : Type v) [CommRing P] [Algebra R P] (indices : ℕ → Type (max u v w)) :
    ∃ (A : Type (max u v w)) (ringA : Ring A),
      letI : Ring A := ringA
      ∃ algebraA : Algebra R A,
        letI : Algebra R A := algebraA
        ∃ (Aᵢ : ℕ → Submodule R A) (gradedA : GradedAlgebra Aᵢ),
          letI : GradedAlgebra Aᵢ := gradedA
          ∃ strictA : IsStrictlyGradedComm Aᵢ,
            letI : IsStrictlyGradedComm Aᵢ := strictA
            ∃ (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
              (generator : (Σ n : ℕ, indices n) → A),
              Function.Injective ι ∧
              (∀ p : P, ι p ∈ Aᵢ 0) ∧
              (∀ j : Σ n : ℕ, indices n, generator j ∈ Aᵢ (j.1 + 1)) ∧
              ∀ {D : Type z} [Ring D] [Algebra R D] (Dᵢ : ℕ → Submodule R D)
                [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ] (δ : DividedPowerStructure Dᵢ)
                (f : P →ₐ[R] D), (∀ p : P, f p ∈ Dᵢ 0) →
                ∀ t : (Σ n : ℕ, indices n) → D, (∀ j, t j ∈ Dᵢ (j.1 + 1)) →
                ∃! g : A →ₐ[R] D,
                  (∀ p : P, g (ι p) = f p) ∧
                  (∀ j : Σ n : ℕ, indices n, g (generator j) = t j) ∧
                  (∀ (n : ℕ) (a : A), a ∈ Aᵢ n → g a ∈ Dᵢ n) ∧
                  (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
                    g (γ.dpow n a) = δ.dpow n (g a)) := by
  obtain ⟨A, ringA, algebraA, Aᵢ, gradedA, strictA, γ, ι, h, hind⟩ :=
    exists_gradedDividedPowerPolynomial.{u, v, w} (R := R) P indices
  let : Ring A := ringA
  let : Algebra R A := algebraA
  let : GradedAlgebra Aᵢ := gradedA
  let : IsStrictlyGradedComm Aᵢ := strictA
  subst hind
  refine ⟨A, ringA, algebraA, Aᵢ, gradedA, strictA, γ, ι, h.generator,
    h.coefficient_injective, h.coefficient_mem, h.generator_mem, ?_⟩
  intro D ringD algebraD Dᵢ gradedD strictD δ f hf t ht
  exact existsUnique_restrictedStageGradedDividedPowerPolynomial_map γ ι h δ f hf t ht

end DividedPowers.TateResolution

end
