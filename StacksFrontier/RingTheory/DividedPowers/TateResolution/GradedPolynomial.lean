module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-!
# Graded divided power polynomial algebras

A *graded divided power polynomial algebra* over a coefficient algebra `P` is a strictly
graded-commutative algebra `A` with divided powers, presented as the directed union of the finite
stages obtained by successively adjoining homogeneous variables of positive degree. Adjoining a
variable of odd degree gives the odd variable extension of Tag 09PH; adjoining one of even degree
gives the even variable algebra of Tag 09PI. This is condition (4) of Tag 09PN.

## Main definitions

* `DividedPowers.TateResolution.GradedDividedPowerPolynomial`: the presentation of `A` as a
  directed union of finite odd and even variable extensions of `P`.

## Implementation notes

The `successor` field is stated by exhibiting an isomorphism of the next finite stage with the
relevant one-variable extension, together with the compatibility of the grading and of the
divided powers under that isomorphism.

The `R`-algebra structure `aS` on a finite stage is supplied existentially by the field rather
than restricted from `A`, because the stage is a `Subring` and so carries no `R`-algebra
structure of its own. The field's first conjunct says that `algebraMap R (finiteVariableStage …)`
is the ambient `algebraMap R A` with its values corestricted to the stage.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

open EvenVariableAlgebra in
/-- A graded divided-power polynomial algebra over `P`, obtained as the directed union of finite
successive odd exterior and even divided-power variable extensions. -/
public structure GradedDividedPowerPolynomial
    {R : Type u} {P : Type v} {A : Type w}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (γ : DividedPowerStructure Aᵢ)
    (ι : P →ₐ[R] A) where
  /-- Indices of the new variables in degree `n + 1`. -/
  indices : ℕ → Type w
  /-- The homogeneous new variables, indexed together with their degrees. -/
  generator : (Σ n : ℕ, indices n) → A
  /-- Each new variable is homogeneous of its prescribed degree. -/
  generator_mem : ∀ j, generator j ∈ Aᵢ (j.1 + 1)
  /-- The coefficient algebra lands in degree zero. -/
  coefficient_mem : ∀ p : P, ι p ∈ Aᵢ 0
  /-- The structure map `ι` is injective. -/
  coefficient_injective : Function.Injective ι
  /-- The finite variable stages cover the algebra. -/
  finite_support : ∀ x : A, ∃ S : Finset (Σ n : ℕ, indices n),
    x ∈ finiteVariableStage γ ι generator S
  /-- Adjoining one variable to a finite stage gives the odd or even divided-power variable
  extension of the stage according to the parity of its degree, compatibly with gradings and
  divided powers; the stage's `R`-algebra structure is the restriction of the ambient one. -/
  successor : ∀ (S : Finset (Σ n : ℕ, indices n))
      (j : Σ n : ℕ, indices n), j ∉ S →
      let d := j.1 + 1
      letI : DecidableEq (Σ n : ℕ, indices n) := Classical.decEq _
      ∃ (aS : Algebra R (finiteVariableStage γ ι generator S)),
        letI : Algebra R (finiteVariableStage γ ι generator S) := aS
        (∀ r : R,
          (algebraMap R (finiteVariableStage γ ι generator S) r : A) = algebraMap R A r) ∧
        ∃ (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι generator S))
          (gS : GradedAlgebra Sᵢ),
          letI : GradedAlgebra Sᵢ := gS
          ∃ (cS : IsStrictlyGradedComm Sᵢ),
            letI : IsStrictlyGradedComm Sᵢ := cS
            ∃ δS : DividedPowerStructure Sᵢ,
              (∀ (n : ℕ) (b : finiteVariableStage γ ι generator S),
                b ∈ positiveEvenPart Sᵢ →
                  (δS.dpow n b : A) = γ.dpow n (b : A)) ∧
              (∀ hodd : Odd d,
                ∃ e : OddVariableExtension Sᵢ d ≃+*
                    finiteVariableStage γ ι generator (insert j S),
                  (∀ b : finiteVariableStage γ ι generator S,
                    ((e (OddVariableExtension.inclusion
                      Sᵢ d b) : finiteVariableStage γ ι generator (insert j S)) : A) = b) ∧
                  ((e (OddVariableExtension.generator
                    Sᵢ d) : finiteVariableStage γ ι generator (insert j S)) : A) = generator j ∧
                  (∀ (m : ℕ) (x : OddVariableExtension Sᵢ d),
                    x ∈ OddVariableExtension.grade Sᵢ d m ↔ (e x : A) ∈ Aᵢ m) ∧
                  (∀ (n : ℕ) (x : OddVariableExtension Sᵢ d),
                    x ∈ positiveEvenPart (OddVariableExtension.grade Sᵢ d) →
                    γ.dpow n (e x : A) =
                      (e ((oddVariableDividedPowerStructure
                        Sᵢ δS d (Nat.zero_lt_succ j.1) hodd).dpow n x) : A))) ∧
              (∀ heven : Even d,
                letI : Fact (Even d) := ⟨heven⟩
                ∃ e : EvenVariableAlgebra (finiteVariableStage γ ι generator S) ≃+*
                    finiteVariableStage γ ι generator (insert j S),
                  (∀ b : finiteVariableStage γ ι generator S,
                    ((e (coeffEmbedding
                      b) : finiteVariableStage γ ι generator (insert j S)) : A) = b) ∧
                  ((e (monomial
                    1 1) : finiteVariableStage γ ι generator (insert j S)) : A) = generator j ∧
                  (∀ (m : ℕ)
                    (x : EvenVariableAlgebra (finiteVariableStage γ ι generator S)),
                    x ∈ EvenVariableAlgebra.grade Sᵢ d m ↔ (e x : A) ∈ Aᵢ m) ∧
                  (∀ (n : ℕ)
                    (x : EvenVariableAlgebra (finiteVariableStage γ ι generator S)),
                    x ∈ positiveEvenPart (EvenVariableAlgebra.grade Sᵢ d) →
                    γ.dpow n (e x : A) =
                      (e ((evenVariableDividedPowerStructure d
                        (Nat.zero_lt_succ j.1) δS).dpow n x) : A)))

end DividedPowers.TateResolution

end
