module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Basis.Fin
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.TransposeGraph
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree-zero correspondence algebra of the projective line

For `X = P¹_k` the degree-zero correspondences from `X` to itself are the rational
codimension-one, equivalently dimension-one, Chow classes of the square:

`Corr⁰(X, X) = CH¹(X × X) ⊗ ℚ = CH₁(X × X) ⊗ ℚ`.

A rational point `x` of `X` gives the two fibre classes `c₀ = [x × X]` and `c₂ = [X × x]`, which
satisfy `1 = [Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀`, `c₀ ∘ c₂ = 0`, `c₂ ∘ c₀ = 0`, `c₂ ∘ c₂ = c₂`:
they are orthogonal idempotents, and being a basis they split the algebra,
`Corr⁰(X, X) = ℚ × ℚ`.

## Main definitions

* `Stacks.WeilCohomology.pointFibreCorrespondence`: the correspondence `c₀ = [x × X]`, the class
  of the graph of the constant morphism of `X` through a section `x`.
* `Stacks.WeilCohomology.fibrePointCorrespondence`: the correspondence `c₂ = [X × x]`, the class
  of the factor switch of that graph.
* `Stacks.WeilCohomology.algEquivProdOfBasisOfAddEqOne`: the splitting `ℚ × ℚ ≃ Corr⁰(X, X)`.

## Main results

* `Stacks.WeilCohomology.mul_eq_zero_of_add_eq_one`,
  `Stacks.WeilCohomology.mul_eq_zero_of_add_eq_one'` and
  `Stacks.WeilCohomology.mul_self_of_add_eq_one`: the composition rules `c₀ ∘ c₂ = 0`,
  `c₂ ∘ c₀ = 0` and `c₂ ∘ c₂ = c₂` follow from `[Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀`.
* `Stacks.WeilCohomology.algEquivProdOfBasisOfAddEqOne_apply`: the splitting sends `(a, b)` to
  `a c₀ + b c₂`.
* `Stacks.WeilCohomology.cycleTranspose_pointFibre`: `[X × x]` is the transpose of `[x × X]`.
* `Stacks.WeilCohomology.correspondence_zero_eq`: the degree bookkeeping
  `Corr⁰(X, X) = CH₁(X × X) ⊗ ℚ` for a source of dimension one.

## Implementation notes

The fibre `x × X ⊆ X ×_S X` of a section `x` of the structure morphism is the graph of the
constant morphism `X ⟶ S ⟶ X` through `x`, so the two fibre correspondences are classes of
graphs and `Stacks.WeilCohomology.cycleTranspose_graph` identifies the second as the transpose
of the first. Neither a base field nor smoothness or projectivity is needed: a section of any
morphism locally of finite type over a base situation in the sense of Stacks 02QL has these two
fibres, and the dimension `d` of the source, which fixes the grading, is a parameter.

The splitting is stated for an abstract algebra `A` over a commutative ring `R`; for the
projective line it is `A = Corr⁰(X, X)` over `R = ℚ`, with `b 0 = c₀`, `b 1 = c₂` and `1 = [Δ]`.
The composition of correspondences is not formalized here, so the decomposition `[Δ] = c₀ + c₂`,
the rule `c₀ ∘ c₀ = c₀` and the fact that `c₀`, `c₂` are a basis enter as hypotheses on `A`.

## References

* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped TensorProduct

universe u v w

namespace Stacks.WeilCohomology

section OrthogonalIdempotents

variable {R : Type v} [CommRing R] {A : Type w} [Ring A] [Algebra R A] {c₀ c₂ : A}

/-- The complement of an idempotent is idempotent: from `[Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀`
follows `c₂ ∘ c₂ = c₂`. -/
@[stacks 0FG6 "c₂ ∘ c₂ = c₂"]
theorem mul_self_of_add_eq_one (hsum : c₀ + c₂ = 1) (h₀ : c₀ * c₀ = c₀) : c₂ * c₂ = c₂ := by
  obtain rfl := eq_sub_of_add_eq' hsum
  exact IsIdempotentElem.one_sub h₀

/-- An idempotent and its complement are orthogonal: from `[Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀`
follows `c₀ ∘ c₂ = 0`. -/
@[stacks 0FG6 "c₀ ∘ c₂ = 0"]
theorem mul_eq_zero_of_add_eq_one (hsum : c₀ + c₂ = 1) (h₀ : c₀ * c₀ = c₀) : c₀ * c₂ = 0 := by
  obtain rfl := eq_sub_of_add_eq' hsum
  exact IsIdempotentElem.mul_one_sub_self h₀

/-- An idempotent and its complement are orthogonal in the other order too: from
`[Δ] = c₀ + c₂` and `c₀ ∘ c₀ = c₀` follows `c₂ ∘ c₀ = 0`. -/
@[stacks 0FG6 "c₂ ∘ c₀ = 0"]
theorem mul_eq_zero_of_add_eq_one' (hsum : c₀ + c₂ = 1) (h₀ : c₀ * c₀ = c₀) : c₂ * c₀ = 0 := by
  obtain rfl := eq_sub_of_add_eq' hsum
  exact IsIdempotentElem.one_sub_mul_self h₀

/-- A two-element basis identifies `R × R` with the module, by `(a, b) ↦ a • b 0 + b • b 1`. -/
private theorem finTwoProd_equiv_apply (b : Module.Basis (Fin 2) R A) (y : R × R) :
    (Module.Basis.finTwoProd R).equiv b (Equiv.refl (Fin 2)) y = y.1 • b 0 + y.2 • b 1 := by
  obtain ⟨y₁, y₂⟩ := y
  have hy : (y₁, y₂) =
      y₁ • (Module.Basis.finTwoProd R) 0 + y₂ • (Module.Basis.finTwoProd R) 1 := by
    simp
  rw [hy, map_add, map_smul, map_smul, Module.Basis.equiv_apply, Module.Basis.equiv_apply]
  simp

/-- An algebra with a two-element basis `c₀`, `c₂` whose sum is the identity and whose first
member is idempotent is the product algebra `R × R`: the two basis elements are orthogonal
idempotents, so multiplication is coordinatewise. For the projective line this is
`Corr⁰(P¹, P¹) = ℚ × ℚ`, with `c₀ = [x × P¹]` and `c₂ = [P¹ × x]`. -/
@[stacks 0FG6 "Corr⁰(X, X) = ℚ × ℚ as a ℚ-algebra"]
def algEquivProdOfBasisOfAddEqOne (b : Module.Basis (Fin 2) R A) (hsum : b 0 + b 1 = 1)
    (h₀ : b 0 * b 0 = b 0) : (R × R) ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv ((Module.Basis.finTwoProd R).equiv b (Equiv.refl (Fin 2)))
    (by rw [finTwoProd_equiv_apply]; simpa using hsum)
    (fun y z => by
      rw [finTwoProd_equiv_apply, finTwoProd_equiv_apply, finTwoProd_equiv_apply, add_mul, mul_add,
        mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
        h₀, mul_eq_zero_of_add_eq_one hsum h₀, mul_eq_zero_of_add_eq_one' hsum h₀,
        mul_self_of_add_eq_one hsum h₀]
      simp [Prod.fst_mul, Prod.snd_mul, add_comm])

/-- The algebra isomorphism `algEquivProdOfBasisOfAddEqOne b hsum h₀` sends `(a, a')` to
`a • b 0 + a' • b 1`. -/
@[simp]
theorem algEquivProdOfBasisOfAddEqOne_apply (b : Module.Basis (Fin 2) R A)
    (hsum : b 0 + b 1 = 1) (h₀ : b 0 * b 0 = b 0) (y : R × R) :
    algEquivProdOfBasisOfAddEqOne b hsum h₀ y = y.1 • b 0 + y.2 • b 1 :=
  finTwoProd_equiv_apply b y

end OrthogonalIdempotents

section FibreCorrespondences

/-- The constant morphism `X ⟶ S ⟶ X` through a section `x` of `sX` is a morphism over the
base. -/
theorem constantMorphism_comp_base {S X : Scheme.{u}} (sX : X ⟶ S) (x : S ⟶ X)
    (hx : x ≫ sX = 𝟙 S) : (sX ≫ x) ≫ sX = sX := by
  rw [Category.assoc, hx, Category.comp_id]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (x : C.S ⟶ X) (hx : x ≫ sX = 𝟙 C.S)

/-- The degree-zero correspondence `c₀ = [x × X]` attached to a section `x` of `sX`, for a source
equidimensional of dimension `d`: the rational class of the fibre `x × X ⊆ X ×_S X`, which is the
graph of the constant morphism of `X` through `x`. -/
@[stacks 0FG6 "c₀ = [x × X]"]
def pointFibreCorrespondence (d : ℤ) : Correspondence C sX sX d 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk
    (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
      (graphMorphism sX sX (sX ≫ x) (constantMorphism_comp_base sX x hx)).imageι (d - 0))

/-- The degree-zero correspondence `c₂ = [X × x]` attached to a section `x` of `sX`: the rational
class of the fibre `X × x ⊆ X ×_S X`, the factor switch of `x × X`. -/
@[stacks 0FG6 "c₂ = [X × x]"]
def fibrePointCorrespondence (d : ℤ) : Correspondence C sX sX d 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk
    (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
      (graphMorphism sX sX (sX ≫ x) (constantMorphism_comp_base sX x hx) ≫
        (pullbackSymmetry sX sX).hom).imageι (d - 0))

/-- The fibre `X × x` is the transpose of the fibre `x × X`: transposing the cycle of the one gives
the cycle of the other. -/
@[stacks 0FG6 "[X × x] is the transpose of [x × X]"]
theorem cycleTranspose_pointFibre (k : ℤ) :
    cycleTranspose C sX sX k
        (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
          (graphMorphism sX sX (sX ≫ x) (constantMorphism_comp_base sX x hx)).imageι k) =
      cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
        (graphMorphism sX sX (sX ≫ x) (constantMorphism_comp_base sX x hx) ≫
          (pullbackSymmetry sX sX).hom).imageι k :=
  cycleTranspose_graph C sX sX (sX ≫ x) (constantMorphism_comp_base sX x hx) k

/-- For a source equidimensional of dimension one, such as the projective line, the degree-zero
correspondences are the rational dimension-one Chow classes of the square,
`Corr⁰(X, X) = CH₁(X × X) ⊗ ℚ`. -/
@[stacks 0FG6 "Corr⁰(X, X) = CH₁(X × X) ⊗ ℚ"]
theorem correspondence_zero_eq :
    Correspondence C sX sX 1 0 =
      TensorProduct ℤ ℚ (chowGroup C (pullback.fst sX sX ≫ sX) 1) :=
  rfl

end FibreCorrespondences

end Stacks.WeilCohomology

end
