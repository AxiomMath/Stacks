module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsNaturality
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.DeRham.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Trace maps on absolute differential forms: the conditions

Let `A → B` be a finite projective ring map, and write `Ω^p_A = ⋀^p_A Ω[A⁄ℤ]` for the module of
absolute differential `p`-forms. Stacks, Lemma 0FLB, Proposition 0FLC study `A`-linear maps

`Θ^p : Ω^p_B → Ω^p_A`, `p ≥ 0`,

whose composition with `B ⊗_A Ω^p_A → Ω^p_B` is `Trace_{B/A} ⊗ id`. This file fixes the objects
in which these conditions are stated, at the level of rings: the pull-back of forms, the trace of
a finite projective algebra, and the three conditions — compatibility with the trace (0FLB (1)),
linearity over the forms of `A` (0FLC (2)) and compatibility with the de Rham differential
(0FLC: a map of complexes).

## Main definitions

* `Stacks.FormsTrace.formsMap`: the pull-back of forms `Ω^p_A → Ω^p_B`, semilinear along
  `A → B`.
* `Stacks.FormsTrace.trace`: `Trace_{B/A} : B → A`, the trace of multiplication on the finite
  projective `A`-module `B` (Discriminants, Section 0BVH, on affine opens).
* `Stacks.FormsTrace.IsFormsTrace`: condition (1) of Lemma 0FLB.
* `Stacks.FormsTrace.IsWedgeLinear`: condition (2) of Proposition 0FLC.
* `Stacks.FormsTrace.CommutesWithD`: the maps form a map of de Rham complexes.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Section 0BVH](https://stacks.math.columbia.edu/tag/0BVH)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.FormsTrace

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **The pull-back of absolute differential forms** `Ω^p_A → Ω^p_B` along `A → B`, semilinear
along `algebraMap A B`: the `p`-th exterior power of `Ω[A⁄ℤ] → Ω[B⁄ℤ]`. -/
abbrev formsMap (p : ℕ) : ⋀[A]^p Ω[A⁄ℤ] →ₛₗ[algebraMap A B] ⋀[B]^p Ω[B⁄ℤ] :=
  ExteriorAlgebra.powMapₛₗ p (algebraMap A B) (Stacks.DeRham.kaehlerMapₛₗ A B)

/-- **The trace** `Trace_{B/A} : B → A` of a finite projective algebra: `b` goes to the trace of
multiplication by `b` on the finite projective `A`-module `B`. -/
@[ega "IV 18.2.1"]
abbrev trace [Module.Finite A B] [Module.Projective A B] : B →ₗ[A] A :=
  (Stacks.Discriminant.finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap

/-- **Condition (1) of Stacks, Lemma 0FLB**, on rings: the composition of `Θ^p` with
`B ⊗_A Ω^p_A → Ω^p_B` is `Trace_{B/A} ⊗ id`, i.e. `Θ^p(b · ω) = Trace_{B/A}(b) · ω` for `b ∈ B`
and `ω ∈ Ω^p_A`. -/
def IsFormsTrace [Module.Finite A B] [Module.Projective A B]
    (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) : Prop :=
  ∀ (p : ℕ) (b : B) (ω : ⋀[A]^p Ω[A⁄ℤ]), Θ p (b • formsMap A B p ω) = trace A B b • ω

/-- **Condition (2) of Stacks, Proposition 0FLC**, on rings: `Θ(ω ∧ η) = ω ∧ Θ(η)` for a form
`ω` of `A` and a form `η` of `B`. -/
def IsWedgeLinear (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) : Prop :=
  ∀ (q p : ℕ) (ω : ⋀[A]^q Ω[A⁄ℤ]) (η : ⋀[B]^p Ω[B⁄ℤ]),
    Θ (q + p) (exteriorPower.wedgeMul q p (formsMap A B q ω) η) =
      exteriorPower.wedgeMul q p ω (Θ p η)

/-- **The maps `Θ^p` form a map of de Rham complexes** `Ω^•_B → Ω^•_A`: they commute with the
de Rham differentials. -/
def CommutesWithD (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) : Prop :=
  ∀ (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]),
    Θ (p + 1) (KaehlerDifferential.deRhamDifferential p η) =
      KaehlerDifferential.deRhamDifferential p (Θ p η)

end Stacks.FormsTrace

end
