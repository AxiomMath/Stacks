module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableLift

/-! # A commutative algebra as a bundled graded divided power algebra in degree zero

A commutative `R`-algebra `P` is a nonnegatively graded algebra with `P` in degree zero and
nothing in positive degree. That grading, its strict graded commutativity and its unique divided
power structure are
`StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero`; this file bundles them into a
`DividedPowers.TateResolution.GradedDPAlgebra` and records what a morphism out of that bundle
amounts to.

This is the base of the `ω`-tower of Tag 09PS: the lift of a divided power differential graded
algebra over a polynomial ring `R[xᵢ]` starts from the polynomial ring `R'[xᵢ]` over the
square-zero extension, with no variables of positive degree adjoined yet. The tower is indexed by
`GradedDPAlgebra`, so the base has to be presented in that bundled form.

## Main definitions

* `DividedPowers.TateResolution.degreeZeroDPAlgebra` — the grading, the strictness and the divided
  powers of `DegreeZero`, bundled as a `DividedPowers.TateResolution.GradedDPAlgebra`.
* `DividedPowers.TateResolution.degreeZeroDPHom` — a morphism out of it, which is no more than an
  algebra map into degree zero of the target.

## Main results

* `DividedPowers.TateResolution.eq_zero_of_mem_degreeZeroDPAlgebra_grade` and
  `DividedPowers.TateResolution.eq_zero_of_mem_positiveEvenPart_degreeZeroDPAlgebra` — the two
  degeneracies: a homogeneous element of positive degree, and an element of the positive even
  part, of the bundled algebra is zero.

## Implementation notes

The grading condition in positive degree and the divided power condition are both vacuous for a
morphism out of the bundle, the source having nothing in positive degree and only `0` in its
positive even part. That is why `degreeZeroDPHom` asks only for an algebra homomorphism landing
in degree zero of the target.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

section Grading

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- A commutative algebra as a graded divided power algebra concentrated in degree zero. -/
public noncomputable def degreeZeroDPAlgebra : GradedDPAlgebra.{u, v} R where
  carrier := P
  ring := inferInstance
  algebra := inferInstance
  grade := degreeZeroGrade R P
  graded := inferInstance
  strict := inferInstance
  gamma := degreeZeroDividedPowers R P

/-- The carrier of the bundled degree-zero algebra is `P`. -/
@[simp]
public theorem degreeZeroDPAlgebra_carrier :
    (degreeZeroDPAlgebra R P).carrier = P := rfl

/-- The grading of the bundled degree-zero algebra is `degreeZeroGrade R P`. -/
@[simp]
public theorem degreeZeroDPAlgebra_grade :
    (degreeZeroDPAlgebra R P).grade = degreeZeroGrade R P := rfl

/-- The divided powers of the bundled degree-zero algebra are `degreeZeroDividedPowers R P`. -/
@[simp]
public theorem degreeZeroDPAlgebra_gamma :
    (degreeZeroDPAlgebra R P).gamma = degreeZeroDividedPowers R P := rfl

/-- The zeroth divided power of the bundled degree-zero algebra at the only point of its
domain. -/
public theorem degreeZeroDPAlgebra_dpow_zero :
    (degreeZeroDPAlgebra R P).gamma.dpow 0 (0 : (degreeZeroDPAlgebra R P).carrier) = 1 :=
  degreeZeroDpow_zero_zero (Q := P)

/-- Positive divided powers of the bundled degree-zero algebra vanish. -/
public theorem degreeZeroDPAlgebra_dpow_succ (n : ℕ) :
    (degreeZeroDPAlgebra R P).gamma.dpow (n + 1) (0 : (degreeZeroDPAlgebra R P).carrier) = 0 :=
  degreeZeroDpow_succ_zero (Q := P) n

/-- A homogeneous element of positive degree of the bundled degree-zero algebra is zero. -/
public theorem eq_zero_of_mem_degreeZeroDPAlgebra_grade {n : ℕ} (hn : n ≠ 0)
    {x : (degreeZeroDPAlgebra R P).carrier}
    (hx : x ∈ (degreeZeroDPAlgebra R P).grade n) : x = 0 :=
  eq_zero_of_mem_degreeZeroGrade R P hn hx

/-- An element of the positive even part of the bundled degree-zero algebra is zero. -/
public theorem eq_zero_of_mem_positiveEvenPart_degreeZeroDPAlgebra
    {x : (degreeZeroDPAlgebra R P).carrier}
    (hx : x ∈ positiveEvenPart (degreeZeroDPAlgebra R P).grade) : x = 0 :=
  eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hx

/-- A morphism of graded divided power algebras out of a degree-zero-concentrated algebra is no
more than an algebra homomorphism landing in degree zero: the grading condition in positive
degree and the divided power condition are both vacuous, the source having nothing in positive
degree and only `0` in its positive even part. -/
public noncomputable def degreeZeroDPHom (D : GradedDPAlgebra.{u, w} R)
    (f : (degreeZeroDPAlgebra R P).carrier →ₐ[R] D.carrier)
    (hf : ∀ p : (degreeZeroDPAlgebra R P).carrier, f p ∈ D.grade 0) :
    GradedDPHom (degreeZeroDPAlgebra R P) D where
  hom := f
  map_grade := by
    intro m a ha
    rcases m with _ | m
    · exact hf a
    · rw [eq_zero_of_mem_degreeZeroDPAlgebra_grade R P (Nat.succ_ne_zero m) ha, map_zero]
      exact Submodule.zero_mem _
  map_dpow := by
    intro n a ha
    have ha0 : a = 0 := eq_zero_of_mem_positiveEvenPart_degreeZeroDPAlgebra R P ha
    rcases n with _ | n
    · rw [ha0, degreeZeroDPAlgebra_dpow_zero, map_zero, map_one]
      exact D.gamma.dpow_zero (Submodule.zero_mem _)
    · rw [ha0, degreeZeroDPAlgebra_dpow_succ, map_zero]
      exact D.gamma.dpow_zero_eq_zero (Nat.succ_ne_zero n)

/-- The underlying algebra homomorphism of `degreeZeroDPHom R P D f hf` is `f`. -/
@[simp]
public theorem degreeZeroDPHom_hom (D : GradedDPAlgebra.{u, w} R)
    (f : (degreeZeroDPAlgebra R P).carrier →ₐ[R] D.carrier)
    (hf : ∀ p : (degreeZeroDPAlgebra R P).carrier, f p ∈ D.grade 0) :
    (degreeZeroDPHom R P D f hf).hom = f := rfl

end Grading

end DividedPowers.TateResolution

end
