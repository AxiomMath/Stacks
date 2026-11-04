module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenPresentation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PolynomialDifferential

/-!
# Functoriality of the odd-variable extension

A graded algebra map `c : A →ₐ[R] B` extends coefficientwise to the odd-variable extensions,
`a + bT ↦ c a + (c b) T`. The only point needing an argument is that the twisted right action is
respected, which is to say that `c` commutes with the grading-sign automorphism; that holds
because `c` preserves the grading, and the grading sign is multiplication by `(-1) ^ (d * m)` on
the degree-`m` piece.

This is the map along which a differential is transported. A degree-lowering map obeying the
signed Leibniz rule is the same thing as a graded divided-power algebra map into the odd-variable
extension by one variable of degree one (`exists_differential_gradedDividedPowerPolynomial`), so
the assertion that a comparison map of graded divided-power polynomial algebras commutes with
their differentials becomes an assertion about two algebra maps into one odd-variable extension,
and the universal property settles it. That is what
`DividedPowers.TateResolution.IndexedPresentation.comparison_differential` does.

## Main definitions

* `DividedPowers.TateResolution.oddExtMap` — the coefficientwise extension of a graded algebra
  map to the odd-variable extensions.

## Main results

* `DividedPowers.TateResolution.algHom_signRingEquiv` — a graded algebra map commutes with the
  grading-sign automorphism.
* `DividedPowers.TateResolution.oddExtMap_mem_grade` and
  `DividedPowers.TateResolution.oddExtMap_dpow` — the extension is graded, and it is compatible
  with the canonical divided powers of the two extensions as soon as `c` is compatible with the
  divided powers of the coefficient algebras.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local implicit_reducible] TwistedModule

section Map

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ]

/-- **A graded algebra map commutes with the grading sign.** On the degree-`m` piece both sides
are multiplication by `(-1) ^ (d * m)`, and a general element is the sum of its homogeneous
components. -/
public theorem algHom_signRingEquiv (c : A →ₐ[R] B)
    (hc : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → c a ∈ Bᵢ m) (d : ℕ) (a : A) :
    c (signRingEquiv Aᵢ d a) = signRingEquiv Bᵢ d (c a) := by
  classical
  rw [← DirectSum.sum_support_decompose Aᵢ a]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hx : ((DirectSum.decompose Aᵢ a m : A)) ∈ Aᵢ m := (DirectSum.decompose Aᵢ a m).property
  rw [signRingEquiv_of_mem Aᵢ d m hx, signRingEquiv_of_mem Bᵢ d m (hc m _ hx), map_smul]

variable (d : ℕ) (c : A →ₐ[R] B) (hc : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → c a ∈ Bᵢ m)

/-- **A graded algebra map extended coefficientwise to the odd-variable extensions**, that is,
`a + bT ↦ c a + (c b) T`. -/
public noncomputable def oddExtMap :
    OddVariableExtension Aᵢ d →ₐ[R] OddVariableExtension Bᵢ d where
  toFun x := (c x.fst, (c (show A from x.snd) : TwistedModule Bᵢ d))
  map_one' := TrivSqZeroExt.ext (by change c (1 : A) = 1; simp) (by change c (0 : A) = 0; simp)
  map_mul' x y := TrivSqZeroExt.ext
    (by change c (x.fst * y.fst) = c x.fst * c y.fst; rw [map_mul])
    (by
      change c (x.fst * (show A from y.snd) + (show A from x.snd) * signRingEquiv Aᵢ d y.fst) =
        c x.fst * c (show A from y.snd) +
          c (show A from x.snd) * signRingEquiv Bᵢ d (c y.fst)
      rw [map_add, map_mul, map_mul, algHom_signRingEquiv Aᵢ Bᵢ c hc d y.fst])
  map_zero' := TrivSqZeroExt.ext (by change c (0 : A) = 0; simp) (by change c (0 : A) = 0; simp)
  map_add' x y := TrivSqZeroExt.ext
    (by change c (x.fst + y.fst) = c x.fst + c y.fst; rw [map_add])
    (by
      change c ((show A from x.snd) + (show A from y.snd)) =
        c (show A from x.snd) + c (show A from y.snd)
      rw [map_add])
  commutes' r := TrivSqZeroExt.ext
    (by change c (algebraMap R A r) = algebraMap R B r; simp)
    (by change c (0 : A) = 0; simp)

/-- The coefficients of `oddExtMap c` applied to `a + bT` are `(c a, c b)`. -/
public theorem coefficients_oddExtMap (x : OddVariableExtension Aᵢ d) :
    OddVariableExtension.coefficients Bᵢ d (oddExtMap Aᵢ Bᵢ d c hc x) =
      (c (OddVariableExtension.coefficients Aᵢ d x).1,
        c (OddVariableExtension.coefficients Aᵢ d x).2) := rfl

/-- `oddExtMap c` extends `c` along the inclusions of the coefficient algebras. -/
public theorem oddExtMap_inclusion (a : A) :
    oddExtMap Aᵢ Bᵢ d c hc (OddVariableExtension.inclusion Aᵢ d a) =
      OddVariableExtension.inclusion Bᵢ d (c a) := by
  apply (OddVariableExtension.coefficients Bᵢ d).injective
  rw [coefficients_oddExtMap, OddVariableExtension.coefficients_inclusion,
    OddVariableExtension.coefficients_inclusion, map_zero]

/-- `oddExtMap c` sends the odd variable `T` to the odd variable `T`. -/
public theorem oddExtMap_generator :
    oddExtMap Aᵢ Bᵢ d c hc (OddVariableExtension.generator Aᵢ d) =
      OddVariableExtension.generator Bᵢ d := by
  apply (OddVariableExtension.coefficients Bᵢ d).injective
  rw [coefficients_oddExtMap, OddVariableExtension.coefficients_generator,
    OddVariableExtension.coefficients_generator, map_zero, map_one]

/-- The coefficientwise extension is graded: the coefficient of `T` is read in the shifted
degree, where below the degree of the variable the piece is trivial. -/
public theorem oddExtMap_mem_grade (m : ℕ) (x : OddVariableExtension Aᵢ d)
    (hx : x ∈ OddVariableExtension.grade Aᵢ d m) :
    oddExtMap Aᵢ Bᵢ d c hc x ∈ OddVariableExtension.grade Bᵢ d m := by
  obtain ⟨h1, h2⟩ := (OddVariableExtension.mem_grade_coefficients_iff Aᵢ d m x).mp hx
  rw [OddVariableExtension.mem_grade_coefficients_iff, coefficients_oddExtMap]
  refine ⟨hc m _ h1, ?_⟩
  by_cases hdm : d ≤ m
  · rw [ite_eq_left hdm] at h2 ⊢
    exact hc _ _ h2
  · rw [ite_eq_right hdm, Submodule.mem_bot] at h2 ⊢
    rw [h2, map_zero]

end Map

section Dpow

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ] [IsStrictlyGradedComm Bᵢ]
  (γ : DividedPowerStructure Aᵢ) (δ : DividedPowerStructure Bᵢ)
  (c : A →ₐ[R] B) (hc : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → c a ∈ Bᵢ m)

/-- **The coefficientwise extension respects the canonical divided powers** of the two
odd-variable extensions by a variable of degree one, as soon as `c` respects the divided powers
of the coefficient algebras. Both sides are computed by the formula
`γ_n (a + bT) = γ_n(a) + γ_{n-1}(a) b T`. -/
public theorem oddExtMap_dpow
    (hcd : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ → c (γ.dpow n a) = δ.dpow n (c a))
    (n : ℕ) {x : OddVariableExtension Aᵢ 1}
    (hx : x ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ 1)) :
    oddExtMap Aᵢ Bᵢ 1 c hc
        ((oddVariableDividedPowerStructure Aᵢ γ 1 Nat.one_pos odd_one).dpow n x) =
      (oddVariableDividedPowerStructure Bᵢ δ 1 Nat.one_pos odd_one).dpow n
        (oddExtMap Aᵢ Bᵢ 1 c hc x) := by
  have hy : oddExtMap Aᵢ Bᵢ 1 c hc x ∈ positiveEvenPart (OddVariableExtension.grade Bᵢ 1) :=
    algHom_mem_positiveEvenPart (OddVariableExtension.grade Aᵢ 1)
      (OddVariableExtension.grade Bᵢ 1) (oddExtMap Aᵢ Bᵢ 1 c hc)
      (fun m z hz => oddExtMap_mem_grade Aᵢ Bᵢ 1 c hc m z hz) hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(oddVariableDividedPowerStructure Aᵢ γ 1 Nat.one_pos odd_one).dpow_zero hx,
      (oddVariableDividedPowerStructure Bᵢ δ 1 Nat.one_pos odd_one).dpow_zero hy, map_one]
  apply (OddVariableExtension.coefficients Bᵢ 1).injective
  rw [coefficients_oddExtMap, coefficients_dpow Aᵢ γ n hn.ne' hx,
    coefficients_dpow Bᵢ δ n hn.ne' hy, coefficients_oddExtMap]
  simp only [Prod.mk.injEq]
  refine ⟨hcd n _ (mem_positiveEvenPart_oddExt Aᵢ hx).1, ?_⟩
  rw [map_mul, hcd (n - 1) _ (mem_positiveEvenPart_oddExt Aᵢ hx).1]

end Dpow

end DividedPowers.TateResolution

end
