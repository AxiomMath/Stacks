module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenDifferential
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.CoefficientFG
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FiniteIndices

/-!
# The cycles of one degree, as a module over the coefficients

The differential a prescribed boundary determines is linear over the base ring only, but it
satisfies the Leibniz rule and kills the coefficients, which sit in degree zero; so the
differential of a coefficient multiple is that coefficient multiple of the differential, with no
sign. The cycles of a given degree are therefore a module over the coefficient algebra, not only
over the base ring — and when the coefficient algebra is Noetherian and each degree contributes
finitely many variables they are a *finitely generated* module over it, by
`fg_of_le_gradeModule`.

A coefficient combination of the prescribed boundaries of variables of degree `d + 1` is the
differential of an element of degree `d + 1` — the element being the same combination of those
variables, whose differential is computed by the Leibniz rule in degree zero.

## Main definitions

* `DividedPowers.TateResolution.IndexedPresentation.cycleModule` — the cycles of one degree, as
  a module over the coefficient algebra.

## Main results

* `DividedPowers.TateResolution.IndexedPresentation.chosenDifferential_coefficient_mul` — the
  differential of a coefficient multiple.
* `DividedPowers.TateResolution.IndexedPresentation.fg_cycleModule` — the cycles of one degree
  are a finitely generated module over a Noetherian coefficient algebra.
* `DividedPowers.TateResolution.IndexedPresentation.chosenDifferential_sum_coefficient_mul_gen`
  — a coefficient combination of the prescribed boundaries of variables of degree `d + 1` is the
  differential of the same combination of those variables, which has degree `d + 1`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

namespace IndexedPresentation

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  {idx : ℕ → Type (max u v w)}
  (T : IndexedPresentation.{u, v, w} R P idx) (t : (Σ n : ℕ, idx n) → T.A)
  (ht : ∀ j, t j ∈ T.grade j.1)

/-- **The prescribed differential of a coefficient multiple is that coefficient multiple of the
differential.** The differential kills the coefficient and the Leibniz sign in degree zero is
`+1`, so there is no sign. -/
public theorem chosenDifferential_coefficient_mul (p : P) (m : ℕ) (x : T.A)
    (hx : x ∈ T.grade m) :
    T.chosenDifferential t ht (T.coefficient p * x) =
      T.coefficient p * T.chosenDifferential t ht x := by
  rw [T.chosenDifferential_leibniz t ht 0 m _ _ (T.coefficient_mem_grade_zero p) hx,
    T.chosenDifferential_coefficient t ht p, zero_mul, zero_add, pow_zero, one_smul]

/-- **The differential of a coefficient combination of variables of one degree**, together with
the degree of that combination: if every variable `ja i` has degree `d`, then
`∑ i ∈ s, coefficient (c i) * gen (ja i)` has degree `d + 1` and its prescribed differential is
`∑ i ∈ s, coefficient (c i) * t (ja i)`. -/
public theorem chosenDifferential_sum_coefficient_mul_gen {α : Type z} (s : Finset α)
    (c : α → P) (ja : α → Σ n : ℕ, idx n) (d : ℕ) (hja : ∀ i : α, (ja i).1 = d) :
    (∑ i ∈ s, T.coefficient (c i) * T.gen (ja i)) ∈ T.grade (d + 1) ∧
      T.chosenDifferential t ht (∑ i ∈ s, T.coefficient (c i) * T.gen (ja i)) =
        ∑ i ∈ s, T.coefficient (c i) * t (ja i) := by
  refine ⟨Submodule.sum_mem _ fun i _ => ?_, ?_⟩
  · have hg := T.gen_mem (ja i)
    rw [hja i] at hg
    simpa using SetLike.mul_mem_graded (T.coefficient_mem_grade_zero (c i)) hg
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg := T.gen_mem (ja i)
    rw [hja i] at hg
    rw [T.chosenDifferential_coefficient_mul t ht (c i) (d + 1) _ hg,
      T.chosenDifferential_gen t ht (ja i)]

variable [Algebra P T.A] (hPA : ∀ p : P, algebraMap P T.A p = T.coefficient p)

/-- **The cycles of degree `m`, as a module over the coefficient algebra.** The carrier is the
degree-`m` part of the kernel of the prescribed differential; it is stable under multiplying by
a coefficient because the coefficient has degree zero and the differential kills it. -/
public noncomputable def cycleModule (m : ℕ) : Submodule P T.A :=
  coefficientSubmodule T.coefficient hPA
    (T.grade m ⊓ LinearMap.ker (T.chosenDifferential t ht))
    (by
      intro p x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_ker.mpr ?_⟩
      · simpa using SetLike.mul_mem_graded (T.coefficient_mem_grade_zero p) hx1
      · rw [T.chosenDifferential_coefficient_mul t ht p m x hx1, LinearMap.mem_ker.mp hx2,
          mul_zero])

/-- An element lies in `cycleModule` of degree `m` exactly when it has degree `m` and its
prescribed differential vanishes. -/
@[simp] public theorem mem_cycleModule (m : ℕ) (x : T.A) :
    x ∈ cycleModule T t ht hPA m ↔ x ∈ T.grade m ∧ T.chosenDifferential t ht x = 0 := Iff.rfl

/-- **The cycles of one degree are a finitely generated module over the coefficient algebra**,
when that algebra is Noetherian and each degree contributes finitely many variables. -/
public theorem fg_cycleModule [IsNoetherianRing P] (hfin : ∀ n : ℕ, Finite (idx n)) (m : ℕ) :
    (cycleModule T t ht hPA m).FG :=
  fg_of_le_gradeModule T.polynomial hPA (T.finite_indices hfin) m _ fun _ hx => hx.1

end IndexedPresentation

end DividedPowers.TateResolution

end
