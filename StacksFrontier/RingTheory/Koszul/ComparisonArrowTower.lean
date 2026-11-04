module

public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraArrow
public import StacksFrontier.RingTheory.Koszul.ComparisonArrowAppend

/-!
# The comparison data of Tag 0GZ7 exists for every sequence

For one element `f` of a commutative ring `R` and exponents `N ≥ n + t` with `n ≥ t ≥ 1`, the
algebra `B_{N,t} = R⟨x, z, u⟩` of `Koszul.comparisonAlgebra` carries the comparison data of
`Koszul.KoszulArrowData`: its homotopy retraction onto `K_t` is
`Koszul.comparisonHomotopyRetract`, its odd part `R⟨x, z⟩` is a Koszul algebra and hence graded
commutative, the two structure maps out of `K_N` and `K_t` are
`Koszul.koszulToComparisonOdd` and `Koszul.koszulToComparisonOddX`, and the arrow into
`K_n ⊗_R K_t` is `Koszul.comparisonToTensor`.

For a sequence of length `q` the data is built by induction on `q`, a sequence of length `p + 1`
being the concatenation of its first `p` terms with its last and the data of a concatenation
being `Koszul.KoszulArrowData.append`. This is the reduction of the case `r > 1` of Tag 0GZ7 to
the case `r = 1`.

## Main definitions

* `Koszul.koszulArrowDataOne`: the comparison data of a sequence of length one.

## Main results

* `Koszul.nonempty_koszulArrowData`: the comparison data exists for every sequence and all
  exponents `N ≥ n + t` with `n ≥ t ≥ 1`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-- **The comparison data of a sequence of length one**: the algebra `B_{N,t} = R⟨x, z, u⟩`,
with its homotopy retraction onto `K_t`, its odd part `R⟨x, z⟩`, and the arrow
`B_{N,t} → K_n ⊗_R K_t` of `Koszul.comparisonToTensor`. -/
def koszulArrowDataOne (a : R) {n t N : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) (hnN : n ≤ N)
    (hN : n + t ≤ N) :
    KoszulArrowData (fun _ : Fin 1 => a) n t N ht htn hnN where
  carrier := comparisonAlgebra a (htn.trans hnN)
  eps := comparisonToKoszul a (htn.trans hnN)
  retract := comparisonHomotopyRetract a (htn.trans hnN)
  odd := comparisonOddAlgebra a N t
  oddComm := isGradedCommutative_cohomological (Fin 2 → R) (seqDual (comparisonSeq a N t))
  oddHom := comparisonOddToAlgebra a (htn.trans hnN)
  kappaOdd := koszulToComparisonOdd a N t
  xiOdd := koszulToComparisonOddX a N t
  beta := comparisonToTensor a (htn.trans hnN) hN
  eps_kappa := comparisonToKoszul_comp_koszulToComparison a ht (htn.trans hnN)
  eps_xi := comparisonToKoszul_comp_koszulToComparisonX a (htn.trans hnN)
  mul_beta := powMul_comp_comparisonToTensor a (htn.trans hnN) ht htn hN
  beta_kappa := comparisonToTensor_comp_koszulToComparison a (htn.trans hnN)
    (ht.trans htn) hnN hN
  beta_xi := comparisonToTensor_comp_koszulToComparisonX a (htn.trans hnN) hN

/-- **The comparison data of Tag 0GZ7 exists for every sequence.** For every sequence
`f₁, …, f_q` in `R` and all exponents `N ≥ n + t` with `n ≥ t ≥ 1`, there is a differential
graded algebra with a homotopy retraction onto `K_t`, a graded-commutative odd part carrying the
structure maps out of `K_N` and `K_t`, and an arrow into `K_n ⊗_R K_t` with the three
compatibilities. The proof is by induction on the length of the sequence. -/
theorem nonempty_koszulArrowData {n t N : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) (hnN : n ≤ N)
    (hN : n + t ≤ N) :
    ∀ (q : ℕ) (f : Fin q → R), Nonempty (KoszulArrowData f n t N ht htn hnN) := by
  intro q
  induction q with
  | zero => exact fun f => ⟨koszulArrowDataEmpty f⟩
  | succ p ih =>
      intro f
      have heq : Fin.append (Fin.init f) (fun _ : Fin 1 => f (Fin.last p)) = f := by
        rw [Fin.append_right_eq_snoc, Fin.snoc_init_self]
      obtain ⟨D⟩ := ih (Fin.init f)
      rw [← heq]
      exact ⟨D.append (koszulArrowDataOne (f (Fin.last p)) ht htn hnN hN)⟩

end Koszul
