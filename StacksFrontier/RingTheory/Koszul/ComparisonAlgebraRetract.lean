module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetract
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraResolution

/-!
# `R⟨x, z, u⟩ → K_t` is a homotopy retraction

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The explicit section and
homotopy of `StacksFrontier/RingTheory/Koszul/ComparisonAlgebraResolution.lean` assemble into a
homotopy retraction, in the sense of
`DifferentialGradedAlgebra.HomotopyRetract`, of the comparison homomorphism
`B_{N,t} = R⟨x, z, u⟩ → K_t = R⟨x⟩`. That packaging is what makes the quasi-isomorphism survive
tensoring with another differential graded algebra, which is how the case of one element of `R` is
propagated to a sequence.

## Main definitions

* `Koszul.comparisonHomotopyRetract`: the homotopy retraction of `Koszul.comparisonToKoszul`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-- **The comparison homomorphism `B_{N,t} → K_t` is a homotopy retraction.** The section is the
inclusion of `R⟨x⟩`, and the homotopy sends `a u⁽ⁿ⁾` to `-(z'⌟a) u⁽ⁿ⁺¹⁾`. -/
def comparisonHomotopyRetract (f : R) {N t : ℕ} (h : t ≤ N) :
    HomotopyRetract (comparisonToKoszul f h) where
  sec := comparisonSectionMap R
  sec_mem n b hb := by
    rw [comparisonAlgebra_grading]
    rw [powAlgebra_grading] at hb
    exact comparisonSectionMap_mem_grading n hb
  sec_d b := (comparisonDifferential_comparisonSectionMap f N t b).symm
  hom_sec b := comparisonAlgHom_comparisonSectionMap f N t b
  htp := comparisonHomotopy R
  htp_mem n a ha := by
    rw [comparisonAlgebra_grading] at ha ⊢
    exact comparisonHomotopy_mem_grading n ha
  htp_eq a := comparisonHomotopy_eq f N t a

end Koszul
