module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistDownFactor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistDownMultiplication

/-!
# The `c`-step scalar/twist law inside the geometric factor `N ↦ 𝒪_X(q) ⊗ p^*Ñ`

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. This file tensors multiplication by a homogeneous scalar of the Rees algebra into the fixed
factor of `Stacks.Blowup.twistedGeometricFactor`, and proves that multiplication by `(b⁽¹⁾)^c`
and twisting down `c` steps (`Stacks.Blowup.twistDownFactorMap`) compose, in either order, to
multiplication by `b^c`.

## Main definitions

* `Stacks.Blowup.twistScalarFactorMap`: multiplication by a homogeneous scalar of degree `i`,
  tensored into the fixed factor: the natural transformation
  `𝒪_X(n) ⊗ p^*(-) ⟶ 𝒪_X(k) ⊗ p^*(-)` for `i + n = k`.

## Main results

* `Stacks.Blowup.twistScalarFactorMap_reesDegOnePow_comp_twistDownFactorMap` and
  `Stacks.Blowup.twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow`: the two `c`-step
  laws inside the geometric factor: multiplication by `(b⁽¹⁾)^c` and twisting down `c` steps
  compose, in either order, to multiplication by `b^c`, as natural transformations of
  `Stacks.Blowup.twistedGeometricFactor`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistedDegree_zero)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange (geometricFactorFormulaMap
  geometricFactorFormulaMap_congr geometricFactorFormulaMap_comp)

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **Multiplication by a homogeneous scalar, tensored into the fixed factor of the geometric
factor**: for `a` homogeneous of degree `i` in the Rees algebra and a degree `k` with `i + n = k`,
the natural transformation `𝒪_X(n) ⊗ p^*Ñ ⟶ 𝒪_X(k) ⊗ p^*Ñ` of functors of the `A`-module `N`.
-/
def twistScalarFactorMap (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (a : reesGrading I i) :
    twistedGeometricFactor I n ⟶ twistedGeometricFactor I k :=
  geometricFactorFormulaMap A (blowUpOver I) (twistScalarSheafMap (reesGrading I) i n k hk a)

/-- **Multiplication by `(b⁽¹⁾)^c` followed by twisting down `c` steps is multiplication by
`b^c`, inside the geometric factor `N ↦ 𝒪_X(q) ⊗ p^*Ñ`.** -/
theorem twistScalarFactorMap_reesDegOnePow_comp_twistDownFactorMap (c : ℕ) (q q' : ℤ)
    (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A} (hb : b ∈ I) :
    twistScalarFactorMap I c q' q hq
          ⟨(reesDegOne I hb : reesAlgebra I) ^ c, reesDegOnePow_mem_reesGrading I hb c⟩ ≫
        twistDownFactorMap I q q' hle =
      twistScalarFactorMap I 0 q' q' (twistedDegree_zero q')
        ⟨(reesConst I (b ^ c) : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩ :=
  (geometricFactorFormulaMap_comp A (blowUpOver I)
        (twistScalarSheafMap (reesGrading I) c q' q hq
          ⟨(reesDegOne I hb : reesAlgebra I) ^ c, reesDegOnePow_mem_reesGrading I hb c⟩)
        (twistDownMap I q q' hle)).symm.trans
    (geometricFactorFormulaMap_congr A (blowUpOver I)
      (twistScalarSheafMap_reesDegOnePow_comp_twistDownMap I c q q' hq hle hb))

/-- **Twisting down `c` steps followed by multiplication by `(b⁽¹⁾)^c` is multiplication by
`b^c`, inside the geometric factor `N ↦ 𝒪_X(q) ⊗ p^*Ñ`.** -/
theorem twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow (c : ℕ) (q q' : ℤ)
    (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A} (hb : b ∈ I) :
    twistDownFactorMap I q q' hle ≫
        twistScalarFactorMap I c q' q hq
          ⟨(reesDegOne I hb : reesAlgebra I) ^ c, reesDegOnePow_mem_reesGrading I hb c⟩ =
      twistScalarFactorMap I 0 q q (twistedDegree_zero q)
        ⟨(reesConst I (b ^ c) : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩ :=
  (geometricFactorFormulaMap_comp A (blowUpOver I) (twistDownMap I q q' hle)
        (twistScalarSheafMap (reesGrading I) c q' q hq
          ⟨(reesDegOne I hb : reesAlgebra I) ^ c,
            reesDegOnePow_mem_reesGrading I hb c⟩)).symm.trans
    (geometricFactorFormulaMap_congr A (blowUpOver I)
      (twistDownMap_comp_twistScalarSheafMap_reesDegOnePow I c q q' hq hle hb))

end Stacks.Blowup

end
