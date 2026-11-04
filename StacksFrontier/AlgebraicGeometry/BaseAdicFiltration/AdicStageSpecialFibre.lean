module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageEndpoints

/-!
# The special fibre inside each stage of the adic tower

Let `p : U ⟶ Spec A` be a morphism of schemes, `I` an ideal of `A`, and `i_X : X ⟶ U` a closed
immersion whose ideal sheaf is `I 𝒪_U`. Since `Iⁿ⁺¹𝒪_U ≤ I 𝒪_U`, the closed immersion `i_X`
factors through the stage `n` of the `I`-adic tower of `p` for every `n`. This file constructs
this factorization `i_{X,n} : X ⟶ Uₙ` and proves that it is a closed immersion compatible with
the steps of the tower.

## Main definitions

* `Stacks.BaseAdicFiltration.adicStageLift`: the closed immersion of `X` into the stage `n`.

## Main results

* `Stacks.BaseAdicFiltration.adicStageLift_comp_adicStageι`: the inclusion of `X` into the stage
  `n` followed by the closed immersion of the stage into `U` is `i_X`.
* `Stacks.BaseAdicFiltration.isClosedImmersion_adicStageLift`: the inclusion is a closed
  immersion.
* `Stacks.BaseAdicFiltration.adicStageLift_comp_adicStageSucc`: the inclusion into the stage `n`
  followed by the step of the tower is the inclusion into the stage `n + 1`.
* `Stacks.BaseAdicFiltration.adicStageLift_zero`: at the bottom stage the inclusion is the
  identification `Stacks.BaseAdicFiltration.adicStageZeroIso`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U X : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (iX : X ⟶ U) [IsClosedImmersion iX] (hk : iX.ker = baseIdeal p I)

/-- **A stage of the adic tower contains the special fibre.** The ideal sheaf `Iⁿ⁺¹𝒪_U` cutting
out the stage `n` is contained in the ideal sheaf `I 𝒪_U` cutting out the special fibre. -/
theorem ker_adicStageι_le (n : ℕ) : (adicStageι p I n).ker ≤ baseIdeal p I := by
  rw [ker_adicStageι]
  refine le_trans (Stacks.Thickenings.idealSheaf_pow_le_pow_right (Nat.succ_le_succ n.zero_le)) ?_
  rw [pow_one]

include hk in
/-- If the ideal sheaf of `i_X` is `I 𝒪_U`, then the ideal sheaf `Iⁿ⁺¹𝒪_U` of the stage `n` is
contained in the ideal sheaf of `i_X`. -/
theorem ker_adicStageι_le_ker (n : ℕ) : (adicStageι p I n).ker ≤ iX.ker := by
  rw [hk]
  exact ker_adicStageι_le p I n

/-- **The special fibre, as a closed subscheme of the stage `n` of the adic tower.** A closed
immersion `i_X : X ⟶ U` whose ideal sheaf is `I 𝒪_U` factors through every stage of the `I`-adic
tower, because the stage is cut out by the smaller ideal sheaf `Iⁿ⁺¹𝒪_U`. -/
def adicStageLift (n : ℕ) : X ⟶ adicStage p I n :=
  IsClosedImmersion.lift (adicStageι p I n) iX (ker_adicStageι_le_ker p I iX hk n)

/-- The inclusion of the special fibre into a stage is a morphism over `U`. -/
@[simp]
theorem adicStageLift_comp_adicStageι (n : ℕ) :
    adicStageLift p I iX hk n ≫ adicStageι p I n = iX :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inclusion of the special fibre into a stage of the adic tower is a closed immersion. -/
theorem isClosedImmersion_adicStageLift (n : ℕ) :
    IsClosedImmersion (adicStageLift p I iX hk n) := by
  have : IsClosedImmersion (adicStageLift p I iX hk n ≫ adicStageι p I n) := by
    rw [adicStageLift_comp_adicStageι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (adicStageι p I n)

/-- The inclusion of the special fibre into a stage is a morphism over the base. -/
@[simp]
theorem adicStageLift_comp_adicStageToBase (n : ℕ) :
    adicStageLift p I iX hk n ≫ adicStageToBase p I n = iX ≫ p := by
  rw [adicStageToBase, ← Category.assoc, adicStageLift_comp_adicStageι]

/-- **The inclusions of the special fibre are compatible with the steps of the tower.** Including
`X` into the stage `n` and then stepping up to the stage `n + 1` is including `X` into the stage
`n + 1`. -/
@[simp]
theorem adicStageLift_comp_adicStageSucc (n : ℕ) :
    adicStageLift p I iX hk n ≫ adicStageSucc p I n = adicStageLift p I iX hk (n + 1) := by
  rw [← cancel_mono (adicStageι p I (n + 1)), Category.assoc, adicStageSucc_comp_adicStageι,
    adicStageLift_comp_adicStageι, adicStageLift_comp_adicStageι]

/-- **At the bottom the inclusion is the identification of the special fibre.** -/
theorem adicStageLift_zero :
    adicStageLift p I iX hk 0 = (adicStageZeroIso p I iX hk).hom :=
  rfl

end Stacks.BaseAdicFiltration

end
