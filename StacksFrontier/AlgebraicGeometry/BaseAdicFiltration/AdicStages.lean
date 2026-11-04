module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.Tower
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower

/-!
# The adic filtration of a family as a tower of square-zero steps

For `p : U ⟶ Spec A` and an ideal `I ⊆ A`, the ideal sheaf `I 𝒪_U`
(`Stacks.BaseAdicFiltration.baseIdeal`) has powers `Iⁿ⁺¹𝒪_U`, and each cuts a closed subscheme
out of `U`.  Consecutive subschemes are joined by a **first-order** thickening, because
`(Iⁿ⁺¹𝒪_U)² ≤ Iⁿ⁺²𝒪_U` (`Stacks.BaseAdicFiltration.baseIdeal_pow_sq_le_pow_succ`), and the
thickenings are compatible with the structure morphisms to `Spec A`.  So the filtration is a
tower of `Stacks.Thickenings.SquareZeroStep`s over the base.

This is the tower the essential-surjectivity direction of [Stacks, Tag 0E3X] runs its induction
along, upstairs: stage `n` is the closed subscheme of the family cut out by `𝔪ⁿ⁺¹`, stage `0` is
the special fibre, and over an Artinian local base the filtration reaches `U` itself
(`Stacks.BaseAdicFiltration.exists_adicFiltration_eq_bot_of_isArtinianRing` supplies the length).

## Main definitions

* `Stacks.BaseAdicFiltration.adicStage`: the closed subscheme of `U` cut out by `Iⁿ⁺¹𝒪_U`.
* `Stacks.BaseAdicFiltration.adicStageι` and `adicStageToBase`: its closed immersion into `U` and
  its structure morphism to `Spec A`.
* `Stacks.BaseAdicFiltration.adicStageSucc`: the inclusion of one stage into the next.
* `Stacks.BaseAdicFiltration.adicSquareZeroStep`: that inclusion as a square-zero step over
  `Spec A`.

## Main results

* `Stacks.BaseAdicFiltration.ker_adicStageι`: the stage is cut out by `Iⁿ⁺¹𝒪_U`, and
  `ker_adicStageι_zero` reads stage `0` as the special fibre, cut out by `I 𝒪_U`.
* `Stacks.BaseAdicFiltration.adicStageSucc_isFirstOrderThickening`: **each step is first
  order.**
* `Stacks.BaseAdicFiltration.adicStageSucc_comp_adicStageι`: the steps are compatible with the
  immersions into `U`, hence with the structure morphisms to the base.

## Implementation notes

The stage is `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` of the power, and the step is
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion` of the containment of ideal sheaves, so the
compatibilities are Mathlib's `ker_subschemeι` and `inclusion_subschemeι` and nothing is proved
chart by chart.  The order of the step is
`Stacks.Thickenings.isFirstOrderThickening_inclusion_of_sq_le`, whose hypothesis is exactly the
inequality `Stacks.BaseAdicFiltration.baseIdeal_pow_sq_le_pow_succ`.

Stage `0` is numbered so that it is the special fibre: the stages are indexed by the exponent
minus one, because `Stacks.BaseAdicFiltration.baseIdeal_pow_sq_le_pow_succ` needs a positive
exponent — the quotient by `I⁰𝒪_U = 𝒪_U` is not a square-zero extension of anything.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ)

/-- **The `n`-th stage of the adic filtration of a family.** It is the closed subscheme of `U`
cut out by `Iⁿ⁺¹𝒪_U`; stage `0` is the special fibre. -/
def adicStage : Scheme.{u} :=
  (baseIdeal p I ^ (n + 1)).subscheme

/-- The closed immersion of a stage of the adic filtration into the family. -/
def adicStageι : adicStage p I n ⟶ U :=
  (baseIdeal p I ^ (n + 1)).subschemeι

/-- The structure morphism of a stage of the adic filtration to the base. -/
def adicStageToBase : adicStage p I n ⟶ Spec (CommRingCat.of A) :=
  adicStageι p I n ≫ p

/-- **A stage is cut out by the corresponding power of `I 𝒪_U`.** -/
@[simp]
theorem ker_adicStageι : (adicStageι p I n).ker = baseIdeal p I ^ (n + 1) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- **Stage `0` is the special fibre**, cut out by `I 𝒪_U` itself. -/
theorem ker_adicStageι_zero : (adicStageι p I 0).ker = baseIdeal p I := by
  rw [ker_adicStageι, pow_one]

/-- The inclusion of one stage of the adic filtration into the next. -/
def adicStageSucc : adicStage p I n ⟶ adicStage p I (n + 1) :=
  Scheme.IdealSheafData.inclusion
    (Stacks.Thickenings.idealSheaf_pow_le_pow_right (I := baseIdeal p I)
      (Nat.le_succ (n + 1)))

/-- The steps of the tower are compatible with the immersions of the stages into the family. -/
@[simp]
theorem adicStageSucc_comp_adicStageι :
    adicStageSucc p I n ≫ adicStageι p I (n + 1) = adicStageι p I n :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- **Each step of the adic filtration is a first-order thickening.** The defining ideal sheaf of
`V(Iⁿ⁺²𝒪_U) ⊇ V(Iⁿ⁺¹𝒪_U)` has square zero because `(Iⁿ⁺¹𝒪_U)² ≤ Iⁿ⁺²𝒪_U`. -/
theorem adicStageSucc_isFirstOrderThickening :
    Stacks.Thickenings.IsFirstOrderThickening (adicStageSucc p I n) :=
  Stacks.Thickenings.isFirstOrderThickening_inclusion_of_sq_le _
    (baseIdeal_pow_sq_le_pow_succ p I (Nat.le_add_left 1 n))

/-- **One square-zero step of the adic filtration, over the base.** The stage `n` sits one
first-order thickening below the stage `n + 1`, compatibly with the two structure morphisms to
`Spec A`. -/
def adicSquareZeroStep :
    Stacks.Thickenings.SquareZeroStep (adicStageToBase p I n) (adicStageToBase p I (n + 1)) where
  immersion := adicStageSucc p I n
  isFirstOrder := adicStageSucc_isFirstOrderThickening p I n
  over_base := by
    rw [adicStageToBase, adicStageToBase, ← Category.assoc, adicStageSucc_comp_adicStageι]

/-- The immersion of the square-zero step of the adic filtration is the inclusion of one stage
into the next. -/
@[simp]
theorem adicSquareZeroStep_immersion :
    (adicSquareZeroStep p I n).immersion = adicStageSucc p I n :=
  rfl

end Stacks.BaseAdicFiltration

end
