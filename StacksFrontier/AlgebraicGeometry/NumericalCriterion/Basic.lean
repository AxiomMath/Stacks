module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Numerical
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.FiberCriterion
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Numerical
public import StacksFrontier.AlgebraicGeometry.Closure.Condition2
public import StacksFrontier.AlgebraicGeometry.Closure.Numerical
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Cotangent
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Dimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The numerical criterion for smoothness at a point

For a morphism `f : X ⟶ S` of schemes locally of finite presentation and a point `x` of `X`, the
following six conditions are equivalent: smoothness at `x`; flatness of the induced map of local
rings together with smoothness of the scheme-theoretic fibre; two numerical conditions on the
relative differentials; a standard smooth affine neighbourhood; and an affine presentation whose
chosen Jacobian minor does not vanish at `x`.

## Main results

* `Stacks.Tag01V9NumericalCriterion.condition4_imp_condition1`: condition (4) implies condition
  (1).
* `Stacks.Tag01V9NumericalCriterion.condition3_imp_condition1` and
  `Stacks.Tag01V9NumericalCriterion.condition4_imp_condition2`: condition (3) implies condition
  (1), and condition (4) implies condition (2).
* `Stacks.Tag01V9NumericalCriterion.smoothAt_tfae`: the six conditions are equivalent.
* `Stacks.Tag01V9NumericalCriterion.tfae_conditions`: the same, phrased with
  `Stacks.SmoothAtJacobian.conditions`.

## References

* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.SmoothAtJacobian
open scoped TensorProduct

universe u

namespace Stacks.Tag01V9NumericalCriterion

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- For a morphism locally of finite presentation, if the induced map of local rings at `x` is
flat and the residue-field fibre of the stalk of the relative differentials is generated over
`κ(x)` by at most `dim_x` elements — `dim_x` being the dimension at `x` of the scheme-theoretic
fibre through `x` — then `f` is smooth at `x`. -/
@[ega "IV 17.15.15" "sufficiency"]
public theorem condition4_imp_condition1 [LocallyOfFinitePresentation f] (h : Condition4 f x) :
    Condition1 f x := by
  obtain ⟨hflat, hgen⟩ := h
  obtain ⟨V, hV, hfxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hfxV
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have _ : Algebra.FinitePresentation Γ(S, V) Γ(X, U) := f.finitePresentation_appLE hV hU hUV
  have _ : Module.Flat Γ(S, V) (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :=
    Stacks.SmoothAtRingCriterion.flat_localizationAtPrime_of_flat_stalkMap f x ⟨U, hU⟩ ⟨V, hV⟩
      hxU hUV hflat
  refine (Stacks.SmoothAtRingCriterion.condition1_iff_isSmoothAt_appLE f x ⟨U, hU⟩ ⟨V, hV⟩
    hxU hUV).mpr (isSmoothAt_of_flat_of_finrank_le _ ?_)
  rw [← finrank_relativeCotangentSpace_eq_chart f x ⟨U, hU⟩ ⟨V, hV⟩ hxU hUV,
    ← fiberDimensionAt_eq_relativeDimensionAt f x ⟨U, hU⟩ ⟨V, hV⟩ hxU hUV]
  exact Stacks.Tag01V9Closure.finrank_le_of_generatedByAtMost hgen

/-- For a morphism locally of finite presentation, if the induced map of local rings at `x` is
flat and the stalk of the relative differentials is generated over the local ring by at most
`dim_x` elements, then `f` is smooth at `x`. -/
public theorem condition3_imp_condition1 [LocallyOfFinitePresentation f] (h : Condition3 f x) :
    Condition1 f x :=
  condition4_imp_condition1 f x (condition3_imp_condition4 f x h)

/-- For a morphism locally of finite presentation, if the induced map of local rings at `x` is
flat and the residue-field fibre of the stalk of the relative differentials is generated over
`κ(x)` by at most `dim_x` elements, then that map is flat and the scheme-theoretic fibre through
`x` is smooth at `x`. -/
public theorem condition4_imp_condition2 [LocallyOfFinitePresentation f] (h : Condition4 f x) :
    Condition2 f x :=
  condition1_imp_condition2 f x (condition4_imp_condition1 f x h)

/-- For a morphism locally of finite presentation, the following
are equivalent: smoothness at `x`; flatness of the local-ring map together with smoothness of the
scheme-theoretic fibre; either of the two numerical differential criteria; a standard smooth
affine neighbourhood; and an affine presentation whose chosen Jacobian determinant does not
vanish at `x`. -/
@[stacks 01V9]
public theorem smoothAt_tfae [LocallyOfFinitePresentation f] :
    List.TFAE [
      InfinitesimalLifting.SmoothAt f x,
      (f.stalkMap x).hom.Flat ∧
        InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x),
      (f.stalkMap x).hom.Flat ∧
        (let B := X.presheaf.stalk x
         let Ω := relativeDifferentialStalk f x
         letI := relativeDifferentialStalkModule f x
         GeneratedByAtMost B Ω (topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x))),
      (f.stalkMap x).hom.Flat ∧
        (let k := X.residueField x
         GeneratedByAtMost k (relativeCotangentSpace f x)
           (topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x))),
      ∃ (U : X.affineOpens) (V : S.affineOpens) (_ : x ∈ U.1)
          (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        AlgebraicGeometry.IsStandardSmooth (f.resLE V.1 U.1 hUV),
      ∃ (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1)
          (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V U hUV).hom.toAlgebra
        ∃ (n c : ℕ) (P : Algebra.PreSubmersivePresentation
            Γ(S, V.1) Γ(X, U.1) (Fin n) (Fin c)),
          P.jacobian ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal] := by
  tfae_have 1 ↔ 5 := condition1_iff_condition5 f x
  tfae_have 5 → 6 := condition5_imp_condition6 f x
  tfae_have 6 → 1 := condition6_imp_condition1 f x
  tfae_have 1 → 2 := condition1_imp_condition2 f x
  tfae_have 2 → 1 := Stacks.Tag01V9Closure.condition2_imp_condition1 f x
  tfae_have 1 → 3 := Stacks.RelativeDifferentialStalkMap.condition1_imp_condition3 f x
  tfae_have 3 → 4 := condition3_imp_condition4 f x
  tfae_have 4 → 1 := condition4_imp_condition1 f x
  tfae_finish

/-- For a morphism locally of finite presentation, the six conditions
`Stacks.SmoothAtJacobian.conditions` at `x` are equivalent. -/
public theorem tfae_conditions [LocallyOfFinitePresentation f] :
    (conditions f x).TFAE :=
  smoothAt_tfae f x

end Stacks.Tag01V9NumericalCriterion

end
