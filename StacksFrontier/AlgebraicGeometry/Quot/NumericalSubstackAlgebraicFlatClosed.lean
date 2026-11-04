module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackOpenClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# `Coh^P_{X/B}` is an algebraic stack, and `Coh^P_{X/B} ⟶ Coh_{X/B}` a flat closed immersion

In Situation 0DNC let `f : X ⟶ B` be separated and of finite presentation, let `E_i`, `i ∈ I`, be
perfect objects of `D(𝒪_X)` and `P : I → ℤ`. **Stacks 0DND**, first part: the substack
`Coh^P_{X/B} ⊆ Coh_{X/B}` of the objects `(T, 𝓕)` with `χ_i(t) = P(i)` for all `i` and `t` is an
algebraic stack, and its inclusion into `Coh_{X/B}` is a flat closed immersion.

The inclusion is representable by algebraic spaces, a closed immersion and flat
(`AlgebraicGeometry.Space.NumericalSituation.numericalSubstackι_isFlatClosedImmersion`), and
`Coh_{X/B}` is an algebraic stack for `f` separated and of finite presentation
(`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG`, Stacks 09DS), so
`Coh^P_{X/B}` is algebraic by Stacks 05UM
(`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_conditionCFG`).

## Main results

* `NumericalSituation.isAlgebraicStack_and_numericalSubstackι_isFlatClosedImmersion`:
  `Coh^P_{X/B}` is an algebraic stack and `Coh^P_{X/B} ⟶ Coh_{X/B}` is a flat closed immersion.

The two remaining cases of Stacks 0DND, `I` finite and `B` locally Noetherian, are
`NumericalSituation.numericalSubstackι_isOpenAndClosedImmersion_of_finite` and
`NumericalSituation.numericalSubstackι_isOpenAndClosedImmersion_of_isLocallyNoetherian`.

## Implementation notes

"Algebraic stack" is `AlgebraicGeometry.Stack.IsAlgebraicStack` (Stacks 026O), at an arbitrary
descent universe `w`, for the full subcategory `Coh^P_{X/B}` of `Coh_{X/B}` as a category over the
big fppf site of `S`. The separatedness of `f` is the field
`AlgebraicGeometry.Space.NumericalSituation.separated` of the standing data of Situation 0DNC.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.NumericalSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} (N : NumericalSituation.{u, v, u} B S hS D)

/-- In Situation 0DNC the substack `Coh^P_{X/B}` of `Coh_{X/B}` cut out by `χ_i = P(i)` is an
algebraic stack, and its inclusion into `Coh_{X/B}` is a flat closed immersion: representable by
algebraic spaces, a closed immersion and flat (Properties of Stacks, Section 04XB). -/
@[stacks 0DND "Coh^P_{X/B} is algebraic and Coh^P_{X/B} -> Coh_{X/B} is a flat closed immersion"]
theorem isAlgebraicStack_and_numericalSubstackι_isFlatClosedImmersion :
    Stack.IsAlgebraicStack.{u, w} B S hS
        (D.conditionCFG N.HasNumericalInvariants N.hasNumericalInvariants_inherited).val ∧
      Stack.IsRepresentableByAlgebraicSpaces B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited).hom ∧
      Stack.IsClosedImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) ∧
      Stack.IsFlat B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) :=
  ⟨N.isAlgebraicStack_conditionCFG_hasNumericalInvariants N.hasNumericalInvariants_inherited
      (fun φ i t => N.numericalEuler_eq_of_hom φ i t) N.isLocallyConstant_numericalEuler
      (D.isAlgebraicStack_coherentCFG N.separated),
    N.numericalSubstackι_isFlatClosedImmersion⟩

end AlgebraicGeometry.Space.NumericalSituation

end
