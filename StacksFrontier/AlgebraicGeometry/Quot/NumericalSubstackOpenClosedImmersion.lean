module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentConditionSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackNoetherianDescent
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImagePerfect
public import StacksCore.Tactic.StacksAttribute

/-!
# The substack `Coh^P_{X/B}` of `Coh_{X/B}`

Let `f : X ⟶ B` be separated and of finite presentation, let `E_i`, `i ∈ I`, be perfect objects
of `D(𝒪_X)` and `P : I → ℤ`. The substack `Coh^P_{X/B} ⊆ Coh_{X/B}` consists of the objects
`(T, 𝓕)` with `χ_i(t) = P(i)` for all `i ∈ I` and all `t ∈ |T|`. Its inclusion
`Coh^P_{X/B} ⟶ Coh_{X/B}` is a flat closed immersion, and an open and closed immersion when `I`
is finite or `B` is locally Noetherian.

## Main results

* `numericalSubstackι_isFlatClosedImmersion`: `Coh^P_{X/B} ⟶ Coh_{X/B}` is representable by
  algebraic spaces, a closed immersion and flat.
* `numericalSubstackι_isOpenAndClosedImmersion_of_finite`: for `I` finite,
  `Coh^P_{X/B} ⟶ Coh_{X/B}` is representable by algebraic spaces, an open immersion and a closed
  immersion.
* `numericalSubstackι_isOpenAndClosedImmersion_of_isLocallyNoetherian`: the same for `B` locally
  Noetherian and `I` arbitrary.

## Implementation notes

The substack and its inclusion are `AlgebraicGeometry.Space.CoherentSituation.conditionCFG` and
`AlgebraicGeometry.Space.CoherentSituation.conditionι` at the condition
`AlgebraicGeometry.Space.NumericalSituation.HasNumericalInvariants`. Flatness, closed and open
immersions of 1-morphisms are `AlgebraicGeometry.Stack.IsFlat`,
`AlgebraicGeometry.Stack.IsClosedImmersion` and `AlgebraicGeometry.Stack.IsOpenImmersion`, and
"`B` locally Noetherian" is `AlgebraicGeometry.Space.IsLocallyNoetherian`.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 03E2](https://stacks.math.columbia.edu/tag/03E2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.NumericalSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} (N : NumericalSituation.{u, v, u} B S hS D)

/-- The condition `χ_i = P(i)` is inherited along the morphisms of `Coh_{X/B}`. -/
theorem hasNumericalInvariants_inherited {A' A : CoherentObject D} (φ : CoherentHom A' A) :
    N.HasNumericalInvariants A → N.HasNumericalInvariants A' :=
  N.hasNumericalInvariants_of_hom φ

/-- **`Coh^P_{X/B} ⟶ Coh_{X/B}` is a flat closed immersion.** The inclusion of the substack
`Coh^P_{X/B}` cut out by `χ_i = P(i)` is representable by algebraic spaces, a closed immersion and
flat. -/
theorem numericalSubstackι_isFlatClosedImmersion :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited).hom ∧
      Stack.IsClosedImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) ∧
      Stack.IsFlat B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) :=
  N.conditionι_hasNumericalInvariants_isFlatClosedImmersion N.hasNumericalInvariants_inherited
    (fun φ i t => N.numericalEuler_eq_of_hom φ i t) N.isLocallyConstant_numericalEuler

/-- If `I` is finite, `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`: its inclusion
is representable by algebraic spaces, an open immersion and a closed immersion. -/
@[stacks 0DND "the case I finite: Coh^P_{X/B} is an open and closed substack of Coh_{X/B}"]
theorem numericalSubstackι_isOpenAndClosedImmersion_of_finite [Finite N.I] :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited).hom ∧
      Stack.IsOpenImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) ∧
      Stack.IsClosedImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) :=
  N.conditionι_hasNumericalInvariants_isOpenAndClosedImmersion_of_finite
    N.hasNumericalInvariants_inherited (fun φ i t => N.numericalEuler_eq_of_hom φ i t)
    N.isLocallyConstant_numericalEuler

/-- If `B` is locally Noetherian (`hB`) and `I` is arbitrary, `Coh^P_{X/B}` is an open and closed
substack of `Coh_{X/B}`: its inclusion is representable by algebraic spaces, an open immersion and
a closed immersion. -/
@[stacks 0DND "the case B locally Noetherian: Coh^P_{X/B} is an open and closed substack of \
Coh_{X/B}"]
theorem numericalSubstackι_isOpenAndClosedImmersion_of_isLocallyNoetherian
    (hB : IsLocallyNoetherian B S hS D.Y.1) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited).hom ∧
      Stack.IsOpenImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) ∧
      Stack.IsClosedImmersion B S hS
        (D.conditionι N.HasNumericalInvariants N.hasNumericalInvariants_inherited) :=
  N.conditionι_hasNumericalInvariants_isOpenAndClosedImmersion_of_noetherianDescent
    N.hasNumericalInvariants_inherited (fun φ i t => N.numericalEuler_eq_of_hom φ i t)
    N.isLocallyConstant_numericalEuler (D.exists_noetherianDescent_of_isLocallyNoetherian hB)

end AlgebraicGeometry.Space.NumericalSituation

end
