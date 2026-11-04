module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.BaseChangeRule
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Uniqueness
import StacksCore.Tactic.StacksAttribute

/-!
# Trace maps on de Rham complexes: Stacks, Lemma 0FLB

There is a unique rule assigning to every finite syntomic morphism of schemes `f : Y ⟶ X` maps
of `𝒪_X`-modules `Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` satisfying

1. the composition with `Ω^p_{X/ℤ} ⊗_{𝒪_X} f_*𝒪_Y → f_*Ω^p_{Y/ℤ}` is `id ⊗ Trace_f`,
2. the rule is compatible with base change.

The two conditions are `AlgebraicGeometry.FormsTraceRule.IsTrace` and
`AlgebraicGeometry.FormsTraceRule.IsBaseChange`; the rule is `AlgebraicGeometry.formsTraceRule`,
`f ↦ AlgebraicGeometry.Scheme.Hom.formsTrace f`.

## Main results

* `AlgebraicGeometry.existsUnique_formsTraceRule`: **Stacks, Lemma 0FLB.**
* `AlgebraicGeometry.FormsTraceRule.eq_formsTraceRule`: every rule with (1) and (2) is
  `formsTraceRule`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks, Lemma 0FLB.** There exists a unique rule that to every finite syntomic morphism of
schemes `f : Y ⟶ X` assigns `𝒪_X`-module maps `Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` such that
(1) the composition with `Ω^p_{X/ℤ} ⊗_{𝒪_X} f_*𝒪_Y → f_*Ω^p_{Y/ℤ}` is `id ⊗ Trace_f`
(`FormsTraceRule.IsTrace`, on local sections `ω ⊗ b ↦ b · f^*ω`), and (2) the rule is compatible
with base change (`FormsTraceRule.IsBaseChange`). The rule is `formsTraceRule`. -/
@[stacks 0FLB]
theorem existsUnique_formsTraceRule :
    ∃! Θ : FormsTraceRule.{u}, Θ.IsTrace ∧ Θ.IsBaseChange :=
  ⟨formsTraceRule, ⟨formsTraceRule_isTrace, formsTraceRule_isBaseChange⟩,
    fun _ h => FormsTraceRule.eq_of_isTrace_of_isBaseChange h.1 h.2 formsTraceRule_isTrace
      formsTraceRule_isBaseChange⟩

/-- Every rule of trace maps on forms with properties (1) and (2) of Lemma 0FLB is
`formsTraceRule`. -/
theorem FormsTraceRule.eq_formsTraceRule {Θ : FormsTraceRule.{u}} (h₁ : Θ.IsTrace)
    (h₂ : Θ.IsBaseChange) : Θ = formsTraceRule :=
  FormsTraceRule.eq_of_isTrace_of_isBaseChange h₁ h₂ formsTraceRule_isTrace
    formsTraceRule_isBaseChange

end AlgebraicGeometry
