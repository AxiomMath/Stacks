module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesBalanced
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedShortExact

/-!
# The middle-term inclusion of Stacks 0CTZ with balancedness discharged

`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedShortExact.lean` proves the middle-term
inclusion of Stacks 0CTZ with `CategoryTheory.Balanced` on the category of `𝒪_X`-modules as an
instance hypothesis.  That hypothesis is a theorem for sections in any universe containing the
universe of the schemes, `AlgebraicGeometry.Space.balanced_modules_max`, so this file states the
inclusion with nothing assumed beyond the source's own hypotheses.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_union_of_shortExact_unconditional`
  is **Stacks 0CTZ**, the middle-term inclusion, for a short exact sequence of `𝒪_X`-modules
  whose sections lie in any universe containing the universe of the schemes.

## References

* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **Stacks 0CTZ, second inclusion.** In a short exact sequence of `𝒪_X`-modules on an
algebraic space, every weakly associated point of the middle module is weakly associated to one
of the outer modules.

This is `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_union_of_shortExact` with its
balancedness instance supplied by `AlgebraicGeometry.Space.balanced_modules_max`: the `𝒪_X`-modules
with sections in a universe containing the universe of the schemes are abelian, the small étale
site being essentially small there, and an abelian category is balanced. -/
@[stacks 0CTZ "middle_term, for sections in any universe containing the universe of the \
schemes and with no assumed inputs: the balancedness of the category of modules that the \
general form takes as an instance hypothesis is discharged here"]
theorem weaklyAssociatedPoints_subset_union_of_shortExact_unconditional
    (σ : ShortComplex (Modules.{u, max u m} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    weaklyAssociatedPoints B S hS X σ.X₂ ⊆
      weaklyAssociatedPoints B S hS X σ.X₁ ∪ weaklyAssociatedPoints B S hS X σ.X₃ := by
  have := balanced_modules_max.{u, m} B S hS X
  exact weaklyAssociatedPoints_subset_union_of_shortExact B S hS X σ hσ

end AlgebraicGeometry.Space

end
