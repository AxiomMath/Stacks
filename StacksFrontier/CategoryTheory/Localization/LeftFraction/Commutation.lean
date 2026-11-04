module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import StacksFrontier.CategoryTheory.Localization.RightFraction.Commutation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localization at a left multiplicative system commutes with finite colimits (Stacks 05Q2)

Let `W` be a left multiplicative system on a category `C`, i.e. one with a left calculus of
fractions, and let `L : C ⥤ D` be a localization of `C` at `W`. Then `L` preserves finite
colimits; specialising to `L = W.Q` gives Stacks 05Q2. As for the dual statement, this does
not claim that `W⁻¹C` *has* finite colimits: only that a finite colimit cocone of `C` is
carried to a colimit cocone.

## Main results

* `CategoryTheory.MorphismProperty.preservesFiniteColimits_of_hasLeftCalculusOfFractions` and
  `CategoryTheory.MorphismProperty.Q_preservesFiniteColimits`: Stacks 05Q2.

## Implementation notes

The source proves this by the filtered-colimit computation of `Mor_{W⁻¹C}(Q X, Q Y)` and then
records the dual statement, Stacks 05Q6, as a formality. Here that argument is already carried
out on the limit side, in
`StacksFrontier/CategoryTheory/Localization/RightFraction/Commutation.lean`, so 05Q2 is obtained
by running the duality in the other direction: a left calculus of fractions on `W` is a right
calculus of fractions on `W.op` (Mathlib's instance for `MorphismProperty.op`), `L.op` is a
localization at `W.op` (`Functor.IsLocalization.op`), hence `L.op` preserves finite limits by
Stacks 05Q6, and a functor whose opposite preserves finite limits preserves finite colimits
(`Limits.preservesFiniteColimits_of_op`).
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

/-- A localization functor at a left multiplicative system preserves finite colimits. -/
@[sga "5 V 2.3.4" "more general"]
theorem preservesFiniteColimits_of_hasLeftCalculusOfFractions
    {C : Type*} [Category C] {D : Type*} [Category D]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] :
    Limits.PreservesFiniteColimits L :=
  have : Limits.PreservesFiniteLimits L.op :=
    preservesFiniteLimits_of_hasRightCalculusOfFractions W.op L.op
  Limits.preservesFiniteColimits_of_op L

/-- **Stacks 05Q2.** For a left multiplicative system `W` on `C`, the localization functor
`Q : C ⥤ W⁻¹C` commutes with finite colimits. This does not assert that `W⁻¹C` has finite
colimits: only that `Q` carries a finite colimit cocone of `C` to a colimit cocone. -/
@[stacks 05Q2, sga "5 V 2.3.4" "first assertion"]
theorem Q_preservesFiniteColimits
    {C : Type*} [Category C] (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] :
    Limits.PreservesFiniteColimits W.Q :=
  preservesFiniteColimits_of_hasLeftCalculusOfFractions W W.Q

end CategoryTheory.MorphismProperty
