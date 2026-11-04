module

public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification preserves finite colimits

The sheafification functor `presheafToSheaf J A : PSh(C) ⥤ Sh(C)`, `F ↦ F^#`, preserves finite
colimits, for sheaves with values in any category `A` admitting sheafification
(`HasWeakSheafify J A`). Together with `presheafToSheaf_preservesFiniteLimits`, which holds when
the plus construction is computed on underlying sets, this says that sheafification is exact.

## Main results

* `CategoryTheory.presheafToSheaf_preservesFiniteColimits`: sheafification preserves finite
  colimits.

## Implementation notes

`presheafToSheaf J A` is a left adjoint, by `sheafificationAdjunction`, and a left adjoint
preserves finite colimits.

## References

* [Stacks Project, Tag 00WJ](https://stacks.math.columbia.edu/tag/00WJ)
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

open Limits

/-- Sheafification `presheafToSheaf J A : PSh(C) ⥤ Sh(C)`, `F ↦ F^#`, preserves finite colimits,
for sheaves with values in any category `A` in which sheafification exists. -/
@[stacks 00WJ "Sheafification `PSh(C) → Sh(C)`, `F ↦ F^#`, is exact: it commutes with finite limits
  and with finite colimits. This is the right-exact half; the left-exact half is
  `presheafToSheaf_preservesFiniteLimits`.",
  sga "3 IV 4.4.1" "(iii)",
  sga "4 II 4.1" "partial, special case",
  sga "7 VI 3.1(a)" "partial"]
noncomputable instance presheafToSheaf_preservesFiniteColimits
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A] :
    PreservesFiniteColimits (presheafToSheaf J A) :=
  have : (presheafToSheaf J A).IsLeftAdjoint := (sheafificationAdjunction J A).isLeftAdjoint
  inferInstance

end CategoryTheory
