module

public import Mathlib.CategoryTheory.Subobject.Comma

/-!
# An under category over a well-powered category is well-powered

For a well-powered, locally small, finitely complete category `C` and an object `S` of `C`, the
under category `CategoryTheory.Under S` is well-powered. It is the structured-arrow category
`CategoryTheory.StructuredArrow S (𝟭 C)`, to which `CategoryTheory.wellPowered_structuredArrow`
applies; instance search does not see through `CategoryTheory.Under`, so the instance is stated
for it directly.

## Main results

* `Stacks.UnderWellPowered.wellPowered`: `CategoryTheory.Under S` is `WellPowered.{w}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ w u₁

namespace Stacks.UnderWellPowered

/-- **An under category over a well-powered, locally small, finitely complete category is
well-powered.** -/
instance wellPowered {C : Type u₁} [Category.{v₁} C] (S : C) [LocallySmall.{w} C]
    [WellPowered.{w} C] [HasFiniteLimits C] : WellPowered.{w} (Under S) :=
  show WellPowered.{w} (StructuredArrow S (𝟭 C)) from inferInstance

end Stacks.UnderWellPowered
