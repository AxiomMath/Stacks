module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Base change of a first-order thickening of algebraic stacks (Stacks 0BPR)

Stacks 0BPR reads, verbatim:

> Let `𝒴 ⊂ 𝒴'` be a thickening of algebraic stacks. Let `𝒳' → 𝒴'` be a morphism of algebraic
> stacks and set `𝒳 = 𝒴 ×_{𝒴'} 𝒳'`. Then `(𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` is a morphism of thickenings.
> If `𝒴 ⊂ 𝒴'` is a first order thickening, then `𝒳 ⊂ 𝒳'` is a first order thickening.

The first sentence is `AlgebraicGeometry.Stack.isThickening_baseChange` together with
`AlgebraicGeometry.Stack.baseChangeThickeningMorphism`. This module proves the second:
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFirstOrderThickening` (**Stacks 0BPQ**) is a closed
immersion together with the condition of **Stacks 04XB** that the base change along every
scheme-valued point be a first-order thickening of algebraic spaces, and both halves are stable
under base change.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFirstOrderThickening_fst_of_isTwoFibreProduct`:
  the second sentence of **Stacks 0BPR**.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0BPQ](https://stacks.math.columbia.edu/tag/0BPQ)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `𝒴 ⊂ 𝒴'` is a first-order thickening of algebraic
stacks over `S` and `𝒳 = 𝒴 ×_{𝒴'} 𝒳'` for a 1-morphism `g : 𝒳' ⟶ 𝒴'`, then `𝒳 ⊂ 𝒳'` — the
projection `P.fst` — is a first-order thickening. -/
@[stacks 0BPR "first order thickening base-changes to a first order thickening"]
theorem isFirstOrderThickening_fst_of_isTwoFibreProduct
    {𝒴 𝒴' 𝒳' : Stack.AlgebraicStacks.{u, w} B S hS} {j : 𝒴 ⟶ 𝒴'} {g : 𝒳' ⟶ 𝒴'}
    (hj : IsFirstOrderThickening B S hS j)
    (P : Bicategory.TwoCommSq g j) (hP : Bicategory.IsTwoFibreProduct P) :
    IsFirstOrderThickening B S hS P.fst :=
  ⟨isClosedImmersion_baseChange B S hS P hP hj.1,
    Stack.prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS
      (fun _ Y m => Space.IsFirstOrderThickening B S hS Y (Subfunctor.range m.hom))
      𝒴.val 𝒴'.val 𝒳'.val j.hom g.hom
      (toCatFiberedInGroupoids B S hS P)
      (isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP) hj.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
