module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomLeftExact

/-!
# Exactness of internal Hom in its second variable

Let `(C, O)` be a ringed site and `F` a sheaf of `O`-modules. Stacks 0GMY says that an exact
sequence `0 → G → G₁ → G₂` of sheaves of `O`-modules induces an exact sequence

`0 → Hom_O(F, G) → Hom_O(F, G₁) → Hom_O(F, G₂)`

of sheaves of `O`-modules. This is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomLeftExact`:
internal Hom in the second variable commutes with limits, hence with kernels, and a left-exact
additive functor between abelian categories carries a left-exact sequence to a left-exact one.
This file records the Stacks tag against those two declarations and introduces no mathematics
of its own.

## Main results

The tag 0GMY is recorded against

* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_map_mono`, the initial zero of
  the target sequence;
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_exact`, exactness at the middle
  term.

## References

* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN), the limit-preservation
  property the proof uses.
-/

@[expose] public section

namespace Stacks.SheafOfModules.InternalHom

add_to_stacks 0GMY "exact_second_argument" internalHomSecondFunctor_map_mono
add_to_stacks 0GMY "exact_second_argument" internalHomSecondFunctor_exact

end Stacks.SheafOfModules.InternalHom
