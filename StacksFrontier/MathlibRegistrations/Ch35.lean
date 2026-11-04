module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.RingTheory.Flat.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations: Descent (Stacks Chapter 35)

Stacks tags from the chapter *Descent* whose statements Mathlib already proves,
recorded on the Mathlib declarations with `add_to_stacks`.

## References

* [Stacks Project, Chapter 35](https://stacks.math.columbia.edu/tag/0238)
-/

-- Definition: a split equalizer.
add_to_stacks 08WH
  "as a structure carrying `h` and `i`; 'is a split equalizer' is its `Nonempty`"
  CategoryTheory.IsSplitEqualizer

-- If `M` is a flat `R`-module, then `C(M) = Hom(M, ℚ/ℤ)` is an injective `R`-module.
add_to_stacks 08XC "Mathlib proves the equivalence, under `[Small.{v} R]`"
  Module.Flat.iff_characterModule_injective
add_to_stacks 08XC "universe-free form, with `Module.Baer.injective`"
  Module.Flat.iff_characterModule_baer
