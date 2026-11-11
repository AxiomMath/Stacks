module
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 09QG for an arbitrary direct sum, as a bicone `c` of `x`
    and `y` whose cone is a limit (resp. whose cocone is a colimit):
    `BinaryBicone.isLimitSndKernelFork` (`i = c.inl` is a kernel of `q = c.snd`) and
    `BinaryBicone.isColimitInrCokernelCofork` (`p = c.fst` is a cokernel of `j = c.inr`).

    The two older lines `add_to_stacks 09QG` in
    `StacksCore/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean`, on `kernelBiprodFstIso` and
    `cokernelBiproductιIso`, only identify chosen (co)kernel objects of the chosen biproduct, not
    the universal properties of `i` and `p`; a human reviewer of `StacksCore/` should drop them. -/

@[expose] public section

add_to_stacks 09QG "For a direct sum `c` of `x` and `y`, `i = c.inl` is a kernel of `q = c.snd`."
  CategoryTheory.Limits.BinaryBicone.isLimitSndKernelFork
add_to_stacks 09QG "For a direct sum `c` of `x` and `y`, `p = c.fst` is a cokernel of `j = c.inr`."
  CategoryTheory.Limits.BinaryBicone.isColimitInrCokernelCofork
