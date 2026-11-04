module

public import Mathlib.RingTheory.PicardGroup
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite locally free and invertible modules

A module over a commutative ring is *finite locally free* when it is finite free on a
neighbourhood of every prime of the base, and *invertible* when those local free modules have
rank one.

Both predicates already exist. `Module.IsFiniteLocallyFree` uses a family of basic opens
covering the spectrum, which is equivalent to choosing one basic neighbourhood at each prime,
and `Module.Invertible` records invertibility through the canonical contraction of the dual
tensor the module into the ring, which for a module over a commutative ring is the same as
being finite locally free of rank one.

## References

* [Stacks Project, Tag 027R](https://stacks.math.columbia.edu/tag/027R)
-/

add_to_stacks 027R "finite locally free modules" Module.IsFiniteLocallyFree
add_to_stacks 027R "invertible modules" Module.Invertible
