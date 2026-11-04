module

public import Mathlib.RingTheory.PicardGroup
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Invertible

/-!
# Invertible and trivial modules

An *invertible* module over a commutative ring is one that is invertible for the tensor
product; equivalently, its associated sheaf on the spectrum is an invertible sheaf. A *trivial*
module is one isomorphic to the ring itself as a module.

`Module.Invertible` records invertibility through the canonical evaluation map from the dual
tensor the module into the ring, which is equivalent to the source's condition that the
associated sheaf on the spectrum be locally isomorphic to the structure sheaf.
`Module.IsTrivialInvertibleModule` records the required module isomorphism directly.

## References

* [Stacks Project, Tag 02AG](https://stacks.math.columbia.edu/tag/02AG)
-/

add_to_stacks 02AG "invertible modules" Module.Invertible
add_to_stacks 02AG "trivial modules" Module.IsTrivialInvertibleModule
