module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms between schemes étale over a common base

A morphism between two schemes étale over a common base, commuting with the structure morphisms,
is étale. This is `AlgebraicGeometry.etale_of_etale_over`, which also states part (10) of
Tag 03PC.

## References

* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
-/

add_to_stacks 03PC "morphism_over_base" AlgebraicGeometry.etale_of_etale_over
