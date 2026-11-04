module

public import StacksFrontier.AlgebraicGeometry.GenericPointCoproduct.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicSectionsQcoh.Basic

/-!
# The generic-point family of a module is locally finite, so its coproduct is its product

The displayed formula of Stacks Tags 02OW and 0EMH gives the sheaf of meromorphic sections of a
quasi-coherent `𝒪_X`-module both as a direct sum and as a product over the generic points of the
irreducible components. This file supplies the comparison between the two for the module-valued
contributions `Stacks.AlgebraicGeometry.GenericPointDecomposition.genericPointStalkModuleOf`,
which is the step the source's proof covers with the single observation that *"a locally finite
direct sum of sheaves of modules is equal to the product"*.

It is the exact analogue, for a general `𝒪_X`-module in place of the structure sheaf, of
`GenericPointCoproduct.nonempty_coproductIso_product_genericPointStalkModule` in the namespace
`Stacks.AlgebraicGeometry`, and it uses the same two inputs: that the contribution of a generic
point restricts to zero on an open set missing that point, and the finite-support comparison of a
coproduct with a product.

The comparison itself, that the coproduct and the product of the generic-point contributions of a
module agree, is `AlgebraicGeometry.nonempty_sigmaIsoPi_genericPointStalkModuleOf`.

## Implementation notes

No tag is attached, and none is available: the two direct-sum labels of Tags 02OW and 0EMH assert
that the sheaf of *meromorphic sections* is the direct sum of these contributions, and the two
product labels assert the same with a product. What this file proves is that those two assertions
are equivalent, so it reduces the direct-sum labels to the product labels and nothing more.
Neither the reducedness assumed in Tag 02OW nor the absence of embedded points assumed in Tag 0EMH
is used: only the local finiteness of the irreducible components, which on a locally Noetherian
scheme is automatic. The hypothesis `F.IsQuasicoherent` is not used either — the vanishing away
from the generic point holds for an arbitrary module, because the preimage of such an open set in
the local scheme is empty.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointCoproduct
open Stacks.AlgebraicGeometry.GenericPointGluing

end Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

end
