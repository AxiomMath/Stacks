module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

import StacksCore.Tactic.StacksAttribute

/-!
# The canonical isomorphisms of tensor products

Stacks 00CY: for `R`-modules `M`, `N`, `P` the bilinear maps `(x, y) ↦ y ⊗ x`,
`(x + y, z) ↦ x ⊗ z + y ⊗ z` and `(r, x) ↦ r x` induce unique isomorphisms
`M ⊗_R N ≅ N ⊗_R M`, `(M ⊕ N) ⊗_R P ≅ (M ⊗_R P) ⊕ (N ⊗_R P)` and `R ⊗_R M ≅ M`.

The three isomorphisms are Mathlib's `TensorProduct.comm`, `TensorProduct.prodLeft` (the direct
sum `M ⊕ N` being `M × N`) and `TensorProduct.lid`, and `TensorProduct.comm_tmul`,
`TensorProduct.prodLeft_tmul` and `TensorProduct.lid_tmul` are the three displayed formulas.
Uniqueness is Mathlib's `TensorProduct.ext'`: a linear map out of a tensor product is
determined by its values on pure tensors.
-/

@[expose] public section

-- The former @[stacks 00CY] theorems are the Mathlib isomorphisms together with their
-- values on pure tensors; uniqueness is `TensorProduct.ext'`.
add_to_stacks 00CY "the first isomorphism" TensorProduct.comm
add_to_stacks 00CY "the first isomorphism, on pure tensors" TensorProduct.comm_tmul
add_to_stacks 00CY "the second isomorphism" TensorProduct.prodLeft
add_to_ega "III 7.2.6" "special case" TensorProduct.prodLeft
add_to_stacks 00CY "the second isomorphism, on pure tensors" TensorProduct.prodLeft_tmul
add_to_stacks 00CY "the third isomorphism" TensorProduct.lid
add_to_stacks 00CY "the third isomorphism, on pure tensors" TensorProduct.lid_tmul
add_to_stacks 00CY "uniqueness of each of the three" TensorProduct.ext'

end
