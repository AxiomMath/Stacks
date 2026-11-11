module

public import StacksCore.RingTheory.FiniteStability
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a ring map and of a module

Stacks Definition 10.14.1 (tag 05G4): for a ring map `φ : R → S`, an `S`-module `M` and a ring
map `R → R'`, the base change of `φ` by `R → R'` is the ring map `R' → S' = S ⊗[R] R'`, and the
base change of `M` is the `S'`-module `M ⊗[R] R'`.

Both parts are registered here on existing declarations:

* the ring map is Mathlib's `Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R'`,
  `r' ↦ 1 ⊗ r'`;
* the `S'`-module structure on `M ⊗[R] R'` is `literalModule` (in
  `StacksCore.RingTheory.FiniteStability`), with `(s ⊗ r) • x = s • r • x` by
  `literalModule_smul_tmul`.
-/

add_to_stacks 05G4 "The base change of the ring map `R → S` by `R → R'` is the ring map
  `R' → S' = S ⊗[R] R'`, `r' ↦ 1 ⊗ r'`." Algebra.TensorProduct.includeRight

add_to_stacks 05G4 "The base change of the `S`-module `M` is the `S' = S ⊗[R] R'`-module
  `M ⊗[R] R'`." literalModule
