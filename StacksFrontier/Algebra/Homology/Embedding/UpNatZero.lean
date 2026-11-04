module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# The zeroth index of the embedding of `ℕ` into `ℤ`

`ComplexShape.embeddingUpNat` sends `n : ℕ` to `(n : ℤ)`, so it sends `0` to `0`. The fact is
one `rfl`, and it was being restated in seven modules; it lives here so that each of them can
use the one declaration.
-/

@[expose] public section

namespace ComplexShape

/-- The embedding of `ℕ` into `ℤ` sends `0` to `0`. -/
public theorem embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl

end ComplexShape

end
