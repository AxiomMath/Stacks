module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DivisorTracePushforward

/-!
# The perfect pairing of axiom (A)(b) for data satisfying (A1)–(A7)

The pushforward `f_*` on the cohomology of the data `𝔚.toWeilData` of Section 0FHA defined by
data (D0), (D1), (D2') satisfying (A1)–(A7) is formed with the perfect pairing of axiom (A)(b),
which holds by Lemma 0FIJ (`Stacks.WeilCohomology.WeilChernData.poincareDuality`). This file
names that pairing once, so that the statements of Section 45.14 about pushforward share it.

## Main results

* `Stacks.WeilCohomology.WeilChernData.perfectPairing`: axiom (A)(b) for `𝔚.toWeilData`.
-/

@[expose] public noncomputable section

universe u w

namespace Stacks.WeilCohomology.WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Axiom (A)(b) for the data of `𝔚`** (Tag 0FIJ): for `X` nonempty and equidimensional of
dimension `d`, `H^i(X) × H^{2d-i}(X)(d) → F`, `(a, b) ↦ λ(a ∪ b)`, is a perfect pairing. -/
theorem perfectPairing : 𝔚.toWeilData.PerfectPairing :=
  𝔚.poincareDuality.perfectPairing

end Stacks.WeilCohomology.WeilChernData

end
