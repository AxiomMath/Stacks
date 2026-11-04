module

public import Mathlib.Algebra.CharP.LinearMaps

/-! # Characteristic of linear maps -/

@[expose] public section

namespace Module

/-- If `R` is a commutative integral domain of characteristic `p` and `M` is a nontrivial
torsion-free `R`-module, then the `R`-linear endomorphism ring of `M` also has characteristic
`p`. -/
instance charP_end' (R M : Type*) [CommSemiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    (p : ℕ) [CharP R p] [Module.IsTorsionFree R M] [Nontrivial M] :
    CharP (M →ₗ[R] M) p :=
  let ⟨x, hx⟩ := exists_ne (0 : M)
  Module.charP_end ⟨x, by simpa⟩

end Module
