module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of projective modules

Let `R` be a commutative ring and `P` a projective `R`-module. Then every exterior power
`⋀[R]^n P` is a projective `R`-module. Indeed `P` is a direct summand of the free module
`P →₀ R`, through a section `s` of `Finsupp.linearCombination R id`, and the exterior power
functor carries this splitting to a splitting of `⋀[R]^n P` off the exterior power of a free
module, which is free (`exteriorPower.instFree`).

## Main results

* `exteriorPower.instProjective`: the exterior powers of a projective module are projective.
-/

@[expose] public section

/-- The exterior powers of a projective module are projective: they are direct summands of the
exterior powers of a free module. -/
instance exteriorPower.instProjective {R : Type*} [CommRing R] {P : Type*} [AddCommGroup P]
    [Module R P] [Module.Projective R P] (n : ℕ) : Module.Projective R (⋀[R]^n P) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R P)
  have := exteriorPower.instFree R (M := P →₀ R) n
  exact Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id))
    (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])

end
