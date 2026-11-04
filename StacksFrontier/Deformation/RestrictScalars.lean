module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Semilinear additive maps as linear maps into a restriction of scalars

An additive map between modules that is semilinear along a ring homomorphism
`f : R →+* S` is the same datum as an `R`-linear map into the target read as an
`R`-module along `f`.

## Main definitions

* `Deformation.restrictAddHom`: the `R`-linear map `M →ₗ[R] N` carried by an additive
  map `M →+ N` that is semilinear along `f`, where `N` is given the `R`-module structure
  `Module.compHom N f`.
-/

@[expose] public section

namespace Deformation

/-- An additive map `g : M →+ N` satisfying `g (r • x) = f r • g x` along a ring
homomorphism `f : R →+* S`, regarded as a linear map into the restriction of scalars
`Module.compHom N f`. -/
def restrictAddHom {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (f : R →+* S) (g : M →+ N) (hg : ∀ r x, g (r • x) = f r • g x) :
    letI : Module R N := Module.compHom N f
    M →ₗ[R] N :=
  letI : Module R N := Module.compHom N f
  { g with map_smul' := hg }

end Deformation

end
