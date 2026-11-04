module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localizing a ring as a module over itself

For a prime `p` of `R`, the localization of `R` at `p` *as an `R`-module* is the localized ring
`R_p` itself, linearly over `R_p`.

## Main definitions

* `localizedModuleSelfEquivLocalization`: the equivalence
  `LocalizedModule T R ≃ₗ[Localization T] Localization T` at an arbitrary submonoid `T`.
* `localizedRingEquiv`: the equivalence `LocalizedModule.AtPrime p R ≃ₗ[R_p] R_p`, the case
  `T = R ∖ p`.

## Implementation notes

The equivalence was reproduced privately in two modules, one of which recorded in its own module
docstring that it was a duplicate "reproduced here because a `private` declaration cannot be used
from another module". It lives here instead, in a module importing only the two Mathlib files
that carry `LocalizedModule.equivTensorProduct` and
`TensorProduct.AlgebraTensorModule.rid`, both of which every host already has.
-/

@[expose] public section

/-- Localizing a ring at a submonoid, as a module over itself, gives the localized ring. -/
public noncomputable def localizedModuleSelfEquivLocalization {R : Type*} [CommRing R]
    (T : Submonoid R) :
    LocalizedModule T R ≃ₗ[Localization T] Localization T :=
  (LocalizedModule.equivTensorProduct T R).trans
    (TensorProduct.AlgebraTensorModule.rid R (Localization T) (Localization T))

/-- Localizing a ring at a prime, as a module over itself, gives the localized ring. -/
public noncomputable def localizedRingEquiv {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  localizedModuleSelfEquivLocalization p.primeCompl

end
