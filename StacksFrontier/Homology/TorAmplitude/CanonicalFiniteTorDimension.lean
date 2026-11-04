module

public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
import all StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# Finite Tor dimension at the canonical derived tensor product, unfolded

Finite Tor dimension at the canonical derived tensor product
(`StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical`) is finite Tor dimension, Stacks 0652
(2), at the canonical certificate `(canonicalDerivedTensorProduct R, canonicalTensorComparison R)`.

## Main results

* `StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff`: finite Tor dimension at the
  canonical derived tensor product is finite Tor dimension at the canonical certificate.
-/

@[expose] public section

open CategoryTheory CochainComplex.DerivedTensor CochainComplex.DerivedTensor.KFlatDerived

namespace StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Finite Tor dimension at the canonical derived tensor product is finite Tor dimension at the
canonical certificate. -/
theorem hasFiniteTorDimensionCanonical_iff (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    HasFiniteTorDimensionCanonical R K ↔
      HasFiniteTorDimension (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) K :=
  Iff.rfl

end StacksDraft.TorAmplitude

end
