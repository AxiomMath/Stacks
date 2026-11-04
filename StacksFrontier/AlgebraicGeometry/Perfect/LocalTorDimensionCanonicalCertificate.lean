module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate

/-!
# Locally finite Tor dimension at the canonical certificate

Locally finite Tor dimension (part (3) of Stacks 08CG) has two forms:
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` asks finite Tor dimension on each
member of an open covering against a *certificate* for the derived tensor product, and
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` asks it against the derived tensor
product of Stacks 06YU. The first restricts `E` with
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the second with
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules |>.mapDerivedCategory`.

This file shows that these two restriction functors are equal, and that the two forms of
locally finite Tor dimension agree at the canonical certificate family.

## Main results

* `AlgebraicGeometry.RingedSpace.pseudoCoherenceRestrictModules_eq`: the two spellings of
  restriction of `𝒪_X`-modules to an open subspace are the same functor.
* `AlgebraicGeometry.RingedSpace.derivedRestrictModules_eq_mapDerivedCategory`: hence the same
  functor on derived categories.
* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`: at the
  canonical certificate family, locally finite Tor dimension is the pinned locally finite Tor
  dimension of `Stacks.Cohomology.TorAmplitude`.
* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq`: the same for any
  family of certificates whose underived tensor products are the genuine ones.

## Implementation notes

All universes of the ringed space and the module universe are equal: at that universe pattern
both spellings of the category of `𝒪_X`-modules are the same type.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect AlgebraicGeometry

universe d d' u

namespace AlgebraicGeometry.RingedSpace

/-! ### The two spellings of restriction to an open subspace -/

section Restriction

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- The two spellings of restriction of `𝒪_X`-modules to an open subspace `U` are the same
functor: the pushforward of sheaves of modules along the functor on opens induced by the
inclusion of `U`. -/
theorem pseudoCoherenceRestrictModules_eq :
    PseudoCoherence.restrictModules.{u, u} X U = restrictModules.{u, u} X U :=
  rfl

/-- Restriction to an open subspace preserves finite limits, at the
`AlgebraicGeometry.RingedSpace.PseudoCoherence` spelling. -/
local instance pseudoCoherenceRestrictModules_preservesFiniteLimits :
    PreservesFiniteLimits (PseudoCoherence.restrictModules.{u, u} X U) :=
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits X U

/-- Restriction to an open subspace preserves finite colimits, at the
`AlgebraicGeometry.RingedSpace.PseudoCoherence` spelling. -/
local instance pseudoCoherenceRestrictModules_preservesFiniteColimits :
    PreservesFiniteColimits (PseudoCoherence.restrictModules.{u, u} X U) :=
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteColimits X U

/-- Restriction `(·)|_U` on derived categories is the derived functor of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`. -/
theorem derivedRestrictModules_eq_mapDerivedCategory
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))] :
    derivedRestrictModules X U =
      (PseudoCoherence.restrictModules.{u, u} X U).mapDerivedCategory :=
  rfl

end Restriction

/-! ### Part (3) of Stacks 08CG at the canonical certificate -/

section Local

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- At the canonical certificate family, `E` has locally finite Tor dimension if and only if it
has locally finite Tor dimension in the sense of `Stacks.Cohomology.TorAmplitude`. -/
theorem locallyHasFiniteTorDimension_canonicalCertificate_iff
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X (canonicalCertifiedDerivedSheafTensoringFamily X) E ↔
      Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension X E :=
  Iff.rfl

/-- For a family `D` of certificates whose underived tensor products are those of the canonical
certificates, `E` has locally finite Tor dimension against `D` if and only if it has locally
finite Tor dimension in the sense of `Stacks.Cohomology.TorAmplitude`. -/
theorem locallyHasFiniteTorDimension_iff_of_tensor_eq
    (D : ∀ U : Opens X.carrier,
      CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding))
    (h : ∀ U : Opens X.carrier,
      (D U).tensor = (canonicalCertifiedDerivedSheafTensoringFamily X U).tensor)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X D E ↔
      Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension X E :=
  (locallyHasFiniteTorDimension_congr X D (canonicalCertifiedDerivedSheafTensoringFamily X) h
      E).trans
    (locallyHasFiniteTorDimension_canonicalCertificate_iff X E)

end Local

end AlgebraicGeometry.RingedSpace

end
