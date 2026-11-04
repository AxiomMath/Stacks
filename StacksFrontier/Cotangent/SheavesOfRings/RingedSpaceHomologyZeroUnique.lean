module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace

/-!
# Uniqueness of the identification `H⁰(L_{X/S}) ≅ Ω_{X/S}`

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` the canonical identification
`Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_homologyZeroIso` carries the universal
derivation of `H⁰(L_{X/S})` to the universal derivation `d : 𝒪_X ⟶ Ω_{X/S}`. That equation
determines it: already among *morphisms* `H⁰(L_{X/S}) ⟶ Ω_{X/S}` there is exactly one carrying
the universal derivation of the source to `d`, because `H⁰(L_{X/S})` corepresents the relative
derivations of `𝒪_X` over `f⁻¹𝒪_S` and the correspondence is a bijection.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_homologyZeroIso_hom_unique`: a morphism
  `H⁰(L_{X/S}) ⟶ Ω_{X/S}` carrying the universal derivation to `d` is the forward map of the
  canonical identification.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_homologyZeroIso_unique`: consequently an
  isomorphism `H⁰(L_{X/S}) ≅ Ω_{X/S}` carrying the universal derivation to `d` is the canonical
  identification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  moduleOfDifferentials universalDerivation)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

/-- A morphism `H⁰(L_{X/S}) ⟶ Ω_{X/S}` carrying the universal derivation of `H⁰(L_{X/S})` to the
universal derivation `d : 𝒪_X ⟶ Ω_{X/S}` is the forward map of the canonical identification. -/
theorem cotangentComplex_homologyZeroIso_hom_unique (f : X ⟶ S)
    (φ : (cotangentComplex f).homology 0 ⟶ moduleOfDifferentials f)
    (hφ : (CategoryTheory.Sheaf.homologyZeroDerivation (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f)).postcomp φ.val = universalDerivation f) :
    φ = (cotangentComplex_homologyZeroIso f).hom :=
  (CategoryTheory.Sheaf.derivationsFunctor_corepresentableBy
      (Opens.grothendieckTopology X.carrier)
      (inverseImageStructureMap f)).homEquiv.injective
    (hφ.trans (cotangentComplex_homologyZeroIso_hom_postcomp f).symm)

/-- An isomorphism `H⁰(L_{X/S}) ≅ Ω_{X/S}` carrying the universal derivation of `H⁰(L_{X/S})` to
the universal derivation `d : 𝒪_X ⟶ Ω_{X/S}` is the canonical identification. -/
theorem cotangentComplex_homologyZeroIso_unique (f : X ⟶ S)
    (e : (cotangentComplex f).homology 0 ≅ moduleOfDifferentials f)
    (he : (CategoryTheory.Sheaf.homologyZeroDerivation (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f)).postcomp e.hom.val = universalDerivation f) :
    e = cotangentComplex_homologyZeroIso f :=
  Iso.ext (cotangentComplex_homologyZeroIso_hom_unique f e.hom he)

end Stacks.Sheaves.RingedSpaceCotangent

end
