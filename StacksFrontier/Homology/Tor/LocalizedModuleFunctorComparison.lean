module

public import StacksFrontier.Homology.ExtendScalars.Localization
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.BaseChangeTensorIsoSupplement

/-!
# The two localized-module functors agree over the base ring

Localization of modules at a submonoid `S` of a commutative ring `R` is carried by two functors
in this library.  Mathlib's `ModuleCat.localizedModuleFunctor` lands in
`ModuleCat (Localization S)` and has carrier `Shrink (LocalizedModule S M)`;
`CochainComplex.DerivedTensor.localizedModuleFunctor` is an endofunctor of `ModuleCat R` with the
literal `LocalizedModule S M` as carrier.  Restricting the first back along
`R ⟶ Localization S` makes the two comparable, and they then agree.

Both are needed as they stand: the derived statements about localizing cohomology are stated in
the second spelling, while the criterion that a map of modules is invertible exactly when all of
its localizations at primes are — hence the degreewise reading of condition (2) of Stacks 0DJ8 —
is stated in the first.  This module is the one step between them.

## Main definitions

* `StacksDraft.localizedModuleFunctorRestrictIso`: the two functors agree over `R`.

## Main results

* `StacksDraft.isIso_localizedModuleFunctor_map_iff`: a map of `R`-modules is inverted by one of
  the two functors exactly when it is inverted by the other.

## Implementation notes

The comparison is the composition of two isomorphisms already in the library:
`extendScalars_iso_localizedModuleFunctor` identifies extension of scalars along
`R ⟶ Localization S` with Mathlib's localized-module functor, and
`CochainComplex.DerivedTensor.extensionScalarsLocalizedModuleNatIso`, taken at
`A = Localization S`, identifies that same extension of scalars, restricted back to `R`, with the
endofunctor spelling.  Nothing is recomputed.

Invertibility transfers because restriction of scalars along a ring homomorphism does not change
the underlying map of a morphism of modules, so it reflects isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace StacksDraft

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- **The two localized-module functors agree over the base ring.** Mathlib's
`ModuleCat.localizedModuleFunctor S`, restricted from `Localization S` back to `R`, is the
endofunctor `CochainComplex.DerivedTensor.localizedModuleFunctor S` of `ModuleCat R`. -/
public def localizedModuleFunctorRestrictIso :
    ModuleCat.localizedModuleFunctor.{u} S ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap R (Localization S)) ≅
      CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S :=
  Functor.isoWhiskerRight (extendScalars_iso_localizedModuleFunctor.{u, u} S).symm
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R (Localization S))) ≪≫
    CochainComplex.DerivedTensor.extensionScalarsLocalizedModuleNatIso.{u, u, u}
      (A := Localization S) S

/-- **The two localized-module functors invert the same morphisms.** -/
public theorem isIso_localizedModuleFunctor_map_iff {M N : ModuleCat.{u} R} (ψ : M ⟶ N) :
    IsIso ((ModuleCat.localizedModuleFunctor.{u} S).map ψ) ↔
      IsIso ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map ψ) := by
  rw [← NatIso.isIso_map_iff (localizedModuleFunctorRestrictIso.{u} S) ψ,
    ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  rfl

end StacksDraft

end
