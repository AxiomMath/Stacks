module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BiproductSum
import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite Tor dimension of a derived direct image, read on the affine opens of the base

Locally finite Tor dimension of an object of `D(𝒪_S)` is a statement about *some* open cover of
`S`, so the affine opens of `S` may always be taken as that cover. For an object of the form
`Rf_*E` the restriction to an open `V ⊆ S` is `R(f|_V)_*(E|_{f^{-1}V})` by [Stacks, Tag 08FE], so
the whole statement reduces to a bound on each affine open of the base. This file carries out that
reduction.

The reduction is not formal, because the two restriction functors involved are not the same
*spelling*: `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` is defined through
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, while [Stacks, Tag 08FE] in the
scheme spelling (`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpensIso`) delivers
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The crossing on derived categories is
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`; what this file
adds is its consequence for the Tor-amplitude predicate, which is what the localisation needs.

## Main results

* `hasTorAmplitude_restrictModules_iff_restrictFunctor` and
  `hasFiniteTorDimension_restrictModules_iff_restrictFunctor`: the two spellings of restriction to
  an open subscheme give the same Tor amplitude, and the same finite Tor dimension.
* `locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor`: locally finite Tor
  dimension follows from finite Tor dimension of `E|_V` for every affine open `V`, with the
  restriction written in Mathlib's spelling.
* `locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen`: **the reduction.**
  `Rf_*E` is of locally finite Tor dimension as soon as `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor
  dimension on `V` for every affine open `V ⊆ S`. No hypothesis beyond the quasi-compactness and
  quasi-separatedness that `AlgebraicGeometry.derivedPushforwardModules` is stated under.

## Implementation notes

`AlgebraicGeometry.RingedSpace.derivedRestrictModules` is, *by `rfl`*,
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` mapped to derived categories —
that is `AlgebraicGeometry.RingedSpace.derivedRestrictModules_eq_mapDerivedCategory`, and it is
why no instance surgery is needed here: the natural isomorphism
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` already has the
left-hand side the predicate asks for, and only its component at `E` is taken.

`AlgebraicGeometry.derivedPushforwardModules` and `AlgebraicGeometry.schemeDerivedPushforward` are
the same functor, both being the total right derived functor of degreewise direct image followed
by localization; the statements below use the former, since that is the spelling
[Stacks, Tag 0B6G] is being assembled at, and hand it to [Stacks, Tag 08FE] directly.

No `@[stacks]` attribute is placed: no tag states this reduction. It is part (3) of
[Stacks, Tag 08CG] specialised to the affine opens as the cover, joined to [Stacks, Tag 08FE].

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open StrictlyPerfect AlgebraicGeometry
open Stacks.Cohomology.TorAmplitude

universe u

namespace Stacks.AlgebraicGeometry.PerfectProperDirectImage

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The two spellings of restriction to an open subscheme, on Tor amplitude -/

/-- **The two spellings of restriction to an open subscheme have the same Tor amplitude.** The
restriction of `E` to `V` computed with the ringed-space functor
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, which is the one
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` is defined through, has Tor
amplitude in `[a, b]` exactly when the restriction computed with Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along `V.ι` does.

The two functors on derived categories are identified by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`, and Tor amplitude is
invariant under isomorphism. -/
theorem hasTorAmplitude_restrictModules_iff_restrictFunctor (S : Scheme.{u}) (V : S.Opens)
    (E : DerivedCategory S.Modules) (a b : ℤ) :
    HasTorAmplitude (S.toRingedSpace.restrict V.isOpenEmbedding)
        ((RingedSpace.PseudoCoherence.restrictModules S.toRingedSpace V).mapDerivedCategory.obj E)
        a b ↔
      HasTorAmplitude (S.toRingedSpace.restrict V.isOpenEmbedding)
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) a b := by
  have e := (RingedSpace.derivedRestrictModulesIsoRestrictFunctor S V).app E
  exact ⟨fun h => FlatOpcycles.hasTorAmplitude_of_iso
      (X := S.toRingedSpace.restrict V.isOpenEmbedding) h e.symm,
    fun h => FlatOpcycles.hasTorAmplitude_of_iso
      (X := S.toRingedSpace.restrict V.isOpenEmbedding) h e⟩

/-- **The two spellings of restriction to an open subscheme have the same finite Tor dimension.**
-/
theorem hasFiniteTorDimension_restrictModules_iff_restrictFunctor (S : Scheme.{u}) (V : S.Opens)
    (E : DerivedCategory S.Modules) :
    HasFiniteTorDimension (S.toRingedSpace.restrict V.isOpenEmbedding)
        ((RingedSpace.PseudoCoherence.restrictModules S.toRingedSpace
          V).mapDerivedCategory.obj E) ↔
      HasFiniteTorDimension (S.toRingedSpace.restrict V.isOpenEmbedding)
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) :=
  ⟨fun ⟨a, b, h⟩ => ⟨a, b, (hasTorAmplitude_restrictModules_iff_restrictFunctor S V E a b).1 h⟩,
    fun ⟨a, b, h⟩ => ⟨a, b, (hasTorAmplitude_restrictModules_iff_restrictFunctor S V E a b).2 h⟩⟩

/-! ### Locally finite Tor dimension on the affine opens -/

/-- **Locally finite Tor dimension is affine-local, with the restriction in Mathlib's spelling.**
An object of `D(𝒪_Y)` on a scheme is of locally finite Tor dimension as soon as its restriction
along `V.ι` has finite Tor dimension for every affine open `V` of `Y`.

This is `locallyHasFiniteTorDimension_of_forall_affineOpen` with the hypothesis stated at the
spelling of restriction that the isomorphisms of this chapter produce, which is the form a
consumer actually has. -/
theorem locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor (Y : Scheme.{u})
    (E : DerivedCategory Y.Modules)
    (h : ∀ V : Y.affineOpens,
      HasFiniteTorDimension (Y.toRingedSpace.restrict (V : Y.Opens).isOpenEmbedding)
        ((Scheme.Modules.restrictFunctor (V : Y.Opens).ι).mapDerivedCategory.obj E)) :
    LocallyHasFiniteTorDimension Y.toRingedSpace E :=
  ⟨Y.affineOpens, fun V => (V : Y.Opens), iSup_affineOpens_eq_top Y,
    fun V => (hasFiniteTorDimension_restrictModules_iff_restrictFunctor Y (V : Y.Opens) E).2 (h V)⟩

/-- **The reduction of locally finite Tor dimension of a derived direct image to the affine opens
of the base.** Let `f : X ⟶ S` be quasi-compact and quasi-separated and let `E` be an object of
`D(𝒪_X)`. If for every affine open `V ⊆ S` the object `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor
dimension on `V`, then `Rf_*E` is of locally finite Tor dimension on `S`.

The affine opens cover `S` and locally finite Tor dimension asks for some cover, and
`(Rf_*E)|_V ≅ R(f|_V)_*(E|_{f^{-1}V})` is [Stacks, Tag 08FE], which this tree carries for
schemes and for an arbitrary object of `D(𝒪_X)` as
`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpensIso`.

This is the first step of the Tor-dimension half of [Stacks, Tag 08EV], and it assumes nothing
beyond what `AlgebraicGeometry.derivedPushforwardModules` is stated under. -/
theorem locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory X.Modules)
    (h : ∀ V : S.affineOpens,
      HasFiniteTorDimension (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
        ((schemeDerivedPushforward (f ∣_ (V : S.Opens))).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj E))) :
    LocallyHasFiniteTorDimension S.toRingedSpace ((derivedPushforwardModules f).obj E) :=
  locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor S _ fun V => by
    obtain ⟨a, b, hab⟩ := h V
    exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso
      (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hab
      (schemeDerivedPushforwardRestrictOpensIso f (V : S.Opens) E)⟩

end Stacks.AlgebraicGeometry.PerfectProperDirectImage

end
