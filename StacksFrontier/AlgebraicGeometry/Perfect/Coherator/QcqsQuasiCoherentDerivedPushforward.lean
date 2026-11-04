module

public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence

/-!
# The unbounded derived direct image preserves quasi-coherence

`AlgebraicGeometry.PreservesQuasicoherentOnCompactTarget` — the assertion that `Rf_*` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)` for every quasi-compact quasi-separated morphism of schemes with
quasi-compact quasi-separated target — is discharged here, and with it the affine-local reduction
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_compactTarget` becomes an unconditional
statement about an arbitrary quasi-compact quasi-separated morphism, namely
`AlgebraicGeometry.isQuasicoherent_derivedPushforward`.

The input is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`, part (1) of
[Stacks, Tag 08D5] for a quasi-compact quasi-separated morphism with quasi-compact target. Only
quasi-compactness of the target is used; the quasi-separatedness of the target carried by
`AlgebraicGeometry.PreservesQuasicoherentOnCompactTarget` is not needed.

## Main results

* `AlgebraicGeometry.preservesQuasicoherentOnCompactTarget`: the hypothesis, discharged.

## Implementation notes

The two spellings of the unbounded derived direct image —
`AlgebraicGeometry.RingedSpace.derivedPushforward` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` — are the same total right
derived functor of degreewise pushforward and are definitionally equal, as are the two spellings
of the category of `𝒪_X`-modules; the statements below cross between them by `exact`, exactly as
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_isAffineHom` does for the affine case.

**No `@[stacks 08D5]` attribute is placed.** Parts (1) and (2) of the tag are now available —
part (1) through the hypothesis discharged here and in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardQuasiCoherence.lean`, part
(2) as `AlgebraicGeometry.exists_isLE_derivedPushforward_obj` — but part (3), that the integer
`N` of part (2) survives an arbitrary base change `S' → S`, is not: it is clause (3) of
[Stacks, Tag 01XJ] transported along the base change, and only the absolute form of that clause
is proved, namely
`Stacks.Cohomology.AffineCover.exists_isZero_hgroup_preimage_of_isBasis`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- **The unbounded derived direct image preserves quasi-coherent cohomology over a
quasi-compact target.** This discharges
`AlgebraicGeometry.PreservesQuasicoherentOnCompactTarget`.

It is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`, part (1) of
[Stacks, Tag 08D5], restated for `AlgebraicGeometry.RingedSpace.derivedPushforward` and for the
object property defining `AlgebraicGeometry.QuasicoherentDerivedCategory`. -/
public theorem preservesQuasicoherentOnCompactTarget :
    PreservesQuasicoherentOnCompactTarget.{u} := by
  intro X S f hqc hqs hcs _ E n
  let _ : QuasiCompact f := hqc
  let _ : QuasiSeparated f := hqs
  let _ : CompactSpace S := hcs
  exact isQuasicoherent_homologyFunctor_derivedPushforward f E.obj E.property n

end AlgebraicGeometry

end
