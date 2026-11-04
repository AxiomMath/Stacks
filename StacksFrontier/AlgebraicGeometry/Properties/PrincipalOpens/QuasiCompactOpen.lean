module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Quasi-coherent modules on a quasi-compact open of an affine scheme

Let `U` be a quasi-compact open subscheme of an affine scheme `Spec R`. For a
quasi-coherent module `F` on `U`, the canonical comparison map from the restriction to `U`
of the sheaf associated to the global sections of the pushforward of `F` is an
isomorphism.

## Main results

* `AlgebraicGeometry.isIso_pullback_fromTildeΓ`: the canonical comparison map is an
  isomorphism.

## Implementation notes

The canonical map is the pullback along the open inclusion of the comparison map
`Scheme.Modules.fromTildeΓ` for the pushforward of `F`, followed by the counit of the
pullback–pushforward adjunction. Global sections of the pushforward are the global
sections on the open subscheme, so this is exactly the comparison map of the statement
in the source.

## References

* [Stacks Project, Tag 0EHM](https://stacks.math.columbia.edu/tag/0EHM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a quasi-coherent module `F` on a quasi-compact open `U` of an affine scheme, the
canonical map to `F` from the restriction to `U` of the sheaf associated to the global sections
of `F` is an isomorphism. -/
@[stacks 0EHM]
theorem isIso_pullback_fromTildeΓ
    (R : CommRingCat.{u}) (U : (Spec R).Opens)
    (hU : IsCompact (U : Set (Spec R)))
    (F : U.toScheme.Modules) [F.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullback U.ι).map
      (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward U.ι).obj F)) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι).counit.app F) := by
  have : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.2))
  infer_instance

end AlgebraicGeometry
