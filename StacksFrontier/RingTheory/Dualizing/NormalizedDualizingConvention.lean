module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# The normalization convention for a dualizing complex over a local ring

Let `(A, 𝔪, κ)` be a Noetherian local ring and let `ω_A^•` be a dualizing complex for `A`. The
derived Hom `RHom_A(κ, ω_A^•)` is the residue field placed in a single degree, and `ω_A^•` is
called *normalized* when that degree is zero, i.e. when `RHom_A(κ, ω_A^•) = κ[0]`. The
convention therefore fixes the one shift in which the comparison with the residue field is an
honest module in degree zero, so that for instance `RHom_A(κ[1], ω_A^•) = κ[-1]`.

The convention is a genuine normalization: a dualizing complex over a Noetherian local ring has
a normalizing shift (`Dualizing.exists_isNormalizedDualizingComplex_shift`), so every dualizing
complex is a shift of a normalized one, and that shift is unique
(`Dualizing.isNormalizedDualizingComplex_shift_iff_eq`).

## Main definitions

There are no definitions in this file; it attaches the tag of the convention to
`Dualizing.IsNormalizedDualizingComplex` and to the existence and uniqueness of the normalizing
shift, which are what make the convention well posed.

## Main results

There are no results in this file. The convention read **on cohomology** — that
`Ext^i_A(κ, ω_A^•)` vanishes for `i ≠ 0` when `ω_A^•` is normalized, and for `i ≠ dim(A)` when
`ω_A^•` is a dualizing *module* over a Cohen–Macaulay local ring, whose normalizing degree the
predicate `Stacks.Duality.IsDualizingRingModule` leaves existentially quantified — is
`Dualizing.subsingleton_ext_residueField_of_isNormalized` of
`…/RingTheory/Dualizing/NormalizedResidueFieldExt.lean` and
`Dualizing.subsingleton_ext_residueField_single_of_ne_localRingDimension` of
`…/RingTheory/Dualizing/CohenMacaulayNormalizedShift.lean`, which carry this tag as well.

## References

* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
-/

@[expose] public section

namespace Dualizing

add_to_stacks 0A7M "the normalization convention `RHom_A(κ, ω_A^•) = κ` in degree zero"
  Dualizing.IsNormalizedDualizingComplex
add_to_stacks 0A7M "every dualizing complex over a Noetherian local ring is a shift of a \
normalized one" Dualizing.exists_isNormalizedDualizingComplex_shift
add_to_stacks 0A7M "the normalizing shift is unique"
  Dualizing.isNormalizedDualizingComplex_shift_iff_eq

end Dualizing

end
