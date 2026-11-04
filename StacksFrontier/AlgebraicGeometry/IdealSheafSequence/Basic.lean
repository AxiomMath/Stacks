module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0C6K: the ideal sequence of a closed subscheme

For a closed subscheme `D` of a scheme `X` the canonical sequence

`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`

is short exact, where `i : D ⟶ X` is the inclusion and `ℐ_D` is the ideal sheaf. In the
decomposition of Stacks Tag 0C6K this is the label `divisor_ideal_sequence`: Tag 0C6K is the
ideal sequence of an *effective Cartier divisor*, whose negative twist `𝒪_X(-D)` **is** the ideal
sheaf, so the sequence holds for every closed subscheme and the effective-Cartier hypothesis is
not needed for this conclusion.

## Main definitions

* `Stacks.IdealSheafSequence.divisorQuotientMap`: the restriction `𝒪_X ⟶ i_* 𝒪_D`.
* `Stacks.IdealSheafSequence.divisorIdealMap`: the inclusion `ℐ_D ⟶ 𝒪_X`.

## Main results

* `Stacks.IdealSheafSequence.divisorIdeal_shortExact`: **the label
  `divisor_ideal_sequence` of Stacks Tag 0C6K.** The sequence above is short exact.

## Why short exactness is the whole content, and where it comes from

The ideal sheaf is *defined* as the kernel of `𝒪_X ⟶ i_* 𝒪_D`
(`Stacks.ClosedImmersion.idealSheaf`), so the left half of
the assertion is `CategoryTheory.kernel.condition` and the exactness at the middle is
`CategoryTheory.ShortComplex.shortExact_mk_kernel_ι` — provided the quotient arrow is an
epimorphism. That is the one real input,
and it is available: `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_
isClosedImmersion` supplies it for any closed immersion
of schemes, and `AlgebraicGeometry.IsClosedImmersion` of `D.subschemeι` is a Mathlib instance
(`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`). So the statement asserts that
*these particular arrows* form a short exact sequence, rather than that some short exact sequence
with these objects exists.

## Implementation notes

The arrows are written over `structureSheafRing X.toRingedSpace`, which is the
sheaf of rings `AlgebraicGeometry.Scheme.Modules` is itself defined over, because that is the
spelling in which the repository's ideal sheaf, its kernel inclusion and the epimorphism theorem
are all stated. Writing the arrows instead over `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`
names the same morphism of sheaves of rings but forces a transport that would have to be paid
for with a transparency option.

`SheafOfModules.unitToPushforwardObjUnit` is Mathlib's `𝒪_X ⟶ i_* 𝒪_D`; it is a morphism of
`𝒪_X`-modules because the `𝒪_D`-module structure on `i_* 𝒪_D` is restricted along `i^♯`.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.IdealSheafSequence

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- Restriction of the structure sheaf to a closed subscheme, pushed forward to the ambient
scheme: the arrow `𝒪_X ⟶ i_* 𝒪_D`. -/
abbrev divisorQuotientMap :
    SheafOfModules.unit (structureSheafRing X.toRingedSpace) ⟶
      (modulePushforward D.subschemeι.toLRSHom.toShHom).obj
        (SheafOfModules.unit (structureSheafRing D.subscheme.toRingedSpace)) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.subschemeι.toLRSHom.toShHom)

/-- **The quotient arrow is the one the source statement asks for, on the nose.**
The `divisor_ideal_sequence` label of Stacks Tag 0C6K writes it over
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, this file over
`RingedSpaceModuleAdjunction.structureSheafHom`; both are `Functor.whiskerRight` of the comparison
`i^♯` along `forget₂ CommRingCat RingCat`, so the two are the same morphism by `rfl`, with no
transport and no transparency option. This records it so that the attribute below is checkably on
the tag's assertion rather than on a variant of it. -/
theorem divisorQuotientMap_eq :
    SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom =
      divisorQuotientMap D :=
  rfl

/-- The inclusion of the ideal sheaf of a closed subscheme into the structure sheaf. The ideal
sheaf is the kernel of `𝒪_X ⟶ i_* 𝒪_D`, so this is the kernel inclusion. -/
abbrev divisorIdealMap :
    Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom ⟶
      SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  kernel.ι (divisorQuotientMap D)

/-- `𝒪_X ⟶ i_* 𝒪_D` is an epimorphism of `𝒪_X`-modules, for `i` the inclusion of a closed
subscheme. This is Stacks Tag 01QO's clause for a closed immersion of schemes, at the Mathlib
instance that makes `D.subschemeι` one. -/
instance epi_divisorQuotientMap : Epi (divisorQuotientMap D) :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
    D.subschemeι

/-- **Stacks Tag 0C6K, the label `divisor_ideal_sequence`.** For a closed subscheme `D` of a
scheme `X` with inclusion `i`, the canonical sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` of sheaves
of `𝒪_X`-modules is short exact.

The effective-Cartier hypothesis of Tag 0C6K is not used: it is what makes `ℐ_D` the invertible
module `𝒪_X(-D)`, and the exactness of the sequence does not depend on it. -/
@[stacks 0C6K "divisor_ideal_sequence", sga "6 X 5.2.2" "more general"]
theorem divisorIdeal_shortExact :
    ∃ hz : divisorIdealMap D ≫ divisorQuotientMap D = 0,
      (ShortComplex.mk (divisorIdealMap D) (divisorQuotientMap D) hz).ShortExact :=
  ⟨kernel.condition _, ShortComplex.shortExact_mk_kernel_ι _⟩

end Stacks.IdealSheafSequence

end
