module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentHomologyZero
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree zero cohomology sheaf of the naive cotangent complex of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` the naive cotangent complex `NL_{X/Y}` is the naive
cotangent complex of the underlying morphism of ringed spaces, so its degree `0` cohomology
sheaf is the sheaf of relative differentials `Ω_{X/Y}`. Being quasi-coherent is then inherited
from `Ω_{X/Y}`, which is quasi-coherent with no hypothesis on `f`.

## Main definitions

* `AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`:
  `H⁰(NL_{X/Y}) ≅ Ω_{X/Y}`.

## Main results

* `AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex_zero`: the degree
  `0` cohomology sheaf of `NL_{X/Y}` is quasi-coherent.

## Implementation notes

Both statements are the ringed-space ones at the underlying morphism of ringed spaces of `f`,
which is the generality in which `AlgebraicGeometry.Scheme.naiveCotangentComplex` is defined.
The identification of the sheaf of relative differentials of that morphism of ringed spaces
with `AlgebraicGeometry.Scheme.Hom.relativeDifferentials f` is definitional, the two being
formed over the same morphism of sheaves of rings
(`AlgebraicGeometry.Scheme.Hom.inverseImageStructureMap_ringedSpaceHom`), so the isomorphism
below is the ringed-space one with nothing transported.

Only the degree `0` identification of [Stacks Project, Tag 0D0J] carries the tag here. The
quasi-coherence clause of the tag is
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex`, which covers every
degree and consumes the degree `0` statement below; that statement is therefore left
untagged.

## References

* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the cohomology
  sheaves of the naive cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US), the sheaf of
  relative differentials of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 0D0J, degree zero.** The degree `0` cohomology sheaf of the naive cotangent
complex `NL_{X/Y}` of a morphism of schemes is the sheaf of relative differentials
`Ω_{X/Y}`. -/
@[stacks 0D0J "the degree-zero identification H^0 of NL with Omega; not quasi-coherence, not
the vanishing in the other degrees"]
noncomputable def naiveCotangentComplexHomologyZeroIso :
    (naiveCotangentComplex f).homology 0 ≅ Hom.relativeDifferentials f :=
  RingedSpace.naiveCotangentComplexHomologyZeroIso f.toLRSHom.toShHom

/-- The degree `0` cohomology sheaf of `NL_{X/Y}` is quasi-coherent: it is `Ω_{X/Y}`, which is
quasi-coherent for every morphism of schemes. The quasi-coherence clause of Stacks 0D0J is
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex`, of which this is the
degree `0` case. -/
theorem isQuasicoherent_homology_naiveCotangentComplex_zero :
    ((naiveCotangentComplex f).homology 0).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (naiveCotangentComplexHomologyZeroIso f).symm
    (Hom.isQuasicoherent_relativeDifferentials f)

end AlgebraicGeometry.Scheme

end
