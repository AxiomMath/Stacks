module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact

/-!
# The cokernel of the first arrow of the conormal sequence of an immersion

Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S`. The conormal sequence of
[Stacks, Tag 01UZ],

```
𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0,
```

packaged as `Stacks.ConormalSequenceRight.conormalShortComplex`, is exact at its middle term
with no hypothesis beyond `IsImmersion i`: that is
`Stacks.ConormalSequenceRight.conormalShortComplex_exact`, proved in
`StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact`. This file draws from it
the colimit form of the right-hand end of the sequence.

## Main results

* `Stacks.ConormalSequenceRight.conormalShortComplexCokernelIso`: the right-hand term `Ω_{Z/S}`
  of the sequence is the cokernel of its first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/S}`, exactness at the
  middle term and the first arrow's epimorphic companion
  `Stacks.ConormalSequenceRight.epi_conormalShortComplex_g` supplying the two halves.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA), short exactness under
  smoothness, of which exactness at the middle term is the unconditional half.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceRight

/-- **`Ω_{Z/S}` is the cokernel of the first arrow of the conormal sequence.** For an immersion
`i : Z ⟶ X` of schemes over `p : X ⟶ S` the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` exhibits
`Ω_{Z/S}` as the cokernel of `𝒞_{Z/X} ⟶ i^*Ω_{X/S}`.

This is exactness at the middle term together with
`Stacks.ConormalSequenceRight.epi_conormalShortComplex_g`. -/
noncomputable def conormalShortComplexCokernelIso {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) :
    Limits.cokernel (conormalDifferential i p) ≅ Scheme.Hom.relativeDifferentials (i ≫ p) :=
  haveI : Epi (conormalShortComplex i p).g := epi_conormalShortComplex_g i p
  Limits.IsColimit.coconePointUniqueUpToIso (Limits.cokernelIsCokernel _)
    (conormalShortComplex_exact i p).gIsCokernel

end Stacks.ConormalSequenceRight

end
