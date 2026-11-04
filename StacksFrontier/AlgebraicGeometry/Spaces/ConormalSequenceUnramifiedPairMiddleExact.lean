module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramifiedMiddleExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPair

/-!
# Stacks 06BE with exactness of Stacks 05ZA at the middle term supplied

This file proves the epimorphism clause of the sequence `𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0` of
Stacks 06BE with no hypothesis on exactness at the middle term of the sequence of Stacks 05ZA at
the universal first-order thickening `Z ⊂ Z'`: that exactness is
`AlgebraicGeometry.Space.exact_conormalSequence_universalThickening`.  The remaining hypotheses
`he` and `hzero` are those of Stacks 060F.

## Main results

* `AlgebraicGeometry.Space.epi_thickeningConormalFirstMap'`: Stacks 06BE, the `⟶ 0` — the
  second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` is an epimorphism.

## References

* [Stacks Project, Tag 06BE](https://stacks.math.columbia.edu/tag/06BE)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' W' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {W : Subfunctor W'.obj}
    {p : Z' ⟶ X} {q : W' ⟶ Y}

/-- **Stacks 06BE, the `⟶ 0`, with exactness of Stacks 05ZA at the middle term supplied**: the
second arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}`, the canonical first arrow of Stacks 060F, is an
epimorphism.  The hypotheses `he` and `hzero` are those of Stacks 060F. -/
theorem epi_thickeningConormalFirstMap' (g : X ⟶ Y)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g))
    (hzero : conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (p ≫ g) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (p ≫ g) = 0)
    (hj : FormallyUnramified (universalThickeningInclusion B S hS hZ ≫ p ≫ g).hom) :
    Epi (thickeningConormalFirstMap B S hS hZ g he) :=
  epi_thickeningConormalFirstMap B S hS g hZ he hzero
    (exact_conormalSequence_universalThickening B S hS hZ g hzero) hj

end AlgebraicGeometry.Space

end
