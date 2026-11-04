module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PuncturedSpectrum
public import StacksFrontier.AlgebraicGeometry.QuasiAffineGlobalGeneration.Basic

/-!
# A section of the invertible triple avoiding a given triple's associated points

The second clause of `Stacks.Algebraization.HasHilbertInductionStep` needs, for the ambient
triple `T` being twisted, a global section of the punctured-spectrum member `L.F` of the fixed
invertible triple `L` that does not vanish at any point of `Ass(T.F) ∪ Ass(T.F / f T.F)`. That
set is finite, `L.F` is invertible on the quasi-affine punctured spectrum, and [Stacks, Tag 0F20]
produces exactly such a section.

## Main results

* `Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints`: a global section of
  `L.F` whose nonvanishing locus contains `Ass(T.F) ∪ Ass(T.F / f T.F)`.

## Implementation notes

Finiteness of the target set is
`Stacks.Divisors.associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum`, read at
`k = 1`, so that the quotient `cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1)` is `T.F / f T.F`.
The section itself is
`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite`, applied on
the whole punctured spectrum (`W = ⊤`), using `isQuasiAffine_puncturedSpectrum` and the
invertibility of `L.F` carried by `hL`.

This is the piece `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction`
names as not an obstacle. The rest of the clause's section-pair obligation -- the
*correspondence over the punctured closed fibre* of this section with one on the closed-fibre
member `L.F₀` -- is
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairClosedFibre`, which also
shows that the source's adjustment of the section by an element of the maximal ideal is
unnecessary when `depth(A) ≥ 3`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace Stacks.Algebraization

/-- **A section of the invertible triple's punctured-spectrum member avoiding the associated
points of a given triple and of its quotient by `f`.** For the fixed invertible triple `L` and
any triple `T` being twisted, some global section of `L.F` does not vanish at any point of
`Ass(T.F) ∪ Ass(T.F / f T.F)`. -/
public theorem exists_section_nonvanishing_on_associatedPoints {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ s : Γ(L.F, ⊤),
      (Stacks.Divisors.associatedPoints T.F ∪
          Stacks.Divisors.associatedPoints
            (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
        (Stacks.NonvanishingOpen.nonvanishingOpen
          (Stacks.Divisors.puncturedSpectrum A).toScheme L.F s : Set _) := by
  let := hL.invertible_F
  have := T.coherent_F
  obtain ⟨s, -, hE, -⟩ :=
    Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite L.F
      (Stacks.Divisors.associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum A T.F
        (scalarOnOpen A f ⊤) 1) ⊤ (by simp)
  exact ⟨s, hE⟩

end Stacks.Algebraization

end
