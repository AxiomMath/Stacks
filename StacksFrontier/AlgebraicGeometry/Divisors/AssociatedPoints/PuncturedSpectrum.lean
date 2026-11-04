module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.CompactFinite
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# Associated points on the punctured spectrum of a Noetherian local ring

Let `A` be a Noetherian local ring and let `U = Spec A ∖ {𝔪}` be its punctured spectrum. The
scheme `U` is locally Noetherian, being an open subscheme of the spectrum of a Noetherian ring,
and its underlying space is quasi-compact, the spectrum of a Noetherian ring being a Noetherian
topological space. Consequently a coherent `𝒪_U`-module has only finitely many associated points,
and so has a pair of coherent modules together — in particular `ℱ` together with the quotient
`ℱ/fᵏℱ` by a power of a global function `f`.

## Main results

* `Stacks.Divisors.compactSpace_puncturedSpectrum`: the punctured spectrum of a Noetherian local
  ring is quasi-compact.
* `Stacks.Divisors.associatedPoints_finite_puncturedSpectrum`: the associated points of a
  coherent module on it form a finite set.
* `Stacks.Divisors.associatedPoints_union_finite_puncturedSpectrum` and
  `Stacks.Divisors.associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum`: the
  same for two coherent modules, and for `ℱ` together with `ℱ/fᵏℱ`.

## Implementation notes

Finiteness on a quasi-compact locally Noetherian scheme is
`AlgebraicGeometry.associatedPoints_finite` and its companions, which is the quasi-compact-open
finiteness of [Stacks, Tag 05AF]. Local Noetherianness of the punctured spectrum is found by
instance search, from the instances for the spectrum of a Noetherian ring and for an open
subscheme; quasi-compactness is not, and is supplied here as an instance.

## References

* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace Stacks.Divisors

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The punctured spectrum of a Noetherian local ring is quasi-compact: it is a subspace of the
spectrum of a Noetherian ring, which is a Noetherian topological space. -/
instance compactSpace_puncturedSpectrum : CompactSpace (puncturedSpectrum A).toScheme :=
  @NoetherianSpace.compactSpace _ _
    (NoetherianSpace.set ((puncturedSpectrum A).1 : Set (PrimeSpectrum A)))

/-- A coherent module on the punctured spectrum of a Noetherian local ring has finitely many
associated points. -/
theorem associatedPoints_finite_puncturedSpectrum
    (F : (puncturedSpectrum A).toScheme.Modules) [F.IsCoherent] :
    (associatedPoints F).Finite :=
  AlgebraicGeometry.associatedPoints_finite F

/-- The points of the punctured spectrum of a Noetherian local ring associated to either of two
coherent modules form a finite set. -/
theorem associatedPoints_union_finite_puncturedSpectrum
    (F G : (puncturedSpectrum A).toScheme.Modules) [F.IsCoherent] [G.IsCoherent] :
    (associatedPoints F ∪ associatedPoints G).Finite :=
  (associatedPoints_finite_puncturedSpectrum A F).union
    (associatedPoints_finite_puncturedSpectrum A G)

/-- For a coherent module `ℱ` on the punctured spectrum of a Noetherian local ring, a global
function `f` and an exponent `k`, the points associated to `ℱ` or to the quotient `ℱ/fᵏℱ` form a
finite set. Taking `k = 1` this is the finiteness of `Ass(ℱ) ∪ Ass(ℱ/fℱ)`. -/
theorem associatedPoints_union_cokernel_smulPowHom_finite_puncturedSpectrum
    (F : (puncturedSpectrum A).toScheme.Modules) [F.IsCoherent]
    (f : Γ((puncturedSpectrum A).toScheme, ⊤)) (k : ℕ) :
    (associatedPoints F ∪ associatedPoints (cokernel (smulPowHom F f k))).Finite :=
  AlgebraicGeometry.associatedPoints_union_cokernel_smulPowHom_finite F f k

end Stacks.Divisors

end
