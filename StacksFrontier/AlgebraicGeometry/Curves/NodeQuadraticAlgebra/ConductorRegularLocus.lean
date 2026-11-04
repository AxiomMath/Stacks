module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorLocalization
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# The normalization agrees with the ring at a regular point

Let `A` be a reduced Noetherian ring and `A' = integralClosure A (FractionRing A)` its
normalization inside its total ring of fractions. At a prime `𝔭` of `A` whose local ring is
regular — that is, at a point of the regular locus, the complement of the singular locus — the
localization of `A'` at `𝔭` is already the image of `A_𝔭`: the finite `A`-module `A' / A` is
supported on the singular locus.

The mechanism is that `A_𝔭` is integrally closed. A regular local ring is a unique
factorization domain, hence normal; this is `isIntegrallyClosed_of_isRegularLocalRing`, and it
needs no hypothesis on the dimension. Being integrally closed says precisely that the integral
closure of `A_𝔭` in its total ring of fractions is the image of `A_𝔭`, and
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing` identifies that
integral closure with the localization `A' ⊗_A A_𝔭`.

This is the counterpart at a regular point of the two node-local computations of
`StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorLocalization`: there the
image of the local ring in the localized normalization is a coatom, here it is everything. The
two together say that `A' / A` is a module supported exactly on the singular points, which is
what makes the product of the maximal ideals of the singular points annihilate it.

## Main results

* `Stacks.Curves.range_algebraMap_integralClosure_eq_top_of_isIntegrallyClosed`: for an
  integrally closed ring the map into its integral closure in its total ring of fractions is
  already surjective.
* `Stacks.Curves.range_algebraMap_localization_integralClosure_eq_top_of_isRegularLocalRing`: at
  a prime with regular local ring, the image of the local ring in the localized normalization is
  the whole of it.

## Implementation notes

The statement is phrased exactly as its node-local twin
`Stacks.Curves.isCoatom_range_algebraMap_localization_integralClosure_of_isNodalAlgebra`: the
localized normalization is `Localization (Algebra.algebraMapSubmonoid A' 𝔭.primeCompl)`, whose
`A_𝔭`-algebra structure is the comparison map `localizationAlgebra` and therefore has to be
supplied by a `letI` in the statement, and the image of the local ring is
`LinearMap.range (Algebra.linearMap _ _)`, a submodule rather than a subring, so that the two
results can be combined in the lattice of `A_𝔭`-submodules.

Regularity of the local ring is taken as an explicit hypothesis rather than an instance, so that
the result can be applied to a point of `AlgebraicGeometry.regularLocus`, where membership is a
proposition that has to be supplied by hand; this also matches the shape in which the node
results take nodality.

No hypothesis on the dimension of `A` appears. The one-dimensional case is the one the conductor
of a nodal curve needs, but the vanishing of `A' / A` at a regular point holds in any dimension,
because a regular local ring is normal in any dimension.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- **An integrally closed ring is all of its integral closure.** For a ring that is integrally
closed in its total ring of fractions, the canonical map into the integral closure taken there is
surjective, so the image of the ring is the whole integral closure. -/
public theorem range_algebraMap_integralClosure_eq_top_of_isIntegrallyClosed
    (C : Type*) [CommRing C] (hC : IsIntegrallyClosed C) :
    LinearMap.range (Algebra.linearMap C ↥(integralClosure C (FractionRing C))) = ⊤ :=
  LinearMap.range_eq_top.mpr fun x =>
    ((isIntegrallyClosed_iff (K := FractionRing C)).mp hC x.2).imp fun _ ha => Subtype.ext ha

/-- **At a regular point the normalization agrees with the ring.** Let `A` be a reduced
Noetherian ring, let `A'` be its integral closure in its total ring of fractions and let `𝔭` be
a prime of `A` at which the local ring is regular. Then the image of `A_𝔭` in `A' ⊗_A A_𝔭` is
everything, so the localization of the finite `A`-module `A' / A` at `𝔭` vanishes.

A regular local ring is integrally closed, by `isIntegrallyClosed_of_isRegularLocalRing`, and the
localization of `A'` is the integral closure of `A_𝔭`, by
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`; the image of `A_𝔭`
in the former corresponds to the image of `A_𝔭` in the latter, which is everything. -/
public theorem range_algebraMap_localization_integralClosure_eq_top_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsReduced A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime 𝔭)) :
    letI : Algebra (Localization.AtPrime 𝔭) (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) 𝔭.primeCompl)) :=
      localizationAlgebra 𝔭.primeCompl ↥(integralClosure A (FractionRing A))
    LinearMap.range (Algebra.linearMap (Localization.AtPrime 𝔭)
      (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) 𝔭.primeCompl))) = ⊤ := by
  let C := Localization.AtPrime 𝔭
  let T := ↥(integralClosure A (FractionRing A))
  let C' := Localization (Algebra.algebraMapSubmonoid T 𝔭.primeCompl)
  let : Algebra C C' := localizationAlgebra 𝔭.primeCompl T
  let : IsRegularLocalRing C := hreg
  obtain ⟨e⟩ := nonempty_algEquiv_localization_integralClosure_fractionRing A
    (minimalPrimes.finite_of_isNoetherianRing A) C 𝔭.primeCompl
  refine LinearMap.range_eq_top.mpr fun y => ?_
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp
    (range_algebraMap_integralClosure_eq_top_of_isIntegrallyClosed C
      (isIntegrallyClosed_of_isRegularLocalRing C)) (e y)
  exact ⟨c, e.injective ((e.commutes c).trans hc)⟩

end Stacks.Curves

end
