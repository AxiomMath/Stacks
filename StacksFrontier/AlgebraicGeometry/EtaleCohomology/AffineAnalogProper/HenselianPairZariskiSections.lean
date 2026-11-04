module

public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.Topology.Sheaves.Spectral.ClosedSubsetGlobalSections

/-!
# Global sections of a Zariski sheaf over a henselian pair

Let `(A, I)` be a henselian pair, let `X = Spec A` and let `Z = V(I)` be the closed subset of `X`
cut out by `I`, that is, the image of `Spec (A ⧸ I)`. Restriction to `Z` is a bijection on global
sections of every sheaf of sets on the topological space `X`, and the same holds after any
integral — in particular any finite — base change `A → B`, where the closed subset lying over
`Z` is `V(IB)`.

The input is the corresponding statement for a closed subset of a spectral space meeting the
closure of every point in a connected set
([Stacks, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)). The spectrum of a ring is a
spectral space, and for a henselian pair the intersection `V(I) ∩ closure {x}` is `V(p + I)` for
the prime `p` corresponding to `x`, which is connected
([Stacks, Tag 09Y6](https://stacks.math.columbia.edu/tag/09Y6)). Integral base change is
available because `(B, IB)` is again a henselian pair
([Stacks, Tag 09XK](https://stacks.math.columbia.edu/tag/09XK)).

## Main results

* `Stacks.isConnected_zeroLocus_inter_closure_of_henselianPair` — for a henselian pair `(A, I)`
  the closed subset `V(I)` of `Spec A` meets the closure of every point in a connected set.
* `Stacks.bijective_globalSectionsRestriction_zeroLocus_of_henselianPair` — restriction to
  `V(I)` is bijective on global sections of every sheaf of sets on `Spec A`.
* `Stacks.bijective_globalSectionsRestriction_range_comap_of_henselianPair` — the same, with the
  closed subset written as the image of `Spec (A ⧸ I)`.
* `Stacks.bijective_globalSectionsRestriction_zeroLocus_map_of_henselianPair` — the same over an
  integral `A`-algebra `B`, for the closed subset of `Spec B` lying over `V(I)`.

## Implementation notes

Restriction of a sheaf to a subspace is its inverse image along the inclusion, and the
restriction map on global sections is the component over the largest open of the unit of the
inverse-image/direct-image adjunction, namely `Stacks.globalSectionsRestriction`. The equality of
section sets asserted by the source is therefore stated as bijectivity of that canonical map.

These statements are the Zariski hypotheses (1) and (2) of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) for the closed immersion
`Spec (A ⧸ I) → Spec A`, that is, the content that the proof of
[Stacks, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH) contributes beyond that tag. The
étale conclusion of Tag 09ZH is not proved here, and consequently no Stacks attribute for that
tag is placed on any declaration below; it is
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_quotient_of_henselianPair` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections`,
deduced from Tag 09ZF by feeding it the two hypotheses in the form these statements take on the
Zariski site of a scheme.
Coefficients here are sheaves of sets in the same universe as the ring, as in Tag 09ZG, whereas
the étale comparison of Tag 09ZF takes coefficients one universe up; that comparison asks for its
Zariski hypotheses at this universe, which is what lets them be supplied from here.

## References

* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace Stacks

variable {A : Type u} [CommRing A]

/-- For a henselian pair `(A, I)` the closed subset `V(I)` of `Spec A` meets the closure of every
point in a connected set: that intersection is `V(p + I)` for the prime `p` of the point. -/
theorem isConnected_zeroLocus_inter_closure_of_henselianPair (I : Ideal A)
    (hI : HenselianPair A I) (x : PrimeSpectrum A) :
    IsConnected (zeroLocus (I : Set A) ∩ closure ({x} : Set (PrimeSpectrum A))) := by
  have h : zeroLocus (I : Set A) ∩ closure ({x} : Set (PrimeSpectrum A)) =
      zeroLocus ((x.asIdeal + I : Ideal A) : Set A) := by
    rw [PrimeSpectrum.closure_singleton, Ideal.add_eq_sup, zeroLocus_sup,
      Set.inter_comm (zeroLocus (I : Set A))]
  rw [h]
  exact isConnected_zeroLocus_add I x.asIdeal hI x.isPrime

/-- For a henselian pair `(A, I)`, restriction to the closed subset `V(I)` of `Spec A` is a
bijection on global sections of every sheaf of sets on `Spec A`. -/
theorem bijective_globalSectionsRestriction_zeroLocus_of_henselianPair (I : Ideal A)
    (hI : HenselianPair A I) (F : TopCat.Sheaf (Type u) (TopCat.of (PrimeSpectrum A))) :
    Function.Bijective (globalSectionsRestriction (zeroLocus (I : Set A)) F) :=
  bijective_globalSectionsRestriction_of_isConnected_inter_closure _ (isClosed_zeroLocus _)
    (isConnected_zeroLocus_inter_closure_of_henselianPair I hI) F

/-- For a henselian pair `(A, I)`, restriction to the image of `Spec (A ⧸ I)` in `Spec A` is a
bijection on global sections of every sheaf of sets on `Spec A`. -/
theorem bijective_globalSectionsRestriction_range_comap_of_henselianPair (I : Ideal A)
    (hI : HenselianPair A I) (F : TopCat.Sheaf (Type u) (TopCat.of (PrimeSpectrum A))) :
    Function.Bijective
      (globalSectionsRestriction (Set.range (comap (Ideal.Quotient.mk I))) F) := by
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact bijective_globalSectionsRestriction_zeroLocus_of_henselianPair I hI F

/-- The closed subset of `Spec B` lying over the zero locus of an ideal `I` of `A` is the zero
locus of the ideal generated by the image of `I`. -/
theorem preimage_comap_zeroLocus_eq_zeroLocus_map {B : Type v} [CommRing B] [Algebra A B]
    (I : Ideal A) :
    comap (algebraMap A B) ⁻¹' zeroLocus (I : Set A) =
      zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B) := by
  rw [preimage_comap_zeroLocus, Ideal.map, zeroLocus_span]

/-- For a henselian pair `(A, I)` and an integral `A`-algebra `B`, restriction to the closed
subset of `Spec B` lying over `V(I)` is a bijection on global sections of every sheaf of sets on
`Spec B`. -/
theorem bijective_globalSectionsRestriction_zeroLocus_map_of_henselianPair {B : Type v}
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal A) (hI : HenselianPair A I)
    (F : TopCat.Sheaf (Type v) (TopCat.of (PrimeSpectrum B))) :
    Function.Bijective
      (globalSectionsRestriction (comap (algebraMap A B) ⁻¹' zeroLocus (I : Set A)) F) := by
  rw [preimage_comap_zeroLocus_eq_zeroLocus_map]
  exact bijective_globalSectionsRestriction_zeroLocus_of_henselianPair _
    (henselianPair_map_of_isIntegral I hI) F

end Stacks
