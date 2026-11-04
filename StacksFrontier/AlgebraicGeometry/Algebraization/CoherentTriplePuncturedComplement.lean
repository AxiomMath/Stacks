module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap

/-!
# The punctured spectrum of `Spec A`, as the complement of an ideal sheaf

`Stacks.Algebraization.puncturedSpectrum_eq_support_compl` already identifies the punctured
spectrum of `Spec A` with the complement of the support of the kernel ideal sheaf of the closed
point, `Scheme.Hom.ker (Spec.map (IsLocalRing.residue A))`. This file records that identification
at the spelling the extension machinery of
`Stacks.LocalCohomology.exists_idealPow_hom_of_section_on_affine_of_torsionFree` consumes: an
`X.IdealSheafData` together with a proof that its `Stacks.LocalCohomology.idealComplement` is the
punctured spectrum. The two spellings of the open complement of an ideal sheaf's support --
`Stacks.LocalCohomology.idealComplement` and `TopologicalSpace.Closeds.compl` applied to
`IdealSheafData.support` -- are the same anonymous constructor up to proof irrelevance, so no
further argument is needed.

## Main results

* `Stacks.Algebraization.puncturedSpectrum_eq_idealComplement`: the punctured spectrum of
  `Spec A` is the ideal-sheaf complement of the closed point.

## References

* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- **The punctured spectrum of `Spec A`, as the complement of an ideal sheaf.** The kernel ideal
sheaf of `Spec (ResidueField A) ⟶ Spec A` has the closed point as its support, so the open
complement of that support -- read as `Stacks.LocalCohomology.idealComplement`, the spelling the
affine extension-of-sections machinery needs -- is the punctured spectrum. -/
public theorem puncturedSpectrum_eq_idealComplement (A : Type u) [CommRing A] [IsLocalRing A] :
    Stacks.Divisors.puncturedSpectrum A =
      Stacks.LocalCohomology.idealComplement
        (Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) :=
  puncturedSpectrum_eq_support_compl A

end Stacks.Algebraization

end
