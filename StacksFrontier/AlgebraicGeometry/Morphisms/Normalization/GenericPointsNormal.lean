module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Normality of the generic-point residue spectrum

The coproduct of the spectra of the residue fields at the generic points of a scheme is a
normal scheme: each of its local rings is a localization of a field, hence a field, and a field
is a normal domain.

This is the remaining elementary property of
`AlgebraicGeometry.Scheme.genericPointResidueSpectrum`; finiteness of the irreducible
components of its quasi-compact opens and dominance of the canonical morphism to the scheme are
in `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints`.

## Main results

* `AlgebraicGeometry.Scheme.genericPointResidueSpectrum_isNormal`: the coproduct of the
  generic-point residue spectra is normal.

## Implementation notes

The stalks are identified through the coproduct inclusion and `Spec.stalkIso`, so normality is
checked for a localization of a residue field at a prime; both the domain structure and
integral closedness transport along those ring isomorphisms.

## References

* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The coproduct of the spectra of the residue fields at the generic points of a scheme is
normal. -/
public instance genericPointResidueSpectrum_isNormal (X : Scheme.{u}) :
    IsNormal (genericPointResidueSpectrum X) := by
  rw [isNormal_iff_stalk_normal]
  intro y
  unfold genericPointResidueSpectrum at y ⊢
  obtain ⟨⟨η, z⟩, rfl⟩ := (sigmaMk
    (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).surjective y
  rw [sigmaMk_mk]
  let e := (asIso ((Sigma.ι (fun η : genericPoints X ↦
    Spec (.of (X.residueField η.1))) η).stalkMap z)).commRingCatIsoToRingEquiv
  let e' := (Spec.stalkIso (.of (X.residueField η.1)) z).commRingCatIsoToRingEquiv
  have : IsDomain ((Spec (.of (X.residueField η.1))).presheaf.stalk z) :=
    Function.Injective.isDomain e' e'.injective
  have : IsIntegrallyClosed ((Spec (.of (X.residueField η.1))).presheaf.stalk z) :=
    IsIntegrallyClosed.of_equiv e'.symm
  have : IsDomain _ := Function.Injective.isDomain e e.injective
  exact ⟨this, IsIntegrallyClosed.of_equiv e.symm⟩

end AlgebraicGeometry.Scheme
