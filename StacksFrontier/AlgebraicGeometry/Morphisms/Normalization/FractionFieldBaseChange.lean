module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange

/-!
# Normalization commutes with base change to the fraction field

Let `B` be a domain with fraction field `L` and let `f : W ⟶ Spec B` be any morphism with `W`
normalizable. The projection `W ×_{Spec B} Spec L ⟶ W` is flat and a preimmersion, `Spec L ⟶
Spec B` being a localization, and along such a morphism normalization commutes with base change:
the normalization of `W ×_{Spec B} Spec L` is `W^ν ×_W (W ×_{Spec B} Spec L)`.

This is the case of [Stacks, Tag 0307] needed in the last paragraph of the proof of the reduced
fibre theorem, where the generic fibre of the normalized base change has to be recognised as the
normalization of the generic fibre.

## Main results

* `AlgebraicGeometry.flat_specMap_algebraMap_fractionRing` and
  `AlgebraicGeometry.isPreimmersion_specMap_algebraMap_fractionRing`: the morphism from the
  spectrum of the fraction field is a flat preimmersion.
* `AlgebraicGeometry.finite_irreducibleComponents_pullbackFst_fractionRing`: finiteness of the
  irreducible components of quasi-compact opens passes to the base change.
* `AlgebraicGeometry.isNormal_pullback_normalization_pullbackFst_fractionRing`: the base change
  of the normalization morphism along the projection has normal source.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_specMap_fractionRing`: the normalization
  square of the projection is cartesian.

## Implementation notes

The general statement
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat_preimmersion` carries the normality
of the base-changed normalization morphism as a hypothesis, and the three results above are
exactly the discharge of its hypotheses for `Spec L ⟶ Spec B`. The normality argument is the
one used for a local ring of the base in
`AlgebraicGeometry.isNormal_pullback_normalization_pullbackFst_fromSpecStalk`: after the
comparison isomorphism `pullbackRightPullbackFstIso` the base change in question is the base
change of `Spec L ⟶ Spec B` along `W^ν ⟶ Spec B`, which is a flat preimmersion with normal
target.

## References

* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {B : Type u} [CommRing B] [IsDomain B] (L : Type u) [Field L] [Algebra B L]
  [IsFractionRing B L]

omit [IsDomain B] in
/-- The morphism from the spectrum of the fraction field of a domain is flat, the fraction field
being a localization. -/
theorem flat_specMap_algebraMap_fractionRing :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap B L))) := by
  rw [Flat.SpecMap_iff]
  show (algebraMap B L).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact IsLocalization.flat L (nonZeroDivisors B)

omit [IsDomain B] in
/-- The morphism from the spectrum of the fraction field of a domain is a preimmersion, the
fraction field being a localization. -/
theorem isPreimmersion_specMap_algebraMap_fractionRing :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap B L))) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors B)

private instance instFlatSpecMapAlgebraMapFractionRing
    {B : Type u} [CommRing B] (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap B L))) :=
  flat_specMap_algebraMap_fractionRing L

private instance instIsPreimmersionSpecMapAlgebraMapFractionRing
    {B : Type u} [CommRing B] (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap B L))) :=
  isPreimmersion_specMap_algebraMap_fractionRing L

variable {W : Scheme.{u}} (q : W ⟶ Spec (.of B))

omit [IsDomain B] in
/-- Finiteness of the irreducible components of quasi-compact opens passes to the base change to
the fraction field of the base. -/
theorem finite_irreducibleComponents_pullbackFst_fractionRing
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    ∀ U : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap B L)))).Opens,
      IsCompact (U : Set ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap B L))))) →
        (irreducibleComponents U).Finite :=
  finite_irreducibleComponents_of_flat_preimmersion
    (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap B L)))) hW

omit [IsDomain B] in
/-- The base change of the normalization morphism of `W` along `W ×_{Spec B} Spec L ⟶ W` has
normal source: after the comparison isomorphism it is the base change of `Spec L ⟶ Spec B` along
`W^ν ⟶ Spec B`, which is a flat preimmersion with normal target. -/
theorem isNormal_pullback_normalization_pullbackFst_fractionRing
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    IsNormal (pullback (W.normalization hW)
      (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap B L))))) := by
  have _ : IsNormal (W.normalizationScheme hW) := Scheme.isNormal_normalizationScheme W hW
  have _ : IsNormal (pullback (W.normalization hW ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap B L)))) :=
    isNormal_of_flat_preimmersion (pullback.fst (W.normalization hW ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap B L))))
  exact isNormal_of_iso (pullbackRightPullbackFstIso q
    (Spec.map (CommRingCat.ofHom (algebraMap B L))) (W.normalization hW))

omit [IsDomain B] in
/-- **Normalization commutes with base change to the fraction field of the base.** For a domain
`B` with fraction field `L` and any `q : W ⟶ Spec B` with `W` normalizable, the normalization of
`W ×_{Spec B} Spec L` is the base change of the normalization of `W`.

This is the case of [Stacks, Tag 0307] used in the proof of the reduced fibre theorem; the
`IsNormal` hypothesis of
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat_preimmersion` is discharged by
`AlgebraicGeometry.isNormal_pullback_normalization_pullbackFst_fractionRing`. -/
theorem isPullback_normalizationSchemeMap_specMap_fractionRing
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    letI := flat_specMap_algebraMap_fractionRing (B := B) L
    IsPullback
      (normalizationSchemeMap (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap B L))))
        (finite_irreducibleComponents_pullbackFst_fractionRing L q hW) hW)
      ((pullback q (Spec.map (CommRingCat.ofHom (algebraMap B L)))).normalization
        (finite_irreducibleComponents_pullbackFst_fractionRing L q hW))
      (W.normalization hW) (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap B L)))) :=
  isPullback_normalizationSchemeMap_of_flat_preimmersion
    (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap B L)))) hW
    (isNormal_pullback_normalization_pullbackFst_fractionRing L q hW)

end AlgebraicGeometry

end
