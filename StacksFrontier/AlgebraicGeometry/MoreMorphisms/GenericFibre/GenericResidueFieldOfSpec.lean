module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The residue field of an affine scheme at its generic point

Part of Step D of the proof of Stacks Tag 0559. For a domain `R`, the residue field of `Spec R`
at the generic point is a field of fractions of `R`: the local ring there is already a field, so
the residue map is an isomorphism onto it, and the local ring at the generic point of an affine
scheme is the fraction field (`AlgebraicGeometry.functionField_isFractionRing_of_affine`).

In the application, `R` is the ring `B'` of Step C and the residue field is the one Tag 0552
compares with the residue field of `X` at the generic point of its generic fibre; identifying it
with `Frac(B') = κ(x)` is what makes
`AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso` applicable.

## Main results

* `AlgebraicGeometry.isIso_residue_genericPoint`: on an integral scheme the residue map at the
  generic point is an isomorphism, the local ring there being a field.
* `AlgebraicGeometry.specResidueFieldAlgebra`: the algebra structure on the residue field of
  `Spec R` at a point, through the global sections.
* `AlgebraicGeometry.isFractionRing_specResidueField_genericPoint` and
  `AlgebraicGeometry.isFractionRing_specResidueField`: for a domain `R` that algebra is a field
  of fractions of `R`, the second for a point presented as the generic point.
* `AlgebraicGeometry.map_genericPoint_Spec_map`: an injective ring homomorphism of domains
  carries generic point to generic point on spectra, which is the hypothesis `h` of Tag 0552.

## Implementation notes

The algebra structure on the residue field is the one its consumers use (compare
`AlgebraicGeometry.geometricallyIrreducible_tfae_functionField`): the composite
`R ⟶ Γ(Spec R, ⊤) ⟶ κ(x)` of the inverse of `Scheme.ΓSpecIso` with `Scheme.Γevaluation`. It is
not declared an instance, since it is one of several algebra structures a residue field can
carry; the statements below take it as a `letI`.

`AlgebraicGeometry.specResidueFieldAlgebra` is stated for an arbitrary point, where it is the
canonical map into the residue field; only at the generic point of a domain is it a
localization.

No Stacks tag is attached: Step D is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step D of the first
  proof
* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On an integral scheme the local ring at the generic point is a field, so the residue map
there is an isomorphism. -/
theorem isIso_residue_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    IsIso (Z.residue (genericPoint Z)) := by
  have hinj : Function.Injective (Z.residue (genericPoint Z)).hom := by
    change Function.Injective (IsLocalRing.residue (Z.presheaf.stalk _))
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      IsLocalRing.maximalIdeal_eq_bot]
  exact ((RingEquiv.ofBijective (Z.residue (genericPoint Z)).hom
    ⟨hinj, Z.residue_surjective _⟩).toCommRingCatIso
      (R := Z.presheaf.stalk (genericPoint Z))
      (S := Z.residueField (genericPoint Z))).isIso_hom

/-- The canonical algebra structure on the residue field of `Spec R` at a point, through the
global sections of `Spec R`. -/
noncomputable abbrev specResidueFieldAlgebra (R : CommRingCat.{u}) (x : Spec R) :
    Algebra R ((Spec R).residueField x) :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x).hom.toAlgebra

/-- The canonical map of a ring into the residue field of its spectrum at a point factors
through the local ring there. -/
theorem specResidueFieldAlgebra_eq (R : CommRingCat.{u}) [IsDomain R] :
    letI := specResidueFieldAlgebra R (genericPoint (Spec R))
    CommRingCat.ofHom (algebraMap R ((Spec R).residueField (genericPoint (Spec R)))) =
      CommRingCat.ofHom (algebraMap R (Spec R).functionField) ≫
        (Spec R).residue (genericPoint (Spec R)) := by
  change (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation (genericPoint (Spec R)) = _
  change (Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.germ ⊤ (genericPoint (Spec R)) trivial ≫
        (Spec R).residue (genericPoint (Spec R)) = _
  rw [← Category.assoc]
  congr 1

/-- **Part of Step D of Stacks Tag 0559.** For a domain `R`, the residue field of `Spec R` at
the generic point is a field of fractions of `R`. -/
theorem isFractionRing_specResidueField_genericPoint (R : CommRingCat.{u}) [IsDomain R] :
    letI := specResidueFieldAlgebra R (genericPoint (Spec R))
    IsFractionRing R ((Spec R).residueField (genericPoint (Spec R))) := by
  let _ := specResidueFieldAlgebra R (genericPoint (Spec R))
  have hiso := isIso_residue_genericPoint (Spec R)
  let ε : (Spec R).functionField ≃+* (Spec R).residueField (genericPoint (Spec R)) :=
    (asIso ((Spec R).residue (genericPoint (Spec R)))).commRingCatIsoToRingEquiv
  have hcomm : ∀ r : R, ε (algebraMap R (Spec R).functionField r) =
      algebraMap R ((Spec R).residueField (genericPoint (Spec R))) r := fun r =>
    (congrArg (fun φ : R ⟶ _ => φ.hom r) (specResidueFieldAlgebra_eq R)).symm
  exact IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := ε) hcomm)

/-- `AlgebraicGeometry.isFractionRing_specResidueField_genericPoint` at a point presented as the
generic point, which is the form its consumers meet. -/
theorem isFractionRing_specResidueField (R : CommRingCat.{u}) [IsDomain R] (s : Spec R)
    (hs : s = genericPoint (Spec R)) :
    letI := specResidueFieldAlgebra R s
    IsFractionRing R ((Spec R).residueField s) := by
  subst hs
  exact isFractionRing_specResidueField_genericPoint R

/-- An injective ring homomorphism between domains carries the generic point of the spectrum of
its target to the generic point of the spectrum of its source. -/
theorem map_genericPoint_Spec_map {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S] (φ : R ⟶ S)
    (hφ : Function.Injective φ.hom) :
    (Spec.map φ) (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  change PrimeSpectrum.comap φ.hom (⊥ : PrimeSpectrum S) = (⊥ : PrimeSpectrum R)
  exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ.hom hφ)

end AlgebraicGeometry

end
