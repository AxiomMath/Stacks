module

public import StacksFrontier.RingTheory.Cech.IdealCechComplexRestriction
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimensionBounds

/-!
# The extended Čech object depends only on the zero locus of the family

Let `R` be a commutative ring, `M` an `R`-module and `f₁, …, f_r` and `g₁, …, g_s` two finite
families of elements of `R` **cutting out the same closed subset of `Spec R`**, that is with
`V(f₁, …, f_r) = V(g₁, …, g_s)`. This file shows that the extended alternating Čech complexes of
the two families are isomorphic in `D(R)` over `M`, that the isomorphism is the unique morphism
over `M`, and — the form the construction of [Stacks, Tag 099D] needs — that *every* map of
complexes between them which is compatible with the augmentations is automatically a
quasi-isomorphism.

`Stacks.IdealCechComplex.canonicalIso` already does this when the two families span the same
ideal **on the nose**. The relaxation matters because the comparison maps of a filtered system of
Čech complexes built by multiplying generating families together land on families spanning the
*powers* of the ideal, never the ideal itself: the product of one element from each of `n`
generating families of `I` spans `Iⁿ`, and `V(Iⁿ) = V(I)`.

Both inputs are already available. Being `I`-power torsion is a condition on the support of a
module when `I` is finitely generated ([Stacks, Tag 0953]), so the full subcategory of `D(R)` cut
out by `I` depends only on `V(I)`: that is
`Stacks.LocalCohomology.derivedPowerTorsionProperty_iff_of_zeroLocus_eq`. And the augmentation of
the Čech object is universal among morphisms from objects of that subcategory:
`Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom`. Transporting the first
across the second is the whole proof, exactly as in
`Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject_of_zeroLocus_eq`.

## Main definitions

* `Stacks.IdealCechComplex.zeroLocusHom` — **the** morphism over `M` between the Čech objects of
  two families with the same zero locus.

## Main results

* `Stacks.IdealCechComplex.existsUnique_hom_over_augmentation_of_zeroLocus_eq` — there is exactly
  one morphism over `M` between the two Čech objects.
* `Stacks.IdealCechComplex.isIso_of_comp_augmentationHom_of_zeroLocus_eq` — every morphism over
  `M` between them is an isomorphism.
* `Stacks.IdealCechComplex.quasiIso_of_comp_augmentation_of_zeroLocus_eq` — every map of
  complexes between the integer-indexed Čech complexes compatible with the augmentations is a
  quasi-isomorphism.
* `Stacks.IdealCechComplex.extendMap_comp_augmentation` — a map of the `ℕ`-indexed Čech complexes
  which is the identity on the degree-zero module extends to one compatible with the
  augmentations, so the previous result applies to it.

## Implementation notes

The hypothesis is stated as equality of the zero loci of the *spans* of the two ranges rather
than of the ranges themselves, because that is the shape
`Stacks.LocalCohomology.derivedPowerTorsionProperty_iff_of_zeroLocus_eq` consumes;
`PrimeSpectrum.zeroLocus_span` converts.

No `@[stacks]` attribute is attached: this is a generator-independence statement for the Čech
model, one input to the construction of [Stacks, Tag 099D] rather than a part of its statement.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.IdealCechComplex

open Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
  (M : ModuleCat.{max u v} R)

/-- The ideal spanned by a finite family of elements of `R` is finitely generated. -/
theorem fg_span_range : (Ideal.span (Set.range f)).FG :=
  Submodule.fg_span (Set.finite_range f)

/-! ### The universal property, relaxed to equal zero loci -/

/-- **The Čech object of `f` lies in the subcategory cut out by the span of `g`** as soon as the
two families cut out the same closed subset: its cohomology is power torsion for the span of `f`,
and for a finitely generated ideal that condition depends only on the zero locus. -/
theorem derivedPowerTorsionProperty_extendedCechObject_of_zeroLocus_eq
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R)) :
    Dualizing.derivedPowerTorsionProperty R (Ideal.span (Set.range g)) (fg_span_range g)
      (extendedCechObject f M) :=
  (derivedPowerTorsionProperty_iff_of_zeroLocus_eq.{v} _ _ (fg_span_range f) (fg_span_range g)
      hfg _).mp
    (derivedPowerTorsionProperty_extendedCechObject f M _ (fg_span_range f) rfl)

/-- **Composing with the augmentation of the Čech object of `g` identifies the morphisms out of
the Čech object of `f`** with the morphisms onto `M`, when the two families cut out the same
closed subset. -/
theorem bijective_comp_augmentationHom_of_zeroLocus_eq
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R)) :
    Function.Bijective (fun φ : extendedCechObject f M ⟶ extendedCechObject g M =>
      φ ≫ extendedCechAugmentationHom g M) :=
  bijective_comp_extendedCechAugmentationHom g M _ (fg_span_range g) rfl _
    (derivedPowerTorsionProperty_extendedCechObject_of_zeroLocus_eq f g M hfg)

/-- Composing with the augmentation of the Čech object of `f` is bijective on its endomorphisms. -/
private theorem bijective_comp_augmentationHom_self :
    Function.Bijective (fun φ : extendedCechObject f M ⟶ extendedCechObject f M =>
      φ ≫ extendedCechAugmentationHom f M) :=
  bijective_comp_extendedCechAugmentationHom f M _ (fg_span_range f) rfl _
    (derivedPowerTorsionProperty_extendedCechObject f M _ (fg_span_range f) rfl)

/-- **There is exactly one morphism over `M`** between the Čech objects of two families cutting
out the same closed subset of `Spec R`. -/
theorem existsUnique_hom_over_augmentation_of_zeroLocus_eq
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R)) :
    ∃! φ : extendedCechObject f M ⟶ extendedCechObject g M,
      φ ≫ extendedCechAugmentationHom g M = extendedCechAugmentationHom f M := by
  have hbij := bijective_comp_augmentationHom_of_zeroLocus_eq.{v} f g M hfg
  obtain ⟨φ, hφ⟩ := hbij.2 (extendedCechAugmentationHom f M)
  exact ⟨φ, hφ, fun ψ hψ => hbij.1 (hψ.trans hφ.symm)⟩

/-- **The** morphism over `M` between the Čech objects of two families cutting out the same closed
subset of `Spec R`. -/
def zeroLocusHom
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R)) :
    extendedCechObject f M ⟶ extendedCechObject g M :=
  (existsUnique_hom_over_augmentation_of_zeroLocus_eq.{v} f g M hfg).choose

/-- `Stacks.IdealCechComplex.zeroLocusHom` is a morphism over `M`. -/
theorem zeroLocusHom_comp_augmentationHom
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R)) :
    zeroLocusHom.{v} f g M hfg ≫ extendedCechAugmentationHom g M =
      extendedCechAugmentationHom f M :=
  (existsUnique_hom_over_augmentation_of_zeroLocus_eq.{v} f g M hfg).choose_spec.1

/-- **Every morphism over `M` between the two Čech objects is an isomorphism**, when the two
families cut out the same closed subset of `Spec R`. There is only one such morphism, and the
universal property of the two augmentations produces an isomorphism over `M`. -/
theorem isIso_of_comp_augmentationHom_of_zeroLocus_eq
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R))
    (φ : extendedCechObject f M ⟶ extendedCechObject g M)
    (hφ : φ ≫ extendedCechAugmentationHom g M = extendedCechAugmentationHom f M) :
    IsIso φ := by
  obtain ⟨e, he⟩ := exists_iso_over_of_universal
    (extendedCechAugmentationHom f M) (extendedCechAugmentationHom g M)
    (bijective_comp_augmentationHom_of_zeroLocus_eq.{v} f g M hfg)
    (bijective_comp_augmentationHom_of_zeroLocus_eq.{v} g f M hfg.symm)
    (bijective_comp_augmentationHom_self.{v} f M).1 (bijective_comp_augmentationHom_self.{v} g M).1
  obtain rfl : φ = e.hom :=
    (existsUnique_hom_over_augmentation_of_zeroLocus_eq.{v} f g M hfg).unique hφ he
  infer_instance

/-! ### The form the construction of tag 099D uses -/

/-- **A map of complexes between the extended Čech complexes of two families cutting out the same
closed subset, compatible with the augmentations, is a quasi-isomorphism.** This is what makes a
filtered system of Čech complexes, with the comparison maps coming from multiplying generating
families together, a system of quasi-isomorphisms. -/
theorem quasiIso_of_comp_augmentation_of_zeroLocus_eq
    (hfg : PrimeSpectrum.zeroLocus ((Ideal.span (Set.range f) : Ideal R) : Set R) =
      PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal R) : Set R))
    (u : extendedCechComplex f M ⟶ extendedCechComplex g M)
    (hu : u ≫ extendedCechAugmentation g M = extendedCechAugmentation f M) :
    QuasiIso u := by
  have hQ : DerivedCategory.Q.map u ≫ extendedCechAugmentationHom g M =
      extendedCechAugmentationHom f M := by
    show DerivedCategory.Q.map u ≫
        DerivedCategory.Q.map (extendedCechAugmentation g M) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M).inv =
      DerivedCategory.Q.map (extendedCechAugmentation f M) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M).inv
    rw [← Category.assoc, ← Functor.map_comp, hu]
  have h := isIso_of_comp_augmentationHom_of_zeroLocus_eq.{v} f g M hfg _ hQ
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ u).mp h

/-- **A map of the `ℕ`-indexed Čech complexes which is the identity on the degree-zero module
extends to a map compatible with the augmentations.** The degree-zero term of either Čech complex
is the single summand indexed by the empty set, identified with `M`; a map of complexes which
respects that identification is a map over `M`.

This generalizes `Stacks.IdealCechComplex.extendMap_cechRestrict_comp_augmentation` from the
restriction to an ordered subfamily to an arbitrary comparison map. -/
theorem extendMap_comp_augmentation (u : Cech.cechComplex f M ⟶ Cech.cechComplex g M)
    (hu : u.f 0 ≫ (cechZeroIso g M).hom = (cechZeroIso f M).hom) :
    HomologicalComplex.extendMap u ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation g M =
      extendedCechAugmentation f M := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
      ComplexShape.embeddingUpNat_f_zero,
    extendedCechAugmentation_f_zero, extendedCechAugmentation_f_zero]
  show ((extendXZeroIso f M).hom ≫ u.f 0 ≫ (extendXZeroIso g M).inv) ≫
      (cechAugIso g M).hom ≫ _ = (cechAugIso f M).hom ≫ _
  rw [cechAugIso, cechAugIso, extendedCechXZeroIso_hom, extendedCechXZeroIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (u.f 0), hu]

end Stacks.IdealCechComplex

end
