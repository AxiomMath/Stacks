module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.Tor.DerivedObjectProduct
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# Dualizing complexes and invertible objects

Let `A` be a Noetherian ring. Tensoring a dualizing complex for `A` with an invertible object of
`D(A)` again gives a dualizing complex for `A`. Together with [Stacks, Tag 0A7F] — two dualizing
complexes differ by derived tensor product with an invertible object — this says that the
dualizing complexes of `A` form a single orbit of the group of invertible objects.

One consequence: whether the derived base change of a dualizing complex along a ring map
`A → B` is a dualizing complex for `B` does not depend on which dualizing complex for `A` is
used, because derived base change carries invertible objects to invertible objects.

## Main results

* `Dualizing.isDualizingComplex_derivedTensor_of_isLocallyShiftedUnit`: the derived tensor
  product of a dualizing complex with an object that is, near every prime, a shifted copy of the
  ring is a dualizing complex.
* `Dualizing.isDualizingComplex_tensor_of_isInvertible`: the converse of [Stacks, Tag 0A7F] — the
  derived tensor product of a dualizing complex with an invertible object is dualizing.
* `Dualizing.isDualizingComplex_derivedExtensionScalars_congr`: if the derived base change of one
  dualizing complex for `A` is dualizing for `B`, then so is the derived base change of every
  dualizing complex for `A`.

## Implementation notes

Invertibility is the predicate of [Stacks, Tag 0FFN] for the canonical derived tensor product of
[Stacks, Tag 0FNQ], which is available because the module universe is the ring's own. Tag 0A7F is
stated for an unspecified monoidal structure whose tensor bifunctor is a derived tensor product;
any two derived tensor products agree on each pair of objects, and both have the ring in degree
zero as unit.

## References

* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-- Tensoring with the ring placed in degree `n` is the shift by `-n`: the derived tensor product
has the ring in degree zero as a right unit and commutes with shifts in the second variable. -/
private def derivedTensorSingleIso {R : Type u} [CommRing R] (T : DerivedTensorProduct R)
    (Y : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (T.tensor.obj Y).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)) ≅ Y⟦-n⟧ :=
  (T.tensor.obj Y).mapIso (((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
      (-n) n 0 (by lia)).app (ModuleCat.of R R)).symm ≪≫
    ((T.tensor.obj Y).commShiftIso (-n)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≪≫
    (shiftFunctor _ (-n)).mapIso (T.rightUnitor.app Y)

/-- An object with a two-sided derived tensor inverse up to the ring in degree zero is invertible
for the canonical derived monoidal structure. -/
private theorem isInvertible_of_derivedTensor_iso_single (R : Type u) [CommRing R]
    (L Linv : DerivedCategory (ModuleCat.{u} R))
    (h₁ : Nonempty (((canonicalDerivedTensorProductFunctor R).obj L).obj Linv ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    (h₂ : Nonempty (((canonicalDerivedTensorProductFunctor R).obj Linv).obj L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    MonoidalCategory.IsInvertible L := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    R).choose_spec.choose_spec.choose
  exact ⟨{ inv := Linv
           isoLeft := (e.app L).app Linv ≪≫ h₁.some ≪≫ (monoidalUnitIsoSingleFunctorObj R).symm
           isoRight := (e.app Linv).app L ≪≫ h₂.some ≪≫ (monoidalUnitIsoSingleFunctorObj R).symm }⟩

/-- The derived tensor product of a dualizing complex for a Noetherian ring with an object that
is, near every prime, a shifted copy of the ring is a dualizing complex. -/
public theorem isDualizingComplex_derivedTensor_of_isLocallyShiftedUnit
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (X L : DerivedCategory (ModuleCat.{u} A)) (hX : IsDualizingComplex X)
    (hL : DerivedCategory.Invertible.IsLocallyShiftedUnit L) :
    IsDualizingComplex (((canonicalDerivedTensorProductFunctor A).obj X).obj L) := by
  let P : A → Prop := fun f => ∃ n : ℤ,
    Nonempty ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A (Localization.Away f))).functor.obj L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f)))
  have hspan : Ideal.span (Set.range (Subtype.val : {f : A // P f} → A)) = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hfL⟩ := hL p hp.isPrime
    exact hf (hle (Ideal.subset_span ⟨⟨f, hfL⟩, rfl⟩))
  refine isDualizingComplex_of_localizations (Subtype.val : {f : A // P f} → A) _ hspan ?_
  rintro ⟨f, n, ⟨eL⟩⟩
  let Rf := Localization.Away f
  let D := totalDerivedExtensionScalars.{u, u, u} (algebraMap A Rf)
  refine isDualizingComplex_of_iso ?_ (isDualizingComplex_shift _ (isDualizingComplex_of_iso
    ((DerivedCategory.Invertible.localizationAwayIso.{u, u} f).app X).symm
    (isDualizingComplex_localizationAway f X hX)) (-n))
  exact (derivedTensorSingleIso (canonicalDerivedTensorProduct Rf) (D.functor.obj X) n).symm ≪≫
    ((canonicalDerivedTensorProductFunctor Rf).obj (D.functor.obj X)).mapIso eL.symm ≪≫
    RingTheory.TorProducts.derivedTensorBaseChangeIso (algebraMap A Rf) D X L ≪≫
    (DerivedCategory.Invertible.localizationAwayIso.{u, u} f).app _

/-- The derived tensor product of a dualizing complex for a Noetherian ring with an invertible
object of its derived category is a dualizing complex. -/
public theorem isDualizingComplex_tensor_of_isInvertible
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X L : DerivedCategory (ModuleCat.{u} A)} (hX : IsDualizingComplex X)
    (hL : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
      MonoidalCategory.IsInvertible L) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    IsDualizingComplex (X ⊗ L) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    A).choose_spec.choose_spec.choose
  exact isDualizingComplex_of_iso ((e.app X).app L).symm
    (isDualizingComplex_derivedTensor_of_isLocallyShiftedUnit X L hX
      ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit L).1.mp hL))

/-- Two dualizing complexes for a Noetherian ring differ by derived tensor product with an object
that is, near every prime, a shifted copy of the ring, for the canonical derived tensor product of
[Stacks, Tag 0FNQ]. -/
private theorem exists_isLocallyShiftedUnit_iso_derivedTensor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X Y : DerivedCategory (ModuleCat.{u} A)}
    (hX : IsDualizingComplex X) (hY : IsDualizingComplex Y) :
    ∃ L : DerivedCategory (ModuleCat.{u} A),
      DerivedCategory.Invertible.IsLocallyShiftedUnit L ∧
        Nonempty (Y ≅ ((canonicalDerivedTensorProductFunctor A).obj X).obj L) := by
  obtain ⟨T, m, ⟨⟨eT⟩, ⟨eU⟩⟩, L, hL, ⟨eY⟩⟩ :=
    IsDualizingComplex.exists_iso_derivedTensorProduct_invertible.{u, u} hX hY
  let g := derivedTensorGeneralObjIso.{u, u} T (canonicalDerivedTensorProduct A).toGeneral
  obtain ⟨Linv, h₁, h₂⟩ : ∃ Linv : DerivedCategory (ModuleCat.{u} A),
      Nonempty (((canonicalDerivedTensorProductFunctor A).obj L).obj Linv ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ∧
      Nonempty (((canonicalDerivedTensorProductFunctor A).obj Linv).obj L ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
    let := m
    obtain ⟨d⟩ := hL
    let eUA : 𝟙_ (DerivedCategory (ModuleCat.{u} A)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
      eU ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (ULift.moduleEquiv : ULift.{u} A ≃ₗ[A] A).toModuleIso
    exact ⟨d.inv,
      ⟨(g L d.inv).symm ≪≫ ((eT.app L).app d.inv).symm ≪≫ d.isoLeft ≪≫ eUA⟩,
      ⟨(g d.inv L).symm ≪≫ ((eT.app d.inv).app L).symm ≪≫ d.isoRight ≪≫ eUA⟩⟩
  refine ⟨L, ?_, ⟨eY ≪≫ g X L⟩⟩
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  exact (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit L).1.mp
    (isInvertible_of_derivedTensor_iso_single A L Linv h₁ h₂)

/-- If the derived base change along `f : A →+* B` of one
dualizing complex for `A` is a dualizing complex for `B`, then the derived base change of every
dualizing complex for `A` is a dualizing complex for `B`. -/
public theorem isDualizingComplex_derivedExtensionScalars_congr
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) {X Y : DerivedCategory (ModuleCat.{u} A)}
    (hX : IsDualizingComplex X) (hY : IsDualizingComplex Y)
    (hXB : IsDualizingComplex ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj X)) :
    IsDualizingComplex ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj Y) := by
  obtain ⟨L, hL, ⟨eY⟩⟩ := exists_isLocallyShiftedUnit_iso_derivedTensor hX hY
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  refine isDualizingComplex_of_iso ?_
    (isDualizingComplex_derivedTensor_of_isLocallyShiftedUnit (D.functor.obj X)
      (D.functor.obj L) hXB
      ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit (D.functor.obj L)).1.mp
        (DerivedCategory.Invertible.isInvertible_derivedExtensionScalars f L
          ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit L).1.mpr hL))))
  exact RingTheory.TorProducts.derivedTensorBaseChangeIso f D X L ≪≫ D.functor.mapIso eY.symm

end Dualizing

end
