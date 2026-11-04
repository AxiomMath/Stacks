module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIsoGeneral
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
public import StacksFrontier.RingTheory.Dualizing.NormalizedUniqueness
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# Perfect objects with one-dimensional fibres and trivial dual

Let `A` be a commutative ring and `P` a perfect object of `D(A)` whose derived fibre at every
maximal ideal of `A` is concentrated in a single degree with one-dimensional cohomology. Then
`P` is locally a shifted unit, hence invertible by [stacks 0FNT]; if moreover derived Hom from
`P` into the tensor unit is the tensor unit, then `P` is the tensor unit.

The invertibility of [stacks 0FNT] is for the monoidal structure of [stacks 0FNQ], while derived
Hom is that of the tensor--Hom adjunction of [stacks 0A63]; the two tensor products, and hence
the two tensor units, are identified.

## Main definitions

* `Dualizing.monoidalTensorIsoDerivedHomTensor` — the tensor product of the monoidal structure of
  [stacks 0FNQ] is the tensor of the tensor--Hom adjunction of [stacks 0A63].
* `Dualizing.derivedTensorUnitIsoMonoidalUnit` — the two tensor units agree.

## Main results

* `Dualizing.nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank` — a perfect object whose
  derived fibre at every maximal ideal is concentrated in one degree with one-dimensional
  cohomology, and whose internal Hom into the tensor unit is the tensor unit, is the tensor unit.
* `Dualizing.exists_iso_single_of_maximalFibre_finrank` — over a local ring, a perfect object
  whose derived fibre at the maximal ideal is concentrated in one degree with one-dimensional
  cohomology is the ring placed in a single degree.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section Bridge

variable (A : Type u) [CommRing A]

/-- **The tensor product of the monoidal structure of [stacks 0FNQ] is the tensor of the
tensor--Hom adjunction of [stacks 0A63].** -/
@[no_expose] def monoidalTensorIsoDerivedHomTensor (P Q : DerivedCategory (ModuleCat.{u} A)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    P ⊗ Q ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj (P, Q) := by
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  let eT := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    A).choose_spec.choose_spec.choose
  exact (eT.app P).app Q ≪≫
    derivedTensorGeneralObjIso (canonicalDerivedTensorProduct A).toGeneral
      (canonicalDerivedTensorProductGeneral.{u, u} A) P Q ≪≫
    (derivedHomAdjunctionTensorNatIsoGeneral.{u, u} A).app (P, Q)

/-- **The tensor unit of [stacks 0A63] is the monoidal unit of [stacks 0FNQ].** -/
@[no_expose] def derivedTensorUnitIsoMonoidalUnit :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} A)) := by
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  let one := StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A
  exact (ρ_ one).symm ≪≫
    monoidalTensorIsoDerivedHomTensor A one (𝟙_ (DerivedCategory (ModuleCat.{u} A))) ≪≫
    StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, u, u + 1} A _

end Bridge

/-- **A perfect object with a concentrated one-dimensional fibre at every maximal ideal has a
tensor inverse for [stacks 0A63].** -/
theorem exists_derivedHomTensor_iso_derivedTensorUnit_of_maximalFibre_finrank
    {A : Type u} [CommRing A] (P : DerivedCategory (ModuleCat.{u} A))
    (hperf : StacksDraft.Perfect.IsPerfect P)
    (hfib : ∀ (m : Ideal A) (_ : m.IsMaximal), ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank m.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj P)) = if i = n then 1 else 0) :
    ∃ Q : DerivedCategory (ModuleCat.{u} A),
      Nonempty ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.obj
        (P, Q) ≅ StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  have hlsu : DerivedCategory.Invertible.IsLocallyShiftedUnit P :=
    DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank
      P hperf hfib
  obtain ⟨d⟩ := (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit P).1.mpr hlsu
  exact ⟨d.inv, ⟨(monoidalTensorIsoDerivedHomTensor A P d.inv).symm ≪≫ d.isoLeft ≪≫
    (derivedTensorUnitIsoMonoidalUnit A).symm⟩⟩

/-- Let `P` be a perfect object of `D(A)` whose derived fibre at every maximal ideal of `A` has a
single cohomology module, of dimension one over the residue field.  If derived Hom from `P` into
the tensor unit is the tensor unit, then `P` is the tensor unit. -/
theorem nonempty_iso_derivedTensorUnit_of_maximalFibre_finrank
    {A : Type u} [CommRing A] (P : DerivedCategory (ModuleCat.{u} A))
    (hperf : StacksDraft.Perfect.IsPerfect P)
    (hfib : ∀ (m : Ideal A) (_ : m.IsMaximal), ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank m.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj P)) = if i = n then 1 else 0)
    (h : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).hom.obj
        (Opposite.op P, StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) ≅
      StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) :
    Nonempty (P ≅ StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A) := by
  obtain ⟨Q, ⟨e⟩⟩ :=
    exists_derivedHomTensor_iso_derivedTensorUnit_of_maximalFibre_finrank P hperf hfib
  exact nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A)
    (StacksDraft.DerivedHom.derivedTensorUnit.{u, u, u + 1} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, u, u + 1} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft_natural.{u, u, u + 1} A) P Q e h

/-- Over a local ring, a perfect object whose derived fibre at the maximal ideal has a single
cohomology module of dimension one is the ring placed in a single degree. -/
theorem exists_iso_single_of_maximalFibre_finrank
    {A : Type u} [CommRing A] [IsLocalRing A] (P : DerivedCategory (ModuleCat.{u} A))
    (hperf : StacksDraft.Perfect.IsPerfect P)
    (hfib : ∀ (m : Ideal A) (_ : m.IsMaximal), ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank m.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj P)) = if i = n then 1 else 0) :
    ∃ n : ℤ, Nonempty (P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)) :=
  exists_iso_single_of_isLocallyShiftedUnit P
    (DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank
      P hperf hfib)

end Dualizing

end
