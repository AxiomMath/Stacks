module

public import StacksFrontier.RingTheory.Dualizing.InvertibleTransport
public import StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# Invertibility over a local ring is read off the cohomology

Over a local ring an object of the derived category is invertible for the derived tensor product
exactly when its cohomology is concentrated in a single degree and is free of rank one there.

## Main results

* `Dualizing.isInvertible_iff_exists_iso_single` — over a local ring, invertibility is being a
  shifted copy of the ring.
* `Dualizing.exists_iso_single_iff_homology` — over any ring, being a shifted copy of a module is
  concentration of the cohomology in one degree together with the identification of that
  cohomology module.
* `Dualizing.isInvertible_iff_homology_concentrated_free` — the combination: a homological
  criterion for invertibility over a local ring.

## Implementation notes

The forward half of `Dualizing.isInvertible_iff_exists_iso_single` is
`DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit` of [Stacks, Tag 0FNT] read at the
maximal ideal: the element the local trivialization is taken away from misses the maximal ideal
and is therefore a unit, so localizing away from it changes nothing. That last step is
`Dualizing.unit_local_shift_iso`, proved for the local trivialization of a dualizing complex.

The backward half needs that the ring placed in degree `n` is itself locally a shifted unit, which
is the definition at the element `1`: localization away from `1` is restriction of scalars along
the induced isomorphism, and restriction of scalars along a ring isomorphism takes the ring in
degree `n` to the ring in degree `n`. The latter is the generic form of
`Dualizing.restrictScalarsSingleIso`, which is stated only for the isomorphism induced by a unit.

The criterion is a statement about one monoidal structure, the canonical one that
`DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory` produces, and it is
introduced where it is needed rather than made an instance: a second ambient monoidal structure on
a derived category breaks instance search.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Restriction of scalars along a ring isomorphism takes the ring placed in degree `n` to the
ring placed in degree `n`.

This is the generic form of `Dualizing.restrictScalarsSingleIso`, which is stated for the
isomorphism `R ≃+* R_g` induced by a unit `g`. -/
private noncomputable def restrictScalarsEquivSingleIso {R S : Type u} [CommRing R] [CommRing S]
    (ε : R ≃+* S) (n : ℤ) :
    (ModuleCat.restrictScalars ε.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R) := by
  let F := ModuleCat.restrictScalars ε.toRingHom
  letI : F.Additive := inferInstance
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesColimitsOfSize.{0, 0} F := inferInstance
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let U := ModuleCat.of S S
  let eFU : F.obj U ≅ ModuleCat.of R R := ModuleCat.restrictScalarsIsoOfEquiv ε
  let P : CochainComplex (ModuleCat.{u} S) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) n).obj U
  exact F.mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) n).app U) ≪≫
    F.mapDerivedCategoryFactors.app P ≪≫
    (DerivedCategory.Q (C := ModuleCat.{u} R)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app U) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) n).app (F.obj U)).symm ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).mapIso eFU

/-- The ring placed in degree `n` is locally a shifted copy of the ring: it already is one, on the
principal neighbourhood at `1`. -/
private theorem isLocallyShiftedUnit_single (R : Type u) [CommRing R] (n : ℤ) :
    DerivedCategory.Invertible.IsLocallyShiftedUnit
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)) := by
  intro p hp
  exact ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), n,
    ⟨(derivedAwayUnitIso (1 : R) isUnit_one).app _ ≪≫
      restrictScalarsEquivSingleIso
        (IsLocalization.atUnit R (Localization.Away (1 : R)) 1 isUnit_one).symm.toRingEquiv n⟩⟩

/-- **Over a local ring an object of the derived category is invertible exactly when it is a
shifted copy of the ring.** -/
public theorem isInvertible_iff_exists_iso_single {B : Type u} [CommRing B] [IsLocalRing B]
    (M : DerivedCategory (ModuleCat.{u} B)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    MonoidalCategory.IsInvertible M ↔
      ∃ n : ℤ, Nonempty (M ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) n).obj (ModuleCat.of B B)) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  constructor
  · intro hM
    obtain ⟨g, hg, n, hshift⟩ :=
      (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit M).1.mp hM
        (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal.isMaximal B).isPrime
    exact ⟨n, unit_local_shift_iso g (IsLocalRing.notMem_maximalIdeal.mp hg) n M hshift⟩
  · rintro ⟨n, ⟨e⟩⟩
    exact isInvertible_of_iso_symm e
      ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit _).1.mpr
        (isLocallyShiftedUnit_single B n))

/-- **A derived object is a module placed in a single degree exactly when its cohomology is
concentrated in that degree and agrees there with the module.** -/
public theorem exists_iso_single_iff_homology {R : Type u} [CommRing R]
    (M : DerivedCategory (ModuleCat.{u} R)) (N : ModuleCat.{u} R) (n : ℤ) :
    Nonempty (M ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj N) ↔
      (∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) ∧
        Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M ≅ N) := by
  have homology_iso : ∀ {Y}, (M ≅ (DerivedCategory.singleFunctor _ n).obj Y) →
      ((DerivedCategory.homologyFunctor _ n).obj M ≅ Y) := fun e =>
    (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app _
  constructor
  · rintro ⟨e⟩
    refine ⟨fun i hi => ?_, ⟨homology_iso e⟩⟩
    · refine ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e).isZero_iff.mpr ?_
      rcases lt_or_gt_of_ne hi with h | h
      · exact (DerivedCategory.isGE_iff _ n).mp inferInstance i h
      · exact (DerivedCategory.isLE_iff _ n).mp inferInstance i h
  · rintro ⟨hvan, ⟨eN⟩⟩
    have : M.IsGE n := (DerivedCategory.isGE_iff M n).mpr fun i hi => hvan i (by omega)
    have : M.IsLE n := (DerivedCategory.isLE_iff M n).mpr fun i hi => hvan i (by omega)
    obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
    exact ⟨e ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).mapIso ((homology_iso e).symm ≪≫ eN)⟩

/-- **Invertibility over a local ring is a condition on the cohomology:** an object of the derived
category of a local ring is invertible exactly when its cohomology vanishes outside one degree and
is the ring itself in that degree. -/
public theorem isInvertible_iff_homology_concentrated_free {B : Type u} [CommRing B]
    [IsLocalRing B] (M : DerivedCategory (ModuleCat.{u} B)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    MonoidalCategory.IsInvertible M ↔
      ∃ n : ℤ,
        (∀ i : ℤ, i ≠ n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj M)) ∧
          Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj M ≅
            ModuleCat.of B B) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  exact (isInvertible_iff_exists_iso_single M).trans
    (exists_congr fun n => exists_iso_single_iff_homology M (ModuleCat.of B B) n)

end Dualizing

end
