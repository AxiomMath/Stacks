module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.InvertibleTransport
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
public import StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import Mathlib.RingTheory.Localization.Away.Basic
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# A global criterion for Gorenstein rings

Let `A` be a Noetherian ring admitting a dualizing complex `K`. Then `A` is Gorenstein exactly
when `K` is an invertible object of `D(A)` for the derived tensor product.

## Main results

* `Dualizing.isGorensteinRing_iff_isInvertible` — **[Stacks, Tag 0DW9 (1)(a)]**, the global
  criterion, for a complex whose module universe contains the ring's.
* `Dualizing.isGorensteinRing_iff_isInvertible_canonical` — the same criterion read at the
  canonical derived tensor product, which exists when the two universes agree.

## Implementation notes

Both directions are checked prime by prime, against the local criterion
`Dualizing.isGorensteinLocalRing_iff_isInvertible_localization` [Stacks, Tag 0DW9 (1)(b)] and the
Zariski-local description of invertibility
`DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit` [Stacks, Tag 0FNT]. The two are
not stated over the same neighbourhoods: invertibility is a condition on principal localizations,
while Gorensteinness constrains the complex only after localizing at a prime. Passing from the
second to the first is `Dualizing.IsDualizingComplex.exists_isLocalized_iso_shift_single`, which
spreads a trivialization at a prime out to a principal neighbourhood of it. In the other direction
invertibility is carried along derived extension of scalars, after the coefficient equivalence of
`Dualizing.isInvertible_iff_scalarLift` has moved it into the universe the localized complex lives
in.

The monoidal structure is the canonical derived tensor product of [Stacks, Tag 0FNQ], which is
extracted from `DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory` rather than
found by instance search: a derived category carries no ambient monoidal structure.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- A dualizing complex over a Noetherian Gorenstein ring is invertible for the canonical derived
tensor product. -/
theorem isInvertible_of_isGorensteinRing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) (hG : Dualizing.IsGorensteinRing A) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    MonoidalCategory.IsInvertible K := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  apply (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit K).1.mpr
  show ∀ p : Ideal A, p.IsPrime →
      ∃ f : A, f ∉ p ∧ ∃ n : ℤ,
        Nonempty
          (((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization.Away f))).functor.obj K) ≅
            ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
              (ModuleCat.of (Localization.Away f) (Localization.Away f))))
  intro p hp
  obtain ⟨f, hfp, n, he⟩ :=
      IsDualizingComplex.exists_isLocalized_iso_shift_single K hK p (hG p)
  let Rf := Localization.Away f
  let Uout := ModuleCat.uliftFunctor.{u} Rf
  let D := totalDerivedExtensionScalars.{u, u, u} (algebraMap A Rf)
  let eD : D.functor.obj ((ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj K) ≅
      D.functor.obj K :=
    D.functor.mapIso ((uliftDerivedSelfIso A).app K)
  let eShift :
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Rf) 0).obj
          (Uout.obj (ModuleCat.of Rf Rf)))⟦-n⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Rf) n).obj (ModuleCat.of Rf Rf) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} Rf)).shiftIso (-n) n 0 (by omega)).app
          (Uout.obj (ModuleCat.of Rf Rf)) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} Rf) n).mapIso
        (ULift.moduleEquiv : ULift.{u} Rf ≃ₗ[Rf] Rf).toModuleIso
  exact ⟨f, hfp, n, ⟨eD.symm ≪≫ he.some ≪≫ eShift⟩⟩

/-- A Noetherian ring with a dualizing complex that is invertible for the canonical derived
tensor product is Gorenstein. -/
theorem isGorensteinRing_of_isInvertible
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    MonoidalCategory.IsInvertible K → Dualizing.IsGorensteinRing A := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  intro hInv p hp
  let B := Localization.AtPrime p
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K
  have hKloc : MonoidalCategory.IsInvertible Kloc :=
    DerivedCategory.Invertible.isInvertible_derivedExtensionScalars (algebraMap A B)
      ((ModuleCat.uliftFunctor.{u} A).mapDerivedCategory.obj K)
      (isInvertible_of_iso ((uliftDerivedSelfIso A).app K).symm hInv)
  have hLift :
      let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        (ULift.{u} B)).choose
      MonoidalCategory.IsInvertible
        ((StacksDraft.TorAmplitude.scalarLift.{u, u} (R := B)).mapDerivedCategory.obj
          Kloc) := by
    let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (ULift.{u} B)).choose
    exact isInvertible_of_iso
      ((scalarLiftDerivedIso.{u, u} B).app Kloc)
      (DerivedCategory.Invertible.isInvertible_derivedExtensionScalars
        (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom Kloc hKloc)
  exact (isGorensteinLocalRing_iff_isInvertible_localization K hK p).2
    ((isInvertible_iff_scalarLift.{u, u} B Kloc).mpr hLift)

/-- **Stacks Project, Tag 0DW9 (1)(a).** A Noetherian ring with a dualizing complex is
Gorenstein exactly when that complex is invertible, for the canonical derived tensor product
of [Stacks, Tag 0FNQ], which is available when the module universe is the ring's own. -/
@[stacks 0DW9 "(1)(a)"]
theorem isGorensteinRing_iff_isInvertible_canonical
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    Dualizing.IsGorensteinRing A ↔ MonoidalCategory.IsInvertible K :=
  ⟨isInvertible_of_isGorensteinRing K hK, isGorensteinRing_of_isInvertible K hK⟩

/-- Gorensteinness of a Noetherian ring transports along a ring isomorphism, even one that
changes the universe: the isomorphism matches up the primes of the two rings and their
localizations at corresponding primes. -/
private theorem isGorensteinRing_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (e : R ≃+* S) (hS : IsGorensteinRing S) : IsGorensteinRing R := by
  intro p hp
  let q : Ideal S := p.comap e.symm.toRingHom
  have hmap : p.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, q, Ideal.mem_comap]
    refine ⟨fun ⟨r, hr, hrx⟩ h => hr (by simpa [← hrx] using h), fun h => ⟨e.symm x, h, by simp⟩⟩
  exact isGorensteinLocalRing_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (M := p.primeCompl) (T := q.primeCompl)
      (Localization.AtPrime p) (Localization.AtPrime q) e hmap) (hS q)

/-- **Stacks Project, Tag 0DW9 (1)(a)**, for a dualizing complex whose module universe is larger
than the ring's. A Noetherian ring with a dualizing complex is Gorenstein if and only if that
complex is invertible, the tensor product being the one transported along the coefficient
equivalence; invertibility does not depend on which of the two is used. -/
@[stacks 0DW9 "(1)(a) at a larger module universe"]
theorem isGorensteinRing_iff_isInvertible
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : Dualizing.IsDualizingComplex K) :
    letI := derivedCategoryMonoidal.{u, v} A
    IsGorensteinRing A ↔ MonoidalCategory.IsInvertible K := by
  let C := ULift.{v} A
  let e : A ≃+* C := ULift.ringEquiv.symm
  have := isNoetherianRing_of_ringEquiv A e
  let := derivedCategoryMonoidal.{u, v} A
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory C).choose
  let K' := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := A)).mapDerivedCategory.obj K
  exact (Iff.intro (isGorensteinRing_of_ringEquiv e.symm)
      (isGorensteinRing_of_ringEquiv e)).trans
    ((isGorensteinRing_iff_isInvertible_canonical (A := C) K' (dualizing_scalarLift K hK)).trans
      (isInvertible_iff_scalarLift.{u, v} A K).symm)

end Dualizing

end
