module

public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Gorenstein ring is Cohen--Macaulay

A Noetherian ring all of whose localizations at primes are Gorenstein local rings is
Cohen--Macaulay, that is, all of those localizations have depth equal to their Krull dimension.

## Main results

* `Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing` — a Gorenstein local ring is
  Cohen--Macaulay.
* `Dualizing.IsGorensteinRing.isCohenMacaulayRing` — a Gorenstein ring is Cohen--Macaulay.

## References

* [Stacks Project, Tag 0DW8](https://stacks.math.columbia.edu/tag/0DW8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The depth of a local ring, read off lists of ring elements, is its depth as a module over
itself. -/
private theorem localRingDepth_eq_depthSup (A : Type*) [CommRing A] [IsLocalRing A] :
    localRingDepth A = Module.depthSup A (IsLocalRing.maximalIdeal A) A := by
  rw [localRingDepth, Module.depthSup_eq_iSup]
  exact le_antisymm
    (iSup_le fun s => le_iSup₂_of_le s.val s.property le_rfl)
    (iSup_le fun rs => iSup_le fun hrs => le_iSup_of_le ⟨rs, hrs⟩ le_rfl)

/-- The two forms of the Cohen--Macaulay condition on a Noetherian local ring agree: being
Cohen--Macaulay as a module over itself is depth equal to Krull dimension. -/
@[ega "IV 7.3.9" "(i), special case"]
private theorem isCohenMacaulayLocalRing_iff_propForm (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    IsCohenMacaulayLocalRing A ↔ IsCohenMacaulayLocalRingPropForm A := by
  show (Module.depthSup A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) =
      Module.supportDim A A ↔
    (localRingDepth A : WithBot ℕ∞) = ringKrullDim A
  rw [← Module.supportDim_self_eq_ringKrullDim, ← localRingDepth_eq_depthSup]

/-- A shift of a module placed in degree zero is cohomologically concentrated in one degree,
namely in the degree the shift moves zero to. -/
private theorem isCohomologicallyConcentratedInOneDegree_shift_single
    {A : Type u} [CommRing A] (M : ModuleCat.{u} A) (m : ℤ) :
    IsCohomologicallyConcentratedInOneDegree
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦-m⟧) := by
  refine ⟨m, fun i hi => ?_⟩
  have e : (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦-m⟧) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) m).obj M :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-m) m 0 (by omega)).app M
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) m).obj M)) :=
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) m M i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) m).obj M))
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e)

/-- A Gorenstein local ring is Cohen--Macaulay. -/
public theorem IsGorensteinLocalRing.isCohenMacaulayLocalRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsGorensteinLocalRing A) :
    IsCohenMacaulayLocalRing A := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0}
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) hA
  exact ((isCohenMacaulay_tfae_dualizingComplex _ hm).out 2 1).mp
    (isCohomologicallyConcentratedInOneDegree_shift_single (ModuleCat.of A A) m)

/-- A Gorenstein ring is Cohen--Macaulay: its localization at every prime is a Cohen--Macaulay
local ring. -/
@[stacks 0DW8]
public theorem IsGorensteinRing.isCohenMacaulayRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hA : IsGorensteinRing A) : IsCohenMacaulayRing A := fun p _hp =>
  (isCohenMacaulayLocalRing_iff_propForm (Localization.AtPrime p)).mp
    (IsGorensteinLocalRing.isCohenMacaulayLocalRing (Localization.AtPrime p) (hA p))

end Dualizing

end
