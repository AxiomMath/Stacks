module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension

/-!
# Cohomological dimension is local on the spectrum

Let `I` be a finitely generated ideal of a commutative ring `A`. Localization at a prime `p` is
flat, so base change for local cohomology (Stacks 0ALZ) identifies the local cohomology of
`A_p` with support in `V(I A_p)` with the localization at `p` of the local cohomology of `A`
with support in `V(I)`. A module vanishes exactly when all its localizations at primes do, so
the local cohomology of `A` vanishes in a degree exactly when all those localizations do, and
the cohomological dimension of `I` is the largest of the cohomological dimensions of the
extended ideals `I A_p`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyModuleLocalizationIso` — the local cohomology of `A_p`
  is the localization at `p` of the local cohomology of `A`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_iff_forall_prime` — vanishing in a degree
  is detected on the local rings.
* `Stacks.LocalCohomology.cohomologicalDimension_eq_sSup_localizations` — the cohomological
  dimension is the supremum of the local ones.

## Implementation notes

The supremum is taken in `ℤ`, over the set of local cohomological dimensions with `-1` adjoined.
Adjoining `-1` makes the formula cover the zero ring, which has no primes; for a nonzero ring it
changes nothing, since every cohomological dimension is at least `-1`.

## References

* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **Local cohomology commutes with localization at a prime.** Restricted back to `A`, the
local cohomology of `A_p` with support in `V(I A_p)` is the localization at `p` of the local
cohomology of `A` with support in `V(I)`. -/
def localCohomologyModuleLocalizationIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (p : PrimeSpectrum A) (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p.asIdeal))).obj
        (localCohomologyModule (Localization.AtPrime p.asIdeal)
          (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (hI.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal)) i) ≅
      ModuleCat.of A (LocalizedModule p.asIdeal.primeCompl
        (localCohomologyModule A I hI (ModuleCat.of A A) i)) := by
  let B := Localization.AtPrime p.asIdeal
  let f := algebraMap A B
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let KB := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  let L := (localCohomologyDerived A I hI).obj K
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let LB := (localCohomologyDerived B (I.map f) (hI.map f)).obj KB
  let eSingle := derivedExtensionScalarsRegularIso.{u} f
  let eBase := (localCohomologyBaseChangeIso.{u, u, u} f I hI).app K
  let eTarget : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      ((localCohomologyDerived B (I.map f) (hI.map f)).obj (D.functor.obj K)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj LB :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
      ((localCohomologyDerived.{u} B (I.map f) (hI.map f)).mapIso eSingle)
  let eChange : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj LB ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj (D.functor.obj L) :=
    eTarget.symm ≪≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso eBase.symm
  let eRes := (ModuleCat.restrictScalars f).mapIso eChange
  let eLoc := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
    p.asIdeal.primeCompl (A := B) i).app L
  exact eRes ≪≫ eLoc

/-- The local cohomology of `A_p` vanishes in a degree exactly when the localization at `p` of
the local cohomology of `A` does. -/
theorem isZero_localCohomologyModule_localization_iff
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (p : PrimeSpectrum A) (i : ℤ) :
    IsZero (localCohomologyModule (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hI.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)) i) ↔
      IsZero (ModuleCat.of A (LocalizedModule p.asIdeal.primeCompl
        (localCohomologyModule A I hI (ModuleCat.of A A) i))) := by
  let B := Localization.AtPrime p.asIdeal
  let f := algebraMap A B
  let M := localCohomologyModule B (I.map f) (hI.map f) (ModuleCat.of B B) i
  have hres : IsZero M ↔ IsZero ((ModuleCat.restrictScalars f).obj M) := by
    rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
    rfl
  let e := localCohomologyModuleLocalizationIso A I hI p i
  exact ⟨fun h => (hres.1 h).of_iso e.symm, fun h => hres.2 (h.of_iso e)⟩

/-- **Vanishing of local cohomology is local on the spectrum.** The local cohomology of `A` with
support in `V(I)` vanishes in a degree exactly when the local cohomology of every local ring
`A_p` with support in `V(I A_p)` does. -/
theorem isZero_localCohomologyModule_iff_forall_prime
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (i : ℤ) :
    IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i) ↔
      ∀ p : PrimeSpectrum A, IsZero
        (localCohomologyModule (Localization.AtPrime p.asIdeal)
          (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (hI.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal)) i) := by
  let M := localCohomologyModule A I hI (ModuleCat.of A A) i
  constructor
  · intro h p
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.1 h
    exact (isZero_localCohomologyModule_localization_iff A I hI p i).mpr
      (ModuleCat.isZero_iff_subsingleton.2 inferInstance)
  · intro h
    refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y => ?_⟩
    exact sub_eq_zero.mp <|
      Module.eq_zero_of_localization_maximal
        (Mₚ := fun J (_ : J.IsMaximal) => LocalizedModule J.primeCompl M)
        (fun J _ => LocalizedModule.mkLinearMap J.primeCompl M) (x - y) (by
          intro J hJ
          let p : PrimeSpectrum A := ⟨J, hJ.isPrime⟩
          have hz := (isZero_localCohomologyModule_localization_iff A I hI p i).mp (h p)
          have hss : Subsingleton (LocalizedModule J.primeCompl M) := by
            simpa [p, M] using ModuleCat.isZero_iff_subsingleton.1 hz
          exact hss.elim _ _)

/-- **Stacks Project, Tag 0DXB.** The cohomological dimension of a finitely generated ideal is
the supremum of the cohomological dimensions of its extensions to the local rings of the
spectrum. -/
@[stacks 0DXB]
theorem cohomologicalDimension_eq_sSup_localizations
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    cohomologicalDimension A I hI =
      sSup (insert (-1 : ℤ) (Set.range fun p : PrimeSpectrum A =>
        cohomologicalDimension (Localization.AtPrime p.asIdeal)
          (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))))) := by
  set localDimensions : Set ℤ := Set.range fun p : PrimeSpectrum A =>
    cohomologicalDimension (Localization.AtPrime p.asIdeal)
      (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
      (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))) with hlocalDimensions
  set d := cohomologicalDimension A I hI with hdDef
  set s := sSup (insert (-1 : ℤ) localDimensions) with hsDef
  have hd : IsLocalCohomologyBound A I hI d := isLocalCohomologyBound_cohomologicalDimension A I hI
  have hUpper : ∀ x ∈ insert (-1 : ℤ) localDimensions, x ≤ d := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · simpa [hx] using hd.1
    · rcases Set.mem_range.mp hx with ⟨p, rfl⟩
      refine cohomologicalDimension_le _ _ _ d ⟨hd.1, fun i hi => ?_⟩
      exact (isZero_localCohomologyModule_iff_forall_prime A I hI i).mp (hd.2 i hi) p
  have hs_le : s ≤ d := csSup_le ⟨-1, Set.mem_insert (-1 : ℤ) localDimensions⟩ hUpper
  have hs_bound : IsLocalCohomologyBound A I hI s := by
    refine ⟨le_csSup ⟨d, hUpper⟩ (Set.mem_insert (-1 : ℤ) localDimensions), fun i hi => ?_⟩
    refine (isZero_localCohomologyModule_iff_forall_prime A I hI i).2 fun p => ?_
    have hle : cohomologicalDimension (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hI.map (algebraMap A (Localization.AtPrime p.asIdeal))) ≤ s :=
      le_csSup ⟨d, hUpper⟩ (Set.mem_insert_of_mem (-1 : ℤ) (Set.mem_range.mpr ⟨p, rfl⟩))
    exact (isLocalCohomologyBound_cohomologicalDimension _ _ _).2 i (lt_of_le_of_lt hle hi)
  exact le_antisymm (cohomologicalDimension_le A I hI s hs_bound) hs_le

end Stacks.LocalCohomology

end
