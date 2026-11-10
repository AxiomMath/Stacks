module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom

/-!
# Local structure of an étale homomorphism of local rings

An étale local homomorphism of Noetherian local rings is, up to isomorphism, the localization at
a prime of a standard étale algebra.

## Main results

* `Algebra.exists_standardEtalePair_localization` exhibits the target as the localization of a
  standard étale algebra at a prime.

## Implementation notes

The essentially-finite-type hypothesis makes the target a localization of a finite type
subalgebra, and étaleness of the induced homomorphism of local rings transfers to that
subalgebra. The local structure theorem for unramified algebras then produces a standard étale
presentation on a basic open, and the two localizations are identified by transitivity of
localization.

## References

* [Stacks Project, Tag 025B](https://stacks.math.columbia.edu/tag/025B)
-/

@[expose] public section

universe u v

namespace Algebra

/-- If `A → B` is an étale local homomorphism of Noetherian local rings, then `B` is isomorphic as
an `A`-algebra to the localization of a standard étale `A`-algebra at a prime. -/
@[stacks 025B]
theorem exists_standardEtalePair_localization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (h : RingHom.IsEtaleLocalHom (algebraMap A B)) :
    ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (hq : q.IsPrime),
      letI := hq
      Nonempty (B ≃ₐ[A] Localization.AtPrime q) := by
  let : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp h.2.2
  let C : Subalgebra A B := Algebra.EssFiniteType.subalgebra A B
  let qC : Ideal C := (IsLocalRing.maximalIdeal B).comap (algebraMap C B)
  have hqC : qC.IsPrime := Ideal.IsPrime.comap (algebraMap C B)
  let p : Ideal A := IsLocalRing.maximalIdeal A
  let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : qC.IsPrime := hqC
  have hcomap : qC.comap (algebraMap A C) = p := by
    rw [Ideal.comap_comap, show (algebraMap C B).comp (algebraMap A C) =
      algebraMap A B from by ext a; simp, IsLocalRing.maximalIdeal_comap]
  let : qC.LiesOver p := ⟨hcomap.symm⟩
  have hloc : ∀ (q : Ideal C) [q.IsPrime], q = qC → IsLocalization q.primeCompl B := by
    intro q _ hq
    have : q.primeCompl = Algebra.EssFiniteType.submonoid A B := by
      ext x
      change x ∉ q ↔ IsUnit (algebraMap C B x)
      rw [hq]
      exact IsLocalRing.notMem_maximalIdeal
    rw [this]
    exact Algebra.EssFiniteType.isLocalization A B
  have : IsLocalization qC.primeCompl B := hloc qC rfl
  let eB : B ≃ₐ[C] Localization.AtPrime qC :=
    IsLocalization.algEquiv qC.primeCompl B (Localization.AtPrime qC)
  have : Algebra.FormallyUnramified A B :=
    RingHom.formallyUnramified_algebraMap.mp h.2.1
  let : Algebra.FormallyUnramified A (Localization.AtPrime qC) :=
    Algebra.FormallyUnramified.of_equiv (eB.restrictScalars A)
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp h.1
  have : Module.Flat A (Localization.AtPrime qC) :=
    Module.Flat.of_linearEquiv (eB.restrictScalars A).symm.toLinearEquiv
  let f := Localization.localRingHom p qC (algebraMap A C) hcomap.symm
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime qC) :=
    Localization.AtPrime.algebraOfLiesOver p qC
  let : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime qC) := inferInstance
  let : Algebra.FiniteType A C := inferInstance
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  let : IsNoetherianRing (Localization.AtPrime qC) :=
    IsLocalization.isNoetherianRing qC.primeCompl _
      (Algebra.FiniteType.isNoetherianRing A C)
  let : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hformLoc : Algebra.FormallyUnramified (Localization.AtPrime p)
      (Localization.AtPrime qC) :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  have hflatLoc : Module.Flat (Localization.AtPrime p) (Localization.AtPrime qC) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime qC)).2 inferInstance
  have hessLoc : Algebra.EssFiniteType (Localization.AtPrime p)
      (Localization.AtPrime qC) := Algebra.EssFiniteType.of_comp A _ _
  have hlocal : RingHom.IsEtaleLocalHom f := by
    simp only [RingHom.IsEtaleLocalHom]
    exact ⟨RingHom.flat_algebraMap_iff.mpr hflatLoc,
      RingHom.formallyUnramified_algebraMap.mpr hformLoc,
      RingHom.essFiniteType_algebraMap.mpr hessLoc⟩
  have hAt : Algebra.IsEtaleAt A qC :=
    (Algebra.isEtaleAt_iff_isEtaleLocalHom p qC).mpr hlocal
  obtain ⟨g, hgq, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := A) (S := C) qC
  let : Algebra.IsStandardEtale A (Localization.Away g) := hstd
  let Pst : StandardEtalePresentation A (Localization.Away g) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let e : Pst.P.Ring ≃ₐ[A] Localization.Away g := Pst.equivRing.symm
  let qG : Ideal (Localization.Away g) := qC.map (algebraMap C (Localization.Away g))
  let : qG.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ hqC
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgq)
  have hqunderRaw :
      qG.comap (algebraMap C (Localization (Submonoid.powers g))) = qC := by
    simpa only [Localization.Away] using
      (IsLocalization.under_map_of_isPrime_disjoint (.powers g) _ hqC
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgq))
  let qC' : Ideal C :=
    qG.comap (algebraMap C (Localization (Submonoid.powers g)))
  let : qC'.IsPrime := Ideal.IsPrime.comap _
  have : IsLocalization qC'.primeCompl B := hloc qC' hqunderRaw
  let eB' : B ≃ₐ[C] Localization.AtPrime qC' :=
    IsLocalization.algEquiv qC'.primeCompl B (Localization.AtPrime qC')
  let qP : Ideal Pst.P.Ring := qG.comap e.toRingHom
  have hqP : qP.IsPrime := Ideal.IsPrime.comap e.toRingHom
  let : qP.IsPrime := hqP
  let eLoc : Localization.AtPrime qC' ≃ₐ[C] Localization.AtPrime qG :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers g) qG
  let eStd : Localization.AtPrime qP ≃ₐ[A] Localization.AtPrime qG :=
    Localization.localAlgEquiv qP qG e rfl
  exact ⟨Pst.P, qP, hqP,
    ⟨(eB'.restrictScalars A).trans (eLoc.restrictScalars A) |>.trans eStd.symm⟩⟩

end Algebra
