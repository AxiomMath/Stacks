module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# Connected punctured strict henselizations of normal local domains

The punctured spectrum of a strict henselization of a normal local domain which is not a field is
connected: the strict henselization is again a normal domain ([Stacks, Tag 06DI]), so its spectrum
is irreducible, and the punctured spectrum is a nonempty open subset of it, being nonempty
because a faithfully flat extension has a prime lying over the zero ideal.

This is the local hypothesis of [Stacks, Tag 0BQG] at such a point. The proof first reconciles
the two residue fields `ResidueField R` and `(maximalIdeal R).ResidueField` of a local ring, and
the two notions of strict henselization in the library.

## Main results

* `AlgebraicGeometry.isConnectedPuncturedStrictHenselization_of_isIntegrallyClosed`: the
  connectedness statement.

## References

* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
* [Stacks Project, Tag 0BQG](https://stacks.math.columbia.edu/tag/0BQG)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Normal local domains -/

/-- **The punctured spectrum of a strict henselization of a normal local domain is connected.**
Let `R` be a local domain, integrally closed in its fraction field, and not a field. Every strict
henselization of `R` is a normal domain, so its spectrum is irreducible, and its punctured
spectrum is a nonempty open subset of it. -/
theorem isConnectedPuncturedStrictHenselization_of_isIntegrallyClosed
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hR : ¬ IsField R) : IsConnectedPuncturedStrictHenselization R := by
  intro κsep _ _ _ Rsh _ _ _ h
  let : Algebra (ResidueField R) κsep :=
    ((algebraMap (maximalIdeal R).ResidueField κsep).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κsep :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- a separable closure of the localized residue field is one of the quotient residue field
  let : IsSepClosure (ResidueField R) κsep := by
    have hbot : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
      Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField R))
        (residueFieldEquivMaximalIdealResidueField R) (RingHom.ext fun _ ↦ rfl)
    have htop : Algebra.IsSeparable (maximalIdeal R).ResidueField κsep := IsSepClosure.separable
    exact ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
      Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κsep⟩
  -- a strict henselization in the sense of Stacks 04GP is a henselization
  let : IsLocalRing.IsHenselization R κsep Rsh := by
    let := h.isLocalHom
    refine ⟨h.henselian, h.isFilteredColimitEtale,
      h.residueFieldEquiv.trans (residueFieldEquivMaximalIdealResidueField Rsh).symm, fun x ↦ ?_⟩
    have hcomp : h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κsep
        (algebraMap R (maximalIdeal R).ResidueField x))
        = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
            (algebraMap R (maximalIdeal R).ResidueField x) :=
      DFunLike.congr_fun h.residueFieldEquiv_comp (algebraMap R (maximalIdeal R).ResidueField x)
    have hlast : residueFieldEquivMaximalIdealResidueField Rsh (residue Rsh (algebraMap R Rsh x))
        = algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap R Rsh x) :=
      algebraMap_residueField_residue Rsh (algebraMap R Rsh x)
    change (residueFieldEquivMaximalIdealResidueField Rsh).symm
      (h.residueFieldEquiv (algebraMap (ResidueField R) κsep (residue R x)))
        = residue Rsh (algebraMap R Rsh x)
    rw [IsScalarTower.algebraMap_apply (ResidueField R) (maximalIdeal R).ResidueField κsep,
      algebraMap_residueField_residue, hcomp, Ideal.ResidueField.map_algebraMap, ← hlast,
      RingEquiv.symm_apply_apply]
  have hdom : IsDomain Rsh := by
    have hRn : IsNormalRing R := fun p hp =>
      ⟨IsLocalization.isDomain_of_local_atPrime hp,
        isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
          (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors⟩
    exact (isNormalRing_of_ind_etale R Rsh hRn
      (IsLocalRing.IsHenselization.ind_etale_of_universe_le κsep)).of_isLocalRing.1
  let : Module.FaithfullyFlat R Rsh := IsLocalRing.IsHenselization.faithfullyFlat (L := κsep)
  obtain ⟨P, hP, hPover⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := Rsh) (⊥ : Ideal R)
  have hopen : IsOpen ({closedPoint Rsh}ᶜ : Set (PrimeSpectrum Rsh)) :=
    (IsLocalRing.isClosed_singleton_closedPoint Rsh).isOpen_compl
  have hne : ({closedPoint Rsh}ᶜ : Set (PrimeSpectrum Rsh)).Nonempty := by
    refine ⟨⟨P, hP⟩, fun hmem ↦ hR ?_⟩
    have hPm : P = maximalIdeal Rsh :=
      congrArg PrimeSpectrum.asIdeal (Set.eq_of_mem_singleton hmem)
    have hbot : (⊥ : Ideal R) = maximalIdeal R := by
      rw [hPover.over, hPm]
      exact maximalIdeal_comap (algebraMap R Rsh)
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot.symm
  exact ((IrreducibleSpace.isIrreducible_univ (PrimeSpectrum Rsh)).2.subset_irreducible
    hne hopen (fun _ ↦ id) (by simp)).isConnected

end AlgebraicGeometry
