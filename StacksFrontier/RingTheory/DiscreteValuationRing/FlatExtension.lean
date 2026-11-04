module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extensions of discrete valuation rings are flat

An injective ring homomorphism from a discrete valuation ring to a domain is flat, since the
target is a torsion-free module over a principal ideal domain. In particular every extension of
discrete valuation rings, that is every injective local homomorphism between discrete valuation
rings, is flat.

Injectivity cannot be dropped: for a discrete valuation ring `R` with residue field `κ`, the
composite `R → κ → κ⟦X⟧` is a local homomorphism of discrete valuation rings which kills a
uniformizer, so it is not flat.

## Main results

* `RingHom.Flat.of_injective_of_isDiscreteValuationRing`: an injective homomorphism from a
  discrete valuation ring to a domain is flat.
* `IsDiscreteValuationRing.not_flat_residue_powerSeries`: the local homomorphism of discrete
  valuation rings `R → κ⟦X⟧` through the residue field is not flat.

## References

* [The Stacks Project, Tag 024Z](https://stacks.math.columbia.edu/tag/024Z)
-/

@[expose] public section

open IsLocalRing

/-- **Stacks Project, Tag 024Z.** An injective ring homomorphism from a discrete valuation ring
to a domain is flat. In particular any extension of discrete valuation rings — an injective local
homomorphism of discrete valuation rings — is flat. -/
@[stacks 024Z "any local homomorphism of discrete valuation rings is flat, in the corrected form \
for injective local homomorphisms (extensions of discrete valuation rings), proved here for any \
injective homomorphism from a discrete valuation ring to a domain",
  ega "0 6.3.4" "last assertion, A a DVR", sga "6 X 7.15" "special case"]
theorem RingHom.Flat.of_injective_of_isDiscreteValuationRing {R S : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hf
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The local homomorphism of discrete valuation rings `R → κ⟦X⟧` through the residue field `κ`
of a discrete valuation ring `R` is not flat: it kills a uniformizer of `R`. So the injectivity
hypothesis of `RingHom.Flat.of_injective_of_isDiscreteValuationRing` cannot be dropped. -/
theorem IsDiscreteValuationRing.not_flat_residue_powerSeries (R : Type*) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] :
    IsLocalHom ((PowerSeries.C (R := ResidueField R)).comp (residue R)) ∧
      ¬ ((PowerSeries.C (R := ResidueField R)).comp (residue R)).Flat := by
  set f := (PowerSeries.C (R := ResidueField R)).comp (residue R) with hfdef
  refine ⟨⟨fun r hr => ?_⟩, fun hflat => ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hfdef, RingHom.comp_apply,
      PowerSeries.constantCoeff_C] at hr
    exact (residue_ne_zero_iff_isUnit r).mp hr.ne_zero
  · have hf : algebraMap R (PowerSeries (ResidueField R)) = f := by
      ext r : 1
      rw [hfdef, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply R (ResidueField R) (PowerSeries (ResidueField R))]
      rfl
    have hflat' : Module.Flat R (PowerSeries (ResidueField R)) :=
      RingHom.flat_algebraMap_iff.mp (hf ▸ hflat)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hϖ0 : ϖ ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := PowerSeries (ResidueField R)) hϖ0
    have hkill : ϖ • (1 : PowerSeries (ResidueField R)) = ϖ • 0 := by
      rw [smul_zero, Algebra.smul_def, mul_one]
      rw [hf, hfdef, RingHom.comp_apply, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, map_zero]
    exact one_ne_zero (hreg hkill)
