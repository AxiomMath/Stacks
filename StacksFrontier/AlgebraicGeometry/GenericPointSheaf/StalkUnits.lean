module

public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.GenericPoints

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.GenericPointSheaf

open Stacks.AlgebraicGeometry.GenericPointGluing

variable {X : Scheme.{u}}

/-- At a generic point the local ring has a single prime ideal, so every non-unit is
nilpotent. -/
theorem isNilpotent_of_notMem_unit {η : X} (hη : η ∈ genericPoints X)
    {r : X.presheaf.stalk η} (hr : ¬ IsUnit r) : IsNilpotent r := by
  have hss : Subsingleton (PrimeSpectrum (X.presheaf.stalk η)) := subsingleton_specStalk hη
  have hmem : ∀ J : Ideal (X.presheaf.stalk η), J.IsPrime → r ∈ J := by
    intro J hJ
    have : (⟨J, hJ⟩ : PrimeSpectrum (X.presheaf.stalk η)) =
        ⟨IsLocalRing.maximalIdeal _, inferInstance⟩ := Subsingleton.elim _ _
    have hJeq : J = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
      congrArg PrimeSpectrum.asIdeal this
    rw [hJeq]
    exact IsLocalRing.mem_maximalIdeal _ |>.2 hr
  have : r ∈ nilradical (X.presheaf.stalk η) := by
    rw [nilradical_eq_sInf]
    exact Ideal.mem_sInf.2 fun {J} hJ ↦ hmem J hJ
  exact this

/-- A nonzerodivisor in the local ring at a generic point is a unit: the spectrum of that local
ring is a single point, so a non-unit is nilpotent, and a nilpotent nonzerodivisor forces the
ring to be trivial. No reducedness hypothesis is used. -/
theorem isUnit_of_mem_nonZeroDivisors_stalk {η : X} (hη : η ∈ genericPoints X)
    {r : X.presheaf.stalk η} (hr : r ∈ (X.presheaf.stalk η)⁰) : IsUnit r := by
  by_contra hnu
  obtain ⟨n, hn⟩ := isNilpotent_of_notMem_unit hη hnu
  have hz : (0 : X.presheaf.stalk η) ∈ (X.presheaf.stalk η)⁰ := hn ▸ pow_mem hr n
  have h10 : (1 : X.presheaf.stalk η) = 0 :=
    (mem_nonZeroDivisors_iff.1 hz).1 1 (zero_mul 1)
  have := subsingleton_of_zero_eq_one h10.symm
  exact hnu (isUnit_of_subsingleton r)

/-- The nonzerodivisors of the local ring at a generic point are contained in the units. -/
theorem nonZeroDivisors_le_isUnit_stalk {η : X} (hη : η ∈ genericPoints X) :
    ∀ r ∈ (X.presheaf.stalk η)⁰, IsUnit r :=
  fun _ hr ↦ isUnit_of_mem_nonZeroDivisors_stalk hη hr

end Stacks.AlgebraicGeometry.GenericPointSheaf
