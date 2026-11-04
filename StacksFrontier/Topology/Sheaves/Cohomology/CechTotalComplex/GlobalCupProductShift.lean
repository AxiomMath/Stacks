module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftCohomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftCohomologyIsoR
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift.ShiftFirstFactor

/-!
# The global cup product and the shift

This file only re-exports its parts, the modules `GlobalCupProductShift.*`:

* `ShiftCohomologyIso`: the unit `Γ ⟶ RΓ` commutes with the shift, the identification
  `Hᵃ(S, 𝒦^•[n]) ≅ Hⁿ⁺ᵃ(S, 𝒦^•)` and its value on the class of a global cocycle, and the
  naturality of the shift identifications of total complexes;
* `ShiftCohomologyIsoR`: the naturality of that identification, its variant for the shift
  `shiftR`, and classes of global cocycles of tensor products;
* `ShiftSecondFactor`: the cup product and the shift of the second factor;
* `ShiftFirstFactor`: the cup product and the shift of the first factor.
-/
