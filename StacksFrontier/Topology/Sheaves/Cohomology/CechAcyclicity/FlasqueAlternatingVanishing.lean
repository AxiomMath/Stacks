module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing

/-!
# Alternating Čech acyclicity of flasque sheaves

A flasque sheaf of abelian groups on a topological space has vanishing Čech cohomology in
every positive degree, for every family of open subsets; this is Tag 09SZ, proved for
Mathlib's Čech complex. The same vanishing holds for the *alternating* Čech complex of Tag
01FH, because the canonical inclusion of the alternating Čech complex into the usual one is a
homotopy equivalence (Tag 01FM).

## Main results

* `Stacks.Cech.isZero_alternatingCechComplex_homology_of_isFlasque`: the positive-degree
  homology of the alternating Čech complex of a flasque sheaf of abelian groups vanishes.

## Implementation notes

Tag 01FM compares the alternating Čech complex with the explicit model
`Stacks.Cech.cechComplex`, whereas Tag 09SZ is stated for Mathlib's
`CategoryTheory.cechComplexFunctor`. The two are identified by
`Stacks.Cech.cechComplexIso`, so the vanishing transports along the composite.

Tag 01FM needs a linear order on the index type, in order to sort the index tuples of a Čech
cochain; a well-ordering serves, and the alternating Čech complex, the usual one and the
inclusion between them do not depend on it, so no order is imposed on the statement.

No covering hypothesis appears: the Čech complex of a family of opens is assembled from the
intersections of its members, so Tag 09SZ may be applied to the family's own union.

## References

* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace Opposite

universe u v

namespace Stacks.Cech

/-- **Alternating Čech acyclicity of a flasque sheaf.** The alternating Čech complex of a
flasque sheaf of abelian groups has vanishing homology in every positive degree, for every
family of open subsets. -/
theorem isZero_alternatingCechComplex_homology_of_isFlasque
    {X : TopCat.{u}} {I : Type v} (U : I → Opens X) (F : TopCat.Sheaf Ab.{v} X)
    [F.IsFlasque] (p : ℕ) (hp : 0 < p) :
    IsZero ((alternatingCechComplex U F.obj).homology p) := by
  classical
  have hmathlib : IsZero (((CategoryTheory.cechComplexFunctor U).obj F.obj).homology p) :=
    Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque F
      (⨆ i, U i) U rfl p hp
  have hfull : IsZero ((cechComplex U F.obj).homology p) :=
    IsZero.of_iso hmathlib
      ((HomologicalComplex.homologyFunctor Ab.{v} (up ℕ) p).mapIso (cechComplexIso U F.obj))
  obtain ⟨e, -⟩ := @alternatingCechInclusion_homotopyEquivalence X I
    (linearOrderOfSTO WellOrderingRel) U F.obj
  exact IsZero.of_iso hfull (e.toHomologyIso p)

end Stacks.Cech

end
