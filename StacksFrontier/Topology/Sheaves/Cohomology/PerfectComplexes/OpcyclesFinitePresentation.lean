module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.CohomologyFiniteness
public import StacksFrontier.Topology.Sheaves.RecoveryExtend.FiniteLocallyFreeRetract

/-!
# The opcycles of a strictly perfect complex are of finite presentation

Let `(X, O_X)` be a ringed space and let `P` be a strictly perfect complex of `O_X`-modules.
Then every term of `P` is a sheaf of modules of finite presentation, and so is each of the
opcycles `Coker(P^{a-1} ⟶ P^a)`.

## Main results

* `Stacks.Cohomology.OpcyclesFinitePresentation`
  `.isFinitePresentation_of_isDirectSummandOfFiniteFree`: a direct summand of a finite free
  `O_X`-module is of finite presentation.
* `Stacks.Cohomology.OpcyclesFinitePresentation.isFinitePresentation_opcycles`: the degree-`a`
  opcycles of a strictly perfect complex is of finite presentation.

## References

* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open StrictlyPerfect

namespace Stacks.Cohomology.OpcyclesFinitePresentation

universe u

variable {X : RingedSpace.{u, u}}

/-- A direct summand of a finite free `O_X`-module is of finite presentation. -/
theorem isFinitePresentation_of_isDirectSummandOfFiniteFree {M : OXMod.{u, u} X}
    (hM : IsDirectSummandOfFiniteFree M) : M.IsFinitePresentation := by
  obtain ⟨n, ⟨ρ⟩⟩ := AlgebraicGeometry.RingedSpace.exists_retract_free hM
  exact Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation (M := M)
    (Stacks.SheafOfModules.presentationOfRetractFree.{u} (I := ULift.{u} (Fin n))
      ρ.i ρ.r ρ.retract)

/-- Every term of a strictly perfect complex is of finite presentation. -/
theorem isFinitePresentation_X {P : CochainComplex (OXMod.{u, u} X) ℤ}
    (hP : IsStrictlyPerfect P) (i : ℤ) : (P.X i).IsFinitePresentation :=
  isFinitePresentation_of_isDirectSummandOfFiniteFree (hP.directSummand i)

/-- The degree-`a` opcycles `Coker(P^{a-1} ⟶ P^a)` of a strictly perfect complex `P` is of
finite presentation. -/
theorem isFinitePresentation_opcycles {P : CochainComplex (OXMod.{u, u} X) ℤ}
    (hP : IsStrictlyPerfect P) (a : ℤ) :
    (HomologicalComplex.opcycles P a).IsFinitePresentation := by
  have _ : (P.X a).IsFinitePresentation := isFinitePresentation_X hP a
  have _ : (P.X (a - 1)).IsFinitePresentation := isFinitePresentation_X hP (a - 1)
  have _ : (cokernel (P.d (a - 1) a)).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel (P.d (a - 1) a)
  have e : cokernel (P.d (a - 1) a) ≅ HomologicalComplex.opcycles P a :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (P.d (a - 1) a))
      (P.opcyclesIsCokernel (a - 1) a (by rw [CochainComplex.prev]))
  exact (SheafOfModules.isFinitePresentation (structureSheafOfRings X)).prop_of_iso e
    inferInstance

end Stacks.Cohomology.OpcyclesFinitePresentation

end
