module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FinitePresentationOfSummands
import StacksCore.Tactic.StacksAttribute

/-!
# The opcycles of a strictly perfect complex on a ringed site are of finite presentation

Let `(C, O)` be a ringed site and let `P` be a strictly perfect complex of `O`-modules (Stacks
08FL). Then each opcycles object `Coker(P^{a-1} ⟶ P^a)` is a sheaf of modules of finite
presentation: its source and target are direct summands of finite free `O`-modules, hence of
finite presentation, and the cokernel of a map from a finite-type module to a finitely presented
one is finitely presented by Stacks 0H98.

This is the finiteness half of the step in the proof of Stacks 08G7 which makes the lowest term
`E' = Coker(E^{a-1} ⟶ E^a)` of the truncated approximation a direct summand of a finite free
module: the Tor-amplitude hypothesis makes `E'` flat, and Stacks 08FD turns a flat module of
*finite presentation* into a local direct summand of a finite free one. The flatness is
`Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles`; the finite
presentation is here.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_X_of_isStrictlyPerfect`: every term of a strictly
  perfect complex of `O`-modules is of finite presentation.
* `Stacks.SheafOfModules.isFinitePresentation_opcycles`: the degree-`a` opcycles of a strictly
  perfect complex of `O`-modules is of finite presentation.

## Implementation notes

The ringed-space analogue is
`Stacks.Cohomology.OpcyclesFinitePresentation.isFinitePresentation_opcycles` of
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/OpcyclesFinitePresentation.lean`, whose
proof is the same two steps against the ringed-space forms of the two inputs; neither statement
specialises to the other, the two `IsDirectSummandOfFiniteFree` predicates being about a ringed
space and about a site respectively, and the two cokernel finiteness results being Stacks 0H96
on the site of opens of a space and Stacks 0H98 on an arbitrary ringed site.

Mathlib computes the opcycles as the cokernel of the differential only up to the canonical
comparison of two colimit cocones, `HomologicalComplex.opcyclesIsCokernel`, and finite
presentation is an `ObjectProperty` closed under isomorphism, which is how the two are matched
up.

The structure sheaf is the one of a ringed site rather than an arbitrary sheaf of rings, since
that is the shape of Stacks 0H98; the sections of the modules live in `Type`, as everywhere in
the ringed-site perfectness development.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.SheafOfModules

variable (Y : RingedSite.{u, v, 0})
  [HasSheafify Y.J AddCommGrpCat.{0}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ T : Y.C, HasSheafify (Y.J.over T) AddCommGrpCat.{0}]
  [∀ T : Y.C, (Y.J.over T).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- **Every term of a strictly perfect complex of `O`-modules is of finite presentation**, being
a direct summand of a finite free `O`-module. -/
theorem isFinitePresentation_X_of_isStrictlyPerfect
    {P : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (i : ℤ) :
    (P.X i).IsFinitePresentation :=
  isFinitePresentation_of_isDirectSummandOfFiniteFree
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ (hP.termDirectSummand i)

/-- **The degree-`a` opcycles of a strictly perfect complex of `O`-modules is of finite
presentation.** It is the cokernel of the differential `P^{a-1} ⟶ P^a`, whose source and target
are both of finite presentation, so Stacks 0H98 applies — it asks of the source only finite
type, which finite presentation implies. -/
theorem isFinitePresentation_opcycles
    {P : CochainComplex (_root_.SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (a : ℤ) :
    (P.opcycles a).IsFinitePresentation := by
  have hprev : (ComplexShape.up ℤ).prev a = a - 1 := by rw [CochainComplex.prev]
  have _ : (P.X a).IsFinitePresentation :=
    isFinitePresentation_X_of_isStrictlyPerfect Y hP a
  have _ : (P.X (a - 1)).IsFinitePresentation :=
    isFinitePresentation_X_of_isStrictlyPerfect Y hP (a - 1)
  have _ : (cokernel (P.d (a - 1) a)).IsFinitePresentation :=
    LocalCokernel.isFinitePresentation_cokernel Y (P.d (a - 1) a)
  have e : cokernel (P.d (a - 1) a) ≅ P.opcycles a :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (P.d (a - 1) a))
      (P.opcyclesIsCokernel (a - 1) a hprev)
  exact (_root_.SheafOfModules.isFinitePresentation
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).prop_of_iso e inferInstance

end Stacks.SheafOfModules

end
