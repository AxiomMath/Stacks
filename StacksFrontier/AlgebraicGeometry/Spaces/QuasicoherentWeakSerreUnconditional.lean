module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional

/-!
# Quasi-coherence on an algebraic space is a weak Serre class, with no hypothesis

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03M1
asserts six closure properties of the quasi-coherent `𝒪_F`-modules; three of them — closure
under kernels, under cokernels and under extensions — are exactly what makes quasi-coherence a
*weak Serre class* in the sense of Stacks 0754, and that is the form in which the property is
consumed by every derived-category argument about `D_QCoh(𝒪_F)`.

The kernel and the cokernel clauses are already available in the
`CategoryTheory.ObjectProperty` shape with no hypothesis
(`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`).  The extension clause is
not: `AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW` carries the
uniform form of Descent, Proposition 03DW, and so does the weak Serre class assembled from the
three.  That hypothesis is a theorem of this development,
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts`, whose
conclusion is its statement verbatim.  This module supplies it, and records the two resulting
unconditional statements at the module universe `u` of the schemes.

## Main results

* `AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse`: **the
  extension clause of Stacks 03M1 in the `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`
  shape, at the universe of the schemes, with no hypothesis.**
* `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`:
  **quasi-coherence of `𝒪_F`-modules on the small étale site of an algebraic space is a weak
  Serre class, with no hypothesis**, at the universe of the schemes.

## Implementation notes

*What is new here and what is not.*  The extension clause itself is not proved here: the
element-level statement is
`AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact'` of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentClausesUnconditional.lean`, which is
unconditional and carries the `@[stacks 03M1]` attribute for clause (4).  What is new is the
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` packaging and, through it, the weak
Serre class: `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` takes the three
closure clauses as *instance* arguments at a free module universe `m`, so it is never found by
instance search without them, and the only `IsClosedUnderExtensions` statement available to
discharge the third was the one carrying Descent, Proposition 03DW.

*Why a separate module.*
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedComparison.lean` carries the three
closure classes as section variables at the free module universe `m`, and
`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` is stated under them, so the
instantiation at `m := u` is not available there.  The arrangement is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentKernelsUnconditional.lean`, which holds the
kernel clause at `m := u` outside
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentKernelsOnSite.lean` for the same kind of
reason.

*The local priority raise is load-bearing.*  `CategoryTheory.SheafOfModules.instAbelian` is raised
in priority, as in `StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherent.lean` and
the other modules of this library that pin the module universe to `u`.  Without it the weak Serre
class below does not elaborate: `CategoryTheory.ObjectProperty.IsWeakSerreClass` mentions
`CategoryTheory.Abelian` of the modules, instance search reaches the module-universe-`max u v r w`
instances of the import closure first, and the statement fails with
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`.  The attribute is `local`, so no
global instance is declared.  The extension clause above needs no such raise, its statement
mentioning only the object property.

*The module universe* is `u`, the universe of the schemes.  It is not free, and cannot be made
so: the extension clause speaks of a `CategoryTheory.ShortComplex.ShortExact` sequence of
`𝒪_F`-modules, which needs them abelian, and the element-level clause (4) is itself stated only
at `u` for that reason — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentClausesUnconditional.lean`.

*The two statements are theorems and not instances.*  Registering either globally would put an
`ObjectProperty` closure class and a weak-Serre class on the search path for every sheaf of
modules in the import closure of this file, and the existing kernel and cokernel clauses at this
universe are deliberately theorems for that reason; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentKernelsUnconditional.lean` on the universe
inference that an extra instance in scope breaks.

*No `@[stacks]` attribute is carried.*  Clause (4) of Stacks 03M1 is already claimed, on the
three element-level statements of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentClausesUnconditional.lean`; a second claim on
a repackaging of one of them would double-count the clause.  Stacks 0754 is a definition, not an
assertion, so the weak Serre class carries no attribute either.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The extension clause of Stacks 03M1 for the small étale site of an algebraic space, in the
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` shape, at the universe of the schemes,
outright.**

The middle term of a short exact sequence of `𝒪_F`-modules whose outer terms are quasi-coherent
is quasi-coherent.  This is
`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW` with its
hypothesis — the uniform form of Descent, Proposition 03DW — supplied by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts`. -/
theorem isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).IsClosedUnderExtensions :=
  isClosedUnderExtensions_quasicoherentSheaves_of_h03DW B S hS F hF
    fun q hq hk W hW =>
      surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts (hF := hF) q hq hk W hW

/-- **Quasi-coherence of `𝒪_F`-modules on the small étale site of an algebraic space is a weak
Serre class, at the universe of the schemes, with no hypothesis.**

This is Stacks 03M1 in the shape the derived-category arguments of this tree consume: the
quasi-coherent modules are closed under kernels, under cokernels and under extensions, which is
the definition of a weak Serre class, Stacks 0754.  The three clauses are
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse`,
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves` and
`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse`, all three
unconditional. -/
theorem quasicoherentSheaves_isWeakSerreClass_schemeUniverse :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).IsWeakSerreClass :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse B S hS F hF
  quasicoherentSheaves_isWeakSerreClass B S hS F hF

end AlgebraicGeometry.Space

end
