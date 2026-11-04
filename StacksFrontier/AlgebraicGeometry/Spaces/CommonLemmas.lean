module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart

/-!
# Shared lemmas for the cohomology of algebraic spaces

Lemmas used by several statements of the cohomology of algebraic spaces (Stacks, Chapter 69).

## Main results

* `AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves`: the middle term of a
  short exact sequence of `𝒪_X`-modules whose outer terms are quasi-coherent is quasi-coherent.
* `AlgebraicGeometry.Space.isWeakSerreClass_quasicoherentSheaves`: **Stacks 03M1 as a weak Serre
  class** — the quasi-coherent `𝒪_X`-modules form a weak Serre subcategory of all `𝒪_X`-modules,
  at the universe of the schemes.

## Implementation notes

The extension clause is
`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW`, whose surjectivity
hypothesis — an epimorphism with quasi-coherent kernel is surjective on the sections over every
affine étale chart — is
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional`.  The
kernel and cokernel clauses are
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-coherence is closed under extensions** on the small étale site of an algebraic
space, at the universe of the schemes. -/
theorem isClosedUnderExtensions_quasicoherentSheaves (X : AlgebraicSpaces B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).IsClosedUnderExtensions :=
  isClosedUnderExtensions_quasicoherentSheaves_of_h03DW B S hS X.1 X.2
    (fun q hq hk W hW =>
      surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS (X := X) q hq hk W hW)

/-- **Stacks 03M1, as a weak Serre class**: the quasi-coherent `𝒪_X`-modules on the small étale
site of an algebraic space form a weak Serre subcategory of all `𝒪_X`-modules, at the universe of
the schemes. -/
theorem isWeakSerreClass_quasicoherentSheaves (X : AlgebraicSpaces B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).IsWeakSerreClass :=
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS X.1 X.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2
  have := isClosedUnderExtensions_quasicoherentSheaves B S hS X
  quasicoherentSheaves_isWeakSerreClass B S hS X.1 X.2

end AlgebraicGeometry.Space

end
