module

public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartLinearForm

/-!
# The kernel of an invertible quotient, on a chart, is the `tilde` of the chart's linear kernel

`Stacks.ProjectiveBundleConormal.splitChartMap` realises the affine bundle on `ker p` as the
standard open `D₊(ι s)` of `Proj(Sym_A M)`, for `A = Γ(X, U)`, `M = Γ(ℰ, U)` and
`p = Stacks.ProjectiveBundleConormal.chartLinearForm` the invertible quotient read on sections
over an affine open `U` in a frame. The source of the conormal map of [Stacks, Tag 0B3V]
clause 3 is, after
`Stacks.ProjectiveBundleConormal.restrictSourceIso` has untwisted it, the module `ker(q)|_U`.
**This file identifies that module with the quasi-coherent sheaf attached to `ker p`**, which is
the module the affine bundle — and hence `Stacks.ProjectiveBundleConormal.conormalZeroSectionIso`
— computes with.

Nothing is reproved. The identification is the composite of three facts from the library:

* over an affine open a quasi-coherent module is the pullback of a `tilde`
  (`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`, [Stacks, Tag 01XZ] (4)),
* the module it is the `tilde` of is the module of sections over that open
  (`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`), and
* those sections are the kernel of the chart's linear form
  (`Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv`).

The middle step is what makes the composite short: `kernelSectionsKerEquiv` already does the
kernel bookkeeping at the level of modules, through
`Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel`, so neither left exactness of restriction
nor the kernel comparison for `tilde` has to be invoked here.

## Main definitions

* `Stacks.ProjectiveBundleConormal.chartKerModule`: `ker p` as a `Γ(X, U)`-module object.
* `Stacks.ProjectiveBundleConormal.specModuleChartKerIso`: the `Γ(X, U)`-module that `ker(q)|_U`
  is the `tilde` of is `ker p`.
* `Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde`: **`ker(q)|_U ≅ (ker p)^~`**, read
  through `U ≅ Spec Γ(X, U)`.

## Implementation notes

Quasi-coherence of `ker q` is needed to apply
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`, and neither half of it is found by
instance search on its own: `Q.L` is invertible by a structure *field* rather than an instance,
and the quasi-coherence of an invertible module
(`Stacks.Divisors.isQuasicoherent_of_isInvertible`) is stated for
`AlgebraicGeometry.SheafOfModules.IsInvertible`. Both are supplied below as instances, after
which `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` fires.

**No composite is nested beyond two folds.** Each definition below is a single `≪≫` of two named
isomorphisms, and the two intermediate objects are named. The reason is recorded in
the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTransport`: reading the `.hom` of a
three-fold `CategoryTheory.Iso.trans` on a local section exceeds the elaborator's budget in this
part of the library, while the same split at a two-fold one is free.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} {E : X.Modules} (Q : Stacks.Divisors.InvertibleQuotient X E)

/-! ### Quasi-coherence of the kernel -/

/-- **An invertible quotient is quasi-coherent.** `Stacks.Divisors.InvertibleQuotient` carries
invertibility of its target as a field rather than as an instance, so
`Stacks.Divisors.isQuasicoherent_of_isInvertible` has to be applied by hand. The field is
ascribed to the `X.sheaf.obj` spelling the lemma is stated in, as in
`Stacks.ProjectiveBundleConormal.exists_affine_open_splitting`: the two spellings are
definitionally equal but instance search does not cross between them. -/
instance isQuasicoherent_invertibleQuotient : Q.L.IsQuasicoherent :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  Stacks.Divisors.isQuasicoherent_of_isInvertible Q.L

/-- **The kernel of an invertible quotient of a quasi-coherent module is quasi-coherent**, by the
kernel half of [Stacks, Tag 01LB]. -/
instance isQuasicoherent_kernel_invertibleQuotient [E.IsQuasicoherent] :
    (kernel Q.q).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel Q.q

/-! ### The chart's linear kernel as a module object -/

variable (U : X.Opens) (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U))

/-- **The kernel of the chart's linear form as a `Γ(X, U)`-module object.** This is the module
`K` for which `Stacks.ProjectiveBundleConormal.splitChartMap` realises `Spec (Sym_{Γ(X,U)} K)` as
a standard open of `Proj(Sym_{Γ(X,U)} Γ(ℰ, U))`. -/
abbrev chartKerModule : ModuleCat.{u} Γ(X, U) :=
  ModuleCat.of Γ(X, U) ↥(LinearMap.ker (chartLinearForm Q U e))

/-- **`Γ(ker q, U) ≅ ker p` as `Γ(X, U)`-modules**, the module-object form of
`Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv`. -/
def sectionsChartKerIso :
    ModuleCat.of Γ(X, U) Γ(kernel Q.q, U) ≅ chartKerModule Q U e :=
  (kernelSectionsKerEquiv Q U e).toModuleIso

/-! ### The identification -/

variable [E.IsQuasicoherent] (hU : IsAffineOpen U)

/-- **The `Γ(X, U)`-module that `ker(q)|_U` is the `tilde` of is `ker p`.** The module
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde` produces is the module of sections
over `U` (`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`), and those
are the kernel of the chart's linear form. -/
def specModuleChartKerIso :
    specModule (kernel Q.q) hU ≅ chartKerModule Q U e :=
  specModuleIsoSections (kernel Q.q) ⟨U, hU⟩ ≪≫ sectionsChartKerIso Q U e

/-- **`ker(q)|_U` is the quasi-coherent sheaf attached to `ker p`**, read through the canonical
isomorphism `U ≅ Spec Γ(X, U)` of the affine open.

This is the source of the conormal map of [Stacks, Tag 0B3V] clause 3 over the chart, in the form
in which `Stacks.ProjectiveBundleConormal.conormalZeroSectionIso` — the conormal sheaf of the zero
section of `𝐀(ker p)` — states its answer. -/
def restrictKernelIsoTilde :
    (kernel Q.q).restrict U.ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde (chartKerModule Q U e)) :=
  restrictIsoSpecTilde (kernel Q.q) hU ≪≫
    (Scheme.Modules.pullback hU.isoSpec.hom).mapIso
      ((tilde.functor Γ(X, U)).mapIso (specModuleChartKerIso Q U e hU))

end Stacks.ProjectiveBundleConormal

end
