module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts

/-!
# Kernels of quasi-coherent modules on an algebraic space

Let `F` be an algebraic space over a scheme `S`, and let `φ : M ⟶ N` be a morphism of
`𝒪_F`-modules, that is, of sheaves of modules on the small étale ringed site of `F`.  Clause (3)
of Stacks 03M1 asserts that if `M` and `N` are quasi-coherent then so are the kernel and the
cokernel of `φ`.  This file is about the kernel half of that clause; the cokernel half is
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite`.

Unlike for cokernels, the module universe stays free throughout: kernels of sheaves of modules
are computed pointwise, so `CategoryTheory.Limits.HasKernel` needs no sheafification instance on
the site, and nothing below constrains the universe of the module sections.

The kernel half is *not* a formal consequence of the two quasi-coherence hypotheses on a general
site: `ChaoticQCoh.KernelCounterexample.not_quasicoherent_closed_under_kernels` in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentKernelCounterexample` exhibits a
two-object ringed site with the chaotic topology on which a kernel of modules whose every slice
restriction has a global presentation does not have that property; the mechanism is the non-flat
ring map `ℤ → ℤ/2` serving as the restriction map of the structure sheaf.  What makes the small
étale site of an algebraic space different is flatness of its restriction maps between affine
charts, and that input is already discharged in the tree, by
`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine` inside
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_affineCharts` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel`: the kernel of a morphism of
  quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the local kernel step — over affine
  étale charts only in the first, over every étale chart in the second.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`: **the kernel clause of
  Stacks 03M1(3), conditional on Descent, Proposition 03DX(2) and on nothing else.**
* `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves`: the same statement in the
  shape `CategoryTheory.ObjectProperty.IsClosedUnderKernels`, which is the hypothesis that
  `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
  `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` carry.
* `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_isCartesian`: the abelian structure of
  Stacks 077V(1) with its kernel hypothesis discharged, leaving only the cokernel one.

## Implementation notes

**Two independent reductions are given, and they are conditional on different things.**

The first, `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_affineCharts`, carries the
purely local hypothesis `hlocal`: over an affine étale chart over which both `M` and `N` have
global presentations, so does the restriction of `ker φ`.  Everything else — the refinement of
the two presenting coverings and the passage from arbitrary charts to affine ones — is the
unconditional
`SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense`, so nothing is
re-derived here.  It is the exact analogue of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts` and `hlocal` is spelled
as there.

The second, `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`, carries
instead `h03DX`, Descent, Proposition 03DX(2) for the small étale site of `F`: an `𝒪_F`-module is
quasi-coherent exactly when it is cartesian on affine charts.  Its mathematical content is then
entirely supplied by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`, which is
unconditional and includes the flatness of the chart restrictions.  `h03DX` is spelled exactly as
in `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`, at a free module universe; no
second spelling is introduced.

The second reduction is the sharper one, and it is why the kernel half of Stacks 03M1(3) is in a
better state than the cokernel half: the cokernel half needs, beyond `h03DX`, the vanishing of
the first étale cohomology of a quasi-coherent module on an affine chart, because sections of
sheaves of modules are only *left* exact.  For the kernel, left exactness is exactly what is
needed, and `CategoryTheory.Limits.PreservesFiniteLimits` of `SheafOfModules.evaluation` is
available — it is `SheafOfModules.Finite.evaluationPreservesFiniteLimits`, and it is what
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel` runs on.  So the kernel clause needs
no cohomological input whatsoever.

`CategoryTheory.ObjectProperty.IsClosedUnderKernels` asks for membership of the vertex of an
*arbitrary* limiting kernel fork, not of `CategoryTheory.Limits.kernel` alone; the passage is the
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance for
`SheafOfModules.isQuasicoherentOnSite`, which is already in the tree.

No `@[stacks 03M1]` attribute is claimed, and no clause of Stacks 03M1 is proved outright here.
Stacks 03M1(3) is unconditional, every statement below is conditional on `hlocal` or on `h03DX`,
and tagging a reduction with the tag it reduces would report that tag as proved.  The same
convention is used by `AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite`,
`AlgebraicGeometry.Spaces.ChartSectionsKernel` and
`AlgebraicGeometry.Spaces.ShortExactQuasicoherent`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The kernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the
local kernel step over affine charts.**  `hlocal` says that over an affine étale chart over which
both `M` and `N` have global presentations, so does the restriction of `ker φ`.

Everything else is discharged by
`SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense` against the
cover density of the affine étale charts, Stacks 04JS.  The module universe is free. -/
theorem isQuasicoherentOnSite_kernel_of_affineCharts {M N : Modules.{u, m} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (φ : M ⟶ N)
    (hlocal : ∀ V : (smallEtaleRingedSite B S hS F hF).C, IsAffineChart B S hS F V →
      (M.over V).HasGlobalPresentation → (N.over V).HasGlobalPresentation →
        ((kernel φ).over V).HasGlobalPresentation) :
    (kernel φ).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense
    (AffineEtale.inclusion B S hS F) (coverByImage_affineEtaleInclusion_mem B S hS F hF)
    ‹M.IsQuasicoherentOnSite› ‹N.IsQuasicoherentOnSite›
    fun W => hlocal _ W.property

/-- **The kernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the
local kernel step.**  The form of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_affineCharts` in which the local step is
asked of every étale chart; it is the weaker of the two, and is recorded because it is the shape
in which this library states Stacks 03M1. -/
theorem isQuasicoherentOnSite_kernel {M N : Modules.{u, m} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (φ : M ⟶ N)
    (hlocal : ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (M.over V).HasGlobalPresentation → (N.over V).HasGlobalPresentation →
        ((kernel φ).over V).HasGlobalPresentation) :
    (kernel φ).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair
    ‹M.IsQuasicoherentOnSite› ‹N.IsQuasicoherentOnSite› hlocal

/-- **The kernel clause of Stacks 03M1(3), conditional on Descent, Proposition 03DX(2).**  The
kernel of a morphism of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

`h03DX` is Descent, Proposition 03DX(2) for the small étale site of `F`: an `𝒪_F`-module is
quasi-coherent exactly when it is cartesian on affine charts, that is, when its sections over a
smaller affine chart are the base change of its sections over a larger one.  It is not available
in the tree and is carried as a hypothesis, spelled as in
`AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact`.

**No other input is used, and in particular no cohomological one**: the geometric content is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`, which is unconditional, flatness of
the restriction maps between affine étale charts being automatic.  The module universe is
free. -/
theorem isQuasicoherentOnSite_kernel_of_isCartesian {M N : Modules.{u, m} B S hS F hF}
    (φ : M ⟶ N)
    (h03DX : ∀ G : Modules.{u, m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G)
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] :
    (kernel φ).IsQuasicoherentOnSite :=
  (h03DX _).2 (isCartesianOnAffineCharts_kernel φ
    ((h03DX M).1 ‹M.IsQuasicoherentOnSite›) ((h03DX N).1 ‹N.IsQuasicoherentOnSite›))

/-- **Quasi-coherence of `𝒪_F`-modules is closed under kernels, conditional on Descent,
Proposition 03DX(2).**  This is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` in the shape
`CategoryTheory.ObjectProperty.IsClosedUnderKernels`, which is the hypothesis carried by
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and by
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure`, in their
universes: the small étale site of an algebraic space over `Scheme.{u}` has objects in
`Type (u + 1)`, morphisms in `Type u` and a `CommRingCat.{u}`-valued structure sheaf, and the
module universe stays free.

The class asks about the vertex of an arbitrary limiting kernel fork, so the canonical kernel is
transported along `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`. -/
theorem isClosedUnderKernels_quasicoherentSheaves
    (h03DX : ∀ G : Modules.{u, m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hφ⟩
    have h₁ : SheafOfModules.IsQuasicoherentOnSite _ := hφ.1
    have h₂ : SheafOfModules.IsQuasicoherentOnSite _ := hφ.2
    exact ObjectProperty.prop_of_iso _
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) hk)
      (isQuasicoherentOnSite_kernel_of_isCartesian B S hS F hF φ h03DX)

/-- **Stacks 077V, part (1), abelian structure, with the kernel hypothesis discharged.**  The
quasi-coherent `𝒪_F`-modules on an algebraic space form an abelian category as soon as
quasi-coherence is closed under cokernels and Descent, Proposition 03DX(2) holds for the small
étale site of `F`.

This is `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` with its kernel
hypothesis supplied by `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` and
its finite-product hypothesis by the unconditional instance
`AlgebraicGeometry.Space.isClosedUnderFiniteProducts_quasicoherentSheaves`; the remaining closure
hypothesis is the cokernel clause of Stacks 03M1(3), for which see
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts`. -/
@[instance_reducible] noncomputable def quasicoherentSheaves_abelian_of_isCartesian
    [HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]
    (h03DX : ∀ G : Modules.{u, m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G) :
    Abelian (QuasicoherentSheaves.{u, m} B S hS F hF) :=
  haveI := isClosedUnderKernels_quasicoherentSheaves B S hS F hF h03DX
  quasicoherentSheaves_abelian_of_closure B S hS F hF

end AlgebraicGeometry.Space

end
