module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional

/-!
# Quasi-coherence of the direct image from the exact sequence of an étale presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03M9 asserts that if `f` is quasi-compact and quasi-separated then the direct
image `f_*` carries quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_Y`-modules.  The source's
proof reduces to an affine base and there exhibits `f_*F` as the kernel of a morphism of two
direct images along étale charts, which are quasi-coherent, and then appeals to stability of
quasi-coherence under kernels.

That last appeal is Stacks 03M1, clause (3), and it is now available on the small étale site of
an algebraic space without any hypothesis: it follows from Descent, Proposition 03DX (2), which
is formalized as `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`.
This file records that, and feeds it to the affine-base reduction of
`StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction`, so that the whole
residue of Stacks 03M9 becomes the exact sequence of Stacks 03M8 with quasi-coherent outer terms.

## Main definitions

* `AlgebraicGeometry.Space.ChartwiseKernelOfQuasicoherent` is the residual hypothesis: over every
  affine étale scheme chart `V` of `Y` the direct image `f'_*(F|_U)` along the base change
  `f' : U ⟶ V` of `f` is a kernel of a morphism of quasi-coherent modules on `V`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`: **the kernel of a
  morphism of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent**, with no
  hypothesis.
* `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`: the same in the
  shape `CategoryTheory.ObjectProperty.IsClosedUnderKernels`, which is the form carried as an
  undischarged hypothesis elsewhere in this directory.
* `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_chartwiseKernel`: **Stacks 03M9
  with the exact sequence of Stacks 03M8 as its only remaining input.**

## Implementation notes

Stacks 03M9 itself, with no hypothesis beyond the source's, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs` in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardQcqs.lean`, which carries the
attribute.  The statement here names the input that route avoids: the exact sequence of
Stacks 03M8 over the affine charts of the target, with its two outer terms quasi-coherent.
Nothing else of the source's argument is assumed — the reduction to
an affine base, the quasi-compactness and quasi-separatedness of the base-changed morphism and
the kernel clause of Stacks 03M1 are all discharged.  What Stacks 03M8 still needs in this
development is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean`, which proves the
equalizer diagram on sections and withholds the tag, and quasi-coherence of its outer terms needs
Descent, Proposition 03LC, part (3) read on a small étale site.

The residual hypothesis is phrased with an isomorphism onto `CategoryTheory.Limits.kernel` rather
than with a limiting kernel fork, because quasi-coherence is invariant under isomorphism and the
chosen kernel is the only one the closure statement mentions; a caller holding a fork obtains the
isomorphism from `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`.

The module universe is the universe `u` of the schemes, as for every statement about
`AlgebraicGeometry.Space.modulePushforward`; Descent, Proposition 03DX (2) is proved at that
universe too, which is what makes the kernel clause unconditional here.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The kernel clause of Stacks 03M1 on an algebraic space -/

/-- **The kernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent.**

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` with its hypothesis
`h03DX` discharged by Descent, Proposition 03DX (2) for the small étale site of an algebraic
space. -/
theorem isQuasicoherentOnSite_kernel_of_quasicoherent
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] :
    (kernel φ).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernel_of_isCartesian B S hS F hF φ
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF)

/-- **Quasi-coherence of `𝒪_F`-modules is closed under kernels.**  The shape
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`, which is the form in
which the closure is carried as a hypothesis elsewhere in this development. -/
alias isClosedUnderKernels_quasicoherentSheaves_smallEtale :=
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse

/-! ### Stacks 03M9 with the exact sequence of Stacks 03M8 as its only input -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The exact sequence of Stacks 03M8 over the affine charts of the target, as a hypothesis: for
every affine étale scheme chart `V` of `Y` the direct image `f'_*(F|_U)` along the base change
`f' : U ⟶ V` of `f`, with `U = V ×_Y X`, is a kernel of a morphism of quasi-coherent modules on
the small étale site of `V`.

The quasi-compactness and quasi-separatedness of `f'` and the quasi-compactness of `U`, which the
source's construction of that sequence consumes, are supplied to the hypothesis as arguments. -/
def ChartwiseKernelOfQuasicoherent (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∀ V : SmallEtale B S hS Y.1,
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
    IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
    IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
    IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 →
    ∃ (A N : Modules.{u, u} B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2)
      (_ : A.IsQuasicoherentOnSite) (_ : N.IsQuasicoherentOnSite) (φ : A ⟶ N),
      Nonempty ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F) ≅ kernel φ)

/-- **Stacks 03M9, with the exact sequence of Stacks 03M8 as its only remaining input.**  Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let `F`
be a quasi-coherent `𝒪_X`-module.  Then `f_*F` is quasi-coherent, granted that over every affine
étale scheme chart of `Y` the direct image along the base change of `f` is a kernel of a morphism
of quasi-coherent modules.

The reduction to an affine base is
`AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine_chart`, which consumes
the two hypotheses on `f` to produce the quasi-compactness and quasi-separatedness of the base
change and the quasi-compactness of its source; the passage from the kernel presentation to
quasi-coherence is `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`, so no
clause of Stacks 03M1 is assumed. -/
theorem pushforward_isQuasicoherentOnSite_of_chartwiseKernel (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hseq : ChartwiseKernelOfQuasicoherent B S hS f F) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
  pushforward_isQuasicoherentOnSite_of_forall_affine_chart B S hS f hfqc hfqs F
    fun V hV hqc hqs hqcs ↦ by
      obtain ⟨A, N, hA, hN, φ, ⟨e⟩⟩ := hseq V hV hqc hqs hqcs
      have := hA
      have := hN
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
        (isQuasicoherentOnSite_kernel_of_quasicoherent B S hS _ _ φ)

end AlgebraicGeometry.Space

end
