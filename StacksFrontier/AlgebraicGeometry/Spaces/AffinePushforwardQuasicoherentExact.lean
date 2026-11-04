module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGlobalSections

/-!
# The direct image along an affine morphism of algebraic spaces is exact on quasi-coherent modules

Let `h : Z ⟶ W` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  `h_*` carries an epimorphism of quasi-coherent `𝒪_Z`-modules to an epimorphism,
`AlgebraicGeometry.Space.epi_modulePushforward_map_of_isAffineHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleAffinePushforwardExactness.lean`.  This file deduces
that `h_*` carries the short exact sequence of a quasi-coherent submodule of a quasi-coherent
module to a short exact sequence, and so preserves the cokernel of its inclusion.

This is the form in which the Stacks Project uses Cohomology of Schemes, Lemma 01SB in the proof
of Divisors, Lemma 080G, and the algebraic-space form that Stacks 0866 needs.  The left-exactness
half is formal: `h_*` is the right adjoint of the adjunction of Stacks 03LU, so it preserves all
limits.

## Main results

* `AlgebraicGeometry.Space.shortExact_map_modulePushforward_of_isAffineHom`: `h_*` carries the
  short exact sequence of a quasi-coherent submodule of a quasi-coherent module and its quotient
  to a short exact sequence.
* `AlgebraicGeometry.Space.preservesCokernel_submoduleι_modulePushforward_of_isAffineHom`:
  **`h_*` preserves the cokernel of the inclusion of a quasi-coherent submodule of a
  quasi-coherent module.**

## Implementation notes

The cokernel statement is formal in the way
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExact.lean` is formal for a
closed immersion, except that right exactness is available only along the quasi-coherent
sequences, so `CategoryTheory.Limits.PreservesColimit` is produced for the one parallel pair at
hand rather than as `PreservesFiniteColimits`: the direct image of the short exact sequence is
short exact — mono and exactness from preservation of finite limits, epimorphy from the above —
and the right-hand map of a short exact sequence is a cokernel of its left-hand map.

No `@[stacks]` attribute is attached.  The assertions of Stacks 07U8 are quasi-coherence of the
direct image, its agreement with the total derived direct image, and its commutation with base
change; right exactness is none of the three, and is used by the source inside proofs rather
than stated.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u + 1`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z W : AlgebraicSpaces B S hS}

/-! ### Short exactness and the cokernel -/

/-- **The direct image along an affine morphism carries the short exact sequence of a
quasi-coherent submodule of a quasi-coherent module to a short exact sequence.**

Monomorphy of the left-hand map and exactness in the middle hold because `h_*` preserves finite
limits, being the right adjoint of the adjunction of Stacks 03LU; epimorphy of the right-hand
map is `AlgebraicGeometry.Space.epi_modulePushforward_map_of_isAffineHom`, the quotient being
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`. -/
theorem shortExact_map_modulePushforward_of_isAffineHom (h : Z ⟶ W)
    (hh : IsAffineHom B S hS h.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (hG : G.IsQuasicoherentOnSite) (K : G.Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite) :
    ((submoduleQuotientShortComplex B S hS Z G K).map
      (modulePushforward B S hS h)).ShortExact := by
  have hSE := shortExact_submoduleQuotientShortComplex B S hS Z G K
  have hlim : PreservesLimits (modulePushforward B S hS h) :=
    (modulePullbackAdjunction B S hS h).rightAdjoint_preservesLimits
  have hfl : PreservesFiniteLimits (modulePushforward B S hS h) := inferInstance
  have hfk := KernelFork.mapIsLimit _ hSE.fIsKernel (modulePushforward B S hS h)
  have hGi : G.IsQuasicoherentOnSite := hG
  have hKi : K.toSheafOfModules.IsQuasicoherentOnSite := hK
  have hcok : (cokernel K.ι).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_cokernel_unconditional B S hS Z.1 Z.2 K.ι
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hfk
          mono_f := mono_of_isLimit_fork hfk
          epi_g := epi_modulePushforward_map_of_isAffineHom h hh hG hcok (cokernel.π K.ι) }

/-- **The direct image along an affine morphism of algebraic spaces preserves the cokernel of
the inclusion of a quasi-coherent submodule of a quasi-coherent module.**

The direct image of the short exact sequence is short exact, and the right-hand map of a short
exact sequence in an abelian category is a cokernel of its left-hand map. -/
theorem preservesCokernel_submoduleι_modulePushforward_of_isAffineHom (h : Z ⟶ W)
    (hh : IsAffineHom B S hS h.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (hG : G.IsQuasicoherentOnSite) (K : G.Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite) :
    PreservesColimit (parallelPair K.ι 0) (modulePushforward B S hS h) := by
  have hSE := shortExact_map_modulePushforward_of_isAffineHom B S hS h hh G hG K hK
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel K.ι) ?_
  exact (CokernelCofork.isColimitMapCoconeEquiv _ (modulePushforward B S hS h)).2
    hSE.gIsCokernel

end AlgebraicGeometry.Space

end
