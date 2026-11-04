module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatPullbackExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian

/-!
# Kernels of quasi-coherent modules are computed on flat objects; Stacks 076X

Let `𝒳` be an algebraic stack and `φ : 𝓕 ⟶ 𝓖` a map of quasi-coherent `𝒪_𝒳`-modules. Its kernel
in `QCoh(𝒪_𝒳)` is `Q(Ker(i φ))`, the coherator `Q` of **Stacks 0778** applied to the kernel
`Ker(i φ)` computed in `Mod(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLimitKernelForkCoherator`).
The kernel `Ker(i φ)` lies in `LQCoh^fbc(𝒪_𝒳)`, a weak Serre subcategory containing `QCoh(𝒪_𝒳)`
(**Stacks 0771** (2)), so the counit `Q(Ker(i φ)) ⟶ Ker(i φ)` has parasitic kernel and cokernel
(**Stacks 0779** (2)) and is therefore bijective on sections over every flat object. On such an
object the kernel in `QCoh(𝒪_𝒳)` thus has the sections of the kernel in `Mod(𝒪_𝒳)`, which are
the kernel of `φ` on sections
(`AlgebraicGeometry.Stack.AlgebraicStacks.injective_and_range_eq_ker_of_isLimit_kernelFork`):
kernels in `QCoh(𝒪_𝒳)` are computed on flat objects
(`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentKernelsOnFlatObjects`).

This is the hypothesis of
`AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_quasicoherentPullback_of_isFlat`, which
gives **Stacks 076X**: for a flat 1-morphism `f` of algebraic stacks, `f^*` is exact on
quasi-coherent modules
(`AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_quasicoherentPullback`).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentKernelsOnFlatObjects`
* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteLimits_quasicoherentPullback`
* `AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_quasicoherentPullback`: **Stacks 076X**.

## References

* [Stacks Project, Tag 076X](https://stacks.math.columbia.edu/tag/076X)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Kernels in `QCoh(𝒪_𝒳)` exist and are computed on flat objects.** The kernel of `φ` is the
coherator of its kernel in `Mod(𝒪_𝒳)`; that kernel lies in `LQCoh^fbc(𝒪_𝒳)` (**Stacks 0771**
(2)), so the counit of the coherator at it has parasitic kernel and cokernel (**Stacks 0779**
(2)) and is bijective on sections over a flat object. -/
theorem quasicoherentKernelsOnFlatObjects (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    QuasicoherentKernelsOnFlatObjects B S hS 𝒳 := fun F G φ =>
  ⟨_, ⟨isLimitKernelForkCoherator B S hS 𝒳 φ⟩, fun x hx => by
    obtain ⟨hinj, hrange⟩ := injective_and_range_eq_ker_of_isLimit_kernelFork B S hS 𝒳 φ
      (isLimitKernelForkCoherator B S hS 𝒳 φ) x hx
    refine ⟨hinj, fun s hs => ?_⟩
    have hs' := hrange.symm ▸ LinearMap.mem_ker.2 hs
    exact LinearMap.mem_range.1 hs'⟩

variable {B S hS} {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image along a flat 1-morphism of algebraic stacks is left exact** on
quasi-coherent modules. -/
theorem preservesFiniteLimits_quasicoherentPullback (hf : AlgebraicStacks.IsFlat B S hS f) :
    PreservesFiniteLimits (quasicoherentPullback B S hS f) :=
  preservesFiniteLimits_quasicoherentPullback_of_isFlat f hf
    (quasicoherentKernelsOnFlatObjects B S hS 𝒳) (quasicoherentKernelsOnFlatObjects B S hS 𝒴)

/-- **Stacks 076X.** If `f : 𝒳 ⟶ 𝒴` is a flat morphism of algebraic stacks, then
`f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` is an exact functor: it preserves finite colimits, as it does for
every `f`, and finite limits, because kernels of quasi-coherent modules are computed on flat
objects (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentKernelsOnFlatObjects`) and `f`
carries flat objects to flat objects. -/
@[stacks 076X]
theorem exactFunctor_quasicoherentPullback (hf : AlgebraicStacks.IsFlat B S hS f) :
    exactFunctor (quasicoherentModules B S hS 𝒴) (quasicoherentModules B S hS 𝒳)
      (quasicoherentPullback B S hS f) :=
  exactFunctor_quasicoherentPullback_of_isFlat f hf
    (quasicoherentKernelsOnFlatObjects B S hS 𝒳) (quasicoherentKernelsOnFlatObjects B S hS 𝒴)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
