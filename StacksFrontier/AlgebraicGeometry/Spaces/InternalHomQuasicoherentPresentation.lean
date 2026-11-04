module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# Quasi-coherence of the internal Hom out of a globally presented `𝒪_F`-module, unconditionally

Clause (6) of Stacks 03M1 asserts that the internal Hom `𝓗om_{𝒪_F}(M, N)` of two quasi-coherent
`𝒪_F`-modules on an algebraic space `F` is quasi-coherent when `M` is of finite presentation.
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentFree` reaches that conclusion for a
module `M` carrying a *global* presentation by finite free modules, but only under the hypothesis
`h03DX` — Descent, Proposition 03DX(2) at the module universe `max (u + 1) m` — because it routes
the inductive step through the base change criterion.

**This file removes that hypothesis.**  The internal Hom of a presented module is a *kernel*, not
merely a module whose base change comparison is controlled: for a presentation
`Q --a--> P --b--> M --> 0` the comparison

`𝓗om_{𝒪_F}(M, N) ⟶ ker (𝓗om_{𝒪_F}(P, N) ⟶ 𝓗om_{𝒪_F}(Q, N))`

is bijective on the sections over every étale chart, by the two exactness statements of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom`, hence an isomorphism.  The
kernel clause of Stacks 03M1 — clause (3) — is available for the small étale ringed site of an
algebraic space with no hypothesis and at exactly the module universe `max (u + 1) m` in which the
internal Hom lives, as `AlgebraicGeometry.Space.kernel_isQuasicoherentOnSite`.  Composed with the
unconditional base case
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_free`, that settles the
global-presentation case with no named hypothesis at all.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomKernelIso`: **the internal Hom of a presented
  `𝒪_F`-module is the kernel of the map between the internal Homs of the presenting modules.**

## Main results

* `SheafOfModules.bijective_kernelLift_val_app`: the comparison into a kernel of sheaves of
  modules is bijective on the sections over an object as soon as the morphism it is built from is
  injective there and exact against the morphism being killed.
* `AlgebraicGeometry.Space.smallEtaleInternalHomMapLeft_comp_eq_zero`: the two first-variable
  precomposition maps of a presentation compose to zero.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian'`: the
  reduction of `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian`
  **with its `h03DX` hypothesis gone.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation'`:
  **quasi-coherence of `𝓗om_{𝒪_F}(M, N)` for a module `M` with a global presentation by finite
  free modules, with no named hypothesis**, improving
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation` by
  dropping `h03DX`.

## Implementation notes

**No `@[stacks 03M1]` attribute is carried and no clause of Stacks 03M1 is proved here.**  The
finite-presentation hypothesis of the source is Stacks 03DL(7), which is *local*: for every object
`U` of the site there is a covering `{U_i → U}` on whose members `M` has a finite global
presentation.  The hypothesis below is a global presentation on the small étale site of `F`
itself, which is strictly stronger, so the statement is **not** clause (6).  The convention — a
reduction carries no tag — is that of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentInternalHom`,
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase`,
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentFree` and
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLocal`.

What remains between the statements below and clause (6) is therefore exactly one step, the same
one recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLocal`: passing from a
presentation on the small étale site of `F` to a presentation on the members of an étale covering.
Nothing of Descent, Proposition 03DX(2) is involved in that step any more, in either direction,
which is what this file changes: before it, a chart-local presentation would still have had to be
turned into quasi-coherence through the base change criterion, and the criterion's converse
direction `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` is stated
for `AlgebraicGeometry.Space.Modules.{u, u}` while the internal Hom of `𝒪_F`-modules in module
universe `m` lands in `max (u + 1) m`, which is never `u`.

Two notes on the comparison into the kernel.

* `SheafOfModules.bijective_kernelLift_val_app` is stated for an arbitrary site, an arbitrary
  sheaf of rings and a free module universe; the two facts about a kernel of sheaves of modules it
  consumes — that its inclusion is injective on sections
  (`SheafOfModules.kernel_ι_val_app_injective`) and that it is exact against the morphism on
  sections (`SheafOfModules.exact_kernel_ι_val_app`) — are themselves generic.  The companion
  statements `Stacks.SheafOfModules.injective_kernelLift_app` and
  `Stacks.SheafOfModules.surjective_kernelLift_app` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice` are the same two halves, but with
  the module universe equal to the universe of the coefficient rings, which on the small étale
  ringed site of an algebraic space over `Scheme.{u}` would force `max (u + 1) m = u`.
* The isomorphism is obtained from objectwise bijectivity by
  `Stacks.SheafOfModules.isIso_of_bijective_val_app`, so no limit of sheaves of modules has to be
  computed and no sheafification hypothesis is needed: the kernel is the categorical one and the
  comparison is `CategoryTheory.Limits.kernel.lift`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The comparison into a kernel of sheaves of modules is bijective on the sections over an
object** as soon as the morphism it is built from is injective there and exact against the
morphism being killed.

For `φ : K ⟶ M` with `φ ≫ g = 0`, the composite of `kernel.lift g φ hφ` with the inclusion of
the kernel is `φ` itself, so injectivity of `φ` on sections gives injectivity of the comparison,
and surjectivity is the statement that a section of the kernel — a section of `M` killed by `g`,
by `SheafOfModules.exact_kernel_ι_val_app` — is hit by `φ`.  The inclusion of the kernel is
injective on sections (`SheafOfModules.kernel_ι_val_app_injective`), which is what turns the
preimage under `φ` into a preimage under the comparison.

The site, the sheaf of rings and the module universe are all arbitrary. -/
theorem bijective_kernelLift_val_app {K M N : SheafOfModules.{m} R} (g : M ⟶ N) [HasKernel g]
    (φ : K ⟶ M) (hφ : φ ≫ g = 0) (X : Cᵒᵖ)
    (hinj : Function.Injective (φ.val.app X))
    (hex : Function.Exact (φ.val.app X) (g.val.app X)) :
    Function.Bijective ((kernel.lift g φ hφ).val.app X) := by
  have hι : ∀ y : K.val.obj X,
      (kernel.ι g).val.app X ((kernel.lift g φ hφ).val.app X y) = φ.val.app X y :=
    fun y => congrArg (fun ψ : K ⟶ M => ψ.val.app X y) (kernel.lift_ι g φ hφ)
  refine ⟨fun y₁ y₂ h => hinj ((hι y₁).symm.trans ((congrArg _ h).trans (hι y₂))), fun w => ?_⟩
  obtain ⟨y, hy⟩ := (hex ((kernel.ι g).val.app X w)).1
    ((exact_kernel_ι_val_app g X ((kernel.ι g).val.app X w)).2 ⟨w, rfl⟩)
  exact ⟨y, kernel_ι_val_app_injective g X ((hι y).trans hy)⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

section Presentation

variable {M P Q : Modules.{u, max (u + 1) m} B S hS F hF} {a : Q ⟶ P} {b : P ⟶ M}

/-- **The two first-variable precomposition maps of a presentation compose to zero.**  For
`Q --a--> P --b--> M --> 0` the composite

`𝓗om_{𝒪_F}(M, N) ⟶ 𝓗om_{𝒪_F}(P, N) ⟶ 𝓗om_{𝒪_F}(Q, N)`

is zero, because over every étale chart it sends `g` to `a|_U ≫ b|_U ≫ g` and `a ≫ b = 0`.  This
is the vanishing half of
`AlgebraicGeometry.Space.exact_smallEtaleInternalHomMapLeft_app`, read as an equation of
morphisms of sheaves of modules. -/
theorem smallEtaleInternalHomMapLeft_comp_eq_zero (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF) :
    smallEtaleInternalHomMapLeft B S hS F hF b N ≫
      smallEtaleInternalHomMapLeft B S hS F hF a N = 0 := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun g => ?_))
  exact (exact_smallEtaleInternalHomMapLeft_app hab hb N X.unop
    ((smallEtaleInternalHomMapLeft B S hS F hF b N).val.app X g)).2 ⟨g, rfl⟩

/-- **The internal Hom of a presented `𝒪_F`-module is the kernel of the map between the internal
Homs of the presenting modules.**  For a presentation `Q --a--> P --b--> M --> 0` of
`𝒪_F`-modules and any `N`,

`𝓗om_{𝒪_F}(M, N) ≅ ker (𝓗om_{𝒪_F}(P, N) ⟶ 𝓗om_{𝒪_F}(Q, N))`.

The comparison is `CategoryTheory.Limits.kernel.lift` applied to first-variable precomposition
with `b`; it is bijective on the sections over every étale chart by
`AlgebraicGeometry.Space.injective_smallEtaleInternalHomMapLeft_app` and
`AlgebraicGeometry.Space.exact_smallEtaleInternalHomMapLeft_app`, hence an isomorphism.

This is the sheaf-level form of the fragment of Stacks 0GMY(1) that clause (6) of Stacks 03M1
uses.  It is strictly more than
`AlgebraicGeometry.Space.exact_smallEtaleInternalHomMapLeft_app`, which only says that the
*sections* of the internal Hom are a kernel. -/
noncomputable def smallEtaleInternalHomKernelIso (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF) :
    smallEtaleInternalHom B S hS F hF M N ≅
      kernel (smallEtaleInternalHomMapLeft B S hS F hF a N) :=
  have : IsIso (kernel.lift (smallEtaleInternalHomMapLeft B S hS F hF a N)
      (smallEtaleInternalHomMapLeft B S hS F hF b N)
      (smallEtaleInternalHomMapLeft_comp_eq_zero hab hb N)) :=
    Stacks.SheafOfModules.isIso_of_bijective_val_app _ fun X =>
      SheafOfModules.bijective_kernelLift_val_app _ _ _ X
        (injective_smallEtaleInternalHomMapLeft_app hab hb N X.unop)
        (exact_smallEtaleInternalHomMapLeft_app hab hb N X.unop)
  asIso (kernel.lift (smallEtaleInternalHomMapLeft B S hS F hF a N)
    (smallEtaleInternalHomMapLeft B S hS F hF b N)
    (smallEtaleInternalHomMapLeft_comp_eq_zero hab hb N))

/-- **Quasi-coherence of the internal Hom of a presented `𝒪_F`-module, unconditionally.**  Given
a presentation `Q --a--> P --b--> M --> 0` of `𝒪_F`-modules and an `𝒪_F`-module `N`, if the
internal Homs out of the two presenting modules are quasi-coherent then so is
`𝓗om_{𝒪_F}(M, N)`.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian`
**with its `h03DX` hypothesis removed**: that statement reaches the conclusion through the base
change criterion of Descent, Proposition 03DX(2) and therefore needs both directions of it, while
this one identifies `𝓗om_{𝒪_F}(M, N)` with a kernel
(`AlgebraicGeometry.Space.smallEtaleInternalHomKernelIso`) and appeals to the kernel clause of
Stacks 03M1, which is unconditional and at the right module universe
(`AlgebraicGeometry.Space.kernel_isQuasicoherentOnSite`). -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian' (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (N : Modules.{u, max (u + 1) m} B S hS F hF)
    (hP : (smallEtaleInternalHom B S hS F hF P N).IsQuasicoherentOnSite)
    (hQ : (smallEtaleInternalHom B S hS F hF Q N).IsQuasicoherentOnSite) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite :=
  (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).prop_of_iso
      (smallEtaleInternalHomKernelIso hab hb N).symm
      (kernel_isQuasicoherentOnSite B S hS F hF
        (smallEtaleInternalHomMapLeft B S hS F hF a N) hP hQ)

/-- **Quasi-coherence of the internal Hom out of a globally presented `𝒪_F`-module, with no named
hypothesis.**  Let `Q --a--> P --b--> M --> 0` be a presentation of `𝒪_F`-modules with `P` and `Q`
finite coproducts of copies of the structure sheaf, and let `N` be a quasi-coherent
`𝒪_F`-module.  Then `𝓗om_{𝒪_F}(M, N)` is quasi-coherent.

This improves
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation` by dropping
its hypothesis `h03DX`, Descent, Proposition 03DX(2) at the module universe `max (u + 1) m`.  The
base case is `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_free`, already
unconditional, and the inductive step is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian'`.

It is **not** clause (6) of Stacks 03M1: the source's finite-presentation hypothesis,
Stacks 03DL(7), asks for a presentation only étale-locally on `F`, and the one here is global.
See the implementation notes. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation' {p q : ℕ}
    {N : Modules.{u, max (u + 1) m} B S hS F hF}
    (ιP : ∀ _ : Fin p, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P)
    (hιP : IsColimit (Cofan.mk P ιP))
    (ιQ : ∀ _ : Fin q, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ Q)
    (hιQ : IsColimit (Cofan.mk Q ιQ))
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (hN : N.IsQuasicoherentOnSite) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian' hab hb N
    (isQuasicoherentOnSite_smallEtaleInternalHom_free ιP hιP hN)
    (isQuasicoherentOnSite_smallEtaleInternalHom_free ιQ hιQ hN)

end Presentation

end AlgebraicGeometry.Space

end
