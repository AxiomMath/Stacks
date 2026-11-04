module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringAugmentationKernel
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite

/-!
# The comparison map from the relative hypercovering complex to the derived direct image

Let `f : X ⟶ S` be a morphism of schemes and let `K` be a hypercovering of the Zariski site of
`X` with base object the top open.  The relative hypercovering complex

`𝓚⁼(K, f, M) = ( ∏_{i ∈ I₀} f_{i,*}M|_{U_i} ⟶ ∏_{i ∈ I₁} f_{i,*}M|_{U_i} ⟶ ⋯ )`

of `𝒪_S`-modules comes with an augmentation `ε : (f_*M)[0] ⟶ 𝓚⁼(K, f, M)`, natural in the
`𝒪_X`-module `M`.  This file assembles the construction in the proof of [Stacks, Tag 09VX] out
of that augmentation and produces a natural transformation

`α : Q(𝓚⁼(K, f, -)) ⟶ R⁺f_*((-)[0])`

of functors `X.Modules ⥤ D⁺(S.Modules)`, compatible with the augmentation and with the unit of
the right derived functor, and an isomorphism at every **injective** `𝒪_X`-module.

## Main results

* `hasFunctorialInjectiveEmbeddings_Modules`:  the category of `𝒪_X`-modules on a scheme has
  functorial injective embeddings.  This is [Stacks, Tag 01DU] read at the scheme-level spelling
  `AlgebraicGeometry.Scheme.Modules`.
* `exists_hypercoveringComparison`:  the comparison `α` exists, is pinned by the augmentation and
  is invertible at every injective `𝒪_X`-module.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an abbreviation, so neither Mathlib's nor this
library's instances for `CategoryTheory.SheafOfModules` are found at the scheme-level spelling by
name; `hasFunctorialInjectiveEmbeddings_Modules` therefore supplies the site and the sheaf of
rings explicitly.  Instance synthesis does find the four typeclass inputs of the construction —
`HasCoproducts.{0} S.Modules`, `HasDerivedCategory S.Modules`, `HasDerivedCategory X.Modules` and
`EnoughInjectives X.Modules` — once `HasDerivedCategory.standard` is a local instance.

Nothing is assumed about `f` or about the members of `K`:  in particular the members need not be
affine and `f` need not be affine or separated.  What is *not* here is the degeneration from
injective coefficients to quasi-coherent ones, which is what [Stacks, Tag 01XN] needs and where
affineness of the members of `K` enters; `α` is recorded here exactly as far as it is proved.

## References

* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open StacksDraft.DerivedSectionsComparison

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.UniversalPushforward

open Stacks.CategoryTheory.Hypercovering (IsHypercovering)

variable {X S : Scheme.{u}}

/-- **The category of `𝒪_X`-modules on a scheme has functorial injective embeddings.**  This is
[Stacks, Tag 01DU] for the Zariski site of `X` and the structure sheaf, read at the scheme-level
spelling `AlgebraicGeometry.Scheme.Modules`.

It is the hypothesis `hFIE` of
`StacksDraft.DerivedSectionsComparison.exists_comparison_of_hasFunctorialInjectiveEmbeddings`,
which is what turns the construction in the proof of [Stacks, Tag 09VX] into a statement about
`𝒪_X`-modules. -/
theorem hasFunctorialInjectiveEmbeddings_Modules (X : Scheme.{u}) :
    HasFunctorialInjectiveEmbeddings X.Modules :=
  Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings
    (Opens.grothendieckTopology X.carrier) X.ringCatSheaf

/-- **The comparison map of [Stacks, Tag 09VX] for the relative hypercovering complex.**  Let
`f : X ⟶ S` be a morphism of schemes and let `K` be a hypercovering of the Zariski site of `X`
with base object the top open.  Then there are natural transformations

* `ψ : Q((f_*-)[0]) ⟶ R⁺f_*((-)[0])`, the canonical map through a functorial injective
  resolution, and
* `α : Q(𝓚⁼(K, f, -)) ⟶ R⁺f_*((-)[0])`

of functors `X.Modules ⥤ D⁺(S.Modules)` with `Q(ε) ≫ α = ψ`, and both are isomorphisms at every
injective `𝒪_X`-module.

The pin `Q(ε) ≫ α = ψ` is what makes the statement non-vacuous:  by
`StacksDraft.DerivedSectionsComparison.isZero_of_pin_zero` the zero transformation satisfies it
only if `f_*` kills every injective `𝒪_X`-module.

The four inputs of the construction are all available at these hypotheses:  the complex vanishes
in negative degrees (`isZero_hypercoveringPushforwardComplexAll_obj_X`), the augmentation is
natural (`hypercoveringAugAll_naturality`), it is a quasi-isomorphism at an injective module
(`quasiIso_hypercoveringAugAll_app_of_injective`, the relative form of [Stacks, Tag 01GV]) and
`X.Modules` has functorial injective embeddings
(`hasFunctorialInjectiveEmbeddings_Modules`).  Nothing is assumed about `f` or about the members
of `K`. -/
theorem exists_hypercoveringComparison (f : X ⟶ S)
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K) :
    ∃ (ψ : (Scheme.Modules.pushforward f ⋙ singlePlus S.Modules) ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus)
      (α : TPlus (hypercoveringPushforwardComplexAll f K)
            (isZero_hypercoveringPushforwardComplexAll_obj_X f K) ⋙ DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus),
      Functor.whiskerRight
          (epsNat (Scheme.Modules.pushforward f) (hypercoveringPushforwardComplexAll f K)
            (fun M ↦ (hypercoveringAugAll f K).app M)
            (fun {_ _} φ ↦ hypercoveringAugAll_naturality f K φ)
            (isZero_hypercoveringPushforwardComplexAll_obj_X f K))
          DerivedCategory.Plus.Q ≫ α = ψ ∧
        (∀ M : X.Modules, Injective M → IsIso (ψ.app M)) ∧
        (∀ M : X.Modules, Injective M → IsIso (α.app M)) :=
  exists_comparison_of_hasFunctorialInjectiveEmbeddings (Scheme.Modules.pushforward f)
    (hypercoveringPushforwardComplexAll f K)
    (fun M ↦ (hypercoveringAugAll f K).app M)
    (fun {_ _} φ ↦ hypercoveringAugAll_naturality f K φ)
    (isZero_hypercoveringPushforwardComplexAll_obj_X f K)
    (fun I hI ↦ @quasiIso_hypercoveringAugAll_app_of_injective _ _ f K hK I hI)
    (hasFunctorialInjectiveEmbeddings_Modules X)

end Stacks.AlgebraicGeometry.UniversalPushforward

end
