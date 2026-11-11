module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLerayCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray collapse along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `𝓕` be a quasi-coherent `𝒪_X`-module.  Stacks 0D2U asserts that
`H^i(X, 𝓕) = H^i(Y, f_*𝓕)` for every `i ≥ 0`; the source's proof is that the higher direct images
of `𝓕` vanish (Stacks 073H), so the Leray spectral sequence of Cohomology on Sites, Lemma 0733
collapses.

This file states that collapse with no input left open:
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom` identifies the derived functors of
`Γ(Y, f_* −)` at `𝓕`, which are the derived functors of `Γ(X, −)` at `𝓕` through
`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`, with `H^i(Y, f_*𝓕)`.  It is
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHomOfChartwise` with its two inputs
proved: the chartwise vanishing of the higher direct images,
`AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isAffineHom` (Stacks 073H), and the
acyclicity of the direct image of an injective module,
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective` (Stacks 072Z through 0731 (3)).  The same
comparison read in abelian groups, with the left-hand side written as `H^i(X, 𝓕)`, is
`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`: Stacks 0D2U as the Leray collapse
  `R^i Γ(Y, f_* −)(𝓕) ≅ H^i(Y, f_*𝓕)`.
* `AlgebraicGeometry.Space.AcyclicPushforwardOfInjective` and
  `AlgebraicGeometry.Space.cohomologyCollapseIsoOfChartwise`: aliases of
  `AlgebraicGeometry.Space.PushforwardInjectiveGlobalSectionsAcyclic` and
  `AlgebraicGeometry.Space.rightDerivedPushforwardGlobalSectionsIsoOfChartwise`.

## References

* [Stacks Project, Lemma 69.6.3 (Tag 0D2U)](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Lemma 69.3.3 (Tag 073H)](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 21.14.5 (Tag 0733)](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The direct image along `f` of an injective `𝒪_X`-module is acyclic for global sections of
`𝒪_Y`-modules: `AlgebraicGeometry.Space.PushforwardInjectiveGlobalSectionsAcyclic`. -/
alias AcyclicPushforwardOfInjective := PushforwardInjectiveGlobalSectionsAcyclic

/-- The Leray collapse along a representable morphism from its two inputs:
`AlgebraicGeometry.Space.rightDerivedPushforwardGlobalSectionsIsoOfChartwise`. -/
alias cohomologyCollapseIsoOfChartwise := rightDerivedPushforwardGlobalSectionsIsoOfChartwise

/-- **Stacks 0D2U.**  Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕`
a quasi-coherent `𝒪_X`-module.  Then for every `i ≥ 0` the cohomology of `𝓕` on `X`, as the
`i`-th derived functor of `Γ(Y, f_* −) = Γ(X, −)` at `𝓕`, is the cohomology `H^i(Y, f_*𝓕)`. -/
@[stacks 0D2U "the Leray collapse R^i Γ(Y, f_* -)(F) ≅ H^i(Y, f_*F), as modules over the global \
  sections of Y, every degree"]
def cohomologyCollapseIsoOfIsAffineHom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  cohomologyCollapseIsoOfIsAffineHomOfChartwise B S hS f hf F
    (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f hf _ F hF n hn)
    (acyclicPushforwardOfInjective B S hS f) i

end AlgebraicGeometry.Space

end

end
