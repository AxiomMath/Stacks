module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The Leray collapse along an affine morphism of algebraic spaces, from its two inputs

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `𝓕` be an `𝒪_X`-module.  The source's proof of Stacks 0D2U is one line: the
higher direct images of a quasi-coherent `𝓕` vanish by Stacks 073H, so the Leray spectral
sequence of Cohomology on Sites, Lemma 0733 collapses.

This file supplies that collapse as a reduction.  The comparison is
`Stacks.RightDerivedComp.objIsoOfAcyclicImage`, the universe-general form of the collapse
isomorphism `R^i (G ⋙ T)(A) ≅ R^i T(G A)`, with `G` the direct image of modules
`AlgebraicGeometry.Space.modulePushforward` and `T` the global sections of `𝒪_Y`-modules.  Its
two inputs, the vanishing of the higher direct images (Stacks 073H) and the acyclicity for global
sections on `Y` of the direct image of an injective `𝒪_X`-module (Stacks 072Z), are arguments
here.  Both are proved, as
`AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isAffineHom` (for quasi-coherent
`𝓕`) and `AlgebraicGeometry.Space.acyclicPushforwardOfInjective`, downstream of this file; the
isomorphism without them is `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`.

## Main definitions

* `AlgebraicGeometry.Space.PushforwardInjectiveGlobalSectionsAcyclic`: the direct image along `f`
  of an injective `𝒪_X`-module is acyclic for global sections of `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.rightDerivedPushforwardGlobalSectionsIsoOfChartwise` and
  `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHomOfChartwise`: the Leray collapse
  `R^i Γ(Y, f_* −)(𝓕) ≅ H^i(Y, f_*𝓕)` from the two inputs, for a representable and for an affine
  morphism respectively.

## Implementation notes

`AlgebraicGeometry.Space.modulePushforward` is a functor `Modules.{u, u} ⥤ Modules.{u, u}`: its
module universe is pinned to the universe of the structure rings, for the reasons given in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage`.  So the cohomology appearing here has
to be available at that module universe, and
`Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, w}` is not: its module
universe contains the universe `u + 1` of the objects of the small étale site, and
`max (u + 1) w = u` is impossible.  The derived functors of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` are available — left
exactness is
`AlgebraicGeometry.Space.preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf` and
enough injectives is `AlgebraicGeometry.Space.enoughInjectives_modules` — and that is the functor
used.

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

/-- The direct image along `f : X ⟶ Y` of an injective `𝒪_X`-module is acyclic for global
sections of `𝒪_Y`-modules, that is, all of its higher cohomology on `Y` vanishes.

This is Stacks 072Z read through part (3) of Stacks 0731; it holds for every `f`, by
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective`. -/
def PushforwardInjectiveGlobalSectionsAcyclic (f : X ⟶ Y) : Prop :=
  have := enoughInjectives_modules B S hS Y.1 Y.2
  ∀ Z : Modules.{u, u} B S hS X.1 X.2, Injective Z →
    Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((modulePushforward B S hS f).obj Z)

/-- **The Leray collapse along a representable morphism.**

If `f : X ⟶ Y` is a representable morphism of algebraic spaces over `S` whose chart base changes
have vanishing higher direct images on `𝓕` (`hvanish`), and if the direct image along `f` of an
injective module is acyclic for global sections on `Y` (`hacyclic`), then the derived functors of
`Γ(Y, f_* −)` at `𝓕` are the cohomology of `f_*𝓕` on `Y`, in every degree.

The comparison is `Stacks.RightDerivedComp.objIsoOfAcyclicImage`, applied to an injective
resolution of `𝓕`: the vanishing makes its direct image a resolution of `f_*𝓕`, and `hacyclic`
makes the terms of that resolution compute the cohomology of `f_*𝓕` as well. -/
def rightDerivedPushforwardGlobalSectionsIsoOfChartwise (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hvanish : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f hf F n)
    (hacyclic : PushforwardInjectiveGlobalSectionsAcyclic B S hS f) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  Stacks.RightDerivedComp.objIsoOfAcyclicImage _ _
    (fun n hn => isZero_rightDerived_modulePushforward_of_chartwise B S hS f hf F n (hvanish n hn))
    hacyclic i

/-- **The Leray collapse along an affine morphism**, from its two inputs.

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕` an `𝒪_X`-module whose
chart base changes have vanishing higher direct images (`hvanish`), and suppose the direct image
along `f` of an injective module is acyclic for global sections on `Y` (`hacyclic`).  Then the
derived functors of `Γ(Y, f_* −)` at `𝓕` are the cohomology of `f_*𝓕` on `Y`, in every degree.

This is the previous isomorphism with representability supplied by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`.  For quasi-coherent `𝓕` both
inputs are proved, and the resulting isomorphism is
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`. -/
def cohomologyCollapseIsoOfIsAffineHomOfChartwise (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hvanish : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f hf) F n)
    (hacyclic : PushforwardInjectiveGlobalSectionsAcyclic B S hS f) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  rightDerivedPushforwardGlobalSectionsIsoOfChartwise B S hS f
    (relativelyRepresentable_of_isAffineHom B S hS f hf)
    F hvanish hacyclic i

end AlgebraicGeometry.Space

end

end
