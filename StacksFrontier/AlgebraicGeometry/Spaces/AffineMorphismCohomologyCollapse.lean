module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `𝓕` be an `𝒪_X`-module.  Stacks 0D2U asserts that `H^i(X, 𝓕)` agrees with
`H^i(Y, f_*𝓕)` in every degree.  The source's proof is one line: the higher direct images of `𝓕`
vanish by Stacks 073H, so the Leray spectral sequence of Cohomology on Sites, Lemma 0733
collapses.

This file supplies that collapse.  The comparison is
`Stacks.RightDerivedComp.objIsoOfAcyclicImage`, the universe-general form of the collapse
isomorphism `R^i (G ⋙ T)(A) ≅ R^i T(G A)`, with `G` the direct image of modules
`AlgebraicGeometry.Space.modulePushforward` and `T` the global sections of `𝒪_Y`-modules.  Its
two inputs are the vanishing of the higher direct images, which is Stacks 073H, and the
acyclicity for global sections on `Y` of the direct image of an injective `𝒪_X`-module, which is
Stacks 072Z.  Both are carried here as explicit named hypotheses, for the reasons in the
implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.AcyclicPushforwardOfInjective` is the hypothesis `h072Z`: the direct
  image along `f` of an injective `𝒪_X`-module is acyclic for global sections of
  `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfChartwise` and
  `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`: **Stacks 0D2U with `h03DW` and
  `h072Z` carried**, for a representable and for an affine morphism respectively.  The second
  carries the qualified `@[stacks 0D2U]` attribute.

## Implementation notes

*Which global sections.*  `AlgebraicGeometry.Space.modulePushforward` is a functor
`Modules.{u, u} ⥤ Modules.{u, u}`: its module universe is pinned to the universe of the
structure rings, deliberately and for the reasons given in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage`.  So the cohomology appearing here has
to be available at that module universe, and
`Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, w}` is not: its module
universe contains the universe `u + 1` of the objects of the small étale site, and
`max (u + 1) w = u` is impossible.  The derived functors of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` are available — left
exactness is
`AlgebraicGeometry.Space.preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf` and
enough injectives is `AlgebraicGeometry.Space.enoughInjectives_modules`, both of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections` — and that is the functor used.
The structure sheaf is written `RingedSite.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2)`
rather than through the abbreviation `structureRingSheaf`, because at the latter spelling
instance search escapes to an `EnoughInjectives` candidate with an unconstrained module universe
and gets stuck on `u + 1 =?= max (u + 1) ?w`.

*What `h072Z` is, and why it is carried.*  Stacks 072Z is proved, as
`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/PushforwardOfAnInjective.lean`), and so
is the step from it to acyclicity for global sections, part (3) of Stacks 0731, as
`Stacks.Cohomology.Leray.acyclic_globalSections_of_isTotallyAcyclic`.  Neither applies here.
The first is stated for a *source* ringed topos with all three of its universes equal and the
second for a small site, whereas the small étale site of an algebraic space over a `Scheme.{u}`
has its objects in `Type (u + 1)` and its morphisms, structure sheaf and modules at `u`.  That
restriction is not incidental: both rest on
`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree`
(`StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparison.lean`), which is
proved for a `CategoryTheory.SmallCategory` site with its sheaves valued in the same universe,
and whose `Ext`-groups would here have to be taken one universe above the sheaves.  Nor is there
a cheaper route past it: the acyclicity cannot be replaced by
`CategoryTheory.Functor.PreservesInjectiveObjects` for the direct image, since that would need
the inverse image of modules to be exact and it is only right exact — this is exactly why the
source proves Stacks 072Z instead.

*What the conclusion says.*  The left-hand side is the `i`-th right derived functor of the
composite `Γ(Y, f_* −)`, which is `H^i(X, 𝓕)` through the identification of `Γ(Y, f_*−)` with
`Γ(X, −)`.  That identification is not available at this universe either: it is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, which is stated for a
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, and the morphism of ringed topoi attached to
`f` by `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is an `AlgebraicGeometry.RingedToposHom`
— it carries the direct-image form of the structure map only, with no inverse-image form and no
adjunction between the two.  The right-hand side is `H^i(Y, f_*𝓕)` as it stands.

*Quasi-coherence and the degree.*  The source states Stacks 0D2U for a quasi-coherent `𝓕` and
`i ≥ 0`.  Neither restriction is used: `i` ranges over `ℕ`, and quasi-coherence enters the
source's proof only through Stacks 073H, which is proved in the form below — with the vanishing
reduced to its chart base changes — for an arbitrary module.

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

/-- The hypothesis `h072Z`: the direct image along `f : X ⟶ Y` of an injective `𝒪_X`-module is
acyclic for global sections of `𝒪_Y`-modules, that is, all of its higher cohomology on `Y`
vanishes.

This is Stacks 072Z read through part (3) of Stacks 0731; see the implementation notes of this
file for why it is not available on the small étale sites. -/
def AcyclicPushforwardOfInjective (f : X ⟶ Y) : Prop :=
  have := enoughInjectives_modules B S hS Y.1 Y.2
  ∀ Z : Modules.{u, u} B S hS X.1 X.2, Injective Z →
    Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((modulePushforward B S hS f).obj Z)

/-- **Stacks 0D2U for a representable morphism, with `h03DW` and `h072Z` carried.**

If `f : X ⟶ Y` is a representable morphism of algebraic spaces over `S` whose chart base changes
have vanishing higher direct images, and if the direct image along `f` of an injective module is
acyclic for global sections on `Y`, then the cohomology of `𝓕` on `X` — computed as the derived
functor of `Γ(Y, f_* −)` — is the cohomology of `f_*𝓕` on `Y`, in every degree.

The comparison is `Stacks.RightDerivedComp.objIsoOfAcyclicImage`, applied to an injective
resolution of `𝓕`: the vanishing makes its direct image a resolution of `f_*𝓕`, and `h072Z`
makes the terms of that resolution compute the cohomology of `f_*𝓕` as well. -/
def cohomologyCollapseIsoOfChartwise (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (h03DW : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f hf F n)
    (h072Z : AcyclicPushforwardOfInjective B S hS f) (i : ℕ) :
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
    (fun n hn => isZero_rightDerived_modulePushforward_of_chartwise B S hS f hf F n (h03DW n hn))
    h072Z i

/-- **Stacks 0D2U with `h03DW` and `h072Z` carried.**

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕` an `𝒪_X`-module.
Then the cohomology of `𝓕` on `X` — computed as the derived functor of `Γ(Y, f_* −)` — is the
cohomology of `f_*𝓕` on `Y`, in every degree.

This is the previous isomorphism with representability supplied by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`, so that `h03DW` is exactly the
hypothesis carried by
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`, the library's
form of Stacks 073H.  The source's statement is this one with `h03DW` and `h072Z`
discharged, for a quasi-coherent `𝓕`; quasi-coherence is not used, and neither hypothesis is
available in this repository. -/
@[stacks 0D2U "Leray collapse of the source's one-line proof; carries two unproved
hypotheses, `h03DW` (073H's own) and `h072Z` (072Z via 0731(3)) -- see the notes"]
def cohomologyCollapseIsoOfIsAffineHom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (h03DW : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f hf) F n)
    (h072Z : AcyclicPushforwardOfInjective B S hS f) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  cohomologyCollapseIsoOfChartwise B S hS f (relativelyRepresentable_of_isAffineHom B S hS f hf)
    F h03DW h072Z i

end AlgebraicGeometry.Space

end

end
