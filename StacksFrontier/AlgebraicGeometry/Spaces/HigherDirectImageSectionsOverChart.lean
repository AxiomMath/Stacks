module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex

/-!
# Cohomology over an étale chart of the target and sections of the higher direct image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `F` be an `𝒪_X`-module.  Stacks 08EX asserts that if `f` is quasi-compact and
quasi-separated then for every quasi-coherent `F` and every affine object `V` of `Y_étale`

`H^q(V ×_Y X, F) = H^0(V, R^q f_*F)`

in every degree.  The source's proof has two steps: étale localization of `Rf_*` replaces `Y` by
`V`, and then the Leray spectral sequence of Stacks 0732 degenerates at `E_2` because the
higher direct images are quasi-coherent (Stacks 0720) and a quasi-coherent module on an affine
has no higher cohomology (Stacks 01XB).

Both steps are carried out here.  The degeneration is proved without any spectral sequence, by
`Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic`: applying `f_*` to an
injective resolution of `F` gives a complex whose cohomology is `R^q f_*F` and whose terms are
acyclic for global sections on `Y`, and a left exact functor commutes with the cohomology of such
a complex.  That is the `E_2`-degeneration of Stacks 0733, part (2), at the universes of the
small étale site of an algebraic space, where the library's form
`Stacks.Cohomology.Leray.nonempty_cohomologyIso_globalSections_higherDirectImage` does not
apply.  The étale localization is the higher-direct-image clause of Stacks 03LX for the
cartesian square of `AlgebraicGeometry.Space.isPullback_chartBaseChangeInclusion`.

## Main definitions

* `AlgebraicGeometry.Space.AcyclicHigherDirectImages` is the hypothesis `hcoh`: every higher
  direct image `R^q f_*F` has vanishing higher cohomology on `Y`.  For an affine `Y` and a
  quasi-coherent `F` this is Stacks 0720 followed by Stacks 01XB read on the small étale site,
  that is by Stacks 03DW.

## Main results

* `AlgebraicGeometry.Space.globalSectionsRightDerivedIso`: **the degeneration**,
  `R^n (Γ(Y, f_*−))(F) ≅ Γ(Y, R^n f_*F)`, granted `hcoh` and the acyclicity of Stacks 072Z.
* `AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage`: the two steps of the
  proof of Stacks 08EX, the identification of the cohomology over `V ×_Y X` with the sections
  over `V` of `R^q f_*F` from the three hypotheses below.  Stacks 08EX itself, with all three
  proved, is `AlgebraicGeometry.Space.cohomologyAffineChartIsoSectionsHigherDirectImage`.
* `AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage_of_representable`: the
  same for a representable morphism, with the injective-preservation hypothesis discharged by
  Stacks 071Z.

## Implementation notes

*What is carried, and which tag each carried hypothesis is.*  Three hypotheses are carried and
none of them is the content of Stacks 08EX itself.

* `h072Z` is `AlgebraicGeometry.Space.AcyclicPushforwardOfInjective`, the acyclicity for global
  sections on the target of the direct image of an injective module.  It is Stacks 072Z read
  through part (3) of Stacks 0731; the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineMorphismCohomologyCollapse.lean`, where the
  hypothesis is defined, record why neither existing form applies at these universes.
* `hcoh` is the vanishing of the higher cohomology of the higher direct images on `Y`.  This is
  where the source uses Stacks 0720 and Stacks 01XB: quasi-coherence of `R^q f_*F` plus
  vanishing of the higher cohomology of a quasi-coherent module on an affine.  Stacks 0720 is
  not proved in this development — see
  `StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherentReduction.lean` — and
  neither is the étale-site reading of Stacks 01XB, which is Stacks 03DW and has no attribute
  site anywhere here.
* `h03F3` is the injective-preservation half of Stacks 03F3, part (1), for the étale structure
  morphism `V ×_Y X ⟶ X`, in the form taken as a hypothesis by
  `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`.
  It is discharged for a representable `f` by Stacks 071Z, which is the content of the second
  main result above, and for an arbitrary étale morphism by
  `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`.

*How the cohomology over `V ×_Y X` is written.*  It is the `q`-th right derived functor of the
composite `Γ(V, f'_*−)`, with `f' : V ×_Y X ⟶ V` the base change of `f`.  The identification of
that composite with `Γ(V ×_Y X, −)` is the factorization of global sections through a direct
image; it is `Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, which is stated for a
`Stacks.Sheaves.RingedToposModules.RingedToposHom` and is built from the adjunction between
inverse and direct image, while the morphism of ringed topoi attached to a morphism of algebraic
spaces by `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries the direct-image form of
the structure map only.  The same reading is used by
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`, the library's form of Stacks 0D2U,
and for the same reason.

*The module universe* is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there; *the degree* runs over `ℕ` in the
injective-resolution convention `CategoryTheory.Functor.rightDerived`, in which the source's
`q ∈ ℤ` is the same statement, the negative degrees being zero on both sides.

*The affineness of `V` and the hypotheses on `f`* are not binders of the results below: they
enter the source's proof only through `hcoh`, which is stated directly.  Affineness and
quasi-compactness are what make `hcoh` true, not what make the degeneration work.

## References

* [Stacks Project, Lemma 69.3.2 (Tag 08EX)](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
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

/-- The algebraic space represented by an étale scheme chart `V` of `Y`, in the spelling in which
`AlgebraicGeometry.Space.chartBaseChangeProjection` has it as its target.

This is `AlgebraicGeometry.Space.chartSpace B S hS Y V`; the two agree by definition, and the
spelling below is the one that matches the codomain of the direct image along the base change of
a morphism at `V`. -/
noncomputable abbrev chartBaseChangeTarget (V : SmallEtale B S hS Y.1) :
    AlgebraicSpaces B S hS :=
  (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V)

/-! ### The degeneration of the Leray spectral sequence at an acyclic target -/

/-- The hypothesis `hcoh`: every higher direct image `R^q f_*F` of an `𝒪_X`-module `F` along
`f : X ⟶ Y` is acyclic for global sections of `𝒪_Y`-modules, that is, `H^p(Y, R^q f_*F) = 0` for
every `p > 0`.

In the source's proof of Stacks 08EX the target is an affine object of `Y_étale` and `F` is
quasi-coherent, so that the higher direct images are quasi-coherent by Stacks 0720 and the
vanishing is Stacks 01XB read on the small étale site, that is Stacks 03DW. -/
def AcyclicHigherDirectImages (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  ∀ q : ℕ, Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (((modulePushforward B S hS f).rightDerived q).obj F)

/-- **The degeneration of the Leray spectral sequence of `f` at an acyclic target**, Stacks 0733
part (2) for the modules on the small étale site of an algebraic space.

If the direct image along `f : X ⟶ Y` of every injective `𝒪_X`-module is acyclic for global
sections on `Y`, and if every higher direct image `R^q f_*F` has vanishing higher cohomology on
`Y`, then the cohomology of `F` on `X` — computed as the right derived functor of the composite
`Γ(Y, f_*−)` — is the module of global sections on `Y` of the degree-`n` higher direct image.

No spectral sequence is used: applying `f_*` to an injective resolution of `F` gives a complex
whose cohomology objects are the higher direct images and whose terms are acyclic by `h072Z`, and
`Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic` says that a left exact
functor commutes with the cohomology of such a complex. -/
def globalSectionsRightDerivedIso (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (h072Z : AcyclicPushforwardOfInjective B S hS f)
    (hcoh : AcyclicHigherDirectImages B S hS f F) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
              Y.2).O))).rightDerived n).obj F ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).obj
        (((modulePushforward B S hS f).rightDerived n).obj F) :=
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  (injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f ⋙
      globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic
      (globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      (Stacks.RightDerivedComp.mapCocomplex (modulePushforward B S hS f)
        (injectiveResolution F))
      (fun q => h072Z _ ((injectiveResolution F).injective q))
      (fun q => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
        ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) q) (hcoh q)) n ≪≫
    (globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).mapIso
      ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) n).symm

/-! ### Stacks 08EX -/

/-- **The two steps of the proof of Stacks 08EX, at an arbitrary chart.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S`, let `F` be an `𝒪_X`-module and let `V` be an étale scheme
chart of `Y`.  Then the cohomology of `F` over
`U = V ×_Y X` agrees with the module of sections over `V` of the degree-`q` higher direct image
`R^q f_*F`, in every degree:

`H^q(V ×_Y X, F) = H^0(V, R^q f_*F)`.

The right hand side is the restriction of `R^q f_*F` to the chart `V`, read through its global
sections there, and the left hand side is the `q`-th right derived functor of `Γ(V, f'_*−)` for
`f' : U ⟶ V` the base change of `f`.  The proof is the source's: the higher-direct-image clause
of Stacks 03LX identifies `(R^q f_*F)|_V` with `R^q f'_*(F|_U)`, and the Leray spectral sequence
of `f'` degenerates at `E_2`, which is `AlgebraicGeometry.Space.globalSectionsRightDerivedIso`.

Three hypotheses are carried, none of them part of this tag's own content: `h072Z` is
Stacks 072Z through part (3) of Stacks 0731, `hcoh` is where the source invokes Stacks 0720 and
Stacks 01XB — for an affine `V` and a quasi-coherent `F` along a quasi-compact and
quasi-separated `f` it is exactly their conjunction — and `h03F3` is the injective-preservation
half of Stacks 03F3, part (1), which is discharged for a representable `f` by Stacks 071Z.

At the source's own data all three are proved in the library, and Stacks 08EX itself is
`AlgebraicGeometry.Space.cohomologyAffineChartIsoSectionsHigherDirectImage`. -/
def cohomologyChartIsoSectionsHigherDirectImage (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1) (q : ℕ)
    (h03F3 : (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects)
    (h072Z : AcyclicPushforwardOfInjective B S hS (chartBaseChangeProjection B S hS f V))
    (hcoh : AcyclicHigherDirectImages B S hS (chartBaseChangeProjection B S hS f V)
      ((chartBaseChangeModulePullback B S hS f V).obj F)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
      (chartBaseChangeSpace B S hS f V).2
    have := enoughInjectives_modules B S hS (chartBaseChangeTarget B S hS V).1
      (chartBaseChangeTarget B S hS V).2
    ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V) ⋙
            globalSectionsFunctor.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
                (chartBaseChangeTarget B S hS V).1
                (chartBaseChangeTarget B S hS V).2).O))).rightDerived q).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F) ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
              (chartBaseChangeTarget B S hS V).1
            (chartBaseChangeTarget B S hS V).2).O))).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
            (isEtale_chartToSpace B S hS Y V)).obj
          (((modulePushforward B S hS f).rightDerived q).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  have := enoughInjectives_modules B S hS (chartBaseChangeTarget B S hS V).1
    (chartBaseChangeTarget B S hS V).2
  globalSectionsRightDerivedIso B S hS (chartBaseChangeProjection B S hS f V)
      ((chartBaseChangeModulePullback B S hS f V).obj F) h072Z hcoh q ≪≫
    (globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (chartBaseChangeTarget B S hS V).1
          (chartBaseChangeTarget B S hS V).2).O))).mapIso
      ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS
        (chartBaseChangeInclusion B S hS f V) (chartBaseChangeProjection B S hS f V) f
        (chartToSpace B S hS Y V) (isPullback_chartBaseChangeInclusion B S hS f V)
        (isEtale_chartToSpace B S hS Y V) h03F3 q).app F)

/-- **Stacks 08EX for a representable morphism, with the injective-preservation hypothesis
discharged.**  For a representable `f : X ⟶ Y` the fibre product `U = V ×_Y X` is an étale
scheme chart of `X`, so the identification of `(R^q f_*F)|_V` with `R^q f'_*(F|_U)` is
Equation 69.3.0.1 of the source, Stacks 071Z, in which the injective-preservation half of
Stacks 03F3 is proved rather than assumed.  Only `h072Z` and `hcoh` remain. -/
def cohomologyChartIsoSectionsHigherDirectImage_of_representable (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (q : ℕ)
    (h072Z : AcyclicPushforwardOfInjective B S hS (smallBaseChangeChartMap B S hS f hf V))
    (hcoh : AcyclicHigherDirectImages B S hS (smallBaseChangeChartMap B S hS f hf V)
      ((etaleModulePullback B S hS
        (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
        (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))).obj F)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).2
    have := enoughInjectives_modules B S hS (chartSpace B S hS Y V).1
      (chartSpace B S hS Y V).2
    ((modulePushforward B S hS (smallBaseChangeChartMap B S hS f hf V) ⋙
            globalSectionsFunctor.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (chartSpace B S
                  hS Y V).1
                (chartSpace B S hS Y V).2).O))).rightDerived q).obj
        ((etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))).obj F) ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (chartSpace B S hS Y
              V).1
            (chartSpace B S hS Y V).2).O))).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
            (isEtale_chartToSpace B S hS Y V)).obj
          (((modulePushforward B S hS f).rightDerived q).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).2
  have := enoughInjectives_modules B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2
  globalSectionsRightDerivedIso B S hS (smallBaseChangeChartMap B S hS f hf V) _ h072Z hcoh q ≪≫
    (globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (chartSpace B S hS Y V).1
          (chartSpace B S hS Y V).2).O))).mapIso
      ((moduleHigherPushforwardChartBaseChangeIso B S hS f hf V q).app F)

end AlgebraicGeometry.Space

end

end
