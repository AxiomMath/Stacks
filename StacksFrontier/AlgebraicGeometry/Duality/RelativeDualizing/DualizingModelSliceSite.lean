module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme

/-!
# A dualizing model, carried to the slice-site model of modules over an affine open

`Stacks.Duality.HasDualizingModelOn K U hU` says that over an affine open `U` of a locally
Noetherian scheme the object `K` of `D(𝒪_X)` is the complex associated to a dualizing complex
over `Γ(X, U)`. It says so in the **open-subscheme** model of `𝒪_U`-modules: the restriction it
names is `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, restriction along the open
immersion `U.ι : U.toScheme ⟶ X`.

Everything about invertibility in a derived category of modules on a site — in particular
`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor`, "invertibility is local on a
covering family", and `Stacks.SheafOfModules.isInvertible_of_isIso_restrict_derivedUnitEvaluation`,
the glueing of an invertible object — is phrased in the **slice-site** model, over
`X.ringCatSheaf.over U`, because that is the model restriction to a member of a covering family
of a site produces. So a dualizing model cannot be fed to the glueing as it stands: its content
sits behind a different restriction functor.

This file carries it across. `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` factors
`restrictFunctor U.ι` as restriction to the slice site followed by the equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv` between the two models, and
`Stacks.SheafOfModules.derivedOverFunctorEquiv` is that factorization on derived categories —
both functors being exact. Composing a dualizing model's isomorphism with it moves the
isomorphism behind the two exact functors the predicate seals, which is what the affine-local
input of [Stacks, Tag 0ATP] over a cover member needs.

## Main results

* `Stacks.Duality.exists_isDualizingComplex_iso_overFunctor_of_hasDualizingModelOn`: **the
  carrying.** From `HasDualizingModelOn K U hU` it produces the dualizing complex `ω` over
  `Γ(X, U)` together with an isomorphism whose left-hand side is the *slice-site* restriction of
  `K`, read in the open-subscheme model through `overEquiv`.
* `Stacks.Duality.exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex`: the same at
  every affine open, for a dualizing complex in the sense of [Stacks, Tag 0A87].
* `Stacks.Duality.hasDualizingModelOn_iff_exists_iso_overFunctor`: the carrying loses nothing —
  the factorization is an isomorphism of functors, so the slice-site form and the
  open-subscheme form of the condition are the same condition.

## What is not proved

**Invertibility is not transported.** The statements below move the *isomorphism* of a dualizing
model behind the slice-site restriction; they do not say that the slice-site restriction of an
invertible object is invertible as an object of the monoidal `D(𝒪_X|_U)`, which would additionally
need the equivalence `overEquiv` upgraded to a monoidal one. The easy half of that,
`Stacks.Cohomology.SliceInvertible.isInvertible_restriction`, is proved independently and does
not go through this file.

Nothing here carries a Stacks attribute: the source has one model of modules over an open and
therefore states no comparison of two.

## Implementation notes

*The model of every derived category here is the standard one.* `HasDualizingModelOn` leaves
the model of `D(𝒪_X)` a free instance argument but seals the models of `D(𝒪_U)` and of
`D(Γ(X, U))` at `HasDerivedCategory.standard` inside its body, and
`Stacks.SheafOfModules.derivedOverFunctorEquiv` is likewise stated at the standard model for all
three of its categories. Since `HasDerivedCategory` is
`CategoryTheory.MorphismProperty.HasLocalization`, a *data*-carrying class, there is no proof
irrelevance that would let a statement at one model be read at another; so the statements below
fix the standard model throughout, which is the model each of their inputs is already at. Freeing
the model of `D(𝒪_X)` would mean first restating `derivedOverFunctorEquiv` with a free binder,
which is possible — its proof is `Functor.mapDerivedCategoryCompIso`, which takes free model
binders — and is a separate change to that file.

The four instance hypotheses are exactly those of `derivedOverFunctorEquiv`; they are what make
restriction to the slice site exact, hence inducible on derived categories.

## References

* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Duality

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)]

/-- **A dualizing model, carried behind the slice-site restriction.** If the affine open `U`
carries a dualizing model of `K`, then the restriction of `K` to the slice site `Opens X / U`,
read in the open-subscheme model of `𝒪_U`-modules, is the complex associated to a dualizing
complex over `Γ(X, U)`.

The isomorphism of `Stacks.Duality.HasDualizingModelOn` has `Scheme.Modules.restrictFunctor U.ι`
on its left; this one has `SheafOfModules.overFunctor` followed by
`Scheme.Modules.overEquiv`, which is what invertibility local on a covering family is phrased
in. The two are the same functor up to the isomorphism
`Stacks.SheafOfModules.derivedOverFunctorEquiv`, and nothing else enters. -/
theorem exists_isDualizingComplex_iso_overFunctor_of_hasDualizingModelOn
    (K : DerivedCategory X.Modules) (hU : IsAffineOpen U)
    (h : HasDualizingModelOn K U hU) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Dualizing.IsDualizingComplex ω ∧
        Nonempty (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory.obj K) ≅
          (tilde.functor Γ(X, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) := by
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  exact ⟨ω, hω, ⟨(Stacks.SheafOfModules.derivedOverFunctorEquiv U).app K ≪≫ e⟩⟩

/-- **The carrying loses nothing.** The slice-site form of the condition and the
open-subscheme form of `Stacks.Duality.HasDualizingModelOn` are the same condition: the
factorization of `Scheme.Modules.restrictFunctor U.ι` through the slice site is an isomorphism
of functors, so the isomorphism may be moved either way. -/
theorem hasDualizingModelOn_iff_exists_iso_overFunctor
    (K : DerivedCategory X.Modules) (hU : IsAffineOpen U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    HasDualizingModelOn K U hU ↔
      ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
        Dualizing.IsDualizingComplex ω ∧
          Nonempty (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
              ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory.obj K) ≅
            (tilde.functor Γ(X, U) ⋙
              Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) := by
  refine ⟨exists_isDualizingComplex_iso_overFunctor_of_hasDualizingModelOn U K hU, ?_⟩
  rintro ⟨ω, hω, ⟨e⟩⟩
  exact ⟨ω, hω, ⟨((Stacks.SheafOfModules.derivedOverFunctorEquiv U).app K).symm ≪≫ e⟩⟩

/-- **A dualizing complex, carried behind the slice-site restriction at every affine open.**
This is `Stacks.Duality.IsDualizingComplex` — [Stacks, Tag 0A87] — read in the model the
affine-local input of [Stacks, Tag 0ATP] over a cover member is phrased in. -/
theorem exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex
    (K : DerivedCategory X.Modules) (hU : IsAffineOpen U)
    (hK : IsDualizingComplex K) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Dualizing.IsDualizingComplex ω ∧
        Nonempty (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory.obj K) ≅
          (tilde.functor Γ(X, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) :=
  exists_isDualizingComplex_iso_overFunctor_of_hasDualizingModelOn U K hU (hK U hU)

end Stacks.Duality

end
