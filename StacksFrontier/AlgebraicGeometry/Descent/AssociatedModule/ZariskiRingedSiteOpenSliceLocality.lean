module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSliceTransport

/-!
# Pseudo-coherence on a scheme is local on open subschemes

Stacks 08FU part (3), `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`,
reduces `m`-pseudo-coherence of an object `E` of `D(𝒪_X)` to `m`-pseudo-coherence of the
restrictions `E|_V` over a covering — but *on the localized ringed sites*
`X.zariskiRingedSite.over V`, which is not where a statement about the open subscheme `V` lives.
This module composes that reduction with the transport of
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv`, so that the
hypothesis is a statement about the *schemes* `V`.

The result,
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme`, is the
form in which "the question is local, so we may assume `X` affine" is usable: the statement to be
discharged over a member `V` of the covering is `m`-pseudo-coherence, on the Zariski ringed site
of the scheme `V`, of the restriction of `E` read as a complex of `𝒪_V`-modules along Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv`.  On an affine `V` that is what the affine-chart
statements — `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` and the
vanishing results beside it — are about.

This is not a Stacks tag: the tag is 08FU (3), carried where it is proved, and this is that
statement read at one site through an identification, so nothing here is tagged.

## Implementation notes

The four `local instance`s below are the spelling bridges that the two sides' presentations
force, and nothing more.

* `AlgebraicGeometry.RingedSite.ringSheaf` of the localization and the restriction
  `CategoryTheory.Sheaf.over` of the sheaf of rings are equal
  (`AlgebraicGeometry.Scheme.zariskiRingedSite_over_ringSheaf`) but do not reduce to one another
  at instance transparency, so a derived-category model stated at one is not found at the other;
  likewise Mathlib's `AlgebraicGeometry.Scheme.Modules` is a definition and not an abbreviation.
* exactness of restriction to a slice,
  `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and its colimit
  counterpart, is not a global instance; it is needed here because the hypothesis mentions
  `CategoryTheory.Functor.mapDerivedCategory` of that restriction.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u d d' dV

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [∀ U : X.Opens,
    HasDerivedCategory.{d'} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over U))]
  [∀ U : X.Opens,
    HasDerivedCategory.{dV} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf U.toScheme.zariskiRingedSite.O))]

/-- A derived-category model for the `𝒪_U`-modules of an open subscheme, at Mathlib's spelling
`AlgebraicGeometry.Scheme.Modules` of that category. -/
local instance hasDerivedCategory_opensToSchemeModules :
    ∀ U : X.Opens, HasDerivedCategory.{dV} U.toScheme.Modules :=
  fun U => inferInstanceAs
    (HasDerivedCategory.{dV} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf U.toScheme.zariskiRingedSite.O)))

/-- A derived-category model for the sheaves of modules of a localized ringed site, at the
spelling `AlgebraicGeometry.RingedSite.ringSheaf` of its sheaf of rings. -/
local instance hasDerivedCategory_zariskiOverRingSheaf :
    ∀ U : X.Opens,
      HasDerivedCategory.{d'} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over U).O)) :=
  fun U => inferInstanceAs
    (HasDerivedCategory.{d'} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over U)))

/-- A derived-category model for the sheaves of modules over the restriction of
`AlgebraicGeometry.Scheme.ringCatSheaf` to an open, which is the spelling Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv` is stated at.  It is the same sheaf of rings as the
one the section's binder names, by `AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf` under
`CategoryTheory.Sheaf.over`, but `Stacks.SheafOfModules.Tensor.ringSheaf` is a definition and
does not reduce at instance transparency, so the model has to be named here as well.  This is the
counterpart of `AlgebraicGeometry.Scheme.hasDerivedCategory_ringCatSheaf_over` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ZariskiRingedSiteOpenSliceTransport.lean`
with the open left free. -/
local instance hasDerivedCategory_ringCatSheafOver :
    ∀ U : X.Opens, HasDerivedCategory.{d'} (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  fun U => inferInstanceAs
    (HasDerivedCategory.{d'} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over U)))

/-- Restriction of sheaves of modules to a slice of the Zariski site preserves finite limits. -/
local instance overFunctorPreservesFiniteLimits (U : X.Opens) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules to a slice of the Zariski site preserves finite
colimits. -/
local instance overFunctorPreservesFiniteColimits (U : X.Opens) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- **Pseudo-coherence on a scheme is local on open subschemes.**  Let `E` be an object of
`D(𝒪_X)` and `m` an integer.  Suppose every open `U` of `X` admits a covering such that, over
each member `V`, the restriction of `E` — read as an object of the derived category of
`𝒪_V`-modules along Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv` — is
`m`-pseudo-coherent on the Zariski ringed site of the *scheme* `V`.  Then `E` is
`m`-pseudo-coherent on the Zariski ringed site of `X`.

This is Stacks 08FU part (3),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, composed with
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv`.  The point of
the composition is the side the hypothesis is stated on: 08FU (3) by itself asks for
pseudo-coherence on the localized ringed site `X.zariskiRingedSite.over V`, whereas every
statement about an affine chart is about the scheme `V`. -/
theorem isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))) (m : ℤ)
    (h : ∀ U : X.Opens, ∃ S : Presieve U, Sieve.generate S ∈ X.zariskiRingedSite.J U ∧
      ∀ ⦃V : X.Opens⦄ (f : V ⟶ U), S f →
        V.toScheme.zariskiRingedSite.IsPseudoCoherentFrom
          ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
              V).mapDerivedCategory.obj E)) m) :
    X.zariskiRingedSite.IsPseudoCoherentFrom E m := by
  refine AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general
    X.zariskiRingedSite E m ?_
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  exact ⟨S, hS, fun {V} f hf =>
    isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv X V _ m (hdata f hf)⟩

end AlgebraicGeometry.Scheme

end
