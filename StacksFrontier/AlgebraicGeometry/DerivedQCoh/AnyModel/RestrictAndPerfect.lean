module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.Homology.Perfect.MapDerivedCategoryAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# Restriction, perfectness and quasi-coherence at an arbitrary model

`HasDerivedCategory.{w} C` carries the chosen localization as data, so a statement proved at one
choice says nothing about another until it is transported. The lifting results of
`StacksFrontier/AlgebraicGeometry/Perfect/LiftingComplexes/` — [Stacks, Tag 09IM] among them — are
proved with `CategoryTheory.HasDerivedCategory.standard` installed as a file-local instance, while
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is a global instance making `D(𝒪_X)` locally
small, and it is only at the latter that `D(𝒪_X)` has the direct sums Brown representability and
the compact-generation statements ask for.

This file supplies the three transports a statement about restriction of perfect objects needs:
restriction itself, perfectness, and membership in `D_QCoh(𝒪_X)`.

Restriction is the only one that is not immediate. `Stacks.Duality.OpenImmersion.derivedRestrict`
is `CategoryTheory.Functor.mapDerivedCategory` of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, so the transport is the general one of
`StacksDraft.DerivedModel.mapDerivedCategoryModelIso`; what has to be said here is only that
restriction of modules along an open immersion is exact, which
`Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor` and its two companions give.

Perfectness and quasi-coherence are immediate because
`Stacks.Cohomology.PerfectComplexes.IsPerfect` and `Stacks.DerivedQCoh.IsDQCoh` already take a
`[HasDerivedCategory]` binder: the first is the existence of a perfect complex representative, and
the comparison equivalence identifies the two localization functors
(`StacksDraft.DerivedModel.modelCompQIso`) and is fully faithful; the second is quasi-coherence of
every cohomology sheaf, and the comparison equivalence identifies the cohomology functors
(`StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso`).

## Main definitions

* `Stacks.DerivedQCoh.AnyModel.derivedRestrictModelIso` — restriction along an open immersion of
  schemes, read at two models of the source and two of the target.

## Main results

* `Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff` — perfectness of an object of the derived
  category of modules on a ringed space is carried both ways by the comparison equivalence.
* `Stacks.DerivedQCoh.AnyModel.isDQCoh_modelEquiv_iff` — membership in `D_QCoh` is carried both
  ways by the comparison equivalence.
* `Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff` — the cohomological support
  condition of `AlgebraicGeometry.CohomologySupportedOn`, carried both ways by the comparison
  equivalence, in the unfolded form that predicate reduces to.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open StacksDraft.DerivedModel

universe u w z w' z'

namespace Stacks.DerivedQCoh.AnyModel

/-! ### Perfectness -/

/-- **Perfectness of an object of `D(𝒪_X)` does not depend on the chosen derived category.**
Perfectness is the existence of a perfect complex of `𝒪_X`-modules representing the object, and
the comparison equivalence of two models identifies the two localization functors out of
cochain complexes and is fully faithful, so a representative at one model is one at the other. -/
theorem isPerfect_modelEquiv_iff {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (h₁ : HasDerivedCategory.{w} (OXMod.{u, u} X))
    (h₂ : HasDerivedCategory.{z} (OXMod.{u, u} X))
    (K : @DerivedCategory (OXMod.{u, u} X) _ _ h₁) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X h₁ K ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X h₂
        ((modelEquiv h₁ h₂).functor.obj K) := by
  constructor
  · rintro ⟨E, hE, ⟨e⟩⟩
    exact ⟨E, hE, ⟨((modelCompQIso h₁ h₂).app E).symm ≪≫ (modelEquiv h₁ h₂).functor.mapIso e⟩⟩
  · rintro ⟨E, hE, ⟨e⟩⟩
    exact ⟨E, hE, ⟨(modelEquiv h₁ h₂).functor.preimageIso ((modelCompQIso h₁ h₂).app E ≪≫ e)⟩⟩

/-! ### Membership in `D_QCoh` -/

section IsDQCoh

/-- **Membership in `D_QCoh(𝒪_X)` does not depend on the chosen derived category.** It is
quasi-coherence of every cohomology sheaf, and the comparison equivalence of two models
identifies their cohomology functors. -/
theorem isDQCoh_modelEquiv_iff {X : AlgebraicGeometry.Scheme.{u}}
    (h₁ : HasDerivedCategory.{w} X.Modules) (h₂ : HasDerivedCategory.{z} X.Modules)
    (E : @DerivedCategory X.Modules _ _ h₁) :
    @Stacks.DerivedQCoh.IsDQCoh _ _ _ X.ringCatSheaf _ _ _ _ h₁ E ↔
      @Stacks.DerivedQCoh.IsDQCoh _ _ _ X.ringCatSheaf _ _ _ _ h₂
        ((modelEquiv h₁ h₂).functor.obj E) := by
  exact forall_congr' fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_iff_of_iso
    ((modelEquivCompHomologyFunctorIso h₁ h₂ i).app E).symm

end IsDQCoh

/-! ### Supported cohomology -/

/-- **A vanishing cohomology stalk is a vanishing cohomology stalk at either model.** This is the
transport of `AlgebraicGeometry.CohomologySupportedOn`, in unfolded form: that predicate is a
`noncomputable abbrev` whose derived category is `CategoryTheory.HasDerivedCategory.standard`,
fixed by a file-local instance in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedCohomology.lean`, so it cannot be *written* at
another model -- but it is reducible, and it unfolds to exactly the
stalk-vanishing condition this statement carries both ways. A consumer holding the support
condition at one model therefore gets it at the other by composing with this equivalence
pointwise, with no restatement of the predicate.

The predicate is the vanishing of every cohomology stalk outside the subset, and the comparison
equivalence of two models identifies their cohomology functors. -/
theorem isZero_stalk_homology_modelEquiv_iff {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (h₁ : HasDerivedCategory.{w} (SheafOfModules.{u} O))
    (h₂ : HasDerivedCategory.{z} (SheafOfModules.{u} O))
    (E : @DerivedCategory (SheafOfModules.{u} O) _ _ h₁) (i : ℤ) (x : Y) :
    IsZero (TopCat.Presheaf.stalk (X := Y)
        ((((@DerivedCategory.homologyFunctor (SheafOfModules.{u} O) _ _ h₁ i).obj
          E).val.presheaf)) x) ↔
      IsZero (TopCat.Presheaf.stalk (X := Y)
        ((((@DerivedCategory.homologyFunctor (SheafOfModules.{u} O) _ _ h₂ i).obj
          ((modelEquiv h₁ h₂).functor.obj E)).val.presheaf)) x) := by
  exact Iso.isZero_iff <| ((SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf _) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((modelEquivCompHomologyFunctorIso h₁ h₂ i).app E).symm

/-! ### Restriction along an open immersion -/

section Restrict

attribute [local instance] Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor

/-- **Restriction along an open immersion of schemes, read at two models.** For an open immersion
`f : X ⟶ Y` and chosen derived categories `hY₁, hY₂` of `𝒪_Y`-modules and `hX₁, hX₂` of
`𝒪_X`-modules, the restriction functors at `(hY₁, hX₁)` and at `(hY₂, hX₂)` agree up to the
comparison equivalences of the two models on source and target. Restriction of modules is exact,
so this is `StacksDraft.DerivedModel.mapDerivedCategoryModelIso`. -/
def derivedRestrictModelIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f]
    (hY₁ : HasDerivedCategory.{w} Y.Modules) (hY₂ : HasDerivedCategory.{z} Y.Modules)
    (hX₁ : HasDerivedCategory.{w'} X.Modules) (hX₂ : HasDerivedCategory.{z'} X.Modules) :
    @Functor.mapDerivedCategory _ _ _ hY₁ _ _ _ hX₁
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) _ _ _ ⋙
        (modelEquiv hX₁ hX₂).functor ≅
      (modelEquiv hY₁ hY₂).functor ⋙
        @Functor.mapDerivedCategory _ _ _ hY₂ _ _ _ hX₂
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) _ _ _ :=
  mapDerivedCategoryModelIso _ hY₁ hY₂ hX₁ hX₂

/-- **Restriction along an open immersion carried from the standard model to any other.** The
specialisation of `Stacks.DerivedQCoh.AnyModel.derivedRestrictModelIso` with the first model on
each side taken to be `CategoryTheory.HasDerivedCategory.standard`, at which
`Stacks.Duality.OpenImmersion.derivedRestrict` and the lifting results of
`StacksFrontier/AlgebraicGeometry/Perfect/LiftingComplexes/` are stated. -/
def derivedRestrictStandardModelIso {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f]
    (hY : HasDerivedCategory.{z} Y.Modules) (hX : HasDerivedCategory.{z'} X.Modules) :
    @Stacks.Duality.OpenImmersion.derivedRestrict _ _ f _ (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard Y.Modules) ⋙
        (modelEquiv (HasDerivedCategory.standard X.Modules) hX).functor ≅
      (modelEquiv (HasDerivedCategory.standard Y.Modules) hY).functor ⋙
        @Functor.mapDerivedCategory _ _ _ hY _ _ _ hX
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor f) _ _ _ :=
  derivedRestrictModelIso f _ hY _ hX

end Restrict

end Stacks.DerivedQCoh.AnyModel

end
