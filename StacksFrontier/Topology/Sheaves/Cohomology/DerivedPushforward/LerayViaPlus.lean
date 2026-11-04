module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionViaPlus
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections

/-!
# The Leray comparison of [Stacks, Tag 0D5W] is the composition comparison of [Stacks, Tag 015M]

Derived sections over an open `V ⊆ Y` of a derived direct image are computed in two models.

* In the **unbounded** derived category the comparison is
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, the transformation
  `RΓ(f⁻¹V, -) ⟶ Rf_* ⋙ RΓ(V, -)` induced by the universal property of the right derived functor
  of sections over `f⁻¹V`, an isomorphism by [Stacks, Tag 0D5W].
* On the **bounded below** derived category the comparison is
  `CategoryTheory.Functor.rightDerivedFunctorPlusComp` for the pair
  `(f_*, Γ(V, -))`, the composition comparison of [Stacks, Tag 015M] between
  `R⁺(Γ(V, -) ∘ f_*)` and `R⁺Γ(V, -) ∘ R⁺f_*`.

`CategoryTheory.Functor.boundedDerivedIso` crosses the two models for one functor, and
`CategoryTheory.Functor.boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp` says that the two
*composition* comparisons correspond under three such crossings, for any unbounded comparison
satisfying the factorisation that characterises it. This file performs that instantiation at the
Leray comparison, which is the one place the hypothesis is discharged on the nose: the
characterising factorisation is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app`, because
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit` and the three-factor transformation of
[Stacks, Tag 015M] are the same expression.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.boundedDerivedSectionsIso_comp_lerayComparison`:
  **the composition comparison of [Stacks, Tag 015M] for `(f_*, Γ(V, -))` on `D⁺`, carried across
  the three model crossings, is the Leray comparison of [Stacks, Tag 0D5W].** No hypothesis on
  `f`, on `V` or on the object; the two ringed spaces are only asked to have enough injective
  sheaves of modules, which is what either model of a right derived functor needs.
* `Stacks.Cohomology.DerivedSectionsLeray.boundedDerivedSectionsIso_app_comp_lerayComparison`:
  the same at an object of `D⁺(𝒪_X)`, which is the form a consumer rewrites with.

## Implementation notes

*Why no new crossing is defined for sections.* `CategoryTheory.Functor.boundedDerivedIso` records
that it is specialized nowhere else at this generality, and names the three candidate sites that
should be retired onto it rather than joined by a fourth. The crossing for `Γ(V, -)` and the
crossing for `Γ(V, -) ∘ f_*` are therefore written out as applications of
`CategoryTheory.Functor.boundedDerivedIso` in the statements below, and only the crossing for the
direct image — which already exists as
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso` — is named.

*Why `hθ` is discharged by a single application.*
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit` is the inverse of
`Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso` read on the homotopy
category, then the unit of `RΓ(V, -)`, then derived sections of the unit of `Rf_*`; and
`pushforwardPreimageSectionsIso f V` **is** `CategoryTheory.Iso.refl` of
`f_* ⋙ Γ(V, -)`, since `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` is sections over
`f⁻¹V` with scalars restricted and that is the same functor. So the required factorisation and
`lerayComparison_fac_app` are the same statement, and the former is the latter after unfolding.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)
  [EnoughInjectives (SheafOfModules.{u} (structureSheafRing X))]
  [EnoughInjectives (SheafOfModules.{u} (structureSheafRing Y))]

/-- **`RΓ(f⁻¹V, -)` is a right derived functor of `Γ(V, -) ∘ f_*`, at that spelling of the
degreewise functor.** `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` is sections over
`f⁻¹V` with scalars restricted along `f^♯`, and `f_* ⋙ Γ(V, -)` is the same functor — which is
why `pushforwardPreimageSectionsIso` is `CategoryTheory.Iso.refl`. The instance Lean finds is
stated at the first spelling; the composition comparison of [Stacks, Tag 015M] asks for it at the
second, and instance search does not cross between them, because the identification needs
`RingedSpaceModuleAdjunction.modulePushforward` unfolded and that is not reducible.

This records the same instance at the second spelling, so that a statement naming
`CategoryTheory.Functor.boundedDerivedIso` for the composite functor elaborates. Nothing is
proved: the two types are definitionally equal and the inhabitant is the one Lean already has. -/
instance isRightDerivedFunctor_derivedPreimageSections_comp :
    (derivedPreimageSections f V).IsRightDerivedFunctor
      (show (modulePushforward f ⋙ sectionsOverOpen Y V).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ derivedPreimageSections f V from
        derivedPreimageSectionsUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs ((derivedPreimageSections f V).IsRightDerivedFunctor
    (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)))

omit [EnoughInjectives (SheafOfModules.{u} (structureSheafRing X))]
  [EnoughInjectives (SheafOfModules.{u} (structureSheafRing Y))] in
/-- **The characterising factorisation of the Leray comparison, in the shape
[Stacks, Tag 015M] asks for.** The unit of `RΓ(f⁻¹V, -)` followed by the Leray comparison is the
inverse of the identification `Γ(V, f_* -) = Γ(f⁻¹V, -)` read on the homotopy category, then the
unit of `RΓ(V, -)`, then derived sections over `V` of the unit of `Rf_*`.

This is `lerayComparison_fac_app` with the identification written as
`CategoryTheory.Iso.refl` of `f_* ⋙ Γ(V, -)`, which is what
`pushforwardPreimageSectionsIso` is. Isolating it keeps the unfolding of
`lerayUnit` out of the instantiation below. -/
theorem lerayComparison_fac_app_refl
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f V).app L ≫
        (lerayComparison f V).app (DerivedCategory.Qh.obj L) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (modulePushforward f ⋙ sectionsOverOpen Y V))
            (ComplexShape.up ℤ)).inv.app L) ≫
        (derivedSectionsOverOpenUnit Y V).app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          (derivedSectionsOverOpen Y V).map ((derivedPushforwardUnit f).app L) :=
  lerayComparison_fac_app f V L

/-- **The composition comparison of [Stacks, Tag 015M] for `(f_*, Γ(V, -))` is the Leray
comparison of [Stacks, Tag 0D5W].** For a morphism `f : X ⟶ Y` of ringed spaces and an open
`V ⊆ Y`, the comparison

> `R⁺(Γ(V, -) ∘ f_*) ⟶ R⁺Γ(V, -) ∘ R⁺f_*`

of the bounded below model, read in the unbounded derived category and conjugated by the three
`D⁺`-to-`D` crossings of `CategoryTheory.Functor.boundedDerivedIso`, is the Leray comparison
`RΓ(f⁻¹V, -) ⟶ Rf_* ⋙ RΓ(V, -)`.

Nothing is assumed of `f` or of `V`, and the two spaces are asked only for enough injective
sheaves of modules. The K-injective resolutions both sides need are [Stacks, Tag 079P], in the
form `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`.

This is the identification that lets a statement proved in one model be read in the other: the
two halves of conclusion (c) of [Stacks, Tag 0EX3] meet the top higher direct image through the
bounded below model on one side — where [Stacks, Tag 01XK] and [Stacks, Tag 089W] live — and
through the Leray comparison on the other. -/
theorem boundedDerivedSectionsIso_comp_lerayComparison :
    Functor.whiskerRight
          (Functor.rightDerivedFunctorPlusComp (modulePushforward f) (sectionsOverOpen Y V))
          DerivedCategory.Plus.ι ≫
        Functor.whiskerLeft (modulePushforward f).rightDerivedFunctorPlus
            (Functor.boundedDerivedIso (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y)).hom ≫
          Functor.whiskerRight (boundedDerivedPushforwardIso f).hom
            (derivedSectionsOverOpen Y V) =
      (Functor.boundedDerivedIso (modulePushforward f ⋙ sectionsOverOpen Y V)
            (derivedPreimageSections f V) (derivedPreimageSectionsUnit f V)
            (exists_quasiIso_isKInjective X)).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι (lerayComparison f V) :=
  Functor.boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp (modulePushforward f)
    (sectionsOverOpen Y V) (derivedPushforward f) (derivedPushforwardUnit f)
    (derivedSectionsOverOpen Y V) (derivedSectionsOverOpenUnit Y V)
    (derivedPreimageSections f V) (derivedPreimageSectionsUnit f V)
    (exists_quasiIso_isKInjective X) (exists_quasiIso_isKInjective Y) (lerayComparison f V)
    (lerayComparison_fac_app_refl f V)

/-- **The composition comparison of [Stacks, Tag 015M] is the Leray comparison**, at an object of
`D⁺(𝒪_X)`. This is the component form of `boundedDerivedSectionsIso_comp_lerayComparison`, and it
is the form a consumer rewrites with. -/
theorem boundedDerivedSectionsIso_app_comp_lerayComparison
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    DerivedCategory.Plus.ι.map
          ((Functor.rightDerivedFunctorPlusComp (modulePushforward f)
            (sectionsOverOpen Y V)).app K) ≫
        (Functor.boundedDerivedIso (sectionsOverOpen Y V) (derivedSectionsOverOpen Y V)
              (derivedSectionsOverOpenUnit Y V) (exists_quasiIso_isKInjective Y)).hom.app
            ((modulePushforward f).rightDerivedFunctorPlus.obj K) ≫
          (derivedSectionsOverOpen Y V).map ((boundedDerivedPushforwardIso f).hom.app K) =
      (Functor.boundedDerivedIso (modulePushforward f ⋙ sectionsOverOpen Y V)
              (derivedPreimageSections f V) (derivedPreimageSectionsUnit f V)
              (exists_quasiIso_isKInjective X)).hom.app K ≫
        (lerayComparison f V).app (DerivedCategory.Plus.ι.obj K) := by
  simpa using congr_app (boundedDerivedSectionsIso_comp_lerayComparison f V) K

end Stacks.Cohomology.DerivedSectionsLeray

end
