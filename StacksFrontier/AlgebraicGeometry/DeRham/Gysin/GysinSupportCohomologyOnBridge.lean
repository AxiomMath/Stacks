module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartData
public import StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomologyCompare
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr

/-!
# `supportCohomologyOnIso` is the derived/classical bridge for `H_T^{on T} ⋙ i_*`

`Stacks.Gysin.supportCohomologyOnIso` identifies the two spellings of the target of the Gysin
map of [Stacks, Tag 0G86]: the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` taken in the
unbounded derived category, in which the class map of [Stacks, Tag 0G7Q] is stated, and
Mathlib's classical right derived functor `Rⁿ H_T` on `X`, in which excision is available. It is
built in two steps — move `i_*` past the cohomology sheaf, then cross from the derived to the
classical spelling on `T` — and so it is not, on its face, an instance of the single generic
comparison `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` that every other
derived/classical crossing in the project is an instance of.

This file proves that it **is** one. Write `w := H_T^{on T}` for the sections supported on the
closed subset `T` realized as a sheaf on `T` — `supportedSectionsOnClosedFunctor` of
`Stacks.SheafOfModules.SupportedSections` — let `P := i_*` be the direct image along the
inclusion of `T`, let `Rw` be the total right derived functor of `w` with its unit `α`, and let

`κ : w ⋙ P ≅ H_T`

be the degree-zero identification
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of
`Stacks.SheafOfModules.SupportedSections`.
Then `supportCohomologyOnIso` is the bridge `Hⁿ(R(w ⋙ P)(ℱ[0])) ≅ Rⁿ(w ⋙ P)(ℱ)` for the
**composite** degree-zero functor `w ⋙ P`, taken at the right derived functor
`Rw ⋙ P.mapDerivedCategory`, followed by `CategoryTheory.NatTrans.rightDerived κ.hom n`, which
is where the identification `κ` is folded in. Nothing else is left over: the first two factors of
`supportCohomologyOnIso` are exactly the first two factors of the post-composition coherence of
the bridge, and the third factor of that coherence is the first half of the third factor of
`supportCohomologyOnIso`, namely
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`.

## Main results

* `Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_bridge`: **componentwise**, at a module `ℱ`,
  `supportCohomologyOnIso` is the bridge for `w ⋙ P` followed by the degree-`n` right derived
  functor of `κ`.
* `Stacks.Gysin.supportCohomologyOnIso_hom_eq_bridge`: the same as an equality of natural
  transformations.

## Implementation notes

**The three factors, and the reassociation that is all the content.** At `ℱ` the left-hand
side is a three-factor
composite, `CategoryTheory.Iso.trans_hom` and `CategoryTheory.NatTrans.comp_app` holding by
`rfl` here:

1. `Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`, which is by
   definition `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` for `P` at
   `Rw(ℱ[0])`, hence by
   `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq` is
   `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` there;
2. `P` applied to
   `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso`, which is by
   definition the bridge for `w` at `Rw`;
3. `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`, which is by definition
   `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at `κ`, hence by
   `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` is
   `CategoryTheory.Functor.rightDerivedCompIso` inverted followed by the right derived functor
   of `κ`.

`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` computes the
bridge for `w ⋙ P` as precisely (1), (2) and `CategoryTheory.Functor.rightDerivedCompIso`
inverted; that last factor is the first half of (3), so the content of the identity is one
reassociation and the three definitional re-spellings. No cancellation of a morphism against its
inverse occurs — the inverse appears once on each side.

**Every step is applied with `exact`, never `rw`.** `(w ⋙ P).mapHomotopyCategory c` and
`w.mapHomotopyCategory c ⋙ P.mapHomotopyCategory c` are definitionally but not syntactically
equal, and the three re-spellings above cross that pair, so `kabstract` refuses even a verbatim
pattern and the motive `rw` builds is ill-typed. The reassociation is therefore `bridge_assoc`, a
`private` helper at an arbitrary category with the objects implicit and the morphisms explicit,
applied by a single `exact` — the house style of
`StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence` and of
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge`.

**The composite `IsRightDerivedFunctor` instance is a `letI` in the statement**, not a
hypothesis: it occurs in the statement, through the bridge for `w ⋙ P`, so it must be available
when the statement is elaborated, and it is not synthesizable from
`Stacks.Cohomology.Localization.enoughKInjectives`, which is not a class.
`Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose` supplies it, so a consumer is never
asked for anything; the class is a `Prop`, so no coherence between two such instances has to be
checked. The exactness of `P` enters the statement for the same reason, through
`CategoryTheory.Functor.mapDerivedCategory`, and is supplied by
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteLimits` and
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits`. This is the shape
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso` already has.

**No `@[stacks ...]` attribute is attached.** This identifies two of the project's own
constructions of the target of the Gysin map of [Stacks, Tag 0G86] and is not the statement of a
tag, exactly as recorded for `Stacks.Gysin.supportCohomologyOnIso` itself.

## References

* [Stacks Project, Section 20.34 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 20.34.7 (Tag 0G7Q)](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-- Two equal isomorphisms of functors have equal components. Stated separately because the
component is taken at an object the caller does not spell out. -/
private theorem iso_hom_app_congr {E D : Type*} [Category* E] [Category* D] {A B : E ⥤ D}
    {i j : A ≅ B} (h : i = j) (K : E) : i.hom.app K = j.hom.app K := by
  subst h; rfl

/-- The reassociation behind `supportCohomologyOnIso_hom_app_eq_bridge`: the first factor is
re-spelled by `ha`, the third splits in two by `hc`, and the first, second and the first half of
the third are the composite's bridge by `hg`. Stated at an arbitrary category with the objects
implicit and the morphisms explicit, since the re-spellings cross two definitionally but not
syntactically equal spellings of one object. -/
private theorem bridge_assoc {E : Type*} [Category* E] {x y z u v : E}
    (a a' : x ⟶ y) (b : y ⟶ z) (cc : z ⟶ u) (d : u ⟶ v) (c' : z ⟶ v) (g : x ⟶ u)
    (ha : a' = a) (hc : c' = cc ≫ d) (hg : g = a ≫ b ≫ cc) :
    (a' ≫ b) ≫ c' = g ≫ d := by
  calc (a' ≫ b) ≫ c' = (a ≫ b) ≫ cc ≫ d := by rw [ha, hc]
    _ = (a ≫ b ≫ cc) ≫ d := by simp only [Category.assoc]
    _ = g ≫ d := by rw [hg]

/-- **`Stacks.Gysin.supportCohomologyOnIso` is the derived/classical bridge for the composite
degree-zero functor `H_T^{on T} ⋙ i_*`, componentwise.** At a module `ℱ`, the identification of
the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` with `Rⁿ H_T(ℱ)` is the generic bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` for `H_T^{on T} ⋙ i_*`,
taken at the right derived functor `R𝓗_T ⋙ D(i_*)` with unit
`Stacks.DerivedFunctor.postcomposeUnit`, followed by the degree-`n` right derived functor of the
degree-zero identification
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of
`Stacks.SheafOfModules.SupportedSections`.

So the two steps `supportCohomologyOnIso` is composed of — moving `i_*` past the cohomology
sheaf, and crossing from the derived to the classical spelling on `T` — amount to one crossing
for the composite functor, with the degree-zero comparison `κ` folded in by
`CategoryTheory.NatTrans.rightDerived`. -/
theorem supportCohomologyOnIso_hom_app_eq_bridge (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)
    (n : ℕ) (F : X.Modules) :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace T
    letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
    letI := Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
      (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
      (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
      (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
      Stacks.Cohomology.Localization.enoughKInjectives
    (supportCohomologyOnIso X T hT n).hom.app F =
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (supportedSectionsOnClosedFunctor X.toRingedSpace T hT ⋙
            modulePushforward (closedSubsetInclusion X.toRingedSpace T))
          (derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
            (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)
          (Stacks.DerivedFunctor.postcomposeUnit
            (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
            (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
            (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT))
          Stacks.Cohomology.Localization.enoughKInjectives n).hom.app F ≫
        (NatTrans.rightDerived
            (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X.toRingedSpace T hT).hom
            n).app F := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace T
  let := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  let := Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
    (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
    (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
    (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
    (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
    Stacks.Cohomology.Localization.enoughKInjectives
  have ha := iso_hom_app_congr (exactFunctorDerivedHomologyIso_eq
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)) (n : ℤ))
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))
  have hc := Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app
    (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
    (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
    (supportedSectionsFunctor X.toRingedSpace T)
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X.toRingedSpace T hT) n F
  have hg := Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app
    (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
    (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
    (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
    (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
    Stacks.Cohomology.Localization.enoughKInjectives n F
  exact bridge_assoc _ _ _ _ _ _ _ ha hc hg

/-- **`Stacks.Gysin.supportCohomologyOnIso` is the derived/classical bridge for
`H_T^{on T} ⋙ i_*`**, as an equality of natural transformations: the componentwise statement
`supportCohomologyOnIso_hom_app_eq_bridge` read through `CategoryTheory.NatTrans.ext`. -/
theorem supportCohomologyOnIso_hom_eq_bridge (X : Scheme.{u}) (T : Set X) (hT : IsClosed T)
    (n : ℕ) :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace T
    letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
    letI := Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
      (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
      (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
      (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
      Stacks.Cohomology.Localization.enoughKInjectives
    (supportCohomologyOnIso X T hT n).hom =
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (supportedSectionsOnClosedFunctor X.toRingedSpace T hT ⋙
            modulePushforward (closedSubsetInclusion X.toRingedSpace T))
          (derivedSupportedSectionsOnClosed X.toRingedSpace T hT ⋙
            (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)
          (Stacks.DerivedFunctor.postcomposeUnit
            (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
            (modulePushforward (closedSubsetInclusion X.toRingedSpace T))
            (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT))
          Stacks.Cohomology.Localization.enoughKInjectives n).hom ≫
        NatTrans.rightDerived
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X.toRingedSpace T hT).hom
          n :=
  NatTrans.ext (funext fun F => supportCohomologyOnIso_hom_app_eq_bridge X T hT n F)

end Stacks.Gysin

end
