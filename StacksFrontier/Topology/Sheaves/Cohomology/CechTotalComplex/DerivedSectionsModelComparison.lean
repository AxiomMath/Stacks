module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
import StacksCore.Tactic.StacksAttribute

/-!
# The two models of `RΓ(X, -)` on bounded below complexes agree

Let `(X, 𝒪_X)` be a ringed space and `U` an open subset.  Derived sections over `U` of complexes
of `𝒪_X`-modules appear in this repository in two models:

* `Stacks.Cech.Linear.derivedSectionsFunctor`, the *bounded below* right derived functor
  `R⁺Γ(U, -)` of `SheafOfModules.evaluation 𝒪_X (op U)` built from injective resolutions, in which
  the comparison of Tag 08BN with the total Čech complex is stated; and
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`, the *unbounded* total right
  derived functor along K-injective resolutions, in which the Leray isomorphism of Tag 0D5W, the
  global cup product of Section 0FKU and the global Künneth maps of Tags 0G7V and 0G49 are stated.

The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedDerivedSections` record
that
"the two agree on bounded below complexes, but that comparison is not made here".  This file makes
it.  The argument is the one of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison`, which does the
same for the derived direct image: both composites are right derived functors of one and the same
functor `K⁺(𝒪_X) ⥤ D(Γ(U, 𝒪_X))`, namely termwise sections followed by localization, and the
isomorphism is the uniqueness of right derived functors.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsModels.boundedSectionsUnitPlus` and
  `Stacks.Cohomology.DerivedSectionsModels.boundedSectionsUnitBig` — the two comparison maps from
  termwise sections of a bounded below complex into `D(Γ(U, 𝒪_X))`, through `R⁺Γ(U, -)` and
  through the unbounded `RΓ(U, -)`.
* `Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso` — **`R⁺Γ(U, -)` followed by
  `D⁺(Γ(U,𝒪_X)) ⥤ D(Γ(U,𝒪_X))` is `D⁺(𝒪_X) ⥤ D(𝒪_X)` followed by `RΓ(U, -)`.**
* `Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso` — **the bridge**, in the
  form the 08BN comparison needs it: the Čech side's model of `RΓ(U, -)` on bounded below cochain
  complexes is the unbounded one precomposed with the inclusion and the localization.
* `Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections` — the bridge at
  `U = ⊤`, where the unbounded side is `Stacks.Cohomology.GlobalKunneth.baseSections`.

## Main results

* `Stacks.Cohomology.DerivedSectionsModels.isIso_derivedSectionsOverOpenUnit_app_of_isKInjective`
  — a K-injective complex computes the unbounded `RΓ(U, -)`: on it the canonical comparison
  `Γ(U, I) ⟶ RΓ(U, I)` is invertible.
* `Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso_fac` and
  `Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso_hom_app` — **the comparison
  that pins the isomorphism**: it carries the comparison map through `R⁺Γ` to the one through
  `RΓ`, which determines it.

## Implementation notes

The two coherences the statements rest on hold by `rfl`, exactly as in `BoundedComparison`:
`DerivedCategory.Plus.Qh` followed by `DerivedCategory.Plus.ι` is the inclusion
`K⁺ ⥤ K` followed by `DerivedCategory.Qh` (Mathlib's
`DerivedCategory.Plus.QhCompιIsoιCompQh` is `Iso.refl`), and the termwise sections functor on
`K⁺(𝒪_X)` followed by that inclusion is the inclusion followed by the termwise sections functor
on `K(𝒪_X)`.  The last step, from the bounded below homotopy category down to bounded below
*cochain complexes*, is the equally definitional fact that `DerivedCategory.Plus.Q` followed by
`DerivedCategory.Plus.ι` is `CochainComplex.Plus.ι` followed by `DerivedCategory.Q`: Mathlib
defines `DerivedCategory.Plus.Q` as the lift of exactly that composite through the full
subcategory.

That a bounded below complex of injectives is K-injective is
`CochainComplex.isKInjective_of_injective`, and that K-injective complexes compute the unbounded
derived functor is `isIso_derivedSectionsOverOpenUnit_app_of_isKInjective`, which is the second
half of the criterion of Tag 079P already used to build `derivedSectionsOverOpen` itself.

No `@[stacks]` attribute is placed: this is a comparison of two models of one functor, a step in
the proof of the statements that use both, and not the statement of a tag.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedSectionsModels

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **A K-injective complex computes the unbounded derived sections over `U`**: on it the
canonical comparison `Γ(U, I) ⟶ RΓ(U, I)` is invertible.  This is the second half of the
criterion of Tag 079P whose first half produced `derivedSectionsOverOpen` itself. -/
theorem isIso_derivedSectionsOverOpenUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedSectionsOverOpenUnit X U).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1}
      (homotopySectionsOverOpen X U) (exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedSectionsOverOpen X U) (derivedSectionsOverOpenUnit X U) I hI

/-! ### The two comparison maps out of termwise sections -/

/-- Termwise sections over `U` of a bounded below complex of `𝒪_X`-modules, read in
`D(Γ(U, 𝒪_X))`.  Both models of derived sections are right derived functors of this one. -/
abbrev boundedSectionsToDerivedCategory :
    HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) :=
  HomotopyCategory.Plus.ι _ ⋙ homotopySectionsOverOpen X U

/-- The comparison `Γ(U, K) ⟶ R⁺Γ(U, K)` from termwise sections of a bounded below complex to
the bounded below derived sections, read in `D(Γ(U, 𝒪_X))`. -/
def boundedSectionsUnitPlus :
    boundedSectionsToDerivedCategory X U ⟶
      DerivedCategory.Plus.Qh ⋙
        ((sectionsOverOpen X U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerRight (sectionsOverOpen X U).rightDerivedFunctorPlusUnith DerivedCategory.Plus.ι

/-- The comparison `Γ(U, K) ⟶ RΓ(U, K)` from termwise sections of a bounded below complex to the
unbounded derived sections. -/
def boundedSectionsUnitBig :
    boundedSectionsToDerivedCategory X U ⟶
      DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X U) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι _) (derivedSectionsOverOpenUnit X U)

/-- The component of `boundedSectionsUnitPlus` at `K` is the image under `DerivedCategory.Plus.ι`
of the component at `K` of the unit of `R⁺Γ(U, -)`. -/
@[simp]
theorem boundedSectionsUnitPlus_app
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    (boundedSectionsUnitPlus X U).app K =
      DerivedCategory.Plus.ι.map
        ((sectionsOverOpen X U).rightDerivedFunctorPlusUnith.app K) :=
  rfl

/-- The component of `boundedSectionsUnitBig` at `K` is the component of the unit of `RΓ(U, -)` at
the underlying unbounded complex of `K`. -/
@[simp]
theorem boundedSectionsUnitBig_app
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    (boundedSectionsUnitBig X U).app K =
      (derivedSectionsOverOpenUnit X U).app ((HomotopyCategory.Plus.ι _).obj K) :=
  rfl

/-- The comparison through `R⁺Γ(U, -)` is invertible on a bounded below complex of injective
modules: it is the image under the fully faithful `D⁺(Γ(U,𝒪_X)) ⥤ D(Γ(U,𝒪_X))` of the unit of
`R⁺Γ(U, -)`, which is invertible there. -/
instance isIso_boundedSectionsUnitPlus_app
    (Z : HomotopyCategory.Plus (InjectiveObject (SheafOfModules.{u} (structureSheafRing X)))) :
    IsIso ((boundedSectionsUnitPlus X U).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) := by
  rw [boundedSectionsUnitPlus_app]
  have h : IsIso ((sectionsOverOpen X U).rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι (SheafOfModules.{u} (structureSheafRing X))).mapHomotopyCategoryPlus.obj
        Z)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
        ((sectionsOverOpen X U).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
      (sectionsOverOpen X U).rightDerivedFunctorPlusUnith Z
  exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Plus.ι
    ((sectionsOverOpen X U).rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι (SheafOfModules.{u} (structureSheafRing X))).mapHomotopyCategoryPlus.obj
        Z)) h

/-- The comparison through the unbounded `RΓ(U, -)` is invertible on a bounded below complex of
injective modules: such a complex is K-injective, and K-injective complexes compute the unbounded
derived sections. -/
instance isIso_boundedSectionsUnitBig_app
    (Z : HomotopyCategory.Plus (InjectiveObject (SheafOfModules.{u} (structureSheafRing X)))) :
    IsIso ((boundedSectionsUnitBig X U).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) := by
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff
    ((InjectiveObject.ι (SheafOfModules.{u} (structureSheafRing X))).mapHomotopyCategoryPlus.obj
      Z).obj.as).1
    ((InjectiveObject.ι (SheafOfModules.{u} (structureSheafRing X))).mapHomotopyCategoryPlus.obj
      Z).2
  have := hn
  have hKI : CochainComplex.IsKInjective
      ((InjectiveObject.ι (SheafOfModules.{u} (structureSheafRing X))).mapHomotopyCategoryPlus.obj
        Z).obj.as :=
    CochainComplex.isKInjective_of_injective _ n
  rw [boundedSectionsUnitBig_app]
  exact isIso_derivedSectionsOverOpenUnit_app_of_isKInjective X U _ hKI

/-- `R⁺Γ(U, -) ⋙ DerivedCategory.Plus.ι`, with `boundedSectionsUnitPlus`, is a right derived
functor of `boundedSectionsToDerivedCategory` with respect to quasi-isomorphisms. -/
instance isRightDerivedFunctor_boundedSectionsUnitPlus :
    ((sectionsOverOpen X U).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).IsRightDerivedFunctor (boundedSectionsUnitPlus X U)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedSectionsToDerivedCategory X U)).isRightDerivedFunctor_of_isIso
    (boundedSectionsUnitPlus X U) (fun _ => inferInstance)

/-- `DerivedCategory.Plus.ι ⋙ RΓ(U, -)`, with `boundedSectionsUnitBig`, is a right derived functor
of `boundedSectionsToDerivedCategory` with respect to quasi-isomorphisms. -/
instance isRightDerivedFunctor_boundedSectionsUnitBig :
    (DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X U).IsRightDerivedFunctor
      (boundedSectionsUnitBig X U)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedSectionsToDerivedCategory X U)).isRightDerivedFunctor_of_isIso
    (boundedSectionsUnitBig X U) (fun _ => inferInstance)

/-- **The bounded below derived sections are the restriction of the unbounded ones**: an
isomorphism `R⁺Γ(U, -) ⋙ ι ≅ ι ⋙ RΓ(U, -)` of functors `D⁺(𝒪_X) ⥤ D(Γ(U, 𝒪_X))`.  It is the
uniqueness isomorphism of the right derived functors of termwise sections on `K⁺(𝒪_X)`. -/
def boundedDerivedSectionsIso :
    (sectionsOverOpen X U).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X U :=
  Functor.rightDerivedUnique _ _ (boundedSectionsUnitPlus X U) (boundedSectionsUnitBig X U)
    (HomotopyCategory.Plus.quasiIso _)

/-- **The comparison that pins the isomorphism**: it carries the comparison map
`Γ(U, K) ⟶ R⁺Γ(U, K)` to the comparison map `Γ(U, K) ⟶ RΓ(U, K)`.  Together with the uniqueness
of transformations out of a right derived functor this determines it. -/
theorem boundedDerivedSectionsIso_fac :
    boundedSectionsUnitPlus X U ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (boundedDerivedSectionsIso X U).hom = boundedSectionsUnitBig X U := by
  simp [boundedDerivedSectionsIso]

/-- **The componentwise form of the pinning comparison.** -/
theorem boundedDerivedSectionsIso_hom_app
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    DerivedCategory.Plus.ι.map
          ((sectionsOverOpen X U).rightDerivedFunctorPlusUnith.app K) ≫
        (boundedDerivedSectionsIso X U).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (derivedSectionsOverOpenUnit X U).app ((HomotopyCategory.Plus.ι _).obj K) :=
  NatTrans.congr_app (boundedDerivedSectionsIso_fac X U) K

/-! ### The bridge in the form the 08BN comparison needs -/

/-- **The bridge between the two models of `RΓ(U, -)`.**  The functor
`Stacks.Cech.Linear.derivedSectionsFunctor`, in which the comparison of Tag 08BN with the total
Čech complex lands, is the unbounded derived sections of
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`, in which the global cup product
is stated, precomposed with the inclusion of bounded below complexes and the localization. -/
def derivedSectionsFunctorIso :
    Stacks.Cech.Linear.derivedSectionsFunctor X.carrier (structureSheafRing X) U ≅
      CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ derivedSectionsOverOpen X U :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.Q (boundedDerivedSectionsIso X U)

/-- **The bridge at `U = ⊤`**, where the unbounded model is
`Stacks.Cohomology.GlobalKunneth.baseSections`, the derived global sections the global cup product
of Section 0FKU and the global Künneth maps of Tags 0G7V and 0G49 are stated at. -/
def derivedSectionsFunctorIsoBaseSections (S : RingedSpace.{u, u}) :
    Stacks.Cech.Linear.derivedSectionsFunctor S.carrier (structureSheafRing S) ⊤ ≅
      CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S :=
  derivedSectionsFunctorIso S ⊤

end Stacks.Cohomology.DerivedSectionsModels

end
