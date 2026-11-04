module

public import Mathlib.CategoryTheory.Limits.Filtered
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FinitelyPresented
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Presentable
public import StacksFrontier.CategoryTheory.KanExtension.Extend
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending functors from finitely presented modules

Let `A` be a ring and let `B` be a category with filtered colimits. A functor from finitely
presented `A`-modules to `B` extends to all `A`-modules while preserving filtered colimits.
This extension is unique up to a unique natural isomorphism compatible with its given
identification on finitely presented modules.

## Main definitions

* `ModuleCat.FilteredColimitExtension` packages an extension together with its two required
  properties.

## Main results

* `ModuleCat.filteredColimitExtension` gives the extension.
* `ModuleCat.FilteredColimitExtension.existsUnique_iso` gives its canonical uniqueness.

## Implementation notes

An extension packages the extended functor, preservation of filtered colimits of the size of
the module category, and its identification on the full subcategory of finitely presented
modules. The target object and morphism universes are independent of the module universe.
Uniqueness means uniqueness of the natural isomorphism between two such extensions after
fixing those identifications.

## References

* [Stacks Project, Tag 0GNJ](https://stacks.math.columbia.edu/tag/0GNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace ModuleCat

variable (A : Type u) [Ring A] {B : Type w} [Category.{x} B]

/-- A filtered-colimit-preserving extension of a functor on finitely presented modules. -/
public structure FilteredColimitExtension
    (F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B) where
  /-- The functor on all modules. -/
  functor : CategoryTheory.Functor (ModuleCat.{max u v} A) B
  /-- The extended functor preserves filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimitsOfSize.{max u v, max u v} functor
  /-- The restriction of the extended functor is the original functor. -/
  iso : CategoryTheory.Iso ((finitelyPresentedModule.{u, max u v} A).ι.comp functor) F

/-- The functor underlying an extension preserves filtered colimits. -/
public instance {F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B}
    (E : FilteredColimitExtension A F) :
    PreservesFilteredColimitsOfSize.{max u v, max u v} E.functor :=
  E.preservesFilteredColimits

/-- A functor on finitely presented modules has an extension to all modules which preserves
filtered colimits. -/
@[stacks 0GNJ "existence",
  stacks 0GP4 "existence, at the target category of all B-modules",
  sga "4 I 8.7.3" "existence, C=Mod^fp_A"]
public noncomputable def filteredColimitExtension
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B) :
    FilteredColimitExtension A F := by
  letI : EssentiallySmall.{max u v} (FinitelyPresentedModuleCat.{u, max u v} A) :=
    essentiallySmall_finitelyPresentedModuleCat A
  let h := ObjectProperty.exists_extension_of_preservesFilteredColimits
      (finitelyPresentedModule.{u, max u v} A)
      (fun M hM => finitePresentation_isFinitelyPresentable A M hM)
      (ind_finitelyPresentedModule A) F
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    Classical.choice (Classical.choose_spec h).2⟩

/-- Two filtered-colimit-preserving extensions are related by a unique natural isomorphism
compatible with their specified identifications on finitely presented modules. -/
@[stacks 0GNJ "uniqueness",
  stacks 0GP4 "existence, at the target category of all B-modules",
  sga "4 I 8.7.3" "uniqueness, C=Mod^fp_A", sga "4 I 8.7.2" "special case"]
public theorem FilteredColimitExtension.existsUnique_iso
    {F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B}
    (E₁ E₂ : FilteredColimitExtension A F) :
    ∃! e : CategoryTheory.Iso E₁.functor E₂.functor,
      Functor.whiskerLeft (finitelyPresentedModule.{u, max u v} A).ι e.hom =
        (CategoryTheory.Iso.trans E₁.iso E₂.iso.symm).hom := by
  let : EssentiallySmall.{max u v} (FinitelyPresentedModuleCat.{u, max u v} A) :=
    essentiallySmall_finitelyPresentedModuleCat A
  exact ObjectProperty.existsUnique_iso_of_preservesFilteredColimits
    (finitelyPresentedModule.{u, max u v} A)
    (fun M hM => finitePresentation_isFinitelyPresentable A M hM)
    (ind_finitelyPresentedModule A) E₁.functor E₂.functor E₁.iso E₂.iso

end ModuleCat
