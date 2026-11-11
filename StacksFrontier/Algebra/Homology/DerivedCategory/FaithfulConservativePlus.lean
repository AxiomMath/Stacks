module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservative

/-!
# A faithful exact functor is conservative on bounded below derived categories

A faithful exact functor `F : C ⥤ D` between abelian categories reflects isomorphisms of the
bounded below derived categories: a morphism `f` of `D⁺(C)` is invertible as soon as
`F.mapDerivedCategoryPlus.map f` is.  In particular a morphism of `D⁺(Mod_A)` is an isomorphism
if and only if its image in `D⁺(Ab)` under the forgetful functor is.

## Main results

* `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategoryPlus_map_of_faithful` — the bounded below
  counterpart of `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_map_of_faithful`.
* `Stacks.Cohomology.isIso_mapDerivedCategoryPlus_map_iff_of_faithful` — the same, as an
  equivalence.
* `Stacks.Cohomology.isIso_forget₂_mapDerivedCategoryPlus_map_iff` — the case of the forgetful
  functor from modules over a ring to abelian groups.

## Implementation notes

`CategoryTheory.Functor.mapDerivedCategoryPlus` is the lift of `F.mapDerivedCategory` through the
fully faithful inclusion `DerivedCategory.Plus.ι`, so the statement reduces to the unbounded one
along that inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Cohomology

/-- The forgetful functor from modules to abelian groups preserves finite colimits, at any module
universe.  Mathlib's instances give this, but one of them is stated at the universe `max w w'` and
leaves instance search stuck on a universe constraint at `ModuleCat.{v} A` for `A : Type u`; this
one is tried first. -/
instance (priority := 1100) forget₂_moduleCat_preservesFiniteColimits {A : Type u} [Ring A] :
    PreservesFiniteColimits (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) :=
  ⟨fun J _ _ => ModuleCat.forget₂PreservesColimitsOfShape.{v} A J⟩

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [Category* D] [Abelian D]
  [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]

/-- **A faithful exact functor is conservative on bounded below derived categories**: a
morphism of `D⁺(C)` whose image in `D⁺(D)` is invertible is itself invertible. -/
theorem isIso_of_isIso_mapDerivedCategoryPlus_map_of_faithful {X Y : DerivedCategory.Plus C}
    (f : X ⟶ Y) (hf : IsIso (F.mapDerivedCategoryPlus.map f)) : IsIso f := by
  have : IsIso (F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f)) :=
    inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f)))
  have := isIso_of_isIso_mapDerivedCategory_map_of_faithful F _ this
  exact isIso_of_reflects_iso f DerivedCategory.Plus.ι

/-- **A morphism of `D⁺(C)` is invertible if and only if its image under a faithful exact functor
is.** -/
theorem isIso_mapDerivedCategoryPlus_map_iff_of_faithful {X Y : DerivedCategory.Plus C}
    (f : X ⟶ Y) : IsIso (F.mapDerivedCategoryPlus.map f) ↔ IsIso f :=
  ⟨isIso_of_isIso_mapDerivedCategoryPlus_map_of_faithful F f, fun _ => inferInstance⟩

/-- **A morphism of `D⁺(Mod_A)` is an isomorphism if and only if its image in `D⁺(Ab)` is**,
the image being taken along the exact and faithful forgetful functor. -/
theorem isIso_forget₂_mapDerivedCategoryPlus_map_iff {A : Type u} [Ring A]
    [HasDerivedCategory (ModuleCat.{v} A)] [HasDerivedCategory AddCommGrpCat.{v}]
    {X Y : DerivedCategory.Plus (ModuleCat.{v} A)} (f : X ⟶ Y) :
    IsIso ((forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).mapDerivedCategoryPlus.map f) ↔
      IsIso f :=
  isIso_mapDerivedCategoryPlus_map_iff_of_faithful _ f

end Stacks.Cohomology

end
