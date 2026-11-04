module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

open Stacks.Injectives.KInjectiveResolution

/-!
# Derived sections of unbounded complexes of sheaves of modules

Specialisation of
  `hasPointwiseRightDerivedFunctor_mapHomologicalComplex_comp_Q`
to the functor of sections of a sheaf of modules over a ringed site: the degreewise sections
of an unbounded complex of modules, followed by the localization to the derived category of
abelian groups, have a right derived functor on the whole unbounded derived category.

## Main results

* `CategoryTheory.Sheaf.additive_sheafSections_obj`: evaluating a sheaf at an object of the
  site is an additive functor.  Mathlib has this for presheaves
  (`CategoryTheory.evaluation`) but not through `sheafSections`, and it is what makes the
  sections functor of a sheaf of modules additive.
* `SheafOfModules.hasPointwiseRightDerivedFunctor_sectionsComplex_comp_Q` and
  `SheafOfModules.hasRightDerivedFunctor_sectionsComplex_comp_Q`: the derived sections
  functor exists, unboundedly.
* `SheafOfModules.isRightDerivedFunctor_sectionsComplex_iff`: a candidate derived sections
  functor is the right derived functor precisely when its unit is invertible on K-injective
  complexes of modules.

## Implementation notes

Mathlib's `IsGrothendieckAbelian.{u} (SheafOfModules.{u} R)` is stated for a site `C` with
`[SmallCategory C]`, a ring sheaf valued in `RingCat.{u}` and modules in universe `u`: a
single universe throughout.  The statements below therefore run in that one universe.  A
consumer whose site, hom, ring and module universes are independent (even with `UnivLE`
between them) does not meet that hypothesis; the narrowing to a common universe is
load-bearing, not cosmetic.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [Preadditive A] [Limits.HasZeroMorphisms A]

/-- Evaluation of a sheaf at an object of the site is additive. -/
instance additive_sheafSections_obj (X : Cᵒᵖ) :
    ((sheafSections J A).obj X).Additive where
  map_add := rfl

end CategoryTheory.Sheaf

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sections over an object of the site, as a functor on sheaves of modules valued in
abelian groups.  This is the functor whose right derived functor is derived sections. -/
noncomputable abbrev sectionsToAddCommGrp : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op U)

/-- Degreewise sections of a complex of sheaves of modules. -/
noncomputable abbrev sectionsComplexToAddCommGrp :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (sectionsToAddCommGrp R U).mapHomologicalComplex (ComplexShape.up ℤ)

variable [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- **Derived sections of unbounded complexes of sheaves of modules exist.**  The
degreewise sections of a complex of sheaves of modules, followed by the localization to the
derived category of abelian groups, have a pointwise right derived functor with respect to
all quasi-isomorphisms of complexes of modules — not merely the bounded below ones. -/
theorem hasPointwiseRightDerivedFunctor_sectionsComplex_comp_Q :
    (sectionsComplexToAddCommGrp R U ⋙
          DerivedCategory.Q).HasPointwiseRightDerivedFunctor
      (HomologicalComplex.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) :=
  hasPointwiseRightDerivedFunctor_mapHomologicalComplex_comp_Q (sectionsToAddCommGrp R U)

/-- **Derived sections of unbounded complexes of sheaves of modules exist**, existence
form. -/
theorem hasRightDerivedFunctor_sectionsComplex_comp_Q :
    (sectionsComplexToAddCommGrp R U ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) :=
  Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (sectionsToAddCommGrp R U)

variable {D : Type*} [Category* D]
  (L : CochainComplex (SheafOfModules.{u} R) ℤ ⥤ D)
  [L.IsLocalization (HomologicalComplex.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ))]
  (RΓ : D ⥤ DerivedCategory AddCommGrpCat.{u})
  (α : sectionsComplexToAddCommGrp R U ⋙ DerivedCategory.Q ⟶ L ⋙ RΓ)

/-- **K-injective complexes of modules compute derived sections.**  A candidate derived
sections functor, with its unit, is the right derived functor of degreewise sections exactly
when the unit is invertible at every K-injective complex of sheaves of modules. -/
theorem isRightDerivedFunctor_sectionsComplex_iff :
    RΓ.IsRightDerivedFunctor α
        (HomologicalComplex.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) ↔
      ∀ (I : CochainComplex (SheafOfModules.{u} R) ℤ), I.IsKInjective → IsIso (α.app I) :=
  Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective L RΓ α
    (fun f hK hL hf =>
      Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.up ℤ)) _
        ((HomologicalComplex.mem_quasiIso_iff _).2
          (Stacks.Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
            (sectionsToAddCommGrp R U) f hK hL hf)))

end SheafOfModules
