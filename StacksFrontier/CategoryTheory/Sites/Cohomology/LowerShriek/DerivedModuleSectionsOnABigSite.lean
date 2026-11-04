module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite

/-!
# Derived sections of sheaves of modules along a functor of sites that are not small

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O` be a sheaf of rings on
`(D, K)`, let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi and let
`O_C = g⁻¹O`. **Stacks 0DD8 (2)** says that for an object `U` of `C` the derived sections over
`U` of a restriction are the derived sections over `u(U)`:

`RΓ(U, g^*M) = RΓ(u(U), M)` for `M` in the unbounded derived category of `O`-modules.

That statement is already in this library as
`Stacks.Cohomology.DerivedLowerShriek.derivedModuleSectionsRestrictionIso`, but only for *small*
sites with the module sections in the one universe `u` of their objects and morphisms. This file
restates the same chain at

`C, D : Type u₁` with `Category.{v}` and sheaves of modules in `AddCommGrpCat.{max u₁ v w}`,

which specialises to a small site at `u₁ = v = w`. It is the module companion of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedSectionsOnABigSite.lean`, which
restates part (1) of the same tag, and it is written against it: the sections functor on modules
is the forgetful functor followed by that file's `abelianSections`, so no second notion of
sections over an object is introduced.

## What the universe constraint is, and why it is this one

As for part (1), the proof runs through corepresentability of sections over `U` by the extension
by zero `j_{U!}O_U` of the unit sheaf of modules on the localization (Stacks 0G1V), and
corepresentability is expressed with `CategoryTheory.preadditiveCoyoneda`, whose coefficient
universe is *the morphism universe of the ambient category*. A morphism of
`SheafOfModules.{t} R` is a family of linear maps indexed by `Cᵒᵖ`, so that morphism universe is
`max u₁ t`, and the corepresentation statement typechecks exactly when `u₁ ≤ t`. Writing the
module universe as `max u₁ v w` is one way to get that.

Unlike part (1), the module statement also pins the *ring* universe to the module universe. The
corepresenting object is built from `SheafOfModules.unit`, whose underlying modules are
`ModuleCat.of _ (R.obj X)` — the sections of the sheaf of rings themselves — so the sheaf of
rings has to live in the universe of the module sections. Both universes are therefore
`max u₁ v w` below. This is not a convenience: there is no corepresenting object for sections of
`SheafOfModules.{t} O` when `O` is a sheaf of rings in a strictly smaller universe, so the
argument of the source is unavailable there however small the sites are.

Nothing in the chain needs `C` or `D` to be small, and nothing needs `Small.{t} C`: Grothendieck
abelianness of the two categories of sheaves of modules, which Mathlib's instance supplies only
for a small site, is carried here as an instance argument, as is the existence of the
lower-shriek functor on sheaves of modules.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleSections` and
  `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleSections`: sections over an object of
  a sheaf of modules, as an abelian group, and their unbounded right derived functor `RΓ(U, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleSectionsCorepresentation`: **Stacks 0G1V**
  as an isomorphism of additive functors, `Hom(j_{U!}O_U, -) ≅ Γ(U, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.DerivedLowerShriekComputesGenerator`: the
  invertibility of the derived lower-shriek counit at the single complex of `j_{U!}O_U`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleSectionsRestrictionIso`:
  **Stacks 0DD8**, part (2), at these universes.

## Implementation notes

Every general lemma the original chain uses — the corepresentability criterion for a
right-derived unit, the transport of bijectivity along an adjunction, the recognition of a right
derived functor on K-injective complexes, and the whole of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean` — is already
universe-polymorphic in the sites, so this file only restates the declarations that were pinned
to a small site and reuses those unchanged. The two sites are kept in one object universe `u₁`
and one morphism universe `v` because the sheaf of modules categories have to have the same
coefficient universe on both sides.

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

/-! ### Sections of a sheaf of modules over an object of a site that is not small -/

section Sections

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{max u₁ v w})

/-- Sections of a sheaf of modules over an object of a site, as an abelian group, at a module
universe containing the object universe, the morphism universe and an arbitrary further
universe. -/
abbrev moduleSections (U : C) :
    SheafOfModules.{max u₁ v w} R ⥤ AddCommGrpCat.{max u₁ v w} :=
  SheafOfModules.toSheaf R ⋙ abelianSections.{w} J U

/-- The functor of sections of a sheaf of modules over an object is additive. -/
instance additive_moduleSections (U : C) : (moduleSections.{w} J R U).Additive where
  map_add := rfl

attribute [local instance] HasDerivedCategory.standard

/-- Sections over an object have an unbounded right derived functor when the category of sheaves
of modules is Grothendieck abelian. -/
instance hasRightDerivedFunctor_moduleSections (U : C)
    [HasSheafify J AddCommGrpCat.{max u₁ v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v w}]
    [IsGrothendieckAbelian.{max u₁ v w} (SheafOfModules.{max u₁ v w} R)] :
    ((moduleSections.{w} J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{max u₁ v w} R) (ComplexShape.up ℤ)) :=
  alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- `RΓ(U, -)` on sheaves of modules: the unbounded right derived functor of sections over `U`.
-/
abbrev derivedModuleSections (U : C)
    [HasSheafify J AddCommGrpCat.{max u₁ v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v w}]
    [IsGrothendieckAbelian.{max u₁ v w} (SheafOfModules.{max u₁ v w} R)] :
    DerivedCategory (SheafOfModules.{max u₁ v w} R) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w} :=
  ((moduleSections.{w} J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{max u₁ v w} R) (ComplexShape.up ℤ))

/-- **Stacks 0G1V as an isomorphism of additive functors, on a site that is not small.**
Sections over `U` of a sheaf of modules are the morphisms out of the extension by zero
`j_{U!}O_U` of the unit sheaf of modules on the localization of the site at `U`.

The module universe is forced to contain the object universe `u₁`: the left-hand side is built
with `CategoryTheory.preadditiveCoyoneda`, whose values live in the morphism universe of the
ambient category, which for sheaves of modules on `(C, J)` is `max u₁` the module universe. -/
def moduleSectionsCorepresentation (U : C)
    [HasWeakSheafify J AddCommGrpCat.{max u₁ v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v w}]
    [∀ V : C, (SheafOfModules.pushforward.{max u₁ v w} (F := Over.forget V)
      (𝟙 (R.over V) : (R.over V) ⟶ (R.over V))).IsRightAdjoint] :
    preadditiveCoyoneda.obj (op (extensionByZeroUnit R U)) ≅ moduleSections.{w} J R U := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact (show (_ ≃+ (F.val.obj (op U) : Type (max u₁ v w))) from
      { Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F with
        map_add' := by
          intro a b
          change Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F (a + b) =
            Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F a +
              Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F b
          rfl }).toAddCommGrpIso
  · intro F G g
    ext φ
    exact Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality J R U φ g

end Sections

/-! ### Stacks 0DD8, part (2), on sites that are not small -/

section Modules

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
  (O : Sheaf K RingCat.{max u₁ v w}) (U : C)
  [HasSheafify J AddCommGrpCat.{max u₁ v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v w}]
  [HasSheafify K AddCommGrpCat.{max u₁ v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v w}]
  [(SheafOfModules.pushforward.{max u₁ v w} (F := f) (idRingMap J K f O)).IsRightAdjoint]

attribute [local instance] HasDerivedCategory.standard

omit [f.IsCocontinuous J K] in
/-- **`Γ(U, g^*(-)) = Γ(u(U), -)`.** The underlying presheaf of a restriction is precomposition
with `uᵒᵖ`, so sections over `U` of a restricted sheaf of modules are sections over `u(U)`. -/
theorem restrictionModules_comp_moduleSections :
    restrictionModules J K f O ⋙
        moduleSections.{w} J (inverseImageRing J K f O) U =
      moduleSections.{w} K O (f.obj U) :=
  rfl

variable [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (sourceQuasiIso J K f O)]
  [IsGrothendieckAbelian.{max u₁ v w} (SheafOfModules.{max u₁ v w} O)]
  [(derivedLowerShriek J K f O ⋙ derivedRestriction J K f O).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedLowerShriek J K f O)
        (derivedRestriction J K f O)).inv ≫
      Functor.whiskerRight (derivedLowerShriekComparison J K f O)
        (derivedRestriction J K f O))
    (sourceQuasiIso J K f O)]
  [∀ V : C, (SheafOfModules.pushforward.{max u₁ v w} (F := Over.forget V)
    (𝟙 ((inverseImageRing J K f O).over V) :
      (inverseImageRing J K f O).over V ⟶ (inverseImageRing J K f O).over V)).IsRightAdjoint]

/-- The invertibility of the derived lower-shriek counit at the single complex of the extension
by zero `j_{U!}O_U`. This is the half of Stacks 0794 saying that the left derived functor is
computed on the `P`-cellular complexes, at a single complex whose term lies in `P`; it is the one
input of Stacks 07AC not available as a declaration in this library, the resolving class of the
construction being private to
`StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`. -/
abbrev DerivedLowerShriekComputesGenerator : Prop :=
  IsIso ((derivedLowerShriekComparison J K f O).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f O) U))))

variable
  [IsGrothendieckAbelian.{max u₁ v w}
    (SheafOfModules.{max u₁ v w} (inverseImageRing J K f O))]

/-- **The restriction of a K-injective complex of modules computes derived sections over an
object.** Sections over `U` are corepresented by `j_{U!}O_U` (Stacks 0G1V), and the derived
adjunction of Stacks 07AC turns morphisms out of that generator into morphisms out of its
derived lower shriek on the other site, where the complex is K-injective. -/
theorem moduleSections_restriction_rightDerivedUnit_isIso
    (hgen : DerivedLowerShriekComputesGenerator.{w} J K f O U)
    (I : CochainComplex (SheafOfModules.{max u₁ v w} O) ℤ) [I.IsKInjective]
    (RT : DerivedCategory (SheafOfModules.{max u₁ v w} (inverseImageRing J K f O)) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w})
    (α : (moduleSections.{w} J (inverseImageRing J K f O) U).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α (HomotopyCategory.quasiIso
      (SheafOfModules.{max u₁ v w} (inverseImageRing J K f O)) (ComplexShape.up ℤ))] :
    IsIso (α.app ((restrictionOnHomotopy J K f O).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hgen' := hgen
  refine rightDerivedUnit_isIso_of_corepresentable
    (moduleSections.{w} J (inverseImageRing J K f O) U)
    (extensionByZeroUnit (inverseImageRing J K f O) U)
    (moduleSectionsCorepresentation.{w} J (inverseImageRing J K f O) U) RT α
    (((restrictionModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (fun n => ?_)
  refine qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((restrictionModules J K f O).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app I)) ?_
  exact map_bijective_of_adjunction_comparison (homotopyAdjunction J K f O)
    DerivedCategory.Qh DerivedCategory.Qh (derivedLowerShriekAdjunction J K f O)
    (derivedLowerShriekComparison J K f O) (derivedRestrictionComparison J K f O)
    (derivedLowerShriekAdjunction_unit_fac J K f O) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))

/-- The unit exhibiting derived restriction followed by derived sections over `U` as a candidate
right derived functor of sections over `u(U)`. -/
def restrictedModuleSectionsUnit :
    (moduleSections.{w} K O (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedRestriction J K f O ⋙
        derivedModuleSections.{w} J (inverseImageRing J K f O) U) :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
    (eqToIso (restrictionModules_comp_moduleSections.{w} J K f O U))
    (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (restrictionOnHomotopy J K f O)
    (((moduleSections.{w} J (inverseImageRing J K f O) U).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{max u₁ v w} (inverseImageRing J K f O)) (ComplexShape.up ℤ))) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (derivedRestrictionComparison J K f O)
    (derivedModuleSections.{w} J (inverseImageRing J K f O) U) ≫
  (Functor.associator _ _ _).hom

/-- **Stacks 0DD8, part (2), on sites that need not be small.** Let `u : C ⥤ D` be a continuous
and cocontinuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of
topoi, let `O_D` be a sheaf of rings on `D` and let `O_C = g⁻¹O_D`. For every object `U` of `C`
and every `M` in the unbounded derived category of `O_D`-modules,
`RΓ(U, g^*M) = RΓ(u(U), M)`, naturally in `M`. -/
def derivedModuleSectionsRestrictionIso
    (hgen : DerivedLowerShriekComputesGenerator.{w} J K f O U) :
    derivedRestriction J K f O ⋙
        derivedModuleSections.{w} J (inverseImageRing J K f O) U ≅
      derivedModuleSections.{w} K O (f.obj U) := by
  have hβ : (derivedRestriction J K f O ⋙
      derivedModuleSections.{w} J (inverseImageRing J K f O) U).IsRightDerivedFunctor
        (restrictedModuleSectionsUnit.{w} J K f O U)
        (HomotopyCategory.quasiIso (SheafOfModules.{max u₁ v w} O) (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_kInjective _ _ _ (fun I hI => ?_)
    have := hI
    have := moduleSections_restriction_rightDerivedUnit_isIso.{w} J K f O U hgen I _
      (((moduleSections.{w} J (inverseImageRing J K f O) U).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{max u₁ v w} (inverseImageRing J K f O)) (ComplexShape.up ℤ)))
    dsimp only [restrictedModuleSectionsUnit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (restrictedModuleSectionsUnit.{w} J K f O U)
    (((moduleSections.{w} K O (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{max u₁ v w} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{max u₁ v w} O) (ComplexShape.up ℤ))

end Modules

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
