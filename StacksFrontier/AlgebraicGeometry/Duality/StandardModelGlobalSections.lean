module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardStructureSheaf
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# `RΓ(X, 𝒪_X)` and the vanishing of `Hom(κ[-1], RΓ(X, 𝒪_X))` at the standard derived category

`HasDerivedCategory.{w} C` is a *chosen* localization of the cochain complexes of `C` at the
quasi-isomorphisms, with morphisms in `Type w`, and two choices give two categories whose
morphism types are different. For `C = ModuleCat.{u} A` and `C = X.Modules` the library runs two
choices side by side: `HasDerivedCategory.standard`, with morphisms in `Type (u + 1)`, and the
locally small model of [Stacks, Tag 079Q], with morphisms in `Type u`.

`AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero` of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardStructureSheaf`
is [Stacks, Tag 0AXC] — in the situation of [Stacks, Tag 0AX8] with `X` normal,
`Hom_{D(A)}(κ[-1], RΓ(X, 𝒪_X)) = 0` — stated at the **locally small** model. This file states
and proves the same vanishing at the **standard** model, which is the model at which the duality
statements that consume it, among them [Stacks, Tags 0A7M, 0AA3, 0GEW], are written.

The transport is uniqueness of right derived functors. `AlgebraicGeometry.globalSectionsOver`
mentions no derived category at all, and `AlgebraicGeometry.derivedGlobalSectionsOver` is its
total right derived functor at free `HasDerivedCategory` binders, so the two readings of
`RΓ(X, -)` are two right derived functors of one functor along two equivalent localizations and
hence agree up to the comparison equivalences; this is
`derivedGlobalSectionsOverModelComparisonIso`. The comparison equivalence commutes with the
shift and identifies the two localizations of cochain complexes, so it also matches `κ[-1]` on
one side with `κ[-1]` on the other, and the vanishing is carried across by full faithfulness.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsOverModelComparisonIso` — `A`-linear derived global
  sections `RΓ(X, -)` of a scheme over `A` at the standard models of `D(𝒪_X)` and `D(A)` and at
  arbitrary models, compared through `StacksDraft.DerivedModel.modelEquiv`.
* `AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheaf` — `RΓ(X, 𝒪_X)` as an object of
  the standard `D(A)`.
* `AlgebraicGeometry.VanishingSituation.standardResidueFieldShift` — `κ[-1]` as an object of the
  standard `D(A)`.

## Main results

* `AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheafModelIso` and
  `AlgebraicGeometry.VanishingSituation.standardResidueFieldShiftModelIso` — the comparison
  equivalence carries the standard `RΓ(X, 𝒪_X)` and `κ[-1]` to the locally small ones.
* `AlgebraicGeometry.VanishingSituation.hom_standardResidueFieldShift_eq_zero` —
  [Stacks, Tag 0AXC] at the standard model: every morphism `κ[-1] ⟶ RΓ(X, 𝒪_X)` in the standard
  `D(A)` is zero.

## Implementation notes

The two parts below treat the `HasDerivedCategory` arguments differently, and deliberately.

`derivedGlobalSectionsOverModelComparisonIso` is stated with free binders for the models being
compared against the standard ones, and every standard instance is written out; this is the
discipline of `StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport`, and it is
what keeps the statement generic. `Stacks.Duality.derivedGlobalSectionsOverModelIso` of
`StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.TracePairing` is the same comparison for
a scheme proper over a field; properness and the base being a field are incidental to it, and
the statement here is the one for a scheme over a commutative ring.

The remaining declarations erase the global locally small instances
`ModuleCat.hasDerivedCategory`, `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and install
`HasDerivedCategory.standard` as a file-local instance, so that `DerivedCategory` means the
standard model throughout; a default-priority local instance alone does not outrank a global
one. The erased instances are still named explicitly, which is how the locally small readings of
[Stacks, Tag 0AXC] are referred to.

The objects of the two models are equal by definitional unfolding —
`StacksDraft.DerivedModel.derivedCategory_eq_standard`, the locally small model being the
standard one with its morphisms shrunk — so the content of the statements below is entirely in
the morphisms: a morphism of the standard `D(A)` lives in `Type (u + 1)` and a morphism of the
locally small one in `Type u`, and neither vanishing statement applies to the other's morphisms.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.DerivedModel

universe w₁ w₂ u

namespace AlgebraicGeometry

/-! ### Derived global sections at two models -/

section Comparison

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [h₁ : HasDerivedCategory.{w₁} X.Modules] [h₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- **`A`-linear derived global sections read at two models.** For a scheme `X` over a
commutative ring `A`, `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` taken at the standard models of `D(𝒪_X)` and
`D(A)` and taken at arbitrary models `h₁`, `h₂` agree up to the comparison equivalences
`StacksDraft.DerivedModel.modelEquiv` on source and target.

Both are total right derived functors of `AlgebraicGeometry.globalSectionsOver`, which mentions
no derived category, along two localizations of the homotopy category of complexes of
`𝒪_X`-modules that the comparison equivalence identifies; so this is uniqueness of right derived
functors, `StacksDraft.DerivedModel.rightDerivedModelIso`. -/
def derivedGlobalSectionsOverModelComparisonIso :
    @derivedGlobalSectionsOver A _ X f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) ⋙
        (modelEquiv (HasDerivedCategory.standard (ModuleCat.{u} A)) h₂).functor ≅
      (modelEquiv (HasDerivedCategory.standard X.Modules) h₁).functor ⋙
        derivedGlobalSectionsOver f :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (@derivedGlobalSectionsOverUnit A _ X f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (derivedGlobalSectionsOverUnit f)
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic X.Modules).trW)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Localization.compUniqFunctor _ _
        (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} A)).trW))

end Comparison

/-! ### `RΓ(X, 𝒪_X)` and `κ[-1]` at the standard model -/

attribute [-instance] ModuleCat.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard Scheme.commRingRingCatSheafObj

/-- The comparison equivalence from the standard derived category of `A`-modules to the locally
small one of [Stacks, Tag 079Q]. -/
abbrev moduleCatDerivedModelEquiv (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ≌
      @DerivedCategory (ModuleCat.{u} A) _ _ ModuleCat.hasDerivedCategory :=
  modelEquiv (HasDerivedCategory.standard _) ModuleCat.hasDerivedCategory

/-- The comparison equivalence from the standard derived category of `𝒪_X`-modules to the
locally small one of [Stacks, Tag 079Q]. -/
abbrev schemeModulesDerivedModelEquiv (X : Scheme.{u}) :
    DerivedCategory X.Modules ≌
      @DerivedCategory X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) :=
  modelEquiv (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory X)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`RΓ(X, 𝒪_X)` as an object of the standard `D(A)`.** The unbounded derived functor of
`A`-linear global sections, at the standard models of `D(𝒪_X)` and `D(A)`, applied to the
structure sheaf placed in cohomological degree zero.

This is `AlgebraicGeometry.derivedGlobalSectionsStructureSheaf` read at the standard model: the
same object, but of a category whose morphisms are in `Type (u + 1)`. -/
def standardDerivedGlobalSectionsStructureSheaf :
    @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _) :=
  (derivedGlobalSectionsOver f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- **The structure sheaf in degree zero at the two models.** The comparison equivalence of
`D(𝒪_X)` carries `𝒪_X[0]` in the standard model to `𝒪_X[0]` in the locally small one, because it
identifies the two localizations of cochain complexes. -/
def derivedUnitObjectModelIso (X : Scheme.{u}) :
    (schemeModulesDerivedModelEquiv X).functor.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
        (SheafOfModules.unit X.ringCatSheaf) :=
  (modelCompQIso (HasDerivedCategory.standard X.Modules)
    (Scheme.Modules.hasDerivedCategory X)).app
      ((CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- **`RΓ(X, 𝒪_X)` at the two models.** The comparison equivalence of `D(A)` carries the standard
`RΓ(X, 𝒪_X)` to the locally small one: the comparison of the two derived global sections
functors at `𝒪_X[0]`, followed by the locally small `RΓ(X, -)` applied to
`derivedUnitObjectModelIso`. -/
def standardDerivedGlobalSectionsStructureSheafModelIso :
    (moduleCatDerivedModelEquiv A).functor.obj
        (standardDerivedGlobalSectionsStructureSheaf f) ≅
      derivedGlobalSectionsStructureSheaf f :=
  (derivedGlobalSectionsOverModelComparisonIso (h₁ := Scheme.Modules.hasDerivedCategory X)
        (h₂ := ModuleCat.hasDerivedCategory) f).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    (@derivedGlobalSectionsOver A _ X f (Scheme.Modules.hasDerivedCategory X)
      ModuleCat.hasDerivedCategory).mapIso (derivedUnitObjectModelIso X)

namespace VanishingSituation

/-- **`κ[-1]` as an object of the standard `D(A)`**, the residue field in cohomological degree
zero shifted by `-1`. The Stacks convention `K[n]ⁱ = K^{n+i}` places it in degree `1`.

This is `AlgebraicGeometry.VanishingSituation.residueFieldShift` read at the standard model. -/
abbrev standardResidueFieldShift (V : VanishingSituation.{u}) :
    DerivedCategory (ModuleCat.{u} V.A) :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)⟦(-1 : ℤ)⟧

/-- **`κ[-1]` at the two models.** The comparison equivalence of `D(A)` carries the standard
`κ[-1]` to the locally small one: it commutes with the shift
(`StacksDraft.Perfect.derivedEquivalenceCommShift`) and identifies the two localizations of
cochain complexes, hence the two readings of `κ` in degree zero. -/
def standardResidueFieldShiftModelIso (V : VanishingSituation.{u}) :
    (moduleCatDerivedModelEquiv V.A).functor.obj V.standardResidueFieldShift ≅
      V.residueFieldShift :=
  letI := StacksDraft.Perfect.derivedEquivalenceCommShift
    (HasDerivedCategory.standard (ModuleCat.{u} V.A)) ModuleCat.hasDerivedCategory
  ((moduleCatDerivedModelEquiv V.A).functor.commShiftIso (-1 : ℤ)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule) ≪≫
    (shiftFunctor (@DerivedCategory (ModuleCat.{u} V.A) _ _ ModuleCat.hasDerivedCategory)
      (-1 : ℤ)).mapIso
      ((modelCompQIso (HasDerivedCategory.standard (ModuleCat.{u} V.A))
        ModuleCat.hasDerivedCategory).app
        ((CochainComplex.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule))

/-- **[Stacks, Tag 0AXC] at the standard derived category.** In Situation [Stacks, Tag 0AX8] with
`X` normal, every morphism `κ[-1] ⟶ RΓ(X, 𝒪_X)` in the **standard** `D(A)` is zero; that is, the
group `Hom_{D(A)}(κ[-1], Rf_*𝒪_X)`, whose elements are in `Type (u + 1)`, vanishes. The
pushforward is read as the derived global sections `RΓ(X, 𝒪_X)`, as it is at the locally small
model.

`AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero` is
the same vanishing at the locally small model of [Stacks, Tag 079Q], where the group is in
`Type u`; the two statements are about different groups, and neither follows from the other by
unfolding. The comparison equivalence of the two models is fully faithful and, by
`standardResidueFieldShiftModelIso` and `standardDerivedGlobalSectionsStructureSheafModelIso`,
carries the standard `κ[-1]` and `RΓ(X, 𝒪_X)` to the locally small ones; so it identifies the
two groups, and the vanishing of the second gives the vanishing of the first.

The source also assumes `A` Nagata; that is not needed, for the reason recorded at the locally
small statement. -/
theorem hom_standardResidueFieldShift_eq_zero (V : VanishingSituation.{u}) [IsNormal V.X]
    (α : V.standardResidueFieldShift ⟶
      standardDerivedGlobalSectionsStructureSheaf V.f) : α = 0 := by
  let _ : (moduleCatDerivedModelEquiv V.A).functor.Additive :=
    modelEquiv_functor_additive _ _
  set Φ := (moduleCatDerivedModelEquiv V.A).functor
  set d := V.standardResidueFieldShiftModelIso
  set e := standardDerivedGlobalSectionsStructureSheafModelIso V.f
  have hzero : d.inv ≫ Φ.map α ≫ e.hom = 0 :=
    V.hom_residueFieldShift_derivedGlobalSections_eq_zero _
  exact Φ.map_injective (by simpa using d.hom ≫= hzero =≫ e.inv)

end VanishingSituation

end AlgebraicGeometry

end
