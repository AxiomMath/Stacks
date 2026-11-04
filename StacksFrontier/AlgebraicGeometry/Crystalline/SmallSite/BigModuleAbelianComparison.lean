module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomologyComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 03FD] at the universes of the big crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` at level `u`. On the big crystalline site
`CRIS(X/S)`, deriving the global sections of a sheaf of `𝒪_{X/S}`-modules *after* forgetting it to
its underlying abelian sheaf is the same as forgetting after deriving, in every degree: this is
[Stacks, Tag 03FD] for `CRIS(X/S)`, whose objects lie in `Type (u + 1)`, its morphisms in
`Type u`, its structure sheaf in `RingCat.{u}` and its modules with sections in `Type (u + 1)`.

## Main definitions

All names are in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigToAbelianSheaf`: the underlying abelian sheaf of a sheaf of `𝒪_{X/S}`-modules on
  `CRIS(X/S)`, landing in `Sheaf (topology S) AddCommGrpCat.{u + 1}`.
* `bigAbelianCorepresentingSheaf`: the constant abelian sheaf on `ULift ℤ`, which corepresents
  `Γ(CRIS(X/S), -)`.
* `bigAbelianCorepresentingModule`: the sheaf of `𝒪_{X/S}`-modules `𝒪_{X/S} ⊗_ℤ ℤ` corepresenting
  the global sections of the underlying abelian sheaf.

## Main results

* `ext_eq_zero_of_injective_bigToAbelianSheaf`: the underlying abelian sheaf of an injective
  module has vanishing positive-degree `Ext` against `bigAbelianCorepresentingSheaf`.
* `bigAbelianComparisonIso`: **[Stacks, Tag 03FD] at the big crystalline site**, the comparison
  `(bigToAbelianSheaf S ⋙ Γ).rightDerived n ≅ bigToAbelianSheaf S ⋙ Γ.rightDerived n` in every
  degree, together with `toRightDerivedZero_comp_bigAbelianComparisonIso`, its degree-zero
  normalization.
* `isZero_bigRightDerived_bigToAbelianSheaf_succ`: the underlying abelian sheaf of an injective
  sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` is `Γ(CRIS(X/S), -)`-acyclic.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The ambient facts about abelian sheaves on the big crystalline site -/

/-- **Abelian sheaves on the big crystalline site have enough injectives** at the coefficient
universe `u + 1` of the objects of the site. -/
@[sga "4 I 7.13" "special case",
  sga "4 II 6.9" "Remark 6.9, special case",
  sga "4 V 0.2.1" "special case"]
instance instEnoughInjectivesBigAbelianSheaf :
    EnoughInjectives (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2} (topology S)
    AddCommGrpCat.{u + 1}

/-- **`Ext`-groups of abelian sheaves on the big crystalline site exist in `Type (u + 1)`.** -/
instance instHasExtBigAbelianSheaf :
    HasExt.{u + 1} (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- Global sections of abelian sheaves on the big crystalline site are additive. -/
instance instAdditiveBigGlobalSections : (bigGlobalSections S).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} (topology S)

/-! ### The corepresenting objects -/

/-- **The underlying abelian sheaf of a sheaf of `𝒪_{X/S}`-modules on the big crystalline site**,
valued in `AddCommGrpCat.{u + 1}`. -/
abbrev bigToAbelianSheaf :
    BigModuleSheaf S ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)

/-- The constant abelian presheaf on `ULift ℤ` on the big crystalline site. -/
abbrev bigConstantIntegerPresheaf : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const (Thickening S)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **The abelian sheaf corepresenting `Γ(CRIS(X/S), -)`**: the constant sheaf on `ULift ℤ`, at
the coefficient universe `u + 1`. -/
abbrev bigAbelianCorepresentingSheaf : Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  (constantSheaf (topology S) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **`Γ(CRIS(X/S), -)` is corepresented by the constant abelian sheaf on `ℤ`.** -/
def bigGlobalSectionsCorepresentation :
    bigGlobalSections S ≅ preadditiveCoyoneda.obj (op (bigAbelianCorepresentingSheaf S)) :=
  Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1, u, u + 1}
    (topology S)

/-- **The sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` corepresenting the global sections of the
underlying abelian sheaf**: the sheafification of the extension of scalars `𝒪_{X/S} ⊗_ℤ ℤ` of the
constant abelian presheaf on `ULift ℤ`. -/
abbrev bigAbelianCorepresentingModule : BigModuleSheaf S :=
  (PresheafOfModules.sheafification (𝟙 (crystallineStructureSheaf S).obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf.{u + 1, u, u + 1, u} (crystallineStructureSheaf S).obj
      (bigConstantIntegerPresheaf S))

/-- **The global sections of the underlying abelian sheaf of a module on `CRIS(X/S)` are
corepresented by `bigAbelianCorepresentingModule`.** -/
def bigModuleCorepresentation :
    preadditiveCoyoneda.obj (op (bigAbelianCorepresentingModule S)) ≅
      bigToAbelianSheaf S ⋙ preadditiveCoyoneda.obj (op (bigAbelianCorepresentingSheaf S)) :=
  Stacks.SheafOfModules.tensorSheafHomIso.{u + 1, u, u, u + 1} (topology S)
    (crystallineStructureSheaf S) (bigConstantIntegerPresheaf S)

/-! ### The acyclicity -/

/-- The constant abelian presheaf on `ULift ℤ` is sectionwise torsion free. -/
theorem isTorsionFree_bigConstantIntegerPresheaf (A : (Thickening S)ᵒᵖ) :
    Module.IsTorsionFree ℤ ((bigConstantIntegerPresheaf S).obj A) := by
  change Module.IsTorsionFree ℤ (ULift.{u + 1} ℤ)
  exact Module.Flat.isTorsionFree

/-- The underlying abelian sheaf of an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` has
vanishing positive-degree `Ext` against the constant sheaf on `ℤ`. -/
theorem ext_eq_zero_of_injective_bigToAbelianSheaf (M : BigModuleSheaf S) [Injective M] (n : ℕ)
    (e : Ext.{u + 1} (bigAbelianCorepresentingSheaf S) ((bigToAbelianSheaf S).obj M) (n + 1)) :
    e = 0 :=
  Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{u + 1, u + 1, u, u, u + 1}
    (topology S) (crystallineStructureSheaf S) M _
    (ModuleSheafCohomology.isTorsionFree_sheafify (topology S)
      (bigConstantIntegerPresheaf S) (isTorsionFree_bigConstantIntegerPresheaf S)) n e

/-! ### The comparison -/

/-- **[Stacks, Tag 03FD] at the big crystalline site**: deriving the composite of forgetting a
sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` to its underlying abelian sheaf with `Γ(CRIS(X/S), -)`
agrees, in every degree, with forgetting and then deriving `Γ(CRIS(X/S), -)`. -/
def bigAbelianComparisonIso (n : ℕ) :
    (bigToAbelianSheaf S ⋙ bigGlobalSections S).rightDerived n ≅
      bigToAbelianSheaf S ⋙ (bigGlobalSections S).rightDerived n :=
  ModuleSheafCohomology.comparisonIso (bigToAbelianSheaf S) (bigGlobalSections S)
    (bigAbelianCorepresentingSheaf S) (bigGlobalSectionsCorepresentation S)
    (bigAbelianCorepresentingModule S) (bigModuleCorepresentation S)
    (fun M _ n e => ext_eq_zero_of_injective_bigToAbelianSheaf S M n e) n

/-- **The degree-zero normalization of the comparison**: it intertwines the two canonical maps
to the zeroth right-derived functors. -/
theorem toRightDerivedZero_comp_bigAbelianComparisonIso :
    (bigToAbelianSheaf S ⋙ bigGlobalSections S).toRightDerivedZero ≫
        (bigAbelianComparisonIso S 0).hom =
      Functor.whiskerLeft (bigToAbelianSheaf S) (bigGlobalSections S).toRightDerivedZero :=
  ModuleSheafCohomology.toRightDerivedZero_comp_comparisonIso _ _ _ _ _ _ _

/-- **The underlying abelian sheaf of an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` is
`Γ(CRIS(X/S), -)`-acyclic:** its higher abelian-valued right derived global sections vanish. -/
theorem isZero_bigRightDerived_bigToAbelianSheaf_succ (I : BigModuleSheaf S) [Injective I]
    (n : ℕ) :
    IsZero (((bigGlobalSections S).rightDerived (n + 1)).obj ((bigToAbelianSheaf S).obj I)) :=
  IsZero.of_iso
    (Functor.isZero_rightDerived_obj_injective_succ
      (bigToAbelianSheaf S ⋙ bigGlobalSections S) n I)
    ((bigAbelianComparisonIso S (n + 1)).app I).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end
