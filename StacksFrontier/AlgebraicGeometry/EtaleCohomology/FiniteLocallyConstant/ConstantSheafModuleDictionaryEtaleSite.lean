module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# The dictionary of Stacks 0DV5 (3) on a constant sheaf, on Mathlib's small étale site

`AlgebraicGeometry.rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf` and
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceConstantSheafEquiv` compute the
value of the dictionary of Stacks 0DV5 (3) on a constant sheaf of `Λ`-modules on the small étale
site of Stacks 021B: the action is trivial and the underlying set is that of the module. This file
proves the same on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`: the
action is trivial and the underlying set has the cardinality of the module. Over a finite field,
two finite modules with trivial action and the same number of elements are isomorphic.

## Main definitions

* `AlgebraicGeometry.constantSheafFiniteTypeLocallyConstantModuleEtaleSite`: the constant sheaf of
  `Λ`-modules on a finite module, as an object of the left-hand side of Stacks 0DV5 (3) on
  Mathlib's small étale site.

## Main results

* `Module.nonempty_linearEquiv_of_natCard_eq`: two finite vector spaces over a finite field with
  the same number of elements are isomorphic.
* `Stacks.GroupCohomology.nonempty_iso_of_rho_eq_one_of_natCard_eq`: two finite modules over a
  finite field with trivial continuous action and the same number of elements are isomorphic.
* `AlgebraicGeometry.isFiniteTypeLocallyConstant_constantSheafModule_etaleSite`: the constant
  sheaf of `Λ`-modules on a finite module is of finite type locally constant on Mathlib's small
  étale site.
* `AlgebraicGeometry.rho_eq_one_moduleSheafEquivalenceEtaleSite_constantSheaf` and
  `AlgebraicGeometry.natCard_moduleSheafEquivalenceEtaleSite_constantSheaf`: Stacks 0DV5 (3) on a
  constant sheaf of modules, on Mathlib's small étale site: the action is trivial and the
  underlying set has the cardinality of the module.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf Stacks.GroupCohomology

universe u v w r

attribute [local instance] ModuleCat.hasLimitsOfSize

/-! ### Finite vector spaces of equal cardinality -/

namespace Module

/-- Two finite vector spaces over a finite field with the same number of elements are
isomorphic. -/
theorem nonempty_linearEquiv_of_natCard_eq (k : Type r) [Field k] [Finite k]
    (V : Type v) [AddCommGroup V] [Module k V] [Finite V]
    (W : Type w) [AddCommGroup W] [Module k W] [Finite W] (h : Nat.card V = Nat.card W) :
    Nonempty (V ≃ₗ[k] W) := by
  have : Fintype k := Fintype.ofFinite k
  have : Fintype V := Fintype.ofFinite V
  have : Fintype W := Fintype.ofFinite W
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  have hV : Fintype.card V = Fintype.card k ^ finrank k V := Module.card_eq_pow_finrank
  have hW : Fintype.card W = Fintype.card k ^ finrank k W := Module.card_eq_pow_finrank
  have hcard : Fintype.card V = Fintype.card W := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h]
  have h2 : 2 ≤ Fintype.card k := Fintype.one_lt_card
  refine Nat.pow_right_injective h2 ?_
  show Fintype.card k ^ finrank k V = Fintype.card k ^ finrank k W
  rw [← hV, ← hW, hcard]

end Module

/-! ### Finite modules with a continuous action: transport along an isomorphism -/

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

variable (Λ : Type r) [Ring Λ] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying `Λ`-module isomorphism of an isomorphism of finite modules with a continuous
action. -/
def isoV {A B : FiniteTypeContinuousModule.{r, v, w} Λ G} (e : A ≅ B) :
    A.obj.obj.obj.V ≅ B.obj.obj.obj.V :=
  (finiteTypeContinuousModuleι.{r, v, w} Λ G ⋙
    Stacks.Injectives.continuousModuleUnderlying.{r, v, w} Λ G).mapIso e

/-- An isomorphic finite module with a continuous action has the same number of elements. -/
theorem natCard_eq_of_iso {A B : FiniteTypeContinuousModule.{r, v, w} Λ G} (e : A ≅ B) :
    Nat.card (ToType A.obj.obj.obj.V) = Nat.card (ToType B.obj.obj.obj.V) :=
  Nat.card_congr ((CategoryTheory.forget (ModuleCat.{w} Λ)).mapIso (isoV Λ G e)).toEquiv

/-- If the action on a finite module with a continuous action is trivial, then so is the action
on any isomorphic one. -/
theorem rho_eq_one_of_iso {A B : FiniteTypeContinuousModule.{r, v, w} Λ G} (e : A ≅ B)
    (h : ∀ σ : G, A.obj.obj.obj.ρ σ = 1) (σ : G) : B.obj.obj.obj.ρ σ = 1 := by
  have hcomm : A.obj.obj.obj.ρ σ ≫ (isoV Λ G e).hom =
      (isoV Λ G e).hom ≫ B.obj.obj.obj.ρ σ := e.hom.hom.hom.hom.comm σ
  have key : B.obj.obj.obj.ρ σ =
      (isoV Λ G e).inv ≫ A.obj.obj.obj.ρ σ ≫ (isoV Λ G e).hom := by
    rw [hcomm, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [key, h σ, show (1 : End A.obj.obj.obj.V) = 𝟙 A.obj.obj.obj.V from rfl, Category.id_comp,
    Iso.inv_hom_id]
  rfl

/-- Two finite modules over a finite field with trivial continuous action and the same number of
elements are isomorphic. -/
theorem nonempty_iso_of_rho_eq_one_of_natCard_eq (k : Type r) [Field k] [Finite k]
    (A B : FiniteTypeContinuousModule.{r, v, w} k G)
    (hA : ∀ σ : G, A.obj.obj.obj.ρ σ = 1) (hB : ∀ σ : G, B.obj.obj.obj.ρ σ = 1)
    (hcard : Nat.card (ToType A.obj.obj.obj.V) = Nat.card (ToType B.obj.obj.obj.V)) :
    Nonempty (A ≅ B) := by
  have : Finite (ToType A.obj.obj.obj.V) := (moduleCat_isFG_iff_finite k _).1 A.property
  have : Finite (ToType B.obj.obj.obj.V) := (moduleCat_isFG_iff_finite k _).1 B.property
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_natCard_eq k _ _ hcard
  refine ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso e.toModuleIso fun g ↦ ?_)))⟩
  rw [hA g, hB g]
  simp

end Stacks.GroupCohomology

/-! ### The constant sheaf of modules on Mathlib's small étale site -/

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.obj] (Λ : Type r) [Ring Λ]

/-- The restriction of the constant sheaf of Mathlib's small étale site to the small étale site
of Stacks 021B is the constant sheaf. -/
def sheafEquivInverseConstantSheafModuleIso (M : ModuleCat.{u + 1} Λ) :
    (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).inverse.obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
      (constantSheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)).obj M :=
  (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    (SmallEtale.topology B X.obj X.property) X.obj.smallEtaleTopology
    (SmallEtale.toEtaleSite B X.obj X.property) (ModuleCat.{u + 1} Λ)).app M

variable [Finite Λ]

omit [ConnectedSpace X.obj] in
/-- The constant sheaf of `Λ`-modules on a finite module is of finite type locally constant on
Mathlib's small étale site. -/
theorem isFiniteTypeLocallyConstant_constantSheafModule_etaleSite (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] :
    IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology
      ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  refine (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B X Λ _).1 ?_
  refine ObjectProperty.prop_of_iso
    (P := fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ↦
      IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.obj X.property) F)
    (sheafEquivInverseConstantSheafModuleIso B X Λ M).symm ?_
  exact (constantSheafFiniteTypeLocallyConstantModule B X Λ M).property

/-- The constant sheaf of `Λ`-modules on a finite module, as an object of the left-hand side of
Stacks 0DV5 (3) on Mathlib's small étale site. -/
def constantSheafFiniteTypeLocallyConstantModuleEtaleSite (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] :
    ObjectProperty.FullSubcategory
      (fun F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :=
  ⟨(constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M,
    isFiniteTypeLocallyConstant_constantSheafModule_etaleSite B X Λ M⟩

section Dictionary

variable (x : GeometricPoint X.obj)

/-- The two constant sheaves of `Λ`-modules, as objects of the two presentations of the left-hand
side of Stacks 0DV5 (3), correspond under
`AlgebraicGeometry.SmallEtale.finiteTypeLocallyConstantSheafEquiv`. -/
def finiteTypeLocallyConstantSheafEquivInverseConstantSheafIso (M : ModuleCat.{u + 1} Λ)
    [Finite (ToType M)] :
    (SmallEtale.finiteTypeLocallyConstantSheafEquiv B X Λ).inverse.obj
        (constantSheafFiniteTypeLocallyConstantModuleEtaleSite B X Λ M) ≅
      constantSheafFiniteTypeLocallyConstantModule B X Λ M :=
  ObjectProperty.isoMk _ (sheafEquivInverseConstantSheafModuleIso B X Λ M)

/-- The value of Stacks 0DV5 (3) on Mathlib's small étale site at a constant sheaf of modules is
its value on the small étale site of Stacks 021B. -/
def finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSiteConstantSheafIso
    (M : ModuleCat.{u + 1} Λ) [Finite (ToType M)] :
    (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj
        (constantSheafFiniteTypeLocallyConstantModuleEtaleSite B X Λ M) ≅
      (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj
        (constantSheafFiniteTypeLocallyConstantModule B X Λ M) :=
  (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.mapIso
    (finiteTypeLocallyConstantSheafEquivInverseConstantSheafIso B X Λ M)

/-- Stacks 0DV5 (3) on Mathlib's small étale site at a constant sheaf of modules: the action is
trivial. -/
theorem rho_eq_one_moduleSheafEquivalenceEtaleSite_constantSheaf
    (M : ModuleCat.{u + 1} Λ) [Finite (ToType M)] (σ : EtaleFundamentalGroup X.obj x) :
    ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj
      (constantSheafFiniteTypeLocallyConstantModuleEtaleSite B X Λ M)).obj.obj.obj.ρ σ = 1 :=
  rho_eq_one_of_iso Λ (EtaleFundamentalGroup X.obj x)
    (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSiteConstantSheafIso B X Λ x M).symm
    (fun τ ↦ rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf
      B X Λ x M τ) σ

/-- Stacks 0DV5 (3) on Mathlib's small étale site at a constant sheaf of finite modules: the
value has as many elements as the module. -/
theorem natCard_moduleSheafEquivalenceEtaleSite_constantSheaf
    (M : ModuleCat.{u + 1} Λ) [Finite (ToType M)] :
    Nat.card (ToType ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj
        (constantSheafFiniteTypeLocallyConstantModuleEtaleSite B X Λ M)).obj.obj.obj.V) =
      Nat.card (ToType M) := by
  rw [natCard_eq_of_iso Λ (EtaleFundamentalGroup X.obj x)
    (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSiteConstantSheafIso B X Λ x M)]
  exact Nat.card_congr
    (finiteTypeLocallyConstantModuleSheafEquivalenceConstantSheafEquiv B X Λ x M)

end Dictionary

end AlgebraicGeometry

end
