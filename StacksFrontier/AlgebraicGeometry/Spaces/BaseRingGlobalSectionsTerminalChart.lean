module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleInverseLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# Global sections of a direct image to an algebraic space with a terminal chart

Let `y : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, and let `U` be a terminal
object of the small étale site of `Y` (an affine `Y` has one, `Y` itself read as a chart).  The
global sections over `X` of the direct image `y_* M` of an `𝒪_Y`-module `M` are the sections of
`M` over `U`, naturally in `M`:

`Γ(X, y_* M) = Hom(𝒪_X, y_* M) = Hom(y^* 𝒪_X, M) = Hom(𝒪_Y, M) = Γ(Y, M) = M(U)`.

The global sections are read on the model of the small étale site, as
`AlgebraicGeometry.Space.baseRingGlobalSectionsModule`, and then as abelian groups.

## Main definitions

* `AlgebraicGeometry.Space.baseRingGlobalSectionsAddCommGrp`: `Γ(X, -)` with values in abelian
  groups.
* `AlgebraicGeometry.Space.pushforwardGlobalSectionsAddEquivOfIsTerminal`: the identification
  above, for one module.
* `AlgebraicGeometry.Space.pushforwardGlobalSectionsIsoOfIsTerminal`: the identification as an
  isomorphism of functors to abelian groups, the target being the sections functor at `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Global sections of an `𝒪_X`-module, read on the model of the small étale site as an
`R`-module along `φ` and then as an abelian group. -/
abbrev baseRingGlobalSectionsAddCommGrp (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
    (φ : R →+* modelGlobalFunctions B S hS X) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u} :=
  baseRingGlobalSectionsModule B S hS X φ ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- Global sections read on the model are additive, being a right adjoint. -/
instance baseRingGlobalSectionsModule_additive (X : AlgebraicSpaces B S hS) {R : Type u}
    [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X) :
    (baseRingGlobalSectionsModule B S hS X φ).Additive :=
  (baseRingTensorModuleAdjunction B S hS X φ).right_adjoint_additive

section Pushforward

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X) {U : SmallEtale B S hS Y.1} (hU : IsTerminal U)

/-- The global sections over `X` of `y_* M`, as morphisms `𝒪_Y ⟶ M`: the model, the adjunction
`y^* ⊣ y_*` and `y^* 𝒪_X ≅ 𝒪_Y`. -/
def pushforwardGlobalSectionsHomEquiv (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M) ≃
      (unitModule B S hS Y.2 ⟶ M) :=
  (modelSectionsHomEquiv B S hS X φ _).trans
    (((modulePullbackAdjunction B S hS y).homEquiv _ _).symm.trans
      ((modulePullbackUnitIso B S hS y).homCongr (Iso.refl M)))

/-- The morphism `𝒪_Y ⟶ M` attached to a global section `s` of `y_* M` is the inverse of
`y^* 𝒪_X ≅ 𝒪_Y` followed by the adjoint of the morphism `𝒪_X ⟶ y_* M` that `s` is on the
model. -/
theorem pushforwardGlobalSectionsHomEquiv_apply (M : Modules.{u, u} B S hS Y.1 Y.2)
    (s : (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M)) :
    pushforwardGlobalSectionsHomEquiv B S hS y φ M s =
      (modulePullbackUnitIso B S hS y).inv ≫ ((modulePullbackAdjunction B S hS y).homEquiv _ _).symm
        (modelSectionsHomEquiv B S hS X φ _ s) := by
  simp only [pushforwardGlobalSectionsHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]

/-- The identification of the global sections of `y_* M` with the morphisms `𝒪_Y ⟶ M` is
additive. -/
theorem pushforwardGlobalSectionsHomEquiv_add (M : Modules.{u, u} B S hS Y.1 Y.2)
    (s t : (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M)) :
    pushforwardGlobalSectionsHomEquiv B S hS y φ M (s + t) =
      pushforwardGlobalSectionsHomEquiv B S hS y φ M s +
        pushforwardGlobalSectionsHomEquiv B S hS y φ M t := by
  have := (modulePullbackAdjunction B S hS y).left_adjoint_additive
  rw [pushforwardGlobalSectionsHomEquiv_apply, pushforwardGlobalSectionsHomEquiv_apply,
    pushforwardGlobalSectionsHomEquiv_apply, modelSectionsHomEquiv_add,
    Adjunction.homAddEquiv_symm_add, Preadditive.comp_add]

/-- The identification of the global sections of `y_* M` with the morphisms `𝒪_Y ⟶ M` is
natural in `M`. -/
theorem pushforwardGlobalSectionsHomEquiv_naturality {M M' : Modules.{u, u} B S hS Y.1 Y.2}
    (g : M ⟶ M')
    (s : (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M)) :
    pushforwardGlobalSectionsHomEquiv B S hS y φ M'
        ((baseRingGlobalSectionsModule B S hS X φ).map ((modulePushforward B S hS y).map g) s) =
      pushforwardGlobalSectionsHomEquiv B S hS y φ M s ≫ g := by
  rw [pushforwardGlobalSectionsHomEquiv_apply, pushforwardGlobalSectionsHomEquiv_apply,
    modelSectionsHomEquiv_naturality, Adjunction.homEquiv_naturality_right_symm, Category.assoc]

include hU in
/-- **The global sections over `X` of `y_* M` are the sections of `M` over a terminal chart of
`Y`**, additively. -/
def pushforwardGlobalSectionsAddEquivOfIsTerminal (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M) ≃+
      M.val.obj (op U) where
  toEquiv := (pushforwardGlobalSectionsHomEquiv B S hS y φ M).trans
    ((SheafOfModules.unitHomEquiv M).trans
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hU))
  map_add' s t := by
    change (pushforwardGlobalSectionsHomEquiv B S hS y φ M (s + t)).val.app (op U)
        (1 : chartRing B S hS Y.1 Y.2 U) =
      (pushforwardGlobalSectionsHomEquiv B S hS y φ M s).val.app (op U)
          (1 : chartRing B S hS Y.1 Y.2 U) +
        (pushforwardGlobalSectionsHomEquiv B S hS y φ M t).val.app (op U)
          (1 : chartRing B S hS Y.1 Y.2 U)
    rw [pushforwardGlobalSectionsHomEquiv_add]
    rfl

/-- The section over the terminal chart `U` attached to a global section `s` of `y_* M` is the
value at `1` over `U` of the morphism `𝒪_Y ⟶ M` attached to `s`. -/
theorem pushforwardGlobalSectionsAddEquivOfIsTerminal_apply
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (s : (baseRingGlobalSectionsModule B S hS X φ).obj ((modulePushforward B S hS y).obj M)) :
    pushforwardGlobalSectionsAddEquivOfIsTerminal B S hS y φ hU M s =
      (pushforwardGlobalSectionsHomEquiv B S hS y φ M s).val.app (op U)
        (1 : chartRing B S hS Y.1 Y.2 U) :=
  rfl

/-- **Global sections of a direct image to a space with a terminal chart**, as an isomorphism of
functors to abelian groups: `Γ(X, y_* −)` is the sections functor at the terminal chart `U`. -/
def pushforwardGlobalSectionsIsoOfIsTerminal :
    modulePushforward B S hS y ⋙ baseRingGlobalSectionsAddCommGrp B S hS X φ ≅
      Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS Y.1 Y.2) U :=
  NatIso.ofComponents
    (fun M => (pushforwardGlobalSectionsAddEquivOfIsTerminal B S hS y φ hU M).toAddCommGrpIso)
    (fun {M M'} g => by
      ext s
      change pushforwardGlobalSectionsAddEquivOfIsTerminal B S hS y φ hU M'
          ((baseRingGlobalSectionsModule B S hS X φ).map ((modulePushforward B S hS y).map g) s) =
        (g.val.app (op U)).hom (pushforwardGlobalSectionsAddEquivOfIsTerminal B S hS y φ hU M s)
      rw [pushforwardGlobalSectionsAddEquivOfIsTerminal_apply,
        pushforwardGlobalSectionsAddEquivOfIsTerminal_apply,
        pushforwardGlobalSectionsHomEquiv_naturality]
      rfl)

end Pushforward

end AlgebraicGeometry.Space

end
