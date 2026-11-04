module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings

/-!
# Base change from a terminal object: the counit and corepresentation

Let `O` be a presheaf of rings with commutative sections on a category with a terminal object
`X`, and let `M ↦ O ⊗_{O(X)} M` be the base change functor
`Stacks.TerminalBaseChange.baseChangePresheaf`, left adjoint to evaluation at `X`. This file
computes the counit `O ⊗_{O(X)} P(X) ⟶ P` of that adjunction: over `U` it is the base-change
comparison of the restriction map `P(X) ⟶ P(U)`. Consequently a module whose counit is locally
bijective is corepresented, among morphisms into sheaves, by its sections over `X`. The base
change of a module is cartesian along every morphism.

## Main results

* `Stacks.TerminalBaseChange.baseChangeAdj_counit_app_app_eq_restrictionBaseChange`.
* `Stacks.TerminalBaseChange.bijective_app_of_isLocallyBijective_counit`.
* `Stacks.TerminalBaseChange.isIso_restrictionBaseChange_baseChangePresheaf_commRing`: the base
  change presheaf is cartesian along every morphism, for a presheaf of commutative rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf changeOfRings changeOfRingsAdjunction)

universe t v u r

namespace Stacks.TerminalBaseChange

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]
  {X : C} (hX : IsTerminal X)

/-- Two additive maps out of a tensor product agreeing on pure tensors agree everywhere. -/
private theorem tensor_apply_congr {R A M N F G : Type*} [CommSemiring R] {_ : AddCommMonoid A}
    {_ : AddCommMonoid M} {_ : Module R A} {_ : Module R M} [AddZeroClass N]
    [FunLike F (TensorProduct R A M) N] [AddMonoidHomClass F (TensorProduct R A M) N]
    [FunLike G (TensorProduct R A M) N] [AddMonoidHomClass G (TensorProduct R A M) N]
    (f : F) (g : G) (h : ∀ (a : A) (x : M), f (TensorProduct.tmul R a x) = g (.tmul R a x))
    (z : TensorProduct R A M) : f z = g z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x => exact h a x

/-- The adjoint transpose of `φ : M ⟶ P(X)` under the base change adjunction is, over `U`, the
adjoint transpose of `φ` followed by the restriction map of `P` along `U ⟶ X`. -/
theorem baseChangeAdj_homEquiv_symm_app (M : ModuleCat.{max t r} (O.obj (Opposite.op X)))
    (P : PresheafOfModules.{max t r} O) (φ : M ⟶ P.obj (Opposite.op X)) (U : Cᵒᵖ) :
    (((baseChangeAdj.{t} O hX).homEquiv M P).symm φ).app U =
      ((ModuleCat.extendRestrictScalarsAdj (rho O hX U)).homEquiv _ _).symm
        (φ ≫ P.map (iota hX U)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  refine tensor_apply_congr _ _ (fun a x => ?_) z
  rfl

/-- The counit of the base change adjunction at `P`, over `U`, is the adjoint transpose of the
restriction map `P(X) ⟶ P(U)` along the unique morphism `U ⟶ X`. -/
theorem baseChangeAdj_counit_app_app (P : PresheafOfModules.{max t r} O) (U : Cᵒᵖ) :
    ((baseChangeAdj.{t} O hX).counit.app P).app U =
      ((ModuleCat.extendRestrictScalarsAdj (rho O hX U)).homEquiv _ _).symm
        (P.map (iota hX U)) := by
  rw [← Adjunction.homEquiv_symm_id]
  exact (baseChangeAdj_homEquiv_symm_app.{t} O hX (P.obj (Opposite.op X)) P (𝟙 _) U).trans rfl

/-- The underlying presheaf of rings of a presheaf of commutative rings has commutative
sections. -/
instance commSections_comp_forget₂ (R : Cᵒᵖ ⥤ CommRingCat.{r}) :
    CommSections (R ⋙ forget₂ CommRingCat RingCat) :=
  ⟨fun U a b => mul_comm (G := R.obj U) a b⟩

/-- Over a presheaf of commutative rings, the counit of the base change adjunction at `P`, over
`U`, is the base-change comparison of the restriction map of `P` along `U ⟶ X`. -/
theorem baseChangeAdj_counit_app_app_eq_restrictionBaseChange (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (P : PresheafOfModules.{max t r} (R ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    ((baseChangeAdj.{t} (R ⋙ forget₂ CommRingCat RingCat) hX).counit.app P).app U =
      Stacks.PresheafOfModules.restrictionBaseChange.{u, v, r, t} (R := R) P (iota hX U) :=
  baseChangeAdj_counit_app_app.{t} _ hX P U

/-- **A module which is locally its base change from the terminal object is corepresented by its
sections there.** If the counit `O ⊗_{O(X)} P(X) ⟶ P` of the base change adjunction is locally
bijective, then a morphism from `P` to a sheaf of modules `Q` is determined by, and can be
prescribed through, its component `P(X) ⟶ Q(X)` over the terminal object. -/
theorem bijective_app_of_isLocallyBijective_counit {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
    (P Q : PresheafOfModules.{max t r} O) (hQ : Presheaf.IsSheaf J Q.presheaf)
    [PresheafOfModules.IsLocallySurjective J ((baseChangeAdj.{t} O hX).counit.app P)]
    [PresheafOfModules.IsLocallyInjective J ((baseChangeAdj.{t} O hX).counit.app P)] :
    Function.Bijective (fun g : P ⟶ Q => g.app (Opposite.op X)) := by
  let e₁ := PresheafOfModules.homEquivOfIsLocallyBijective
    (f := (baseChangeAdj.{t} O hX).counit.app P) hQ
  let e₂ := (baseChangeAdj.{t} O hX).homEquiv (P.obj (Opposite.op X)) Q
  have h : (fun g : P ⟶ Q => g.app (Opposite.op X)) = e₂ ∘ e₁ := by
    funext g
    show g.app (Opposite.op X) =
      (baseChangeAdj.{t} O hX).homEquiv _ Q ((baseChangeAdj.{t} O hX).counit.app P ≫ g)
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      Adjunction.right_triangle_components_assoc]
    exact (Category.id_comp _).symm
  exact h ▸ e₂.bijective.comp e₁.bijective

/-- A constant presheaf of modules over a constant presheaf of rings is cartesian along every
morphism: its base-change comparison is `R ⊗_R M ≅ M`. -/
theorem isIso_restrictionBaseChange_constMod (M : ModuleCat.{max t r} (O.obj (Opposite.op X)))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u, v, r, t} (R := constRing O X)
      ((constMod.{t} O X).obj M) f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let A := O.obj (Opposite.op X)
  have h : (Stacks.PresheafOfModules.restrictionBaseChange.{u, v, r, t} (R := constRing O X)
      ((constMod.{t} O X).obj M) f : _ → _) = TensorProduct.lid A M := by
    refine funext fun z => tensor_apply_congr _ (TensorProduct.lid A M) (fun a x => ?_) z
    rfl
  exact h ▸ (TensorProduct.lid A M).bijective

/-- **A base change from the terminal object is cartesian along every morphism**, for a presheaf
`R` of commutative rings and any morphism of `Cᵒᵖ` (the ring presheaf with commutative sections
form is `Stacks.TerminalBaseChange.isIso_restrictionBaseChange_baseChangePresheaf`). -/
theorem isIso_restrictionBaseChange_baseChangePresheaf_commRing (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (M : ModuleCat.{max t r} ((R ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op X)))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u, v, r, t} (R := R)
      ((baseChangePresheaf.{t} (R ⋙ forget₂ CommRingCat RingCat) hX).obj M) f) := by
  have := isIso_restrictionBaseChange_constMod.{t} (R ⋙ forget₂ CommRingCat RingCat) M f
  exact Stacks.PresheafOfModules.ChangeOfRings.isIso_restrictionBaseChange_changeOfRings
    (theta _ hX) ((constMod.{t} _ X).obj M) f

end Stacks.TerminalBaseChange
