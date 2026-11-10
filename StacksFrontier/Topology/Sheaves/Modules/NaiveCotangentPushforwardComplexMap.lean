module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPushforwardMap

/-!
# The map of naive cotangent complexes along a morphism into a pushforward

Let `f : Y ⟶ X` be a continuous map, let `α₁ : E₁ ⟶ B₁` present a sheaf of commutative rings
`B₁` on `X` over `A₁` and let `α₂ : E₂ ⟶ B₂` present a sheaf of commutative rings `B₂` on `Y`
over `A₂`. Morphisms `ρ : A₁ ⟶ f_*A₂` and `b : B₁ ⟶ f_*B₂` compatible with the structure maps,
together with a morphism `ε : E₁ ⟶ f_*E₂` of families of generators over `b`, induce a morphism
of polynomial presentations `A₁[E₁] ⟶ f_*(A₂[E₂])` and hence a chain map

`NL(α₁) ⟶ f_*NL(α₂)`,

linear over `b`. For a morphism of ringed spaces this is the map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}`
adjoint to the canonical `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`.

## Main definitions

* `Stacks.SheafOfModules.freeAlgebraPushMap`: the morphism `A₁[E₁] ⟶ f_*(A₂[E₂])`.
* `Stacks.SheafOfModules.presentationNaiveCotangentPushMap`: the chain map
  `NL(α₁) ⟶ f_*NL(α₂)`.

## Main results

* `Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne` and
  `presentationNaiveCotangentPushMap_f_zero`: its components in degrees `-1` and `0` are
  `presentationConormalPushMap` and `presentationTensorPushMap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

section Push

variable {X Y : TopCat.{u}} (f : Y ⟶ X)

/-- Pushforward of sheaves of modules along `pushforwardRingHom f b` is additive. -/
instance pushforwardRingHom_pushforward_additive {B₁ : TopCat.Sheaf CommRingCat.{u} X}
    {B₂ : TopCat.Sheaf CommRingCat.{u} Y}
    (b : B₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂) :
    (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).Additive where
  map_add := rfl

variable (A₁ B₁ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a₁ : A₁ ⟶ B₁)
  (E₁ : (Opens X)ᵒᵖ ⥤ Type u) (α₁ : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X) B₁)
  (A₂ B₂ : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) (a₂ : A₂ ⟶ B₂)
  (E₂ : (Opens Y)ᵒᵖ ⥤ Type u) (α₂ : E₂ ⟶ underlyingPresheaf (Opens.grothendieckTopology Y) B₂)
  (ρ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂)
  (b : B₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂)
  (ε : E₁ ⟶ (Opens.map f).op ⋙ E₂)

/-- The morphism of polynomial presentations `A₁[E₁] ⟶ f_*(A₂[E₂])`: `ρ` on coefficients and
`[x] ↦ [ε x]` on variables. -/
noncomputable def freeAlgebraPushMap :
    freeAlgebraSheaf (Opens.grothendieckTopology X) A₁ E₁ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology Y) A₂ E₂) :=
  freeAlgebraSheafDesc (Opens.grothendieckTopology X) A₁
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      (freeAlgebraSheaf (Opens.grothendieckTopology Y) A₂ E₂)) E₁
    (ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A₂ E₂))
    (ε ≫ Functor.whiskerLeft (Opens.map f).op
      (freeAlgebraSheafVariable (Opens.grothendieckTopology Y) A₂ E₂))

/-- On coefficients, `freeAlgebraPushMap` restricts to `ρ` followed by the coefficient map of
`A₂[E₂]`. -/
theorem freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A₁ E₁ ≫
        freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε =
      ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A₂ E₂) :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- On variables, `freeAlgebraPushMap` sends `[x]` to `[ε x]`. -/
theorem freeAlgebraSheafVariable_comp_freeAlgebraPushMap :
    freeAlgebraSheafVariable (Opens.grothendieckTopology X) A₁ E₁ ≫ Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map
          (freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε)) (forget CommRingCat.{u}) =
      ε ≫ Functor.whiskerLeft (Opens.map f).op
        (freeAlgebraSheafVariable (Opens.grothendieckTopology Y) A₂ E₂) :=
  freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- Forgetting to presheaves of types, `g ≫ f_*h` is the composite of `g` and `h` whiskered by
`f`. -/
private theorem whiskerRight_map_comp_pushforward_map {P : Sheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}} {Q R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    (g : P ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj Q) (h : Q ⟶ R) :
    Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map
        (g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map h)) (forget CommRingCat.{u}) =
      Functor.whiskerRight ((sheafToPresheaf (Opens.grothendieckTopology X)
        CommRingCat.{u}).map g) (forget CommRingCat.{u}) ≫
      Functor.whiskerLeft (Opens.map f).op (Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map h)
          (forget CommRingCat.{u})) := rfl

variable {A₁ B₁ a₁ E₁ α₁ A₂ B₂ a₂ E₂ α₂ ρ b ε}
  (hab : a₁ ≫ b = ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)
  (hε : ε ≫ Functor.whiskerLeft (Opens.map f).op α₂ = α₁ ≫ Functor.whiskerRight b.hom
    (forget CommRingCat.{u}))

include hab hε in
/-- The morphism of polynomial presentations lies over `b`. -/
theorem freeAlgebraPushMap_comp_presentation :
    freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂) =
      presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁ ≫ b := by
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap f A₁ E₁ A₂
      E₂ ρ ε)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ρ ≫ ·) ((Functor.map_comp _ _ _).symm.trans (congrArg _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _)))).trans ?_
    refine hab.symm.trans ?_
    refine (congrArg (· ≫ b) (freeAlgebraSheafCoefficientMap_comp_desc
      (Opens.grothendieckTopology X) A₁ B₁ E₁ a₁ α₁).symm).trans ?_
    exact Category.assoc _ _ _
  · rw [whiskerRight_map_comp_pushforward_map]
    erw [Functor.map_comp, Functor.whiskerRight_comp]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (freeAlgebraSheafVariable_comp_freeAlgebraPushMap f A₁ E₁ A₂
      E₂ ρ ε)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ε ≫ ·) ((Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg _
      (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _)))).trans ?_
    refine hε.trans ?_
    refine (congrArg (· ≫ Functor.whiskerRight b.hom (forget CommRingCat.{u}))
      (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X) A₁ B₁ E₁ a₁
        α₁).symm).trans ?_
    exact Category.assoc _ _ _

/-- The morphism of polynomial presentations lies under `ρ`. -/
theorem freeAlgebraPushMap_coefficient :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A₁ E₁ ≫
        freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε =
      ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A₂ E₂) :=
  freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε

/-- Pushforward of sheaves of modules along `pushforwardRingHom f b` is additive. -/
instance : (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).Additive :=
  pushforwardRingHom_pushforward_additive f b

/-- Pushforward of sheaves of modules along `pushforwardRingHom f b` preserves zero morphisms. -/
instance :
    (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).PreservesZeroMorphisms :=
  inferInstance

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).hom]

/-- The map `K₁/K₁² ⟶ f_*(K₂/K₂²)` of conormal sheaves induced by the morphism of presentations. -/
noncomputable abbrev presentationConormalPushMap :
    (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).X₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).obj
        (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂
          α₂).X₁ :=
  conormalSheafMapPush f B₁ B₂ b (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂)
    (freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε) (freeAlgebraPushMap_comp_presentation f hab hε)

/-- The map `B₁ ⊗[A₁[E₁]] Ω[A₁[E₁]/A₁] ⟶ f_*(B₂ ⊗[A₂[E₂]] Ω[A₂[E₂]/A₂])` induced by the morphism
of presentations. -/
noncomputable abbrev presentationTensorPushMap :
    (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).X₂ ⟶
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).obj
        (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂
          α₂).X₂ :=
  tensorSheafMapPush f B₁ B₂ b (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂)
    (freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε) (freeAlgebraPushMap_comp_presentation f hab hε) A₁ A₂
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A₁ E₁)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A₂ E₂) ρ
    (freeAlgebraPushMap_coefficient f)

/-- The maps `presentationConormalPushMap` and `presentationTensorPushMap` commute with the
differentials in degree `-1` of `NL(α₁)` and of `f_*NL(α₂)`. -/
theorem presentationConormalPushMap_comm :
    (presentationConormalPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm)) ≫
      (((_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (presentationNaiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂)).d (-1) 0 =
    (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).f ≫
      (presentationTensorPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm)) := by
  change _ ≫ (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
    ((presentationNaiveCotangentComplex.{u, u, u, u}
      (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).d (-1) 0) = _
  rw [presentationNaiveCotangentComplex_d_negOne_zero, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp, ← Category.assoc]
  exact congrArg (· ≫ _) (conormalSequence_f_naturality_push f B₁ B₂ b
    (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂)
    (freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε) (freeAlgebraPushMap_comp_presentation f hab hε) A₁ A₂
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A₁ E₁)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology Y) A₂ E₂) ρ
    (freeAlgebraPushMap_coefficient f)).symm

/-- The composite of `presentationTensorPushMap` with the differential of `f_*NL(α₂)` out of
degree `0` is zero. -/
theorem presentationTensorPushMap_comp_d (k : ℤ) :
    (presentationTensorPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm)) ≫
      (((_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (presentationNaiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂)).d 0 k = 0 := by
  change _ ≫ (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
    ((presentationNaiveCotangentComplex.{u, u, u, u}
      (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).d 0 k) = 0
  rw [presentationNaiveCotangentComplex_d_zero, Functor.map_zero, Limits.comp_zero]

/-- **The chain map `NL(α₁) ⟶ f_*NL(α₂)`** induced by a morphism of presentations along `f`. -/
noncomputable def presentationNaiveCotangentPushMap :
    presentationNaiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁ ⟶
      ((_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (presentationNaiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂) := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B₁)) := hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (presentationConormalPushMap f hab hε ≫
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
        (eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm))
    (presentationTensorPushMap f hab hε ≫
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
        (eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm))
    (presentationConormalPushMap_comm f hab hε)
    (fun k _ ↦ presentationTensorPushMap_comp_d f hab hε k)

/-- In degree `-1`, the chain map `NL(α₁) ⟶ f_*NL(α₂)` is `presentationConormalPushMap`. -/
theorem presentationNaiveCotangentPushMap_f_negOne :
    (presentationNaiveCotangentPushMap f hab hε).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁) ≫
        presentationConormalPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm) := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B₁)) := hasZeroObject_of_hasTerminal_object
  have h₀ : (HomologicalComplex.doubleXIso₀
      (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
        (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁) := by
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  rw [← h₀]
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationConormalPushMap_comm f hab hε)
    (fun k _ ↦ presentationTensorPushMap_comp_d f hab hε k)

/-- In degree `0`, the chain map `NL(α₁) ⟶ f_*NL(α₂)` is `presentationTensorPushMap`. -/
theorem presentationNaiveCotangentPushMap_f_zero :
    (presentationNaiveCotangentPushMap f hab hε).f 0 =
      eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁) ≫
        presentationTensorPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).symm) := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B₁)) := hasZeroObject_of_hasTerminal_object
  have h₁ : (HomologicalComplex.doubleXIso₁
      (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
        (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁) := by
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  rw [← h₁]
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationConormalPushMap_comm f hab hε)
    (fun k _ ↦ presentationTensorPushMap_comp_d f hab hε k)

end Push

/-! ### Naturality in the presentations -/

section Naturality

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {A₁ B₁ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} {a₁ : A₁ ⟶ B₁}
  {E₁ E₁' : (Opens X)ᵒᵖ ⥤ Type u}
  {α₁ : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X) B₁}
  {α₁' : E₁' ⟶ underlyingPresheaf (Opens.grothendieckTopology X) B₁}
  {A₂ B₂ : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {a₂ : A₂ ⟶ B₂}
  {E₂ E₂' : (Opens Y)ᵒᵖ ⥤ Type u}
  {α₂ : E₂ ⟶ underlyingPresheaf (Opens.grothendieckTopology Y) B₂}
  {α₂' : E₂' ⟶ underlyingPresheaf (Opens.grothendieckTopology Y) B₂}
  {ρ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂}
  {b : B₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂}
  {ε : E₁ ⟶ (Opens.map f).op ⋙ E₂} {ε' : E₁' ⟶ (Opens.map f).op ⋙ E₂'}
  (k₁ : E₁ ⟶ E₁') (k₂ : E₂ ⟶ E₂')
  (hcomm : ε ≫ Functor.whiskerLeft (Opens.map f).op k₂ = k₁ ≫ ε')

include hcomm in
/-- **The morphisms of polynomial presentations along `f` are natural** in the families of
generators. -/
theorem freeAlgebraPushMap_naturality :
    freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map
        (freeAlgebraMap (Opens.grothendieckTopology Y) A₂ E₂ E₂' k₂) =
      freeAlgebraMap (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁ ≫
        freeAlgebraPushMap f A₁ E₁' A₂ E₂' ρ ε' := by
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap f A₁ E₁ A₂
      E₂ ρ ε)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ρ ≫ ·) ((Functor.map_comp _ _ _).symm.trans (congrArg _
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap _ _ _ _ _)))).trans ?_
    refine (freeAlgebraSheafCoefficientMap_comp_freeAlgebraPushMap f A₁ E₁' A₂ E₂' ρ
      ε').symm.trans ?_
    refine (congrArg (· ≫ _) (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap
      (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁).symm).trans ?_
    exact Category.assoc _ _ _
  · rw [whiskerRight_map_comp_pushforward_map]
    erw [Functor.map_comp, Functor.whiskerRight_comp]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (freeAlgebraSheafVariable_comp_freeAlgebraPushMap f A₁ E₁ A₂
      E₂ ρ ε)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ε ≫ ·) ((Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg _
      (freeAlgebraSheafVariable_comp_freeAlgebraMap _ _ _ _ _)))).trans ?_
    refine (congrArg (ε ≫ ·) (Functor.whiskerLeft_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hcomm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (k₁ ≫ ·) (freeAlgebraSheafVariable_comp_freeAlgebraPushMap f A₁ E₁' A₂
      E₂' ρ ε').symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ _) (freeAlgebraSheafVariable_comp_freeAlgebraMap
      (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁).symm

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁' α₁').hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂ α₂).hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
    (presentation (Opens.grothendieckTopology Y) A₂ B₂ a₂ E₂' α₂').hom]
  (hk₁ : k₁ ≫ α₁' = α₁) (hk₂ : k₂ ≫ α₂' = α₂)
  (hab : a₁ ≫ b = ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)
  (hε : ε ≫ Functor.whiskerLeft (Opens.map f).op α₂ = α₁ ≫ Functor.whiskerRight b.hom
    (forget CommRingCat.{u}))
  (hε' : ε' ≫ Functor.whiskerLeft (Opens.map f).op α₂' = α₁' ≫ Functor.whiskerRight b.hom
    (forget CommRingCat.{u}))

include hcomm in
/-- **The maps of conormal sheaves along `f` are natural** in the families of generators. -/
theorem presentationConormalPushMap_naturality :
    presentationConormalPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (presentationConormalMap.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ E₂ E₂' k₂ B₂ a₂
            α₂ α₂' hk₂) =
      presentationConormalMap.{u, u, u, u} (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁ B₁ a₁ α₁
          α₁' hk₁ ≫ presentationConormalPushMap f hab hε' := by
  refine conormal_hom_ext.{u, u, u, u} (presentation (Opens.grothendieckTopology X) A₁ B₁ a₁ E₁ α₁)
    _ (fun U x ↦ ?_)
  have hring := congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X) A₁ E₁ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology Y) A₂ E₂') ↦ (t.hom.app U).hom x.1)
    (freeAlgebraPushMap_naturality (ρ := ρ) f k₁ k₂ hcomm)
  refine (congrArg ((presentationConormalMap.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ E₂
      E₂' k₂ B₂ a₂ α₂ α₂' hk₂).val.app ((Opens.map f).op.obj U))
    (conormalSheafMapPush_toAssociatedModule f B₁ B₂ b _ _ _ _ U _)).trans ?_
  refine (conormalSheafMapOfFac_toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y)
    B₂ _ _ _ _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg ((presentationConormalPushMap f hab hε').val.app U)
    (conormalSheafMapOfFac_toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X)
      B₁ _ _ _ _ _ _ U _)).symm
  refine Eq.trans ?_ (conormalSheafMapPush_toAssociatedModule f B₁ B₂ b _ _ _ _ U _).symm
  exact congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) _ B₂ _
    (conormalPresheaf _) ((Opens.map f).op.obj U))
    (congrArg (kernelIdeal _ ((Opens.map f).op.obj U)).toCotangent (Subtype.ext hring))

include hcomm in
/-- **The maps of scalar extensions of differentials along `f` are natural** in the families of
generators. -/
theorem presentationTensorPushMap_naturality :
    presentationTensorPushMap f hab hε ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (presentationTensorMap.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ E₂ E₂' k₂ B₂ a₂
            α₂ α₂' hk₂) =
      presentationTensorMap.{u, u, u, u} (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁ B₁ a₁ α₁
          α₁' hk₁ ≫ presentationTensorPushMap f hab hε' := by
  have hring : ∀ (U : (Opens X)ᵒᵖ) (z : (freeAlgebraSheaf (Opens.grothendieckTopology X) A₁
      E₁).obj.obj U), ((freeAlgebraMap (Opens.grothendieckTopology Y) A₂ E₂ E₂' k₂).hom.app
        ((Opens.map f).op.obj U)).hom (((freeAlgebraPushMap f A₁ E₁ A₂ E₂ ρ ε).hom.app U).hom z) =
      ((freeAlgebraPushMap f A₁ E₁' A₂ E₂' ρ ε').hom.app U).hom
        (((freeAlgebraMap (Opens.grothendieckTopology X) A₁ E₁ E₁' k₁).hom.app U).hom z) :=
    fun U z ↦ congrArg (fun t : freeAlgebraSheaf (Opens.grothendieckTopology X) A₁ E₁ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology Y) A₂ E₂') ↦ (t.hom.app U).hom z)
      (freeAlgebraPushMap_naturality (ρ := ρ) f k₁ k₂ hcomm)
  refine sheafify_hom_ext.{u, u, u, u} (Opens.grothendieckTopology X) _ B₁ _ _ _ (fun U t ↦ ?_)
  refine (congrArg ((presentationTensorMap.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ E₂
      E₂' k₂ B₂ a₂ α₂ α₂' hk₂).val.app ((Opens.map f).op.obj U))
    (tensorSheafMapPush_toAssociatedModule f B₁ B₂ b _ _ _ _ _ _ _ _ _ _ U _)).trans ?_
  refine (tensorSheafMapOfFac_toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y)
    _ B₂ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg ((presentationTensorPushMap f hab hε').val.app U)
    (tensorSheafMapOfFac_toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X)
      _ B₁ _ _ _ _ _ _ _ _ _ U _)).symm
  refine Eq.trans ?_ (tensorSheafMapPush_toAssociatedModule f B₁ B₂ b _ _ _ _ _ _ _ _ _ _ U
    _).symm
  refine congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) _ B₂ _
    (tensorPresheaf _ _) ((Opens.map f).op.obj U)) ?_
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx
      hy).trans ((map_add _ _ _).symm.trans (congrArg _ (map_add _ x y).symm))))
  | tmul y ω =>
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ((congrArg _ (TensorProduct.map_tmul _ _ _ _)).trans
      (TensorProduct.map_tmul _ _ _ _)).trans ?_
    refine Eq.trans ?_ ((congrArg _ (TensorProduct.map_tmul _ _ _ _)).trans
      (TensorProduct.map_tmul _ _ _ _)).symm
    refine congrArg₂ (fun z (w : (differentialsPresheaf _).obj ((Opens.map f).op.obj U)) ↦
      z ⊗ₜ w) (congrArg (Ideal.Quotient.mk _) (hring U y)) ?_
    let := ((freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A₁ E₁).hom.app
      U).hom.toAlgebra
    have mem : ω ∈ Submodule.span ((freeAlgebraSheaf (Opens.grothendieckTopology X) A₁ E₁).obj.obj
        U) (Set.range (KaehlerDifferential.D (A₁.obj.obj U)
          ((freeAlgebraSheaf (Opens.grothendieckTopology X) A₁ E₁).obj.obj U))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction mem using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨z, rfl⟩ := hz
      change differentialsMapOfFac _ _ _ _ _ (differentialsMapPush _ _ _ _ _ _ _ _ _
          (CommRingCat.KaehlerDifferential.d z)) =
        differentialsMapPush _ _ _ _ _ _ _ _ _ (differentialsMapOfFac _ _ _ _ _
          (CommRingCat.KaehlerDifferential.d z))
      refine (congrArg _ (differentialsMapPush_d f _ A₁ A₂ _ _ ρ _ U z)).trans ?_
      refine (differentialsMapOfFac_d _ _ _ _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg _ (differentialsMapOfFac_d _ _ _ _ _ z)).symm
      refine Eq.trans ?_ (differentialsMapPush_d f _ A₁ A₂ _ _ ρ _ U _).symm
      exact congrArg CommRingCat.KaehlerDifferential.d (hring U z)
    | zero =>
      exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
        ((map_zero _).symm.trans (congrArg _ (map_zero _).symm)))
    | add x y _ _ hx hy =>
      exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx
        hy).trans ((map_add _ _ _).symm.trans (congrArg _ (map_add _ x y).symm))))
    | smul r x _ hx =>
      rw [map_smulₛₗ, map_smulₛₗ, hx, map_smulₛₗ, map_smulₛₗ]
      exact congrArg (· • _) (hring U r)

include hcomm in
/-- **The chain maps `NL(α₁) ⟶ f_*NL(α₂)` along `f` are natural** in the families of
generators: they commute with the chain maps of morphisms of presentations on both sides. -/
theorem presentationNaiveCotangentPushMap_naturality :
    presentationNaiveCotangentPushMap f hab hε ≫
        ((_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (presentationNaiveCotangentComplexMap.{u, u, u, u}
            (Opens.grothendieckTopology Y) A₂ E₂ E₂' k₂ B₂ a₂ α₂ α₂' hk₂) =
      presentationNaiveCotangentComplexMap.{u, u, u, u} (Opens.grothendieckTopology X) A₁ E₁ E₁'
          k₁ B₁ a₁ α₁ α₁' hk₁ ≫ presentationNaiveCotangentPushMap f hab hε' := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      presentationNaiveCotangentPushMap_f_negOne, presentationNaiveCotangentPushMap_f_negOne,
      presentationNaiveCotangentComplexMap_f_negOne, Functor.mapHomologicalComplex_map_f,
      presentationNaiveCotangentComplexMap_f_negOne]
    simp only [Category.assoc, Functor.map_comp, eqToHom_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (presentationConormalPushMap f hab hε),
      presentationConormalPushMap_naturality f k₁ k₂ hcomm hk₁ hk₂ hab hε hε', Category.assoc]
  by_cases h0 : i = 0
  · subst h0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      presentationNaiveCotangentPushMap_f_zero, presentationNaiveCotangentPushMap_f_zero,
      presentationNaiveCotangentComplexMap_f_zero, Functor.mapHomologicalComplex_map_f,
      presentationNaiveCotangentComplexMap_f_zero]
    simp only [Category.assoc, Functor.map_comp, eqToHom_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (presentationTensorPushMap f hab hε),
      presentationTensorPushMap_naturality f k₁ k₂ hcomm hk₁ hk₂ hab hε hε', Category.assoc]
  exact (presentationNaiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology X)
    A₁ B₁ a₁ E₁ α₁ i h1 h0).eq_of_src _ _

end Naturality

end Stacks.SheafOfModules

end
