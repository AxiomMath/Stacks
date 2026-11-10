module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FormalCoverNeighbourhoodLift
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackMultiplicationLaws
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerStability

/-!
# The algebra structure on the algebraization of the formal finite étale cover

Let `𝒢` be a finite locally free module on an open neighbourhood `V` of the closed subscheme,
with a formal datum `pₙ : 𝒢 ⟶ (Cₙ ⟶ V)_* 𝒪_{Cₙ}`
(`Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum`). Granted condition (4) of
[Stacks, Tag 0EK2] on `V`, this file carries out the step of the proof of [Stacks, Tag 0EK1]
that puts an algebra structure on `𝒢` after shrinking `V`: the multiplications of the algebras
`(Cₙ ⟶ V)_* 𝒪_{Cₙ}` form a morphism `(𝒢 ⊗ 𝒢)^∧ ⟶ 𝒢^∧` of completions, which by condition (4)
comes from a morphism `μ : 𝒢 ⊗ 𝒢 ⟶ 𝒢` on a smaller neighbourhood, and the algebra laws, which
hold after completion, hold after shrinking once more.

## Main definitions

* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.nearMap` — the map
  `𝒢|_W ⟶ (Cₙ ⟶ W)_* 𝒪_{Cₙ}` on an open `W` of `V` containing the closed subscheme.
* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.mulAt`, `unitAt` — the multiplication
  and the unit of `(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}` read on `zₙ^* 𝒢` through `φₙ`.

## Main results

* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.exists_algebraData` — there is an open
  `W` of `V` containing the closed subscheme and a commutative unital algebra structure on
  `𝒢|_W` for which `nearMap` at `n = 0` is multiplicative and unital.

## Implementation notes

The multiplications `mulAt n` form a compatible family on the terms of the tower: their adjoints
are the multiplications of the `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` read on `𝒢` through the `pₙ`, which are
compatible with the transitions because these are morphisms of algebras. Condition (4) turns the
family into a morphism `μ : (𝒢 ⊗ 𝒢)|_W ⟶ 𝒢|_W`, and similarly for the unit. Each algebra law is
an equation between morphisms of restrictions of finite locally free modules on `V`, written with
the tensor products of morphisms between pullbacks of
`Stacks.Algebraization.pullbackTensorHom`; it holds on every `Zₙ` since it holds for `mulAt n`,
hence on a smaller open by condition (4), and it survives further restriction. On the
intersection of the three opens the laws are read through the comparison of [Stacks, Tag 01CD]
as the laws of a multiplication `𝒢|_W ⊗ 𝒢|_W ⟶ 𝒢|_W`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.Thickenings
open scoped TensorProduct

universe u

namespace Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum

open Stacks.Algebraization MonoidalCategory
open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication unitModuleMap)

attribute [local instance] AlgebraicGeometry.monoidalOfScheme

variable {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {A : FiniteEtaleOver Z}
  {V : X.Opens} {hV : Set.range i.base ⊆ V} {G : V.toScheme.Modules} [G.IsQuasicoherent]
  (D : FormalDatum i A V hV G)


/-! ### The multiplications and units on the infinitesimal neighbourhoods -/

/-- The identification `φₙ`, with its target spelled as the module underlying the algebra
`(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}`. -/
def φUnderlying (n : ℕ) : (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G ≅
    Stacks.RelativeSpec.AlgebraSheaf.underlyingModule (pushforwardAlgebra (cover i A n).hom) :=
  D.φ n

/-- The multiplication of `(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}` read on `zₙ^* 𝒢` through `φₙ`. -/
def mulAt (n : ℕ) :
    (Scheme.Modules.pullback (nbhdHom i V hV n)).obj (G ⊗ G) ⟶
      (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G :=
  (schemePullbackTensorIso (nbhdHom i V hV n) G G).hom ≫
    ((D.φUnderlying n).hom ⊗ₘ (D.φUnderlying n).hom) ≫
    multiplication (pushforwardAlgebra (cover i A n).hom) ≫ (D.φUnderlying n).inv

/-- The unit of `(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}` read on `zₙ^* 𝒢` through `φₙ`. -/
def unitAt (n : ℕ) :
    (Scheme.Modules.pullback (nbhdHom i V hV n)).obj (𝟙_ V.toScheme.Modules) ⟶
      (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G :=
  (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso (nbhdHom i V hV n)).hom ≫
    unitModuleMap (pushforwardAlgebra (cover i A n).hom) ≫ (D.φUnderlying n).inv

/-- The multiplications of the `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` read on `𝒢` through the `pₙ`. -/
def mulFamily (n : ℕ) : G ⊗ G ⟶ openModule i A V hV n :=
  (D.p n ⊗ₘ D.p n) ≫ multiplication (pushforwardAlgebra (toOpen i A V hV n))

/-- The multiplication on `zₙ^* 𝒢` is the adjoint of the multiplications of the
`(Cₙ ⟶ V)_* 𝒪_{Cₙ}` read on `𝒢`. -/
theorem pullbackHomEquivPushforward_mulFamily (n : ℕ) :
    pullbackHomEquivPushforward (nbhdHom i V hV n) (G ⊗ G) _
      (D.mulFamily n ≫ (compIso i A V hV n).inv ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φUnderlying n).inv) = D.mulAt n := by
  refine (Equiv.eq_symm_apply _).1 ?_
  have key : D.mulFamily n ≫ (compIso i A V hV n).inv =
      (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app (G ⊗ G) ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map
          ((schemePullbackTensorIso (nbhdHom i V hV n) G G).hom ≫
            ((D.φUnderlying n).hom ⊗ₘ (D.φUnderlying n).hom) ≫
            multiplication (pushforwardAlgebra (cover i A n).hom)) := by
    refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b => ?_
    have hp : ∀ x, (D.p n).val.app U x = (D.φUnderlying n).hom.val.app
        (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) G U.unop x) :=
      fun x => by rw [D.p_eq n]; rfl
    have hT := Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit
      (nbhdHom i V hV n) G G U.unop a b
    have L : ((D.mulFamily n ≫ (compIso i A V hV n).inv).val.app U)
        (Stacks.PullbackTensorCoherence.tmul _ G G U a b) =
        Stacks.RelativeSpec.AlgebraSheaf.mulSection (pushforwardAlgebra (toOpen i A V hV n)) U
          ((D.p n).val.app U a) ((D.p n).val.app U b) :=
      (congrArg (fun t => ((multiplication _).val.app U) t)
        (Stacks.PullbackTensorCoherence.tensorHom_tmul (D.p n) (D.p n) U a b)).trans
          (AlgebraicGeometry.multiplication_tmul' _ U _ _)
    have R1 : ((schemePullbackTensorIso (nbhdHom i V hV n) G G).hom.val.app
          (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop)))
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) (G ⊗ G) U.unop
          (Stacks.PullbackTensorCoherence.tmul _ G G U a b)) =
        Stacks.PullbackTensorCoherence.tmul _ _ _ _
          (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) G U.unop a)
          (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) G U.unop b) := hT
    refine L.trans (Eq.trans ?_
      (show ((multiplication (pushforwardAlgebra (cover i A n).hom)).val.app
        (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop)))
          ((((D.φUnderlying n).hom ⊗ₘ (D.φUnderlying n).hom).val.app
          (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))) (((schemePullbackTensorIso
            (nbhdHom i V hV n) G G).hom.val.app (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop)))
              (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) (G ⊗ G) U.unop
                (Stacks.PullbackTensorCoherence.tmul _ G G U a b)))) = _ from rfl))
    rw [R1]
    refine Eq.trans ?_ (congrArg (fun t => ((multiplication (pushforwardAlgebra
      (cover i A n).hom)).val.app (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))) t)
      (Stacks.PullbackTensorCoherence.tensorHom_tmul (D.φUnderlying n).hom (D.φUnderlying n).hom
        (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop)) _ _)).symm
    have hM := AlgebraicGeometry.multiplication_tmul' (pushforwardAlgebra (cover i A n).hom)
      (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))
      ((D.φUnderlying n).hom.val.app (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) G U.unop a))
      ((D.φUnderlying n).hom.val.app (Opposite.op (nbhdHom i V hV n ⁻¹ᵁ U.unop))
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (nbhdHom i V hV n) G U.unop b))
    refine Eq.trans ?_ hM.symm
    rw [hp, hp]
    rfl
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)).trans ?_
  simp only [pullbackHomEquivPushforward, Equiv.symm_symm, Adjunction.homEquiv_unit, mulAt]
  exact (Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t)
    (((Scheme.Modules.pushforward _).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pushforward _).map ((Category.assoc _ _ _).trans
        (congrArg (fun t => _ ≫ t) (Category.assoc _ _ _))))))


omit [SheafOfModules.IsQuasicoherent G] in
/-- The multiplications of the `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` read on `𝒢` are compatible with the
transitions. -/
theorem mulFamily_step (n : ℕ) :
    D.mulFamily (n + 1) ≫ openModuleStep i A V hV n = D.mulFamily n := by
  have h1' := multiplication_comp_underlyingModuleMap_tensorHom
    (AdicFiniteAlgebra.pushforwardAlgebraHomOfEq (toOpen i A V hV n) (toOpen i A V hV (n + 1))
      (step i A n) (step_toOpen i A V hV n))
  have h2 : (D.p (n + 1) ⊗ₘ D.p (n + 1)) ≫ (openModuleStep i A V hV n ⊗ₘ openModuleStep i A V hV n)
      = (D.p n ⊗ₘ D.p n) :=
    (tensorHom_comp_tensorHom _ _ _ _).trans (congrArg₂ (· ⊗ₘ ·) (D.p_step n) (D.p_step n))
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => (D.p (n + 1) ⊗ₘ D.p (n + 1)) ≫ t)
    h1').trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ multiplication (pushforwardAlgebra (toOpen i A V hV n))) h2)))

/-- A family of maps `S ⟶ (Cₙ ⟶ V)_* 𝒪_{Cₙ}` compatible with the transitions, whose adjoints are
the maps `x n`, gives a compatible family `x`. -/
private theorem homTrans_eq_of_pullbackHomEquivPushforward (S : V.toScheme.Modules)
    (fam : ∀ n, S ⟶ openModule i A V hV n)
    (hfam : ∀ n, fam (n + 1) ≫ openModuleStep i A V hV n = fam n)
    (x : ∀ n, (Scheme.Modules.pullback (nbhdHom i V hV n)).obj S ⟶
      (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G)
    (hx : ∀ n, pullbackHomEquivPushforward (nbhdHom i V hV n) S _
      (fam n ≫ (compIso i A V hV n).inv ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φUnderlying n).inv) = x n)
    (n m : ℕ) (h : n ≤ m) : (nbhdTower i V hV).homTrans S G n m h (x m) = x n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 := pullbackHomEquivPushforward_pushforwardPullbackRestriction
    (nbhdHom i V hV (n + k)) ((nbhdTower i V hV).trans n (n + k) h).left (nbhdHom i V hV n)
    (Over.w ((nbhdTower i V hV).trans n (n + k) h)) S G
    (fam (n + k) ≫ (compIso i A V hV (n + k)).inv ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV (n + k))).map (D.φUnderlying (n + k)).inv)
  have e2 : (fam (n + k) ≫ (compIso i A V hV (n + k)).inv ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV (n + k))).map (D.φUnderlying (n + k)).inv) ≫
        pushforwardPullbackRestriction (nbhdHom i V hV (n + k))
          ((nbhdTower i V hV).trans n (n + k) h).left (nbhdHom i V hV n)
          (Over.w ((nbhdTower i V hV).trans n (n + k) h)) G =
      fam n ≫ (compIso i A V hV n).inv ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φUnderlying n).inv := by
    have e := D.compIso_inv_pushforwardPullbackRestriction n k h
    have e' := comp_openModuleTrans i A V hV fam hfam n k
    refine (Category.assoc _ _ _).trans ((congrArg (fun t => fam (n + k) ≫ t)
      ((Category.assoc _ _ _).trans e)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e')
  refine (congrArg (pullbackHomMap S G ((nbhdTower i V hV).trans n (n + k) h).left
    (Over.w ((nbhdTower i V hV).trans n (n + k) h))) (hx (n + k)).symm).trans ?_
  exact e1.symm.trans ((congrArg (pullbackHomEquivPushforward (nbhdHom i V hV n) S _)
    e2).trans (hx n))

/-- The multiplications on the infinitesimal neighbourhoods form a compatible family. -/
theorem mulAt_trans (n m : ℕ) (h : n ≤ m) :
    (nbhdTower i V hV).homTrans (G ⊗ G) G n m h (D.mulAt m) = D.mulAt n :=
  D.homTrans_eq_of_pullbackHomEquivPushforward _ D.mulFamily D.mulFamily_step _
    D.pullbackHomEquivPushforward_mulFamily n m h

/-- The units of the `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`. -/
def unitFamily (n : ℕ) : 𝟙_ V.toScheme.Modules ⟶ openModule i A V hV n :=
  unitModuleMap (pushforwardAlgebra (toOpen i A V hV n))

/-- The unit on `zₙ^* 𝒢` is the adjoint of the unit of `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`. -/
theorem pullbackHomEquivPushforward_unitFamily (n : ℕ) :
    pullbackHomEquivPushforward (nbhdHom i V hV n) (𝟙_ V.toScheme.Modules) _
      (unitFamily (i := i) (A := A) (hV := hV) n ≫ (compIso i A V hV n).inv ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φUnderlying n).inv)
          = D.unitAt n := by
  refine (Equiv.eq_symm_apply _).1 ?_
  have key : unitFamily (i := i) (A := A) (hV := hV) n ≫ (compIso i A V hV n).inv =
      Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom (nbhdHom i V hV n) ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map
          (unitModuleMap (pushforwardAlgebra (cover i A n).hom)) := by
    apply SheafOfModules.hom_ext
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    rfl
  simp only [pullbackHomEquivPushforward, Equiv.symm_symm, Adjunction.homEquiv_unit, unitAt]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) key)).trans ?_
  refine (congrArg (· ≫ _) (congrArg (· ≫ _)
    (Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso
      (nbhdHom i V hV n)).symm)).trans ?_
  refine ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans ?_
  exact congrArg (fun t => _ ≫ t) ((congrArg (fun t => _ ≫ t)
    ((Scheme.Modules.pushforward _).map_comp _ _).symm).trans
      ((Scheme.Modules.pushforward _).map_comp _ _).symm)

/-- The units of the `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` are compatible with the transitions. -/
theorem unitFamily_step (n : ℕ) :
    unitFamily (i := i) (A := A) (hV := hV) (n + 1) ≫ openModuleStep i A V hV n =
      unitFamily (i := i) (A := A) (hV := hV) n :=
  Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_comp _

/-- The units on the infinitesimal neighbourhoods form a compatible family. -/
theorem unitAt_trans (n m : ℕ) (h : n ≤ m) :
    (nbhdTower i V hV).homTrans (𝟙_ V.toScheme.Modules) G n m h (D.unitAt m) = D.unitAt n :=
  D.homTrans_eq_of_pullbackHomEquivPushforward _ unitFamily unitFamily_step _
    D.pullbackHomEquivPushforward_unitFamily n m h



/-- The computation of a restricted multiplication against the identification `φₙ`, as pure
category algebra. -/
private theorem restrict_mul_chain {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    (F : D ⥤ C) {X T N : D} {X₁ N₁ M : C} (t : X ≅ T) (μ : X ⟶ N)
    (τ : F.obj T ≅ F.obj N ⊗ F.obj N) (f₁ : F.obj X ≅ X₁) (f₂ : F.obj N ≅ N₁)
    (t₁ : X₁ ≅ N₁ ⊗ N₁) (φ : N₁ ≅ M) (mul : M ⊗ M ⟶ M)
    (hμ : f₁.inv ≫ F.map μ ≫ f₂.hom = t₁.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv)
    (hC : (F.map t.hom ≫ τ.hom) ≫ (f₂.hom ⊗ₘ f₂.hom) = f₁.hom ≫ t₁.hom) :
    F.map (t.inv ≫ μ) ≫ f₂.hom ≫ φ.hom =
      τ.hom ≫ ((f₂.hom ≫ φ.hom) ⊗ₘ (f₂.hom ≫ φ.hom)) ≫ mul := by
  have h₁ : F.map μ ≫ f₂.hom = f₁.hom ≫ t₁.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv := by
    rw [← hμ, Iso.hom_inv_id_assoc]
  have h₂ : F.map t.inv ≫ f₁.hom ≫ t₁.hom = τ.hom ≫ (f₂.hom ⊗ₘ f₂.hom) := by
    rw [← hC]
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [F.map_comp, Category.assoc, reassoc_of% h₁, reassoc_of% h₂, ← tensorHom_comp_tensorHom]
  simp

/-- The computation of a restricted unit against the identification `φₙ`, as pure category
algebra. -/
private theorem restrict_unit_chain {C D : Type*} [Category C] [Category D]
    (F : D ⥤ C) {O O' N : D} {O₁ N₁ M U : C} (p : O ≅ O') (η : O ⟶ N)
    (pw : F.obj O' ≅ U) (f₀ : F.obj O ≅ O₁) (f₂ : F.obj N ≅ N₁) (pz : O₁ ≅ U)
    (φ : N₁ ≅ M) (u : U ⟶ M)
    (hη : f₀.inv ≫ F.map η ≫ f₂.hom = pz.hom ≫ u ≫ φ.inv)
    (hPU : pz.hom = f₀.inv ≫ F.map p.hom ≫ pw.hom) :
    F.map (p.inv ≫ η) ≫ f₂.hom ≫ φ.hom = pw.hom ≫ u := by
  have h₁ : F.map η ≫ f₂.hom = f₀.hom ≫ pz.hom ≫ u ≫ φ.inv := by
    rw [← hη, Iso.hom_inv_id_assoc]
  rw [F.map_comp, Category.assoc, reassoc_of% h₁, hPU]
  simp [← F.map_comp_assoc]

/-! ### The algebra laws on the infinitesimal neighbourhoods -/

/-- The multiplication on `zₙ^* 𝒢` is associative. -/
theorem mulAt_assoc (n : ℕ) :
    pullbackTensorHom (nbhdHom i V hV n) (D.mulAt n) (𝟙 _) ≫ D.mulAt n =
      (Scheme.Modules.pullback (nbhdHom i V hV n)).map (α_ G G G).hom ≫
        pullbackTensorHom (nbhdHom i V hV n) (𝟙 _) (D.mulAt n) ≫ D.mulAt n :=
  pullbackTensorHom_assoc_of_iso (nbhdHom i V hV n) G (D.φUnderlying n) _
    (AlgebraicGeometry.multiplication_assoc _ _ rfl)

/-- The multiplication on `zₙ^* 𝒢` is commutative. -/
theorem mulAt_comm (n : ℕ) :
    (Scheme.Modules.pullback (nbhdHom i V hV n)).map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
          V.toScheme.toRingedSpace G G).hom ≫
        D.mulAt n = D.mulAt n :=
  pullback_tensorSheafSwap_of_iso (nbhdHom i V hV n) G (D.φUnderlying n) _
    (AlgebraicGeometry.tensorSheafSwap_comp_multiplication _)

/-- The unit on `zₙ^* 𝒢` is a left unit for the multiplication. -/
theorem unitAt_mulAt (n : ℕ) :
    (Scheme.Modules.pullback (nbhdHom i V hV n)).map (λ_ G).inv ≫
        pullbackTensorHom (nbhdHom i V hV n) (D.unitAt n) (𝟙 _) ≫ D.mulAt n = 𝟙 _ :=
  pullback_leftUnitor_inv_of_iso (nbhdHom i V hV n) G (D.φUnderlying n) _ _
    (AlgebraicGeometry.unitModuleMap_comp_multiplication _ _ rfl _ rfl)

/-- **The formal datum read on an open `W` of `V` containing the closed subscheme:** the map
`𝒢|_W ⟶ (Cₙ ⟶ W)_* 𝒪_{Cₙ}` adjoint to the identification `φₙ` of `𝒢|_{Zₙ}`. -/
public def nearMap {W : V.toScheme.Opens} (hW : (nbhdTower i V hV).support ⊆ W) (n : ℕ) :
    (Scheme.Modules.pullback W.ι).obj G ⟶
      (Scheme.Modules.pushforward ((cover i A n).hom ≫ (nbhdTower i V hV).homToOpen hW n)).obj
        (SheafOfModules.unit _) :=
  (Scheme.Modules.pullbackPushforwardAdjunction ((nbhdTower i V hV).homToOpen hW n)).unit.app _ ≫
    (Scheme.Modules.pushforward ((nbhdTower i V hV).homToOpen hW n)).map
      ((pullbackObjFactorIso G ((nbhdTower i V hV).homToOpen hW n)
        ((nbhdTower i V hV).homToOpen_ι hW n)).hom ≫ (D.φ n).hom) ≫
    (Scheme.Modules.pushforwardComp (cover i A n).hom
      ((nbhdTower i V hV).homToOpen hW n)).hom.app _

/-! ### The map `nearMap` is multiplicative and unital -/

section NearMap

variable {W : V.toScheme.Opens} (hW : (nbhdTower i V hV).support ⊆ W)

/-- The identification of `w^* (𝒢|_W)` with `(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}`, for `w : Zₙ ⟶ W`. -/
abbrev nearIso (n : ℕ) :
    (Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n)).obj
        ((Scheme.Modules.pullback W.ι).obj G) ≅
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModule (pushforwardAlgebra (cover i A n).hom) :=
  pullbackObjFactorIso G ((nbhdTower i V hV).homToOpen hW n)
    ((nbhdTower i V hV).homToOpen_ι hW n) ≪≫ D.φUnderlying n

/-- A multiplication on `𝒢|_W` inducing the multiplication of `zₙ^* 𝒢` is, after pullback
to `Zₙ`, the multiplication of `(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}`. -/
theorem pullback_mul_nearIso (n : ℕ)
    (μ : (Scheme.Modules.pullback W.ι).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback W.ι).obj G)
    (hμ : (nbhdTower i V hV).homAt (G ⊗ G) G hW n μ = D.mulAt n) :
    (Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n)).map
        ((schemePullbackTensorIso W.ι G G).inv ≫ μ) ≫ (D.nearIso hW n).hom =
      (schemePullbackTensorIso ((nbhdTower i V hV).homToOpen hW n)
          ((Scheme.Modules.pullback W.ι).obj G) ((Scheme.Modules.pullback W.ι).obj G)).hom ≫
        ((D.nearIso hW n).hom ⊗ₘ (D.nearIso hW n).hom) ≫
        multiplication (pushforwardAlgebra (cover i A n).hom) :=
  restrict_mul_chain (Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n))
    (schemePullbackTensorIso W.ι G G) μ (schemePullbackTensorIso ((nbhdTower i V hV).homToOpen hW n)
      ((Scheme.Modules.pullback W.ι).obj G) ((Scheme.Modules.pullback W.ι).obj G))
    (pullbackObjFactorIso (G ⊗ G) ((nbhdTower i V hV).homToOpen hW n)
      ((nbhdTower i V hV).homToOpen_ι hW n))
    (pullbackObjFactorIso G ((nbhdTower i V hV).homToOpen hW n)
      ((nbhdTower i V hV).homToOpen_ι hW n))
    (schemePullbackTensorIso (nbhdHom i V hV n) G G) (D.φUnderlying n) _ hμ
    (schemePullbackTensorIso_pullbackObjFactorIso ((nbhdTower i V hV).homToOpen hW n) W.ι
      ((nbhdTower i V hV).homToOpen_ι hW n) G G)

/-- A unit on `𝒢|_W` inducing the unit of `zₙ^* 𝒢` is, after pullback to `Zₙ`, the unit of
`(Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}`. -/
theorem pullback_unit_nearIso (n : ℕ)
    (η : (Scheme.Modules.pullback W.ι).obj (𝟙_ V.toScheme.Modules) ⟶
      (Scheme.Modules.pullback W.ι).obj G)
    (hη : (nbhdTower i V hV).homAt (𝟙_ V.toScheme.Modules) G hW n η = D.unitAt n) :
    (Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n)).map
        ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso W.ι).inv ≫ η) ≫
          (D.nearIso hW n).hom =
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
          ((nbhdTower i V hV).homToOpen hW n)).hom
            ≫ unitModuleMap (pushforwardAlgebra (cover i A n).hom) :=
  restrict_unit_chain (Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n))
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso W.ι) η
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso ((nbhdTower i V hV).homToOpen hW n))
    (pullbackObjFactorIso (𝟙_ V.toScheme.Modules) ((nbhdTower i V hV).homToOpen hW n)
      ((nbhdTower i V hV).homToOpen_ι hW n))
    (pullbackObjFactorIso G ((nbhdTower i V hV).homToOpen hW n)
      ((nbhdTower i V hV).homToOpen_ι hW n))
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso (nbhdHom i V hV n))
      (D.φUnderlying n) _ hη
    (pullbackObjFactorIso_pullbackUnitIso ((nbhdTower i V hV).homToOpen hW n) W.ι
      ((nbhdTower i V hV).homToOpen_ι hW n))

/-- `nearMap` on sections: the adjunction unit followed by `nearIso`. -/
theorem nearMap_app (n : ℕ) (U : W.toScheme.Opensᵒᵖ)
    (z : ((Scheme.Modules.pullback W.ι).obj G).val.obj U) :
    (D.nearMap hW n).val.app U z = (D.nearIso hW n).hom.val.app
      (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
        ((Scheme.Modules.pullback W.ι).obj G) U.unop z) := rfl

/-- `nearMap` after a morphism, on sections. -/
theorem nearMap_app_comp {E : W.toScheme.Modules} (n : ℕ)
    (f : E ⟶ (Scheme.Modules.pullback W.ι).obj G) (U : W.toScheme.Opensᵒᵖ) (z : E.val.obj U) :
    (D.nearMap hW n).val.app U (f.val.app U z) =
      ((Scheme.Modules.pullback ((nbhdTower i V hV).homToOpen hW n)).map f ≫
        (D.nearIso hW n).hom).val.app
      (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
        E U.unop z) := by
  rw [nearMap_app]
  have nat := (Scheme.Modules.pullbackPushforwardAdjunction
    ((nbhdTower i V hV).homToOpen hW n)).unit.naturality f
  have := congrArg (fun k => k.val.app U z) nat
  exact congrArg _ this

/-- **`nearMap` is multiplicative** for a multiplication inducing the multiplications of the
`zₙ^* 𝒢`. -/
theorem nearMap_mul (n : ℕ)
    (μ : (Scheme.Modules.pullback W.ι).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback W.ι).obj G)
    (hμ : (nbhdTower i V hV).homAt (G ⊗ G) G hW n μ = D.mulAt n) (U : W.toScheme.Opensᵒᵖ)
    (x y : ((Scheme.Modules.pullback W.ι).obj G).val.obj U) :
    (D.nearMap hW n).val.app U (((schemePullbackTensorIso W.ι G G).inv ≫ μ).val.app U
        (Stacks.PullbackTensorCoherence.tmul _ _ _ U x y)) =
      Mul.mul (α := Γ((cover i A n).left,
        ((cover i A n).hom ≫ (nbhdTower i V hV).homToOpen hW n) ⁻¹ᵁ U.unop))
        ((D.nearMap hW n).val.app U x) ((D.nearMap hW n).val.app U y) := by
  refine (D.nearMap_app_comp hW n _ U _).trans ?_
  refine (congrArg (fun k => k.val.app (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
      ((Scheme.Modules.pullback W.ι).obj G ⊗ (Scheme.Modules.pullback W.ι).obj G) U.unop
      (Stacks.PullbackTensorCoherence.tmul _ _ _ U x y)))
        (D.pullback_mul_nearIso hW n μ hμ)).trans ?_
  have hT := Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit
    ((nbhdTower i V hV).homToOpen hW n) ((Scheme.Modules.pullback W.ι).obj G)
    ((Scheme.Modules.pullback W.ι).obj G) U.unop x y
  have R1 : ((schemePullbackTensorIso ((nbhdTower i V hV).homToOpen hW n)
        ((Scheme.Modules.pullback W.ι).obj G) ((Scheme.Modules.pullback W.ι).obj G)).hom.val.app
          (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop)))
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
        ((Scheme.Modules.pullback W.ι).obj G ⊗ (Scheme.Modules.pullback W.ι).obj G) U.unop
        (Stacks.PullbackTensorCoherence.tmul _ _ _ U x y)) =
      Stacks.PullbackTensorCoherence.tmul _ _ _ _
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
          ((Scheme.Modules.pullback W.ι).obj G) U.unop x)
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
          ((Scheme.Modules.pullback W.ι).obj G) U.unop y) := hT
  refine (congrArg (fun t => ((multiplication (pushforwardAlgebra (cover i A n).hom)).val.app
    (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop)))
      (((D.nearIso hW n).hom ⊗ₘ (D.nearIso hW n).hom).val.app
        (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop)) t)) R1).trans ?_
  refine (congrArg (fun t => ((multiplication (pushforwardAlgebra (cover i A n).hom)).val.app
    (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))) t)
    (Stacks.PullbackTensorCoherence.tensorHom_tmul (D.nearIso hW n).hom (D.nearIso hW n).hom
      (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop)) _ _)).trans ?_
  exact AlgebraicGeometry.multiplication_tmul' (pushforwardAlgebra (cover i A n).hom)
    (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop)) _ _

/-- **`nearMap` is unital** for a unit inducing the units of the `zₙ^* 𝒢`. -/
theorem nearMap_one (n : ℕ)
    (η : (Scheme.Modules.pullback W.ι).obj (𝟙_ V.toScheme.Modules) ⟶
      (Scheme.Modules.pullback W.ι).obj G)
    (hη : (nbhdTower i V hV).homAt (𝟙_ V.toScheme.Modules) G hW n η = D.unitAt n)
    (U : W.toScheme.Opensᵒᵖ) :
    (D.nearMap hW n).val.app U
        (((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso W.ι).inv ≫ η).val.app U
          (1 : Γ(W.toScheme, U.unop))) =
      (1 : Γ((cover i A n).left,
        ((cover i A n).hom ≫ (nbhdTower i V hV).homToOpen hW n) ⁻¹ᵁ U.unop)) := by
  refine (D.nearMap_app_comp hW n _ U _).trans ?_
  refine (congrArg (fun k => k.val.app (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ((nbhdTower i V hV).homToOpen hW n)
      (𝟙_ W.toScheme.Modules) U.unop (1 : Γ(W.toScheme, U.unop))))
    (D.pullback_unit_nearIso hW n η hη)).trans ?_
  have h1 := congrArg (fun k => k.val.app U (1 : Γ(W.toScheme, U.unop)))
    (Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso
      ((nbhdTower i V hV).homToOpen hW n))
  refine (congrArg (fun t => ((unitModuleMap (pushforwardAlgebra (cover i A n).hom)).val.app
    (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))) t) h1).trans ?_
  refine (congrArg (fun t => ((unitModuleMap (pushforwardAlgebra (cover i A n).hom)).val.app
    (Opposite.op ((nbhdTower i V hV).homToOpen hW n ⁻¹ᵁ U.unop))) t)
    (map_one (((nbhdTower i V hV).homToOpen hW n).app U.unop).hom)).trans ?_
  exact Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_one _ _

end NearMap

/-- **The algebra structure on the algebraization, after shrinking the neighbourhood.** Granted
condition (4) of [Stacks, Tag 0EK2] for all pairs of finite locally free modules on `V`, there is
an open `W` of `V` containing the closed subscheme and a commutative unital algebra structure on
`𝒢|_W` for which `nearMap` at `n = 0` is unital and multiplicative. -/
public theorem exists_algebraData
    (hFF : ∀ E F : V.toScheme.Modules, SheafOfModules.IsFiniteLocallyFree.{u, u, u} E →
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} F → (nbhdTower i V hV).IsHomsComplete E F)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    ∃ (W : V.toScheme.Opens) (hW : (nbhdTower i V hV).support ⊆ W)
      (d : ModuleAlgebraData ((Scheme.Modules.pullback W.ι).obj G)),
      (∀ U : W.toScheme.Opensᵒᵖ, (D.nearMap hW 0).val.app U (d.unit.val.app U
          (1 : Γ(W.toScheme, U.unop))) =
        (1 : Γ((cover i A 0).left,
          ((cover i A 0).hom ≫ (nbhdTower i V hV).homToOpen hW 0) ⁻¹ᵁ U.unop))) ∧
      (∀ (U : W.toScheme.Opensᵒᵖ) (x y : ((Scheme.Modules.pullback W.ι).obj G).val.obj U),
        (D.nearMap hW 0).val.app U (d.mul.app U (x ⊗ₜ[Γ(W.toScheme, U.unop)] y)) =
          Mul.mul (α := Γ((cover i A 0).left,
            ((cover i A 0).hom ≫ (nbhdTower i V hV).homToOpen hW 0) ⁻¹ᵁ U.unop))
            ((D.nearMap hW 0).val.app U x) ((D.nearMap hW 0).val.app U y)) := by
  have hGG := isFiniteLocallyFree_tensorObj G G hG hG
  have hGGG := isFiniteLocallyFree_tensorObj (G ⊗ G) G hGG hG
  have hO := isFiniteLocallyFree_unit V.toScheme
  obtain ⟨W₁, hW₁, μ₁, hμ₁⟩ := (hFF (G ⊗ G) G hGG hG).exists_hom D.mulAt D.mulAt_trans
  obtain ⟨W₂, hW₂, η₁, hη₁⟩ := (hFF (𝟙_ V.toScheme.Modules) G hO hG).exists_hom D.unitAt
    D.unitAt_trans
  have hW₀ := (nbhdTower i V hV).support_subset_inf hW₁ hW₂
  let μ₀ := homRestrict (G ⊗ G) G (inf_le_left : W₁ ⊓ W₂ ≤ W₁) μ₁
  let η₀ := homRestrict (𝟙_ V.toScheme.Modules) G (inf_le_right : W₁ ⊓ W₂ ≤ W₂) η₁
  have hμ₀ : ∀ n, (nbhdTower i V hV).homAt (G ⊗ G) G hW₀ n μ₀ = D.mulAt n := fun n =>
    ((nbhdTower i V hV).homAt_homRestrict _ _ hW₁ hW₀ _ n μ₁).trans (hμ₁ n)
  have hη₀ : ∀ n, (nbhdTower i V hV).homAt _ G hW₀ n η₀ = D.unitAt n := fun n =>
    ((nbhdTower i V hV).homAt_homRestrict _ _ hW₂ hW₀ _ n η₁).trans (hη₁ n)
  -- associativity
  obtain ⟨Wa, hWa, ha, ha₂, hassoc⟩ := (hFF _ G hGGG hG).eq_of_homAt_eq _ _ hW₀ hW₀
    (pullbackTensorHom (W₁ ⊓ W₂).ι μ₀ (𝟙 _) ≫ μ₀)
    ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map (α_ G G G).hom ≫
      pullbackTensorHom (W₁ ⊓ W₂).ι (𝟙 _) μ₀ ≫ μ₀) (fun n => by
        refine (pullbackHomMap_assoc_left _ _ _ G μ₀).trans ?_
        refine Eq.trans ?_ (pullbackHomMap_assoc_right _ _ _ G μ₀).symm
        have h := hμ₀ n
        simp only [InfinitesimalTower.homAt] at h
        rw [h]
        exact D.mulAt_assoc n)
  -- commutativity
  obtain ⟨Wc, hWc, hc, hc₂, hcomm⟩ := (hFF _ G hGG hG).eq_of_homAt_eq _ _ hW₀ hW₀
    ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
        V.toScheme.toRingedSpace G G).hom ≫
        μ₀) μ₀ (fun n =>
        (pullbackHomMap_swap _ _ _ G μ₀).trans ((congrArg (fun t =>
          (Scheme.Modules.pullback (nbhdHom i V hV n)).map
            (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap V.toScheme.toRingedSpace
              G G).hom ≫ t) (hμ₀ n)).trans ((D.mulAt_comm n).trans (hμ₀ n).symm)))
  -- unit
  obtain ⟨Wu, hWu, hu, hu₂, hone⟩ := (hFF G G hG hG).eq_of_homAt_eq _ _ hW₀ hW₀
    ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map (λ_ G).inv ≫
      pullbackTensorHom (W₁ ⊓ W₂).ι η₀ (𝟙 _) ≫ μ₀) (𝟙 _) (fun n => by
        refine (pullbackHomMap_unit_left _ _ _ G μ₀ η₀).trans ?_
        refine Eq.trans ?_ (pullbackHomMap_id _ _ _).symm
        have h := hμ₀ n
        have h' := hη₀ n
        simp only [InfinitesimalTower.homAt] at h h'
        rw [h, h']
        exact D.unitAt_mulAt n)
  -- the final open
  let W := (Wa ⊓ Wc) ⊓ Wu
  have hW : (nbhdTower i V hV).support ⊆ W :=
    (nbhdTower i V hV).support_subset_inf ((nbhdTower i V hV).support_subset_inf hWa hWc) hWu
  have hWa' : W ≤ Wa := inf_le_left.trans inf_le_left
  have hWc' : W ≤ Wc := inf_le_left.trans inf_le_right
  have hWu' : W ≤ Wu := inf_le_right
  have hW0 : W ≤ W₁ ⊓ W₂ := hWa'.trans ha
  let μ := homRestrict (G ⊗ G) G hW0 μ₀
  let η := homRestrict (𝟙_ V.toScheme.Modules) G hW0 η₀
  have hμ : ∀ n, (nbhdTower i V hV).homAt (G ⊗ G) G hW n μ = D.mulAt n := fun n =>
    ((nbhdTower i V hV).homAt_homRestrict _ _ hW₀ hW _ n μ₀).trans (hμ₀ n)
  have hη : ∀ n, (nbhdTower i V hV).homAt _ G hW n η = D.unitAt n := fun n =>
    ((nbhdTower i V hV).homAt_homRestrict _ _ hW₀ hW _ n η₀).trans (hη₀ n)
  -- the laws on the final open
  have Lassoc : pullbackTensorHom W.ι μ (𝟙 _) ≫ μ =
      (Scheme.Modules.pullback W.ι).map (α_ G G G).hom ≫ pullbackTensorHom W.ι (𝟙 _) μ ≫ μ := by
    have e1 := pullbackHomMap_assoc_left (V.toScheme.homOfLE hW0) (W₁ ⊓ W₂).ι
      (V.toScheme.homOfLE_ι hW0) G μ₀
    have e2 := pullbackHomMap_assoc_right (V.toScheme.homOfLE hW0) (W₁ ⊓ W₂).ι
      (V.toScheme.homOfLE_ι hW0) G μ₀
    refine e1.symm.trans (Eq.trans ?_ e2)
    have h1 := homRestrict_homRestrict _ G ha hWa' (pullbackTensorHom (W₁ ⊓ W₂).ι μ₀ (𝟙 _) ≫ μ₀)
    have h2 := homRestrict_homRestrict _ G ha hWa'
      ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map (α_ G G G).hom ≫
        pullbackTensorHom (W₁ ⊓ W₂).ι (𝟙 _) μ₀ ≫ μ₀)
    exact h1.symm.trans ((congrArg (homRestrict _ G hWa') hassoc).trans h2)
  have Lcomm : (Scheme.Modules.pullback W.ι).map
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
        V.toScheme.toRingedSpace G G).hom ≫
        μ = μ := by
    have e1 := pullbackHomMap_swap (V.toScheme.homOfLE hW0) (W₁ ⊓ W₂).ι
      (V.toScheme.homOfLE_ι hW0) G μ₀
    refine e1.symm.trans ?_
    have h1 := homRestrict_homRestrict _ G hc hWc'
      ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
          V.toScheme.toRingedSpace G G).hom ≫
          μ₀)
    have h2 := homRestrict_homRestrict _ G hc hWc' μ₀
    exact h1.symm.trans ((congrArg (homRestrict _ G hWc') hcomm).trans h2)
  have Lone : (Scheme.Modules.pullback W.ι).map (λ_ G).inv ≫
      pullbackTensorHom W.ι η (𝟙 _) ≫ μ = 𝟙 _ := by
    have e1 := pullbackHomMap_unit_left (V.toScheme.homOfLE hW0) (W₁ ⊓ W₂).ι
      (V.toScheme.homOfLE_ι hW0) G μ₀ η₀
    refine e1.symm.trans ?_
    have h1 := homRestrict_homRestrict _ G hu hWu'
      ((Scheme.Modules.pullback (W₁ ⊓ W₂).ι).map (λ_ G).inv ≫
        pullbackTensorHom (W₁ ⊓ W₂).ι η₀ (𝟙 _) ≫ μ₀)
    have h2 := homRestrict_homRestrict G G hu hWu' (𝟙 _)
    exact h1.symm.trans ((congrArg (homRestrict _ G hWu') hone).trans
      (h2.trans (pullbackHomMap_id _ _ _)))
  -- the algebra data
  have hA := (pullbackTensorHom_assoc_iff W.ι G μ).1 Lassoc
  have hC := (pullback_tensorSheafSwap_iff W.ι G μ).1 Lcomm
  have hU := (pullback_leftUnitor_inv_comp W.ι G μ η).symm.trans Lone
  refine ⟨W, hW,
    moduleAlgebraDataOfLaws _ ((schemePullbackTensorIso W.ι G G).inv ≫ μ)
      ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso W.ι).inv ≫ η) hC hA hU,
    fun U => ?_, fun U x y => ?_⟩
  · exact D.nearMap_one hW 0 η (hη 0) U
  · exact D.nearMap_mul hW 0 μ (hμ 0) U x y

end Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum

end
