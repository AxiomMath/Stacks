module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerSystem

/-!
# Multiplication by a section is divisible by `g` where `s = g e`

On an open `D` on which the global section `s` of `ℱ` factors as `g e` for a function `g` and a
section `e`, every transition map `ℱ^{[n]} ⟶ ℱ^{[n + 1]}` of the system of [Stacks, Tag 0EBN]
carries a section over `D` to `g` times a section over `D`.  Iterating, the image of the unit
section of `𝒪_X` in `ℱ^{[k]}` is divisible by `g^k`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.unitHomEquiv_symm_app_unitSection`: the morphism
  `𝒪_X ⟶ ℱ` determined by `s` carries the unit section over `D` to `s|_D`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.unitHomEquiv_symm_app`: on a local section `a` it is
  `a ↦ a s|_D`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.exists_transition_app_eq_smul`: **multiplication by
  `s` is divisible by `g`** on such a `D`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.unitPower`: the image of the unit section of `𝒪_X`
  in `ℱ^{[k]}` over `D`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.unitPower_succ`: the images of the unit section are
  related by the transition maps.
* `Stacks.AlgebraicGeometry.ReflexivePowers.exists_unitPower_eq_pow_smul`: **it is divisible by
  `g^k`.**

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHull toDoubleDual)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection sheafifyUnit)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable {X : Scheme.{u}} (F : X.Modules) (s : F.sections)

/-- **The morphism `𝒪_X ⟶ ℱ` determined by `s` carries the unit section over `D` to `s|_D`.** -/
theorem unitHomEquiv_symm_app_unitSection (D : X.Opens) :
    ((F.unitHomEquiv.symm s).val.app (op D)).hom (unitSection X.toRingedSpace (op D) 1) =
      s.eval (op D) :=
  one_smul Γ(X, D) (show Γ(F, D) from s.eval (op D))

/-- **The morphism `𝒪_X ⟶ ℱ` determined by `s`, on an arbitrary local section**: it is
multiplication by `s|_D`. -/
theorem unitHomEquiv_symm_app (D : X.Opens) (a : Γ(X, D)) :
    ((F.unitHomEquiv.symm s).val.app (op D)).hom (unitSection X.toRingedSpace (op D) a) =
      a • (show Γ(F, D) from s.eval (op D)) := rfl

/-- **Multiplication by `s` is divisible by `g`** on an open `D` on which `s|_D = g e`: the
transition `ℱ^{[n]} ⟶ ℱ^{[n + 1]}` carries every section over `D` to `g` times a section. -/
theorem exists_transition_app_eq_smul (n : ℕ) (D : X.Opens) (e : Γ(F, D)) (g : Γ(X, D))
    (hs : s.eval (op D) = g • e) (b : Γ(reflexivePower F n, D)) :
    ∃ b' : Γ(reflexivePower F (n + 1), D),
      Scheme.Modules.Hom.app (reflexivePowerTransition F s n) D b = g • b' := by
  cases n with
  | zero =>
    refine ⟨(show Γ(X, D) from b) • e, ?_⟩
    rw [reflexivePowerTransition_zero]
    refine Eq.trans (unitHomEquiv_symm_app F s D (show Γ(X, D) from b)) ?_
    rw [show (show Γ(F, D) from s.eval (op D)) = g • e from hs]
    exact smul_comm (show Γ(X, D) from b) g e
  | succ n =>
    rw [reflexivePowerTransition_succ]
    refine ⟨Scheme.Modules.Hom.app (toDoubleDual _) D
      (tensorObjTmul X.toRingedSpace F (reflexivePower F (n + 1)) (op D) e b), ?_⟩
    have hmul : Scheme.Modules.Hom.app (mulSectionHom X.toRingedSpace (F.unitHomEquiv.symm s)
          (G := reflexivePower F (n + 1))) D b =
        tensorObjTmul X.toRingedSpace F (reflexivePower F (n + 1)) (op D) (g • e) b := by
      refine (mulSectionHom_app X.toRingedSpace (F.unitHomEquiv.symm s) (op D) b).trans ?_
      exact congrArg
        (fun z : Γ(F, D) =>
          tensorObjTmul X.toRingedSpace F (reflexivePower F (n + 1)) (op D) z b)
        ((unitHomEquiv_symm_app_unitSection F s D).trans hs)
    have hsm : tensorObjTmul X.toRingedSpace F (reflexivePower F (n + 1)) (op D) (g • e) b =
        g • tensorObjTmul X.toRingedSpace F (reflexivePower F (n + 1)) (op D) e b := by
      let : Module ↑Γ(X, D) ↑Γ(F, D) := (F.val.obj (op D)).isModule
      let : Module ↑Γ(X, D) ↑Γ(reflexivePower F (n + 1), D) :=
        ((reflexivePower F (n + 1)).val.obj (op D)).isModule
      have h3 : ((g • e) ⊗ₜ[↑Γ(X, D)] b) = g • (e ⊗ₜ[↑Γ(X, D)] b) :=
        (TensorProduct.smul_tmul' g e b).symm
      refine (congrArg (toTensorSheafSection X.toRingedSpace F (reflexivePower F (n + 1))
        (op D)) h3).trans ?_
      exact ((sheafifyUnit X.toRingedSpace _).app (op D)).hom.map_smul g _
    refine (congrArg (Scheme.Modules.Hom.app (toDoubleDual _) D) (hmul.trans hsm)).trans ?_
    exact Scheme.Modules.Hom.app_smul _ g _

/-- The image over `D` of the unit section of `𝒪_X` under the `k`-fold transition
`𝒪_X ⟶ ℱ^{[k]}`: the section `s^k` of `ℱ^{[k]}` over `D`. -/
def unitPower (D : X.Opens) (k : ℕ) : Γ(reflexivePower F k, D) :=
  Scheme.Modules.Hom.app ((reflexivePowerSystem F s).map (homOfLE (Nat.zero_le k))) D
    (unitSection X.toRingedSpace (op D) 1)

/-- The images of the unit section are related by the transition maps. -/
theorem unitPower_succ (D : X.Opens) (k : ℕ) :
    unitPower F s D (k + 1) =
      Scheme.Modules.Hom.app (reflexivePowerTransition F s k) D (unitPower F s D k) := by
  have h : (homOfLE (Nat.zero_le (k + 1)) : (0 : ℕ) ⟶ k + 1) =
      homOfLE (Nat.zero_le k) ≫ homOfLE (k.le_add_right 1) := rfl
  rw [unitPower, h, Functor.map_comp, reflexivePowerSystem_map_succ]
  rfl

/-- **On an open on which `s|_D = g e` the image of `1` in `ℱ^{[k]}` is divisible by `g^k`.** -/
theorem exists_unitPower_eq_pow_smul (D : X.Opens) (e : Γ(F, D)) (g : Γ(X, D))
    (hs : s.eval (op D) = g • e) (k : ℕ) :
    ∃ b : Γ(reflexivePower F k, D), unitPower F s D k = g ^ k • b := by
  induction k with
  | zero =>
    refine ⟨unitSection X.toRingedSpace (op D) 1, ?_⟩
    have h0 : unitPower F s D 0 = unitSection X.toRingedSpace (op D) 1 := by
      rw [unitPower]
      have h : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0) = 𝟙 0 := rfl
      rw [h, CategoryTheory.Functor.map_id]
      rfl
    refine h0.trans ?_
    rw [pow_zero]
    exact (one_smul _ _).symm
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨b', hb'⟩ := exists_transition_app_eq_smul F s k D e g hs b
    refine ⟨b', ?_⟩
    rw [unitPower_succ, hb, Scheme.Modules.Hom.app_smul, hb', smul_smul, pow_succ]

end Stacks.AlgebraicGeometry.ReflexivePowers

end
