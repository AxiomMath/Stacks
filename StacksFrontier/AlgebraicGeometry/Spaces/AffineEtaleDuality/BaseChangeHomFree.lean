module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.BaseChangeHom
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.Int.Interval

/-!
# The base-change map of Hom complexes out of a finite free complex

For a complex `Q` of finite free `A`-modules and a bounded complex `I`, the base-change map
`θ : R ⊗_A Hom^•_A(Q, I) ⟶ Hom^•_A(Q, R ⊗_A I)` is an isomorphism in every degree. In a fixed
degree only finitely many terms of the Hom complex are nonzero, because `I` is bounded, and on
each of them the map is `R ⊗_A Hom_A(M, N) ⟶ Hom_A(M, R ⊗_A N)` for a finite free `M`, which is
bijective: a basis of `M` identifies both sides with `(R ⊗_A N)^ι`.

## Main results

* `Stacks.FlatBaseChangeHom.bijective_thetaHom`: the comparison for a finite free module.
* `Stacks.FlatBaseChangeHom.bijective_theta_f`: `θ` is bijective in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex TensorProduct

universe u

namespace Stacks.FlatBaseChangeHom

variable {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)

/-- The map `f ↦ b · (1 ⊗ f)`, for `b ∈ R`. -/
def thetaHomAt (b : R) (M N : ModuleCat.{u} A) : (M ⟶ N) →ₗ[A] (M ⟶ (RE ρ).obj N) where
  toFun f := f ≫ (unitRE ρ).app N ≫ mulApp ρ b N
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Linear.smul_comp _ _ _ _ _ _

/-- `thetaHomAt` is additive in the scalar `b`. -/
lemma thetaHomAt_add (b b' : R) (M N : ModuleCat.{u} A) :
    thetaHomAt ρ (b + b') M N = thetaHomAt ρ b M N + thetaHomAt ρ b' M N := by
  ext f : 1
  change f ≫ _ ≫ mulApp ρ (b + b') N = f ≫ _ ≫ mulApp ρ b N + f ≫ _ ≫ mulApp ρ b' N
  rw [mulApp_add, Preadditive.comp_add, Preadditive.comp_add]

/-- `thetaHomAt` at `ρ a * b` is `a` times `thetaHomAt` at `b`. -/
lemma thetaHomAt_smul (a : A) (b : R) (M N : ModuleCat.{u} A) :
    thetaHomAt ρ (ρ a * b) M N = a • thetaHomAt ρ b M N := by
  ext f : 1
  change f ≫ _ ≫ mulApp ρ (ρ a * b) N = a • (f ≫ _ ≫ mulApp ρ b N)
  rw [mulApp_mul, mulApp_algebraMap, Linear.comp_smul, Category.comp_id, Linear.comp_smul,
    Linear.comp_smul]

/-- The comparison `R ⊗_A Hom_A(M, N) ⟶ Hom_A(M, R ⊗_A N)`, `b ⊗ f ↦ b · (1 ⊗ f)`. -/
def thetaHom (M N : ModuleCat.{u} A) : RR ρ ⊗[A] (M ⟶ N) →ₗ[A] (M ⟶ (RE ρ).obj N) :=
  TensorProduct.lift
    { toFun := fun b => thetaHomAt ρ b M N
      map_add' := fun b b' => thetaHomAt_add ρ b b' M N
      map_smul' := fun a b => thetaHomAt_smul ρ a b M N }

/-- `thetaHom` sends `b ⊗ f` to `b · (1 ⊗ f)`. -/
lemma thetaHom_tmul (M N : ModuleCat.{u} A) (b : R) (f : M ⟶ N) :
    thetaHom ρ M N ((b : RR ρ) ⊗ₜ f) = f ≫ (unitRE ρ).app N ≫ mulApp ρ b N := rfl

/-- **For a finite free `M`, `R ⊗_A Hom_A(M, N) ⟶ Hom_A(M, R ⊗_A N)` is bijective.** -/
lemma bijective_thetaHom (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Free A M] :
    Function.Bijective (thetaHom ρ M N) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A M
  let bM : Module.Basis ι A M := Module.Free.chooseBasis A M
  let e₁ : (M ⟶ N) ≃ₗ[A] (ι → N) := ModuleCat.homLinearEquiv.trans (bM.constr A).symm
  let e₂ : (M ⟶ (RE ρ).obj N) ≃ₗ[A] (ι → (RE ρ).obj N) :=
    ModuleCat.homLinearEquiv.trans (bM.constr A).symm
  let π := TensorProduct.piRight A A (RR ρ) (fun _ : ι => (N : Type u))
  let c : (ι → RR ρ ⊗[A] N) → (ι → (RE ρ).obj N) := fun v i => v i
  have key : ∀ x, e₂ (thetaHom ρ M N x) = c (π (LinearMap.lTensor (RR ρ) e₁.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b f =>
      funext i
      change (mulApp ρ (b : R) N).hom ((unitRE ρ).app N (f.hom (bM i))) =
        π ((b : RR ρ) ⊗ₜ[A] e₁ f) i
      rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
        ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      exact (ModuleCat.ExtendScalars.smul_tmul ρ (b : R) 1 _).trans
        (congrArg (fun r : R => TensorProduct.tmul A (M := RR ρ) (N := N) r (f.hom (bM i)))
          (mul_one (M := R) b))
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add]
      rfl
  have hfac : (thetaHom ρ M N : _ → _) =
      e₂.symm ∘ c ∘ π ∘ LinearMap.lTensor (RR ρ) e₁.toLinearMap := by
    funext x
    exact (e₂.symm_apply_eq.mpr (key x).symm).symm
  rw [hfac]
  exact e₂.symm.bijective.comp <| Function.Bijective.comp
    (⟨fun _ _ h => h, fun w => ⟨w, rfl⟩⟩ : Function.Bijective c)
    (π.bijective.comp (LinearEquiv.lTensor (RR ρ) e₁).bijective)

/-! ### Cochains into a complex supported on a finite window -/

section Window

variable {K L : CochainComplex (ModuleCat.{u} A) ℤ}

/-- The components of a degree-`n` cochain at the source degrees in a finite set `S`. -/
def resCochain (S : Finset ℤ) (n : ℤ) :
    Cochain K L n →ₗ[A] (∀ p : S, K.X p ⟶ L.X ((p : ℤ) + n)) where
  toFun z p := z.v p (p + n) rfl
  map_add' z z' := funext fun _ => Cochain.add_v z z' _ _ _
  map_smul' a z := funext fun _ => Cochain.smul_v a z _ _ _

/-- The component of `resCochain S n z` at `p ∈ S` is the component `z.v p (p + n)`. -/
lemma resCochain_apply (S : Finset ℤ) (n : ℤ) (z : Cochain K L n) (p : S) :
    resCochain S n z p = z.v p (p + n) rfl := rfl

/-- `resCochain`, on the terms of the `A`-module Hom complex. -/
def resCochainR (S : Finset ℤ) (n : ℤ) :
    (CochainComplex.HomComplexR A K L).X n →ₗ[A] (∀ p : S, K.X p ⟶ L.X ((p : ℤ) + n)) :=
  resCochain S n

/-- **A cochain into a complex vanishing outside `S + n` is determined by its components at the
degrees in `S`, and these can be prescribed freely.** -/
lemma bijective_resCochain (S : Finset ℤ) (n : ℤ)
    (hS : ∀ p, p ∉ S → IsZero (L.X (p + n))) :
    Function.Bijective (resCochain (K := K) (L := L) S n) := by
  classical
  refine ⟨fun z z' h => Cochain.ext _ _ fun p q hpq => ?_, fun w => ⟨Cochain.mk fun p q hpq =>
    if hp : p ∈ S then w ⟨p, hp⟩ ≫ eqToHom (congrArg L.X hpq) else 0, ?_⟩⟩
  · subst hpq
    by_cases hp : p ∈ S
    · exact congrFun h ⟨p, hp⟩
    · exact (hS p hp).eq_of_tgt _ _
  · funext p
    rw [resCochain_apply, Cochain.mk_v, dite_eq_left p.2, eqToHom_refl, Category.comp_id]

end Window

/-! ### The base-change map out of a finite free complex -/

variable (Q I : CochainComplex (ModuleCat.{u} A) ℤ)

/-- `θ` commutes with taking components at the degrees in a finite set. -/
lemma resCochain_thetaLin (S : Finset ℤ) (n : ℤ) (p : S) :
    (LinearMap.proj p ∘ₗ resCochain (K := Q) (L := REc ρ I) S n) ∘ₗ thetaLin ρ Q I n =
      thetaHom ρ (Q.X p) (I.X ((p : ℤ) + n)) ∘ₗ LinearMap.proj p ∘ₗ
        (TensorProduct.piRight A A (RR ρ)
          (fun p : S => (Q.X p ⟶ I.X ((p : ℤ) + n)))).toLinearMap ∘ₗ
        LinearMap.lTensor (RR ρ) (resCochainR S n) := by
  classical
  refine TensorProduct.ext' (fun b c => ?_)
  change (thetaCochain ρ Q I b c).v p (p + n) rfl = thetaHom ρ _ _
    (TensorProduct.piRight A A (RR ρ) (fun p : S => (Q.X p ⟶ I.X ((p : ℤ) + n)))
      (b ⊗ₜ resCochainR S n c) p)
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  exact thetaCochain_v ρ Q I b c p (p + n) rfl

/-- **For a complex `Q` of finite free modules and a complex `I` vanishing outside the finite
window `S + n`, the base-change map `θ` is bijective in degree `n`.** -/
lemma bijective_thetaLin_of_window (n : ℤ) (S : Finset ℤ)
    (hQ : ∀ p, Module.Finite A (Q.X p) ∧ Module.Free A (Q.X p))
    (hS : ∀ p, p ∉ S → IsZero (I.X (p + n))) :
    Function.Bijective (thetaLin ρ Q I n) := by
  classical
  let r₁ := LinearEquiv.ofBijective (resCochainR (K := Q) (L := I) S n)
    (bijective_resCochain S n hS)
  let π := TensorProduct.piRight A A (RR ρ) (fun p : S => (Q.X p ⟶ I.X ((p : ℤ) + n)))
  let Θ : (∀ p : S, RR ρ ⊗[A] (Q.X p ⟶ I.X ((p : ℤ) + n))) →
      (∀ p : S, Q.X p ⟶ (RE ρ).obj (I.X ((p : ℤ) + n))) :=
    fun v p => thetaHom ρ (Q.X p) (I.X ((p : ℤ) + n)) (v p)
  have hΘ : Function.Bijective Θ := by
    have := fun p : S => (hQ p).1
    have := fun p : S => (hQ p).2
    let e : ∀ p : S, RR ρ ⊗[A] (Q.X p ⟶ I.X ((p : ℤ) + n)) ≃
        (Q.X p ⟶ (RE ρ).obj (I.X ((p : ℤ) + n))) :=
      fun p => Equiv.ofBijective _ (bijective_thetaHom ρ (Q.X p) (I.X ((p : ℤ) + n)))
    exact (Equiv.piCongrRight e).bijective
  have hfac : (resCochain (K := Q) (L := REc ρ I) S n) ∘ (thetaLin ρ Q I n) =
      Θ ∘ π ∘ LinearMap.lTensor (RR ρ) r₁.toLinearMap := by
    funext x p
    exact LinearMap.congr_fun (resCochain_thetaLin ρ Q I S n p) x
  refine (Function.Bijective.of_comp_iff' (bijective_resCochain (K := Q) (L := REc ρ I) S n
    fun p hp => (RE ρ).map_isZero (hS p hp)) _).mp ?_
  rw [hfac]
  exact hΘ.comp (π.bijective.comp (LinearEquiv.lTensor (RR ρ) r₁).bijective)

/-- **`θ` is bijective in every degree** for a complex `Q` of finite free modules and a bounded
complex `I`. -/
lemma bijective_theta_f (a b : ℤ) [I.IsStrictlyGE a] [I.IsStrictlyLE b]
    (hQ : ∀ p, Module.Finite A (Q.X p) ∧ Module.Free A (Q.X p)) (n : ℤ) :
    Function.Bijective ((theta ρ Q I).f n) := by
  refine bijective_thetaLin_of_window ρ Q I n (Finset.Icc (a - n) (b - n)) hQ (fun p hp => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hp
  rcases hp with hp | hp
  · exact I.isZero_of_isStrictlyGE a _ (by omega)
  · exact I.isZero_of_isStrictlyLE b _ (by omega)

end Stacks.FlatBaseChangeHom

end
