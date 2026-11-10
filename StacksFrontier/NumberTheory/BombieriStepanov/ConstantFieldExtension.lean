module

public import StacksFrontier.NumberTheory.BombieriStepanov.ConstantExtension
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Fixed

/-!
# The constant field extension `L ⊗_E E₁`

Let `E ⊆ L` be fields with `E` algebraically closed in `L`, and let `E₁/E` be a finite separable
extension with a primitive element `θ` of minimal polynomial `g`. Since `g` stays irreducible over
`L` (`Stacks.BombieriStepanov.irreducible_map_of_forall_isIntegral`), `L₁ = L[X]/(g)` is a field:
the constant field extension of `L` by `E₁`. This file records its structure.

* `E₁` embeds into `L₁` over `E`, `θ` going to the root (`Stacks.BombieriStepanov.constJ`).
* A ring automorphism `σ` of `L` fixing `E` extends to `L₁` fixing `E₁`
  (`Stacks.BombieriStepanov.liftRingEquiv`).
* Every automorphism `τ` of `E₁/E` extends to an automorphism of `L₁/L`
  (`Stacks.BombieriStepanov.galoisOfAut`), so for finite `E₁` the extension `L₁/L` is Galois with
  group acting faithfully on `E₁`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.BombieriStepanov

variable {E L E₁ : Type*} [Field E] [Field L] [Algebra E L] [Field E₁] [Algebra E E₁]
  (pb : PowerBasis E E₁)

/-- The polynomial defining the constant field extension. -/
abbrev constPoly (L : Type*) [Field L] [Algebra E L] : L[X] :=
  (minpoly E pb.gen).map (algebraMap E L)

/-- Two ring homomorphisms out of `AdjoinRoot f` agreeing on the coefficients and the root are
equal. -/
theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [CommRing S] {f : R[X]}
    {φ ψ : AdjoinRoot f →+* S} (h₁ : ∀ r, φ (AdjoinRoot.of f r) = ψ (AdjoinRoot.of f r))
    (h₂ : φ (AdjoinRoot.root f) = ψ (AdjoinRoot.root f)) : φ = ψ := by
  have : φ.comp (AdjoinRoot.mk f) = ψ.comp (AdjoinRoot.mk f) :=
    Polynomial.ringHom_ext (fun r => h₁ r) h₂
  exact Ideal.Quotient.ringHom_ext this

/-- The embedding `E₁ → L₁` over `E`, sending the primitive element to the root. -/
def constJ : E₁ →ₐ[E] AdjoinRoot (constPoly pb L) :=
  pb.lift (AdjoinRoot.root _) (by
    rw [aeval_def, IsScalarTower.algebraMap_eq E L (AdjoinRoot (constPoly pb L)), ← eval₂_map]
    exact AdjoinRoot.eval₂_root _)

/-- The embedding `constJ` sends the primitive element to the root. -/
theorem constJ_gen : constJ (L := L) pb pb.gen = AdjoinRoot.root _ :=
  pb.lift_gen _ _

/-- For a ring automorphism `τ` of `L` fixing `E`, the root is a root of `constPoly pb L` after
twisting the coefficients by `τ`. -/
theorem eval₂_constPoly_root (τ : L ≃+* L)
    (hτ : ∀ e : E, τ (algebraMap E L e) = algebraMap E L e) :
    (constPoly pb L).eval₂ ((AdjoinRoot.of (constPoly pb L)).comp (τ : L →+* L))
      (AdjoinRoot.root _) = 0 := by
  rw [eval₂_map, RingHom.comp_assoc,
    show (τ : L →+* L).comp (algebraMap E L) = algebraMap E L from RingHom.ext hτ,
    ← eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- The inverse of a ring automorphism of `L` fixing `E` also fixes `E`. -/
theorem symm_algebraMap_eq (σ : L ≃+* L)
    (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e) (e : E) :
    σ.symm (algebraMap E L e) = algebraMap E L e := by
  rw [RingEquiv.symm_apply_eq, hσ]

/-- **Extending an automorphism to the constant field extension.** A ring automorphism `σ` of
`L` fixing `E` extends to `L₁` with the root fixed. -/
def liftRingEquiv (σ : L ≃+* L) (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e) :
    AdjoinRoot (constPoly pb L) ≃+* AdjoinRoot (constPoly pb L) where
  toFun := AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ hσ)
  invFun := AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ.symm (symm_algebraMap_eq σ hσ))
  left_inv := fun z => by
    have : (AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ.symm (symm_algebraMap_eq σ hσ))).comp
        (AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ hσ)) = RingHom.id _ :=
      adjoinRoot_ringHom_ext (fun r => by simp [AdjoinRoot.lift_of])
        (by simp [AdjoinRoot.lift_root])
    exact congrArg (fun F : AdjoinRoot (constPoly pb L) →+* _ => F z) this
  right_inv := fun z => by
    have : (AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ hσ)).comp
        (AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ.symm (symm_algebraMap_eq σ hσ))) =
          RingHom.id _ :=
      adjoinRoot_ringHom_ext (fun r => by simp [AdjoinRoot.lift_of])
        (by simp [AdjoinRoot.lift_root])
    exact congrArg (fun F : AdjoinRoot (constPoly pb L) →+* _ => F z) this
  map_mul' := map_mul _
  map_add' := map_add _

/-- `liftRingEquiv pb σ hσ` is the lift of `σ` sending the root to itself. -/
theorem liftRingEquiv_apply (σ : L ≃+* L) (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e)
    (z : AdjoinRoot (constPoly pb L)) :
    liftRingEquiv pb σ hσ z = AdjoinRoot.lift _ _ (eval₂_constPoly_root pb σ hσ) z := rfl

/-- The extension of `σ` acts as `σ` on `L`. -/
theorem liftRingEquiv_of (σ : L ≃+* L) (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e)
    (l : L) : liftRingEquiv pb σ hσ (AdjoinRoot.of _ l) = AdjoinRoot.of _ (σ l) := by
  rw [liftRingEquiv_apply, AdjoinRoot.lift_of]
  rfl

/-- The extension of `σ` fixes the root. -/
theorem liftRingEquiv_root (σ : L ≃+* L) (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e) :
    liftRingEquiv pb σ hσ (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [liftRingEquiv_apply, AdjoinRoot.lift_root]

/-- Two `E`-algebra maps out of `E₁` that agree on the primitive element agree everywhere. -/
private theorem apply_eq_of_apply_gen_eq {A : Type*} [Semiring A] [Algebra E A]
    (f g : E₁ →ₐ[E] A) (h : f pb.gen = g pb.gen) (e : E₁) : f e = g e :=
  DFunLike.congr_fun (pb.algHom_ext h) e

/-- The extension of `σ` fixes the constants `E₁`. -/
theorem liftRingEquiv_constJ (σ : L ≃+* L)
    (hσ : ∀ e : E, σ (algebraMap E L e) = algebraMap E L e) (e₁ : E₁) :
    liftRingEquiv pb σ hσ (constJ pb e₁) = constJ pb e₁ := by
  let τ : E₁ →ₐ[E] AdjoinRoot (constPoly pb L) :=
    { ((liftRingEquiv pb σ hσ : AdjoinRoot (constPoly pb L) ≃+* AdjoinRoot (constPoly pb L)) :
          AdjoinRoot (constPoly pb L) →+* AdjoinRoot (constPoly pb L)).comp
        ((constJ (L := L) pb : E₁ →ₐ[E] AdjoinRoot (constPoly pb L)) :
          E₁ →+* AdjoinRoot (constPoly pb L)) with
      commutes' := fun e => by
        change liftRingEquiv pb σ hσ (constJ pb (algebraMap E E₁ e)) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E L (AdjoinRoot (constPoly pb L)) e,
          AdjoinRoot.algebraMap_eq, liftRingEquiv_of, hσ] }
  exact apply_eq_of_apply_gen_eq pb τ (constJ pb) (by
    change liftRingEquiv pb σ hσ (constJ pb pb.gen) = constJ pb pb.gen
    rw [constJ_gen, liftRingEquiv_root]) e₁

section Galois

variable [Fact (Irreducible (constPoly pb L))]

/-- The constant field extension `L₁` is finite-dimensional over `L`. -/
instance : FiniteDimensional L (AdjoinRoot (constPoly pb L)) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible (constPoly pb L)).ne_zero).finite

/-- For an `E`-algebra endomorphism `τ` of `E₁`, the image of `τ θ` in `L₁` is a root of
`constPoly pb L`. -/
theorem aeval_constJ_eq_zero (τ : E₁ →ₐ[E] E₁) :
    (constPoly pb L).eval₂ (algebraMap L (AdjoinRoot (constPoly pb L))) (constJ pb (τ pb.gen)) =
      0 := by
  rw [eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def, aeval_algHom_apply,
    aeval_algHom_apply, minpoly.aeval, map_zero, map_zero]

/-- **An automorphism of `E₁/E` extends to `L₁/L`.** -/
def galoisOfAut (τ : E₁ →ₐ[E] E₁) :
    AdjoinRoot (constPoly pb L) ≃ₐ[L] AdjoinRoot (constPoly pb L) :=
  AlgEquiv.ofBijective (AdjoinRoot.liftAlgHom _ (Algebra.ofId L _) (constJ pb (τ pb.gen))
    (aeval_constJ_eq_zero pb τ)) (AlgHom.bijective _)

/-- The extension `galoisOfAut pb τ` restricts to `τ` on the constants `E₁`. -/
theorem galoisOfAut_constJ (τ : E₁ →ₐ[E] E₁) (e : E₁) :
    galoisOfAut (L := L) pb τ (constJ pb e) = constJ pb (τ e) := by
  exact apply_eq_of_apply_gen_eq pb
    (((galoisOfAut (L := L) pb τ).toAlgHom.restrictScalars E).comp (constJ pb))
    ((constJ pb).comp τ) (by
    change galoisOfAut (L := L) pb τ (constJ pb pb.gen) = constJ pb (τ pb.gen)
    rw [constJ_gen]
    exact AdjoinRoot.liftAlgHom_root (constPoly pb L) (Algebra.ofId L _) (constJ pb (τ pb.gen))
      (aeval_constJ_eq_zero pb τ)) e

/-- An automorphism of `L₁/L` fixing the constants `E₁` is the identity. -/
theorem eq_one_of_forall_constJ (γ : AdjoinRoot (constPoly pb L) ≃ₐ[L] AdjoinRoot (constPoly pb L))
    (hγ : ∀ e : E₁, γ (constJ pb e) = constJ pb e) : γ = 1 := by
  have : (γ : AdjoinRoot (constPoly pb L) →ₐ[L] _) = AlgHom.id L _ :=
    AdjoinRoot.algHom_ext (by
      change γ (AdjoinRoot.root _) = AdjoinRoot.root _
      rw [← constJ_gen pb, hγ])
  ext z
  exact congrArg (fun F : AdjoinRoot (constPoly pb L) →ₐ[L] _ => F z) this

/-- **The constant field extension by a finite field is Galois.** -/
theorem isGalois_constPoly [Finite E₁] : IsGalois L (AdjoinRoot (constPoly pb L)) := by
  have hinj : Function.Injective (fun τ : E₁ ≃ₐ[E] E₁ => galoisOfAut (L := L) pb τ.toAlgHom) := by
    intro τ τ' h
    ext e
    have := congrArg (fun γ : AdjoinRoot (constPoly pb L) ≃ₐ[L] _ => γ (constJ pb e)) h
    simp only [galoisOfAut_constJ] at this
    exact (constJ pb).injective this
  have hfin : Module.finrank L (AdjoinRoot (constPoly pb L)) = Module.finrank E E₁ := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible (constPoly pb L)).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_map, pb.natDegree_minpoly, pb.finrank]
  have : FiniteDimensional E E₁ := pb.finite
  refine IsGalois.of_card_aut_eq_finrank _ _ (le_antisymm ?_ ?_)
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [hfin, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_le_card_of_injective _ hinj

end Galois

end Stacks.BombieriStepanov

end
