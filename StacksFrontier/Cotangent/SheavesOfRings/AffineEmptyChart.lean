module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The affine space with no variables

For a commutative ring `Λ`, the polynomial ring `Λ[∅]` in no variables is `Λ` itself, so the
arrow `Spec Λ[∅] ⟶ Spec Λ` induced by the constants is an isomorphism, with inverse the arrow
induced by evaluation. For an arbitrary index type `σ`, the constants of `Λ[σ]` factor through
`Λ[∅]`.

All names are in the namespace `AlgebraicGeometry.AffineEmptyChart`.

## Main definitions

* `specEmptyConstants`: the arrow `Spec Λ[∅] ⟶ Spec Λ` induced by the constants.
* `specEmptyEval`: the arrow `Spec Λ ⟶ Spec Λ[∅]` induced by evaluation.
* `specEmptyToVariables`: the arrow `Spec Λ[σ] ⟶ Spec Λ[∅]` induced by the constants.

## Main results

* `specEmptyEval_comp_specEmptyConstants` and `specEmptyConstants_comp_specEmptyEval`: the two
  arrows are mutually inverse.
* `mono_specEmptyConstants`: the arrow induced by the constants is a monomorphism.
* `specEmptyToVariables_comp_specEmptyConstants`: the factorisation of the constants of `Λ[σ]`
  through `Λ[∅]`.

## Implementation notes

The universe of the empty index type is independent of the universe of `Λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineEmptyChart

universe u

variable (Λ : Type u) [CommRing Λ]

/-- Evaluation of a polynomial in no variables, as a ring map `Λ[∅] →+* Λ`. -/
public def emptyEval : MvPolynomial PEmpty Λ →+* Λ :=
  (MvPolynomial.isEmptyRingEquiv Λ PEmpty).toRingHom

/-- The morphism `Spec Λ ⟶ Spec Λ[∅]` inverse to the one induced by the constants. -/
public def specEmptyEval :
    Spec (CommRingCat.of Λ) ⟶ Spec (CommRingCat.of (MvPolynomial PEmpty Λ)) :=
  Scheme.Spec.map (CommRingCat.ofHom (emptyEval Λ)).op

/-- The structural arrow of the affine space with no variables, `Spec Λ[∅] ⟶ Spec Λ`. -/
public def specEmptyConstants :
    Spec (CommRingCat.of (MvPolynomial PEmpty Λ)) ⟶ Spec (CommRingCat.of Λ) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : Λ →+* MvPolynomial PEmpty Λ)).op

/-- Evaluation of a constant polynomial in no variables gives back the constant. -/
private theorem emptyEval_C (x : Λ) : emptyEval Λ (MvPolynomial.C x) = x := by
  rw [← MvPolynomial.isEmptyRingEquiv_symm_apply Λ PEmpty x]
  exact RingEquiv.apply_symm_apply _ x

/-- Every polynomial in no variables is the constant given by its evaluation. -/
private theorem C_emptyEval (p : MvPolynomial PEmpty Λ) :
    MvPolynomial.C (emptyEval Λ p) = p := by
  rw [← MvPolynomial.isEmptyRingEquiv_symm_apply Λ PEmpty]
  exact RingEquiv.symm_apply_apply _ p

/-- Evaluation followed by the constants is the identity of `Spec Λ`. -/
public theorem specEmptyEval_comp_specEmptyConstants :
    specEmptyEval Λ ≫ specEmptyConstants Λ = 𝟙 (Spec (CommRingCat.of Λ)) := by
  have hring : CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial PEmpty Λ) ≫
      CommRingCat.ofHom (emptyEval Λ) = 𝟙 _ := by
    ext x
    exact emptyEval_C Λ x
  rw [specEmptyEval, specEmptyConstants, ← Scheme.Spec.map_comp, ← op_comp, hring, op_id,
    Scheme.Spec.map_id]
  rfl

/-- The constants followed by evaluation is the identity of `Spec Λ[∅]`. -/
public theorem specEmptyConstants_comp_specEmptyEval :
    specEmptyConstants Λ ≫ specEmptyEval Λ =
      𝟙 (Spec (CommRingCat.of (MvPolynomial PEmpty Λ))) := by
  have hring : CommRingCat.ofHom (emptyEval Λ) ≫
      CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial PEmpty Λ) = 𝟙 _ := by
    exact CommRingCat.hom_ext (RingHom.ext (C_emptyEval Λ))
  rw [specEmptyConstants, specEmptyEval, ← Scheme.Spec.map_comp, ← op_comp, hring, op_id,
    Scheme.Spec.map_id]
  rfl

/-- The arrow `Spec Λ[∅] ⟶ Spec Λ` induced by the constants is a monomorphism. -/
public instance mono_specEmptyConstants : Mono (specEmptyConstants Λ) :=
  mono_of_mono_fac (specEmptyConstants_comp_specEmptyEval Λ)

/-- The ring map `Λ[∅] →+* Λ[σ]` through the constants. -/
public def emptyToVariables {σ : Type u} : MvPolynomial PEmpty Λ →+* MvPolynomial σ Λ :=
  (MvPolynomial.C : Λ →+* MvPolynomial σ Λ).comp (emptyEval Λ)

/-- The induced morphism `Spec Λ[σ] ⟶ Spec Λ[∅]` of affine spaces. -/
public def specEmptyToVariables {σ : Type u} :
    Spec (CommRingCat.of (MvPolynomial σ Λ)) ⟶
      Spec (CommRingCat.of (MvPolynomial PEmpty Λ)) :=
  Scheme.Spec.map (CommRingCat.ofHom (emptyToVariables (Λ := Λ) (σ := σ))).op

/-- The constants `Λ →+* Λ[∅]` followed by `Λ[∅] →+* Λ[σ]` are the constants of `Λ[σ]`. -/
public theorem emptyToVariables_comp_constants (σ : Type u) :
    CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial PEmpty Λ) ≫
      CommRingCat.ofHom (emptyToVariables (Λ := Λ) (σ := σ)) =
        CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial σ Λ) := by
  rw [← CommRingCat.ofHom_comp]
  refine congrArg CommRingCat.ofHom (RingHom.ext fun x => ?_)
  exact congrArg MvPolynomial.C (emptyEval_C Λ x)

/-- The arrow `Spec Λ[σ] ⟶ Spec Λ[∅]` followed by `Spec Λ[∅] ⟶ Spec Λ` is the arrow induced by the
constants of `Λ[σ]`. -/
public theorem specEmptyToVariables_comp_specEmptyConstants (σ : Type u) :
    specEmptyToVariables (Λ := Λ) (σ := σ) ≫ specEmptyConstants Λ =
      Scheme.Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Λ →+* MvPolynomial σ Λ)).op := by
  rw [specEmptyToVariables, specEmptyConstants, ← Scheme.Spec.map_comp, ← op_comp,
    emptyToVariables_comp_constants]

end AlgebraicGeometry.AffineEmptyChart

end
