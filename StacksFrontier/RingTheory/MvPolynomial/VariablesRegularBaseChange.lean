module

public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Flat.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Some variables of a polynomial ring, after a quotient and a flat base change

Let `B` be a ring identified with a polynomial ring `A[x_j, y_i]` over a ring `A`, by an
isomorphism compatible with `A`. For an ideal `I ⊆ A` and a flat `B`-algebra `S`, the images of
the variables `x_j` in `S / I S` form a weakly regular sequence. This is the local algebra behind
the statement that a linear subbundle of a vector bundle stays a regular immersion after
restricting the vector bundle to any closed subscheme of the base.

## Main results

* `MvPolynomial.isWeaklyRegular_ofFn_X_inl` — the variables indexed by the left summand of
  `Fin e ⊕ σ` form a weakly regular sequence.
* `MvPolynomial.isWeaklyRegular_quotient_ofFn_X_inl` — the main statement.
-/

@[expose] public section

open MvPolynomial RingTheory.Sequence TensorProduct

namespace MvPolynomial

/-- **The variables indexed by `Fin e` in `R[x_j, y_i]_{j : Fin e, i : σ}` form a weakly regular
sequence**, over any coefficient ring. -/
@[sga "6 VII 1.2" "partial"]
theorem isWeaklyRegular_ofFn_X_inl (R : Type*) [CommRing R] (e : ℕ) (σ : Type*) :
    IsWeaklyRegular (MvPolynomial (Fin e ⊕ σ) R)
      (List.ofFn fun j : Fin e => (X (Sum.inl j) : MvPolynomial (Fin e ⊕ σ) R)) := by
  cases e with
  | zero => simp
  | succ n =>
    have h := isWeaklyRegular_ofFn_X (R := MvPolynomial σ R) n
    have h' :=
      (Koszul.isWeaklyRegular_ringEquiv (sumAlgEquiv R (Fin (n + 1)) σ).symm.toRingEquiv _).mp h
    simpa [List.map_ofFn, Function.comp_def, sumAlgEquiv_symm_X] using h'

variable {A B S : Type*} [CommRing A] [CommRing B] [CommRing S] [Algebra B S]
  [Module.Flat B S] {e : ℕ} {σ : Type*}

/-- **Some variables of a polynomial ring stay weakly regular after a quotient by an ideal of the
coefficient ring and a flat base change.** Let `χ : B ≃ A[x_j, y_i]` be an isomorphism of rings
under which `ψ : A → B` is the inclusion of constants, `I ⊆ A` an ideal and `S` a flat
`B`-algebra. Then the images in `S / I S` of the elements of `B` corresponding to the variables
`x_j` form a weakly regular sequence. -/
@[sga "6 VII 1.2" "partial"]
theorem isWeaklyRegular_quotient_ofFn_X_inl (χ : B ≃+* MvPolynomial (Fin e ⊕ σ) A)
    (ψ : A →+* B) (hψ : ∀ a, χ (ψ a) = C a) (I : Ideal A) :
    IsWeaklyRegular (S ⧸ ((I.map ψ).map (algebraMap B S)))
      (List.ofFn fun j : Fin e => Ideal.Quotient.mk ((I.map ψ).map (algebraMap B S))
        (algebraMap B S (χ.symm (X (Sum.inl j))))) := by
  set J := I.map ψ with hJ
  -- `B / J` is a polynomial ring over `A / I`
  have hJχ : J.map (χ : B →+* MvPolynomial (Fin e ⊕ σ) A) = I.map C := by
    rw [hJ, Ideal.map_map]
    congr 1
    exact RingHom.ext hψ
  let χ' : B ⧸ J ≃+* MvPolynomial (Fin e ⊕ σ) (A ⧸ I) :=
    (Ideal.quotientEquiv J (I.map C) χ hJχ.symm).trans
      (quotientEquivQuotientMvPolynomial I).symm.toRingEquiv
  have hχ' : ∀ j, χ'.symm (X (Sum.inl j)) = Ideal.Quotient.mk J (χ.symm (X (Sum.inl j))) := by
    intro j
    apply χ'.injective
    rw [RingEquiv.apply_symm_apply]
    have h1 : Ideal.quotientEquiv J (I.map C) χ hJχ.symm
        (Ideal.Quotient.mk J (χ.symm (X (Sum.inl j)))) =
          Ideal.Quotient.mk (I.map C) (X (Sum.inl j)) := by
      rw [Ideal.quotientEquiv_apply]
      exact Ideal.quotientMap_mk.trans (by rw [RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply])
    have h2 : quotientEquivQuotientMvPolynomial (σ := Fin e ⊕ σ) I (X (Sum.inl j)) =
        Ideal.Quotient.mk (I.map C) (X (Sum.inl j)) := by
      simp [quotientEquivQuotientMvPolynomial]
    change _ = (quotientEquivQuotientMvPolynomial I).symm
      (Ideal.quotientEquiv J (I.map C) χ hJχ.symm (Ideal.Quotient.mk J _))
    rw [h1, ← h2, AlgEquiv.symm_apply_apply]
  -- weak regularity in `B / J`, as a ring and then over `B`
  have h1 :=
    (Koszul.isWeaklyRegular_ringEquiv χ'.symm _).mp (isWeaklyRegular_ofFn_X_inl (A ⧸ I) e σ)
  rw [List.map_ofFn] at h1
  simp only [Function.comp_def, hχ'] at h1
  have h2 : IsWeaklyRegular (B ⧸ J) (List.ofFn fun j : Fin e => χ.symm (X (Sum.inl j))) := by
    rwa [← isWeaklyRegular_map_algebraMap_iff (S := B ⧸ J), List.map_ofFn]
  -- flat base change to `S`
  have h3 : IsWeaklyRegular (S ⊗[B] (B ⧸ J)) _ := h2.isWeaklyRegular_lTensor
  have e1 : S ⊗[B] (B ⧸ J) ≃ₗ[B] S ⧸ J.map (algebraMap B S) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm.toLinearEquiv).restrictScalars B
  have h4 := (e1.isWeaklyRegular_congr _).mp h3
  rwa [← isWeaklyRegular_map_algebraMap_iff (S := S ⧸ J.map (algebraMap B S)), List.map_ofFn]
    at h4

end MvPolynomial
