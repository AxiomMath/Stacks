module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The first naive cotangent homology of a surjection is its conormal module

Let `A → B` be a surjective ring map with kernel `I := RingHom.ker (algebraMap A B)`. The first
homology `Algebra.H1Cotangent A B` of the naive cotangent complex is `A`-linearly isomorphic to the
conormal module `I/I² = I.Cotangent`.

## Main definitions

* `kerIdeal`: the kernel ideal `RingHom.ker (algebraMap A B)`.
* `h1Cotangent_equiv_cotangent_of_surjective`: the `A`-linear isomorphism
  `Algebra.H1Cotangent A B ≃ₗ[A] I.Cotangent` for a surjective `algebraMap A B`.

## Main results

* `h1Cotangent_self_equiv_ofSurjective`: `Algebra.H1Cotangent A B` is `B`-linearly isomorphic to
  the first homology of the extension `Algebra.Extension.ofSurjective (Algebra.ofId A B) h`.
* `ofSurjective_h1Cotangent_equiv_cotangent`: the first homology of that extension is `A`-linearly
  isomorphic to `I.Cotangent`.
* `h1Cotangent_nonempty_equiv_cotangent_of_surjective`: there is an `A`-linear isomorphism
  `Algebra.H1Cotangent A B ≃ₗ[A] I.Cotangent`.
-/

@[expose] public section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The kernel ideal `I := ker (algebraMap A B)`. -/
abbrev kerIdeal : Ideal A := RingHom.ker (algebraMap A B)

set_option backward.isDefEq.respectTransparency false in
/-- For a surjective `algebraMap A B`, the first homology `Algebra.H1Cotangent A B` of the naive
cotangent complex is `B`-linearly isomorphic to the first homology of the extension
`Algebra.Extension.ofSurjective (Algebra.ofId A B) h`, whose ring is `A`. -/
theorem h1Cotangent_self_equiv_ofSurjective
    (h : Function.Surjective (algebraMap A B)) :
    Nonempty (Algebra.H1Cotangent A B ≃ₗ[B]
      (Algebra.Extension.ofSurjective (Algebra.ofId A B) h).H1Cotangent) := by
  set P₀ := Algebra.Extension.ofSurjective (Algebra.ofId A B) h
  let P₁ := (Algebra.Generators.self A B).toExtension
  have f₁ : P₁.Hom P₀ := by
    refine ⟨(MvPolynomial.aeval (fun b ↦ Function.surjInv h b) : P₁.Ring →ₐ[A] A).toRingHom,
      ?_, ?_⟩
    · intro x
      change (MvPolynomial.aeval (fun b ↦ Function.surjInv h b))
        ((algebraMap A (MvPolynomial B A)) x) = _
      simp only [Algebra.algebraMap_self, MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C,
        RingHom.id_apply]
      rfl
    · intro x
      change (algebraMap A B) ((MvPolynomial.aeval (fun b ↦ Function.surjInv h b)) x)
        = (algebraMap B B) ((MvPolynomial.aeval (R := A) (S₁ := B) (fun b ↦ b)) x)
      rw [Algebra.algebraMap_self, RingHom.id_apply]
      refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun a ↦ ?_) fun b ↦ ?_ :
        (algebraMap A B).comp ((MvPolynomial.aeval (fun b ↦ Function.surjInv h b) :
          MvPolynomial B A →ₐ[A] A) : MvPolynomial B A →+* A)
          = (MvPolynomial.aeval (R := A) (S₁ := B) (fun b ↦ b) : MvPolynomial B A →+* B)) x
      · simp
      · simp [Function.surjInv_eq h]
  have f₂ : P₀.Hom P₁ := by
    refine ⟨(algebraMap A P₁.Ring : P₀.Ring →+* P₁.Ring), fun x ↦ ?_, fun x ↦ ?_⟩
    · rw [Algebra.algebraMap_self]
      rfl
    · change (algebraMap P₁.Ring B) ((algebraMap A P₁.Ring) x)
        = (algebraMap B B) ((algebraMap A B) x)
      rw [← IsScalarTower.algebraMap_apply A P₁.Ring B]
      rfl
  exact ⟨Algebra.Extension.H1Cotangent.equiv f₁ f₂⟩

/-- For a surjective `algebraMap A B`, the first homology of the naive cotangent complex of the
extension `Algebra.Extension.ofSurjective (Algebra.ofId A B) h`, with ring `A` and kernel
`I := RingHom.ker (algebraMap A B)`, is `A`-linearly isomorphic to the conormal module
`I.Cotangent`. -/
theorem ofSurjective_h1Cotangent_equiv_cotangent
    (h : Function.Surjective (algebraMap A B)) :
    Nonempty ((Algebra.Extension.ofSurjective (Algebra.ofId A B) h).H1Cotangent ≃ₗ[A]
      (RingHom.ker (algebraMap A B)).Cotangent) := by
  set P₀ := Algebra.Extension.ofSurjective (Algebra.ofId A B) h
  have hss : Subsingleton P₀.CotangentSpace := by
    have hΩ : Subsingleton (Ω[P₀.Ring⁄A]) :=
      KaehlerDifferential.subsingleton_of_surjective A A Function.surjective_id
    unfold Algebra.Extension.CotangentSpace
    infer_instance
  have hzero : P₀.cotangentComplex = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have e3 : P₀.H1Cotangent ≃ₗ[B] P₀.Cotangent :=
    LinearEquiv.ofTop _ (by rw [hzero, LinearMap.ker_zero])
  have e4 : P₀.Cotangent ≃ₗ[A] P₀.ker.Cotangent :=
    { toFun := Algebra.Extension.Cotangent.val
      invFun := Algebra.Extension.Cotangent.of
      map_add' := Algebra.Extension.Cotangent.val_add
      map_smul' := Algebra.Extension.Cotangent.val_smul''
      left_inv := Algebra.Extension.Cotangent.of_val
      right_inv := Algebra.Extension.Cotangent.val_of }
  exact ⟨(e3.restrictScalars A).trans e4⟩

/-- For a surjective ring map `A → B` with kernel `I := RingHom.ker (algebraMap A B)` there is an
`A`-linear isomorphism `Algebra.H1Cotangent A B ≃ₗ[A] I.Cotangent`. -/
theorem h1Cotangent_nonempty_equiv_cotangent_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Nonempty (Algebra.H1Cotangent A B ≃ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent) := by
  obtain ⟨e1⟩ := h1Cotangent_self_equiv_ofSurjective A B h
  obtain ⟨e2⟩ := ofSurjective_h1Cotangent_equiv_cotangent A B h
  exact ⟨(e1.restrictScalars A).trans e2⟩

/-- For a surjective ring map `A → B` with kernel `I := RingHom.ker (algebraMap A B)`, the
`A`-linear isomorphism `Algebra.H1Cotangent A B ≃ₗ[A] I.Cotangent`. -/
@[stacks 07BP]
noncomputable def h1Cotangent_equiv_cotangent_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Algebra.H1Cotangent A B ≃ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent :=
  (h1Cotangent_nonempty_equiv_cotangent_of_surjective A B h).some
