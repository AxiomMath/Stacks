module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Extending derivations along formally étale maps

Let `R → S → T` be ring maps with `S → T` formally étale. Then every `R`-derivation
`d : S → T` extends uniquely to an `R`-derivation `T → T`. Existence comes from the isomorphism
`T ⊗[S] Ω[S⁄R] ≃ Ω[T⁄R]` of `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`. Uniqueness
only needs `S → T` to be formally unramified: two `R`-derivations out of `T` which agree on the
image of `S` differ by an `S`-derivation, and `Ω[T⁄S] = 0`.

## Main definitions

* `Derivation.extendOfFormallyEtale`: the extension of `d : Derivation R S T` to a derivation of
  `T`.

## Main results

* `Derivation.extendOfFormallyEtale_algebraMap`: the extension restricts to `d`.
* `Derivation.eq_of_formallyUnramified`: derivations out of a formally unramified algebra are
  determined by their restriction to the base.
-/

@[expose] public section

open KaehlerDifferential TensorProduct

namespace Derivation

variable {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

omit [Algebra R S] [IsScalarTower R S T] in
/-- **Derivations out of a formally unramified algebra are determined by their restriction to
the base.** If `S → T` is formally unramified, two `R`-derivations of `T` into a `T`-module which
agree on the image of `S` are equal: their difference is `S`-linear, hence an `S`-derivation,
and `Ω[T⁄S]` vanishes. -/
theorem eq_of_formallyUnramified [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower R T M]
    [Algebra.FormallyUnramified S T] (d₁ d₂ : Derivation R T M)
    (h : ∀ s : S, d₁ (algebraMap S T s) = d₂ (algebraMap S T s)) : d₁ = d₂ := by
  let : Module S M := Module.compHom M (algebraMap S T)
  have : IsScalarTower S T M := ⟨fun s t m ↦ by
    show (s • t) • m = algebraMap S T s • (t • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let e : Derivation S T M :=
    { toFun := fun t ↦ d₁ t - d₂ t
      map_add' := fun x y ↦ by simp only [map_add]; abel
      map_smul' := fun s t ↦ by
        show d₁ (s • t) - d₂ (s • t) = algebraMap S T s • (d₁ t - d₂ t)
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz, h s, smul_sub]
        abel
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        show d₁ (a * b) - d₂ (a * b) = a • (d₁ b - d₂ b) + b • (d₁ a - d₂ a)
        rw [Derivation.leibniz, Derivation.leibniz, smul_sub, smul_sub]
        abel }
  have he : e = 0 := by
    rw [← (linearMapEquivDerivation S T).apply_symm_apply e]
    have : (linearMapEquivDerivation S T).symm e = 0 := LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    rw [this, map_zero]
  ext t
  have := congrArg (fun d : Derivation S T M ↦ d t) he
  simpa [e, sub_eq_zero] using this

variable (R S T)

/-- **The extension of a derivation along a formally étale map.** For `S → T` formally étale,
an `R`-derivation `d : S → T` extends to an `R`-derivation of `T`: it is the derivation
corresponding to the `T`-linear map `Ω[T⁄R] ≃ T ⊗[S] Ω[S⁄R] → T` obtained by base change from
the `S`-linear map `Ω[S⁄R] → T` of `d`. -/
noncomputable def extendOfFormallyEtale [Algebra.FormallyEtale S T] (d : Derivation R S T) :
    Derivation R T T :=
  linearMapEquivDerivation R T
    ((LinearMap.liftBaseChange T ((linearMapEquivDerivation R S).symm d)).comp
      (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap)

variable {R S T}

/-- The extension of a derivation along a formally étale map restricts to it. -/
@[simp]
theorem extendOfFormallyEtale_algebraMap [Algebra.FormallyEtale S T] (d : Derivation R S T)
    (s : S) : extendOfFormallyEtale R S T d (algebraMap S T s) = d s := by
  show ((LinearMap.liftBaseChange T ((linearMapEquivDerivation R S).symm d)).comp
      (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap) (D R T (algebraMap S T s)) = d s
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul, one_smul]
  exact congrArg (fun e : Derivation R S T ↦ e s)
    ((linearMapEquivDerivation R S).apply_symm_apply d)

end Derivation
