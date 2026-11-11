module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.FinitePresentation

/-!
# Moving one coordinate of a point of a finitely presented algebra along a line

Let `B` be a finitely presented algebra over a polynomial ring `A = R[t_i : i ∈ ι]` and let
`χ : B → K` be a point of `B` with values in a ring `K`. A presentation
`B = A[y_1, …, y_n] / (g_1, …, g_m)` involves only finitely many of the variables `t_i` in the
coefficients of its relations. For every other index `j`, the point `χ` deforms along the line
`t_j ↦ X` in `K[X]`: there is a ring map `ρ : B → K[X]` sending `t_j` to `X`, every other `t_i` to
the constant `χ(t_i)` and every constant of `R` to its value under `χ`, and specializing back to
`χ` at `X = χ(t_j)`.

## Main results

* `MvPolynomial.exists_finset_forall_exists_polynomial_lift`: for a finitely presented ring map
  `φ : R[t_i : i ∈ ι] → B` and a ring map `χ : B → K`, all but finitely many indices `j` admit a
  ring map `ρ : B → K[X]` moving `t_j` along `X`, fixing the other coordinates of `χ`, and
  specializing to `χ` at `X = χ(φ(t_j))`.
-/

@[expose] public section

namespace MvPolynomial

variable {ι R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    [DecidableEq ι]

/-- Let `φ : R[t_i : i ∈ ι] → B` be of finite presentation and `χ : B → K` a ring map. Outside a
finite set of indices `s`, each `j` admits a ring map `ρ : B → K[X]` sending `φ(t_j)` to `X`, each
other `φ(t_i)` to the constant `χ(φ(t_i))` and each `φ(r)`, `r ∈ R`, to the constant `χ(φ(r))`,
whose specialization at `X = χ(φ(t_j))` is `χ`. The set `s` collects the variables occurring in
the coefficients of a finite set of relations of a presentation of `B`. -/
theorem exists_finset_forall_exists_polynomial_lift
    (φ : MvPolynomial ι R →+* B) (hφ : φ.FinitePresentation) (χ : B →+* K) :
    ∃ s : Finset ι, ∀ j ∉ s, ∃ ρ : B →+* Polynomial K,
      (∀ i, ρ (φ (X i)) = if i = j then Polynomial.X else Polynomial.C (χ (φ (X i)))) ∧
      (∀ r, ρ (φ (C r)) = Polynomial.C (χ (φ (C r)))) ∧
      (Polynomial.evalRingHom (χ (φ (X j)))).comp ρ = χ := by
  let := φ.toAlgebra
  obtain ⟨n, f, hsurj, G, hG⟩ := hφ.out
  have hfC : ∀ a, f (C a) = φ a := fun a => f.commutes a
  refine ⟨G.biUnion fun g => g.support.biUnion fun m => vars (g.coeff m), fun j hj => ?_⟩
  set σ' : MvPolynomial ι R →+* Polynomial K := Polynomial.C.comp (χ.comp φ)
  set σ : MvPolynomial ι R →+* Polynomial K :=
    eval₂Hom (σ'.comp C) fun i => if i = j then Polynomial.X else σ' (X i)
  set v : Fin n → Polynomial K := fun k => Polynomial.C (χ (f (X k)))
  set ψ : MvPolynomial (Fin n) (MvPolynomial ι R) →+* Polynomial K := eval₂Hom σ v
  have hψ' : eval₂Hom σ' v = Polynomial.C.comp (χ.comp f.toRingHom) := by
    ext <;> simp [σ', v, hfC]
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker ψ := by
    rw [← hG, Ideal.span_le]
    intro g hg
    have hmap : map σ g = map σ' g := by
      ext m : 1
      rw [coeff_map, coeff_map]
      refine hom_congr_vars (by ext; simp [σ]) (fun i hi _ => ?_) rfl
      have hij : i ≠ j := by
        rintro rfl
        refine hj (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨m, ?_, hi⟩⟩)
        exact mem_support_iff.2 fun h0 => by simp [h0] at hi
      simp [σ, hij]
    have hg0 : f g = 0 := RingHom.mem_ker.1 (hG ▸ Ideal.subset_span hg)
    rw [SetLike.mem_coe, RingHom.mem_ker]
    calc ψ g = eval₂ (RingHom.id _) v (map σ g) := by rw [eval₂_map]; rfl
      _ = eval₂ (RingHom.id _) v (map σ' g) := by rw [hmap]
      _ = eval₂Hom σ' v g := by rw [eval₂_map]; rfl
      _ = 0 := by rw [hψ']; simp [hg0]
  set ρ := f.toRingHom.liftOfSurjective hsurj ⟨ψ, hker⟩
  have hρ : ∀ x, ρ (f x) = ψ x := fun x =>
    RingHom.liftOfSurjective_comp_apply f.toRingHom hsurj ⟨ψ, hker⟩ x
  have hρφ : ∀ a, ρ (φ a) = σ a := fun a => by rw [← hfC, hρ]; simp [ψ]
  refine ⟨ρ, fun i => ?_, fun r => ?_, ?_⟩
  · rw [hρφ]
    simp [σ, σ']
  · rw [hρφ]
    simp [σ, σ']
  · have hcomp : (Polynomial.evalRingHom (χ (φ (X j)))).comp ψ = χ.comp f.toRingHom := by
      ext i <;> simp [ψ, σ, σ', v, hfC]
      split_ifs with h <;> simp [h]
    refine RingHom.ext fun b => ?_
    obtain ⟨x, rfl⟩ := hsurj b
    simpa [hρ] using RingHom.congr_fun hcomp x

end MvPolynomial
