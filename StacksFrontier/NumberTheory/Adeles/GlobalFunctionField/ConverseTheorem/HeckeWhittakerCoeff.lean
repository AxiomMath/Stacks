module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.EulerProduct
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerSum

/-!
# The Whittaker coefficients prescribed by Hecke eigenvalues

For an eigenform with eigenvalues `(t, u)` and a nontrivial adelic character `ψ` of divisor `W₀`,
the Whittaker coefficients are `c(D) = λ(W₀ - D) c(W₀)` for `D ≤ W₀` and `0` otherwise, with
`λ = heckeCoeff t u` (`IsEigenform.whittakerDiv_sub_eq`). Conversely, for ANY `(t, u)` this file
shows that `c(D) = λ(W₀ - D)` (and `0` off `D ≤ W₀`) satisfies the two conditions used in
`ConverseTheorem/WhittakerSum.lean`: `c(D) ≠ 0 ⇒ ψ(A(D)) = 1`, and the Hecke recursion
`t_v c(D) = q_v c(D - v) + u_v c(D + v)` wherever `ψ(A(D)) = 1` (from `heckeCoeff_rec`).
Hence the Fourier–Whittaker sum of these coefficients is an eigenform with eigenvalues `(t, u)` as
soon as it is right `GL₂(K)`-invariant (`isEigenform_whittakerSum_heckeWhittakerCoeff`).

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.heckeWhittakerCoeff W₀ t u`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.heckeWhittakerCoeff_rec` — the Hecke recursion.
* `Stacks.Adeles.GlobalFunctionField.isEigenform_whittakerSum_heckeWhittakerCoeff`.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §11.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

variable (K) in
open scoped Classical in
/-- The coefficients `c(D) = λ(W₀ - D)` for `D ≤ W₀` and `0` otherwise, `λ = heckeCoeff t u`. -/
public def heckeWhittakerCoeff (W₀ : Place K →₀ ℤ) (t u : Place K → Λ) (D : Place K →₀ ℤ) : Λ :=
  if D ≤ W₀ then heckeCoeff t u (W₀ - D) else 0

variable {W₀ : Place K →₀ ℤ} {t u : Place K → Λ} {ψ : AddChar (AdeleRing K) Λ}

/-- `c(W₀) = λ(0) = 1`. -/
public theorem heckeWhittakerCoeff_self : heckeWhittakerCoeff K W₀ t u W₀ = 1 := by
  simp [heckeWhittakerCoeff]

/-- `c(D) ≠ 0` only where `ψ(A(D)) = 1`, for `W₀` the divisor of `ψ`. -/
public theorem heckeWhittakerCoeff_ne_zero
    (hW : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) {D : Place K →₀ ℤ}
    (h : heckeWhittakerCoeff K W₀ t u D ≠ 0) : ∀ a ∈ adeleLattice K D, ψ a = 1 := by
  classical
  refine (hW D).2 ?_
  by_contra hD
  exact h (by simp [heckeWhittakerCoeff, hD])

/-- **The Hecke recursion** `t_v c(D) = q_v c(D - v) + u_v c(D + v)` for `ψ(A(D)) = 1`. -/
public theorem heckeWhittakerCoeff_rec [NeZero (ringChar k : Λ)]
    (hW : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) (v : Place K) {D : Place K →₀ ℤ}
    (hD : ∀ a ∈ adeleLattice K D, ψ a = 1) :
    t v * heckeWhittakerCoeff K W₀ t u D =
      (v.residueCard : Λ) * heckeWhittakerCoeff K W₀ t u (D - Finsupp.single v 1) +
        u v * heckeWhittakerCoeff K W₀ t u (D + Finsupp.single v 1) := by
  classical
  have hq : ∀ v : Place K, (v.residueCard : Λ) ≠ 0 := fun v =>
    (isUnit_residueCard k (Ne.isUnit (NeZero.ne (ringChar k : Λ))) v).ne_zero
  have hle := (hW D).1 hD
  have hsv : (0 : Place K →₀ ℤ) ≤ Finsupp.single v 1 := Finsupp.single_nonneg.2 zero_le_one
  have h1 : D - Finsupp.single v 1 ≤ W₀ := le_trans (sub_le_self _ hsv) hle
  have hE : 0 ≤ W₀ - D := sub_nonneg.2 hle
  have e1 : W₀ - (D - Finsupp.single v 1) = W₀ - D + Finsupp.single v 1 := by abel
  have e3 : W₀ - (D + Finsupp.single v 1) = W₀ - D - Finsupp.single v 1 := by abel
  have e2 : D + Finsupp.single v 1 ≤ W₀ ↔ 1 ≤ (W₀ - D) v := by
    simp only [Finsupp.le_def, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_apply]
    exact ⟨fun h => by grind, fun h w => by grind [hle w]⟩
  simp only [heckeWhittakerCoeff, if_pos hle, if_pos h1, e1, e3]
  rw [heckeCoeff_rec hq hE v]
  by_cases h : 1 ≤ (W₀ - D) v
  · rw [if_pos (e2.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e2.1 h')), if_neg h]

/-- **The converse construction, up to `GL₂(K)`-invariance.** For any `(t, u)`, a nontrivial
adelic character `ψ` of divisor `W₀`, and an idele character `ω` trivial on `Oˣ` with
`ω(ϖ_v⁻¹) = u_v`, the Fourier–Whittaker sum `f` of the coefficients `λ(W₀ - D)` is an eigenform
with eigenvalues `(t, u)` once it is right `GL₂(K)`-invariant. -/
public theorem isEigenform_whittakerSum_heckeWhittakerCoeff [NeZero (ringChar k : Λ)]
    (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    (hW : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) {ω : (AdeleRing K)ˣ →* Λˣ}
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hωu : ∀ (v : Place K) {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v)
    (hK : ∀ (x : GL (Fin 2) (AdeleRing K)) (γ : GL (Fin 2) (principalAdeles K)),
      whittakerSum k K ψ ω (heckeWhittakerCoeff K W₀ t u)
          (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) =
        whittakerSum k K ψ ω (heckeWhittakerCoeff K W₀ t u) x) :
    IsEigenform (whittakerSum k K ψ ω (heckeWhittakerCoeff K W₀ t u)) t u :=
  isEigenform_whittakerSum k hψ hψ1 hω (fun _ h => heckeWhittakerCoeff_ne_zero hW h)
    (fun v _ hD => heckeWhittakerCoeff_rec k hW v hD) hωu
    (by rw [heckeWhittakerCoeff_self]; exact one_ne_zero) hK

end Stacks.Adeles.GlobalFunctionField

end
