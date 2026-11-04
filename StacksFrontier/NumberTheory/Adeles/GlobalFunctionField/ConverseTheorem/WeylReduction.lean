module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.CentralCharacter
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.GeneratorsGL2
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.HeckeWhittakerCoeff

/-!
# The converse construction, reduced to invariance under the Weyl element

Let `(t_v, u_v)` be a system of eigenvalues with `u_v` units and `q_v u_v = d_v`, where
`v ↦ d_v` kills principal divisors (for `d_v = det ρ(F_v)` this is the unramified reciprocity
law). Let `ψ` be a nontrivial adelic character with divisor `W₀`, `ω` the central character of
`u` (`ConverseTheorem/CentralCharacter.lean`), and `f` the Fourier–Whittaker sum of the
coefficients `c(D) = λ(W₀ - D)` (`ConverseTheorem/HeckeWhittakerCoeff.lean`). Then `f` is an
eigenform with eigenvalues `(t, u)` as soon as `f(x w) = f(x)` for the Weyl element
`w = (0, -1; 1, 0)`: the central character is trivial on `Kˣ`, and the Bruhat decomposition
(`ConverseTheorem/GeneratorsGL2.lean`) turns `w`-invariance into right `GL₂(K)`-invariance.

What remains for the converse theorem is the invariance `f(x w) = f(x)` itself.

## Main results

* `Stacks.Adeles.GlobalFunctionField.isEigenform_whittakerSum_centralCharacter`.
* `Stacks.Adeles.GlobalFunctionField.whittakerSum_diagGL_mul_weylK` —
  `f(diag(y, 1) w) = ω(y) f(diag(y⁻¹, 1))`, the first step of the converse theorem.

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

/-- The central character `ω` of `u` is trivial on `Kˣ` when `q_v u_v = d_v` and `v ↦ d_v`
kills principal divisors. -/
public theorem centralCharacter_units_map_diag [NeZero (ringChar k : Λ)] {u d : Place K → Λˣ}
    (hud : ∀ v, (v.residueCard : Λ) * u v = d v)
    (hd : ∀ κ : K, κ ≠ 0 → divisorCharacter d (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    (κ : Kˣ) : centralCharacter k K u (Units.map (diag k K).toMonoidHom κ) = 1 := by
  have h := centralCharacter_diagUnit_of_mul k (NeZero.ne (ringChar k : Λ)).isUnit hud hd
    κ.ne_zero
  rwa [diagUnit, Units.mk0_val] at h

/-- **The converse construction, up to `w`-invariance.** For eigenvalues `(t, u)` with `u_v`
units, `q_v u_v = d_v` and `v ↦ d_v` trivial on principal divisors, a nontrivial adelic
character `ψ` of divisor `W₀`, the Fourier–Whittaker sum `f` of `c(D) = λ(W₀ - D)` with central
character `centralCharacter u` is an eigenform with eigenvalues `(t, u)` as soon as
`f(x w) = f(x)` for the Weyl element `w`. -/
public theorem isEigenform_whittakerSum_centralCharacter [NeZero (ringChar k : Λ)]
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    {W₀ : Place K →₀ ℤ} (hW : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀)
    {t : Place K → Λ} {u d : Place K → Λˣ} (hud : ∀ v, (v.residueCard : Λ) * u v = d v)
    (hd : ∀ κ : K, κ ≠ 0 → divisorCharacter d (Multiplicative.ofAdd (principalDivisor k K κ)) = 1)
    (hw : ∀ x, whittakerSum k K ψ (centralCharacter k K u)
        (heckeWhittakerCoeff K W₀ t fun v => (u v : Λ)) (x * weylK k K) =
      whittakerSum k K ψ (centralCharacter k K u) (heckeWhittakerCoeff K W₀ t fun v => (u v : Λ))
        x) :
    IsEigenform (whittakerSum k K ψ (centralCharacter k K u)
      (heckeWhittakerCoeff K W₀ t fun v => (u v : Λ))) t fun v => (u v : Λ) :=
  isEigenform_whittakerSum_heckeWhittakerCoeff k hψ hψ1 hW (centralCharacter_integral k u)
    (fun v _ hπ => by rw [centralCharacter_localIdele_inv k u v hπ])
    (whittakerSum_right_invariant k hψ (centralCharacter_integral k u)
      (fun _ h => heckeWhittakerCoeff_ne_zero hW h) (centralCharacter_units_map_diag k hud hd) hw)

variable (K) in
/-- The Weyl element `w = (0, -1; 1, 0)` as an element of `GL₂(O)`. -/
public def weylO : GL (Fin 2) (integralAdeles K) where
  val := !![0, -1; 1, 0]
  inv := !![0, 1; -1, 0]
  val_inv := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The Weyl element of `GL₂(K)` is the Weyl element of `GL₂(O)`. -/
public theorem mapO_weylO : mapO (weylO K) = weylK k K := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_weylK, coe_mapO_apply]
  fin_cases i <;> fin_cases j <;> simp [weylO]

/-- `diag(y, 1) w = w · y · diag(y⁻¹, 1)`. -/
public theorem diagGL_mul_weylK (y : (AdeleRing K)ˣ) :
    diagGL y * weylK k K = mapO (weylO K) * (scalarGL y * diagGL y⁻¹) := by
  rw [mapO_weylO k]
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [Units.val_mul, coe_diagGL, coe_weylK, coe_scalarGL, mul_fin_two, Matrix.scalar_apply,
    Matrix.diagonal_fin_two]
  fin_cases i <;> fin_cases j <;> simp

variable {ψ : AddChar (AdeleRing K) Λ} {ω : (AdeleRing K)ˣ →* Λˣ} {c : (Place K →₀ ℤ) → Λ}

/-- **The Weyl element on the diagonal**: `f(diag(y, 1) w) = ω(y) f(diag(y⁻¹, 1))`, because
`diag(y, 1) w = w diag(1, y)` with `w ∈ GL₂(O)`. -/
public theorem whittakerSum_diagGL_mul_weylK
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (y : (AdeleRing K)ˣ) :
    whittakerSum k K ψ ω c (diagGL y * weylK k K) = ω y * whittakerSum k K ψ ω c (diagGL y⁻¹) := by
  rw [diagGL_mul_weylK, whittakerSum_mapO_mul k hω hc, whittakerSum_scalarGL_mul k hω hc]

end Stacks.Adeles.GlobalFunctionField

end
