module

public import StacksFrontier.RingTheory.DeRham.Cartier.InverseCartier

/-!
# Interior products and Lie derivatives on the de Rham complex

Let `A → B` be a ring map and `θ : Ω[B⁄A] →ₗ[B] B` a `B`-linear form on the differentials, that is
an `A`-derivation `θ ∘ d` of `B` (a vector field). Contraction against `θ` is the interior product
`ι_θ : Ω^{i+1}_{B/A} ⟶ Ω^i_{B/A}`, and **Cartan's formula** defines the Lie derivative

`L_θ = d ι_θ + ι_θ d : Ω^i_{B/A} ⟶ Ω^i_{B/A}`

(on functions `L_θ = ι_θ d`). This file proves:

* `L_θ` commutes with `d`, so it preserves closed forms;
* on closed forms of positive degree `L_θ z = d(ι_θ z)` is exact, and so is every power
  `L_θ^m z` with `m ≥ 1`; on closed functions `L_θ z = 0`;
* `L_θ (f ξ) = θ(df) ξ + f L_θ ξ` and `L_θ (dg ∧ ξ) = d(θ(dg)) ∧ ξ + dg ∧ L_θ ξ`, which compute
  `L_θ` on forms `f dg₁ ∧ ⋯ ∧ dg_i`;
* in characteristic `p`, `L_θ (c^p ξ) = c^p L_θ ξ`.

## Main definitions

* `KaehlerDifferential.Cartier.lie`: the Lie derivative `L_θ` in degree `i`.

## Main results

* `KaehlerDifferential.Cartier.deRhamDifferential_lie`: `d L_θ = L_θ d`.
* `KaehlerDifferential.Cartier.lie_pow_eq_deRhamDifferential`: `L_θ^m z` is exact for `z` closed
  of positive degree and `m ≥ 1`.
* `KaehlerDifferential.Cartier.lie_smul` and `KaehlerDifferential.Cartier.lie_wedgeLeft_D`: the
  two derivation rules.

## References

* N. Katz, *Nilpotent connections and the monodromy theorem*, Publ. Math. IHÉS 39 (1970), §7.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential exteriorPower

universe u

namespace KaehlerDifferential.Cartier

variable (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (θ : Ω[B⁄A] →ₗ[B] B)

/-- **The Lie derivative** `L_θ = d ι_θ + ι_θ d` on `Ω^i_{B/A}`, with `L_θ = ι_θ d` on
functions. -/
def lie : (i : ℕ) → ⋀[B]^i (Ω[B⁄A]) →ₗ[A] ⋀[B]^i (Ω[B⁄A])
  | 0 => (contraction θ 0).restrictScalars A ∘ₗ deRhamDifferential 0
  | i + 1 => deRhamDifferential i ∘ₗ (contraction θ i).restrictScalars A +
      (contraction θ (i + 1)).restrictScalars A ∘ₗ deRhamDifferential (i + 1)

/-- On functions, `L_θ x = ι_θ dx`. -/
theorem lie_zero_apply (x : ⋀[B]^0 (Ω[B⁄A])) :
    lie A θ 0 x = contraction θ 0 (deRhamDifferential (A := A) 0 x) := rfl

/-- In positive degree, `L_θ x = d(ι_θ x) + ι_θ dx`. -/
theorem lie_succ_apply (i : ℕ) (x : ⋀[B]^(i + 1) (Ω[B⁄A])) :
    lie A θ (i + 1) x = deRhamDifferential (A := A) i (contraction θ i x) +
      contraction θ (i + 1) (deRhamDifferential (A := A) (i + 1) x) := rfl

/-- **`L_θ` commutes with `d`.** -/
theorem deRhamDifferential_lie (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i (lie A θ i x) = lie A θ (i + 1) (deRhamDifferential i x) := by
  cases i with
  | zero =>
      rw [lie_zero_apply, lie_succ_apply, deRhamDifferential_comp_self, map_zero, add_zero]
  | succ i =>
      rw [lie_succ_apply, lie_succ_apply, map_add, deRhamDifferential_comp_self,
        deRhamDifferential_comp_self, map_zero, add_zero, zero_add]

/-- `L_θ` kills closed functions. -/
theorem lie_zero_eq_zero_of_closed (x : ⋀[B]^0 (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) 0 x = 0) : lie A θ 0 x = 0 := by
  rw [lie_zero_apply, hx, map_zero]

/-- On a closed form of positive degree, `L_θ z = d(ι_θ z)`. -/
theorem lie_succ_eq_of_closed (i : ℕ) (x : ⋀[B]^(i + 1) (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) (i + 1) x = 0) :
    lie A θ (i + 1) x = deRhamDifferential (A := A) i (contraction θ i x) := by
  rw [lie_succ_apply, hx, map_zero, add_zero]

/-- The powers of `L_θ` commute with `d`. -/
theorem deRhamDifferential_lie_pow (i m : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i ((lie A θ i ^ m) x) =
      (lie A θ (i + 1) ^ m) (deRhamDifferential i x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, deRhamDifferential_lie, ih, pow_succ',
        Module.End.mul_apply]

/-- The powers of `L_θ` preserve closed forms. -/
theorem deRhamDifferential_lie_pow_eq_zero (i m : ℕ) (x : ⋀[B]^i (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) i x = 0) :
    deRhamDifferential (A := A) i ((lie A θ i ^ m) x) = 0 := by
  rw [deRhamDifferential_lie_pow, hx, map_zero]

/-- **`L_θ^m z` is exact** for `z` closed of positive degree and `m ≥ 1`:
`L_θ^m z = d(L_θ^{m-1} ι_θ z)`. -/
theorem lie_pow_eq_deRhamDifferential (i m : ℕ) (x : ⋀[B]^(i + 1) (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) (i + 1) x = 0) :
    (lie A θ (i + 1) ^ (m + 1)) x =
      deRhamDifferential (A := A) i ((lie A θ i ^ m) (contraction θ i x)) := by
  rw [deRhamDifferential_lie_pow, pow_succ, Module.End.mul_apply, lie_succ_eq_of_closed A θ i x hx]

/-- The powers `L_θ^m`, `m ≥ 1`, kill closed functions. -/
theorem lie_pow_zero_eq_zero_of_closed (m : ℕ) (x : ⋀[B]^0 (Ω[B⁄A]))
    (hx : deRhamDifferential (A := A) 0 x = 0) : (lie A θ 0 ^ (m + 1)) x = 0 := by
  rw [pow_succ, Module.End.mul_apply, lie_zero_eq_zero_of_closed A θ x hx, map_zero]

/-- In degree zero, `ι_θ (e ∧ ξ) = θ(e) ξ`. -/
private theorem contraction_wedgeLeft_zero_apply (e : Ω[B⁄A]) (ξ : ⋀[B]^0 (Ω[B⁄A])) :
    contraction θ 0 (wedgeLeft e 0 ξ) = θ e • ξ :=
  LinearMap.congr_fun (contraction_comp_wedgeLeft_zero θ e) ξ

/-- The Koszul identity `ι_θ (e ∧ ξ) + e ∧ ι_θ ξ = θ(e) ξ`, applied to a form. -/
private theorem contraction_wedgeLeft_add_wedgeLeft_contraction (e : Ω[B⁄A]) (i : ℕ)
    (ξ : ⋀[B]^(i + 1) (Ω[B⁄A])) :
    contraction θ (i + 1) (wedgeLeft e (i + 1) ξ) + wedgeLeft e i (contraction θ i ξ) =
      θ e • ξ := by
  simpa only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq] using
    LinearMap.congr_fun (contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction θ e i) ξ

/-- **The first derivation rule**: `L_θ (f ξ) = θ(df) ξ + f L_θ ξ`. -/
theorem lie_smul (i : ℕ) (f : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    lie A θ i (f • ξ) = θ (D A B f) • ξ + f • lie A θ i ξ := by
  cases i with
  | zero =>
      rw [lie_zero_apply, lie_zero_apply, deRhamDifferential_smul, map_add, map_smul,
        contraction_wedgeLeft_zero_apply A θ]
  | succ i =>
      rw [lie_succ_apply, lie_succ_apply, map_smul, deRhamDifferential_smul,
        deRhamDifferential_smul, map_add, map_smul]
      rw [smul_add, ← contraction_wedgeLeft_add_wedgeLeft_contraction A θ (D A B f) i ξ]
      abel

/-- **The second derivation rule**: `L_θ (dg ∧ ξ) = d(θ(dg)) ∧ ξ + dg ∧ L_θ ξ`. -/
theorem lie_wedgeLeft_D (i : ℕ) (g : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    lie A θ (i + 1) (wedgeLeft (D A B g) i ξ) =
      wedgeLeft (D A B (θ (D A B g))) i ξ + wedgeLeft (D A B g) i (lie A θ i ξ) := by
  rw [lie_succ_apply, deRhamDifferential_wedgeLeft_D, map_neg]
  cases i with
  | zero =>
      rw [contraction_wedgeLeft_zero_apply A θ, deRhamDifferential_smul, lie_zero_apply,
        eq_sub_iff_add_eq.mpr
          (contraction_wedgeLeft_add_wedgeLeft_contraction A θ (D A B g) 0
            (deRhamDifferential (A := A) 0 ξ))]
      abel
  | succ i =>
      rw [eq_sub_iff_add_eq.mpr (contraction_wedgeLeft_add_wedgeLeft_contraction A θ (D A B g) i ξ),
        eq_sub_iff_add_eq.mpr (contraction_wedgeLeft_add_wedgeLeft_contraction A θ (D A B g) (i + 1)
          (deRhamDifferential (A := A) (i + 1) ξ)), map_sub,
        deRhamDifferential_smul, deRhamDifferential_wedgeLeft_D, lie_succ_apply, map_add]
      abel

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP B p]

omit [Fact p.Prime] in
/-- `L_θ` is linear for the Frobenius action: `L_θ (c^p ξ) = c^p L_θ ξ`. -/
theorem lie_pow_char_smul (i : ℕ) (c : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    lie A θ i (c ^ p • ξ) = c ^ p • lie A θ i ξ := by
  rw [lie_smul, D_pow_char p A c, map_zero, zero_smul, zero_add]

omit [Fact p.Prime] in
/-- The powers of `L_θ` are linear for the Frobenius action. -/
theorem lie_pow_pow_char_smul (i m : ℕ) (c : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    (lie A θ i ^ m) (c ^ p • ξ) = c ^ p • (lie A θ i ^ m) ξ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, lie_pow_char_smul]

end CharP

end KaehlerDifferential.Cartier

end
