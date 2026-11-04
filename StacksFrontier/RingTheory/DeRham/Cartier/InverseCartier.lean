module

public import StacksFrontier.RingTheory.DeRham.Cartier.Basic

/-!
# The inverse Cartier map

Let `p` be a prime and `A → B` a ring map with `B` of characteristic `p`. This file constructs the
**inverse Cartier map**

`C⁻¹ : Ω^i_{B/A} ⟶ H^i(F_*Ω^•_{B/A})`, `db₁ ∧ ⋯ ∧ db_i ↦ [b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i]`,

a `B`-linear map into the cohomology of the Frobenius-twisted de Rham complex
`KaehlerDifferential.Cartier.twistedDeRhamComplex`, on which `b` acts as `b^p`.

In degree one it is induced, through the universal property of `Ω[B⁄A]`, by the `A`-derivation
`b ↦ [b^{p-1} db]` of `B` into `H^1`: additivity is
`KaehlerDifferential.Cartier.pow_pred_smul_D_add`, and the Leibniz rule
`(bc)^{p-1} d(bc) = b^p · c^{p-1} dc + c^p · b^{p-1} db` is exactly the twisted module structure.
In degree `i` it is the composite of `(C⁻¹)^{×i}` with the wedge of classes
`H^1 × ⋯ × H^1 ⟶ H^i`, read off representatives: the wedge of closed one-forms is closed
(`KaehlerDifferential.Cartier.ιMulti_mem_closedForms`), and it is exact as soon as one factor
is exact (`KaehlerDifferential.Cartier.twist_ιMulti_update_D_mem_exactForms`), so the wedge of
classes is a well-defined alternating map on `H^1`, and the universal property of `⋀^i` applies.

## Main definitions

* `KaehlerDifferential.Cartier.cartierForm`: the closed one-form `b^{p-1} db`.
* `KaehlerDifferential.Cartier.cartierDerivation`: the `A`-derivation `b ↦ [b^{p-1} db]`.
* `KaehlerDifferential.Cartier.wedgeClosed` and `KaehlerDifferential.Cartier.wedgeClass`: the
  wedge of closed one-forms, and of their classes, as alternating maps.
* `KaehlerDifferential.Cartier.inverseCartier`: **the inverse Cartier map** in degree `i`.

## Main results

* `KaehlerDifferential.Cartier.inverseCartier_ιMulti_D`: `C⁻¹(db₁ ∧ ⋯ ∧ db_i)` is the class of
  `b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i`.

## References

* N. Katz, *Nilpotent connections and the monodromy theorem*, Publ. Math. IHÉS 39 (1970), §7.
* P. Deligne and L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), §1.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace KaehlerDifferential.Cartier

/-! ### One-forms -/

section OneForms

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A form of degree zero is a multiple of `1 = ιMulti B 0 ![]`, and its differential is `d` of the
multiple. -/
theorem deRhamDifferential_zero_smul_ιMulti (c : B) (v : Fin 0 → Ω[B⁄A]) :
    deRhamDifferential (A := A) 0 (c • exteriorPower.ιMulti B 0 v) =
      exteriorPower.ιMulti B 1 (fun _ ↦ D A B c) := by
  have h := deRhamDifferential_smul_ιMulti_D (A := A) (B := B) 0 ![c]
  rw [Subsingleton.elim v fun i : Fin 0 ↦ D A B (![c] i.succ)]
  simpa using h

/-- `d(b₀ db) = db₀ ∧ db` on one-forms. -/
theorem deRhamDifferential_one_smul_ιMulti_D (b₀ b : B) :
    deRhamDifferential (A := A) 1 (b₀ • exteriorPower.ιMulti B 1 (fun _ ↦ D A B b)) =
      exteriorPower.ιMulti B 2 ![D A B b₀, D A B b] := by
  have h := deRhamDifferential_smul_ιMulti_D (A := A) (B := B) 1 ![b₀, b]
  have hv : (fun _ : Fin 1 ↦ D A B b) = fun i : Fin 1 ↦ D A B (![b₀, b] i.succ) := by
    funext i; fin_cases i; rfl
  have hw : ![D A B b₀, D A B b] = fun i ↦ D A B (![b₀, b] i) := by
    funext i; fin_cases i <;> rfl
  rwa [hv, hw]

/-- `x w ∧ w = 0` for a one-form `w`. -/
theorem ιMulti_two_smul_self (x : B) (w : Ω[B⁄A]) :
    exteriorPower.ιMulti B 2 ![x • w, w] = 0 := by
  classical
  have h : (![x • w, w] : Fin 2 → Ω[B⁄A]) = Function.update ![w, w] 0 (x • w) := by
    funext i; fin_cases i <;> rfl
  have h' : Function.update ![w, w] 0 w = ![w, w] := by
    funext i; fin_cases i <;> rfl
  rw [h, AlternatingMap.map_update_smul, h',
    AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide), smul_zero]

/-- The one-form `ιMulti B 1 (fun _ ↦ ω)` is additive in `ω`. -/
theorem ιMulti_one_add (ω ω' : Ω[B⁄A]) :
    exteriorPower.ιMulti B 1 (fun _ ↦ ω + ω') =
      exteriorPower.ιMulti B 1 (fun _ ↦ ω) + exteriorPower.ιMulti B 1 (fun _ ↦ ω') :=
  map_add (exteriorPower.oneEquiv B (Ω[B⁄A])).symm ω ω'

/-- The one-form `ιMulti B 1 (fun _ ↦ ω)` is linear in `ω`. -/
theorem ιMulti_one_smul (c : B) (ω : Ω[B⁄A]) :
    exteriorPower.ιMulti B 1 (fun _ ↦ c • ω) = c • exteriorPower.ιMulti B 1 (fun _ ↦ ω) :=
  map_smul (exteriorPower.oneEquiv B (Ω[B⁄A])).symm c ω

/-- The one-form `ιMulti B 1 (fun _ ↦ 0)` is `0`. -/
theorem ιMulti_one_zero : exteriorPower.ιMulti B 1 (fun _ ↦ (0 : Ω[B⁄A])) = 0 :=
  map_zero (exteriorPower.oneEquiv B (Ω[B⁄A])).symm

/-- The exact one-form `dc` is closed. -/
theorem deRhamDifferential_ιMulti_one_D (c : B) :
    deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ D A B c)) = 0 := by
  rw [← deRhamDifferential_zero_smul_ιMulti c Fin.elim0, deRhamDifferential_comp_self]

/-- The de Rham differential of `ω ∧ ξ`, for `ω` a one-form and `ξ` closed, is `dω ∧ ξ`, read in
the exterior algebra. -/
theorem coe_deRhamDifferential_wedgeLeft (ω : Ω[B⁄A]) (j : ℕ) (ξ : ⋀[B]^j (Ω[B⁄A]))
    (hξ : deRhamDifferential (A := A) j ξ = 0) :
    ((deRhamDifferential (A := A) (j + 1) (exteriorPower.wedgeLeft ω j ξ) :
        ⋀[B]^(j + 2) (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A])) =
      ((deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ ω)) :
        ⋀[B]^2 (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A])) * (ξ : ExteriorAlgebra B (Ω[B⁄A])) := by
  have hcoe : ((exteriorPower.wedgeLeft ω j ξ : ⋀[B]^(j + 1) (Ω[B⁄A])) :
      ExteriorAlgebra B (Ω[B⁄A])) =
      ((exteriorPower.wedgeMul 1 j (exteriorPower.ιMulti B 1 (fun _ ↦ ω)) ξ :
        ⋀[B]^(1 + j) (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A])) := by
    rw [exteriorPower.coe_wedgeLeft, exteriorPower.wedgeMul_apply_coe,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rw [coe_deRhamDifferential_congr (A := A) (Nat.add_comm j 1) hcoe,
    coe_deRhamDifferential_wedgeMul, hξ]
  simp

/-- **The wedge of closed one-forms is closed.** -/
theorem ιMulti_mem_closedForms {i : ℕ} (v : Fin i → Ω[B⁄A])
    (hv : ∀ k, deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ v k)) = 0) :
    deRhamDifferential (A := A) i (exteriorPower.ιMulti B i v) = 0 := by
  induction i with
  | zero =>
      have h := deRhamDifferential_zero_smul_ιMulti (A := A) (1 : B) v
      rw [one_smul, Derivation.map_one_eq_zero] at h
      rw [h, ιMulti_one_zero]
  | succ j ih =>
      have hv' : exteriorPower.ιMulti B (j + 1) v =
          exteriorPower.wedgeLeft (v 0) j (exteriorPower.ιMulti B j (Fin.tail v)) := by
        rw [exteriorPower.wedgeLeft_ιMulti, Fin.cons_self_tail]
      rw [hv']
      apply Subtype.ext
      rw [coe_deRhamDifferential_wedgeLeft _ _ _ (ih (Fin.tail v) fun k ↦ hv k.succ), hv 0]
      simp

end OneForms

section Twisted

variable (p : ℕ) [Fact p.Prime] (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [CharP B p]

variable {A B} in
omit [Fact p.Prime] [CharP B p] in
/-- The one-form `b^{p-1} db` is closed. -/
theorem deRhamDifferential_pow_pred_smul_D (b : B) :
    deRhamDifferential (A := A) 1
        ((b ^ (p - 1)) • exteriorPower.ιMulti B 1 (fun _ ↦ D A B b)) = 0 := by
  rw [deRhamDifferential_one_smul_ιMulti_D, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul B, smul_smul]
  exact ιMulti_two_smul_self _ _

variable {A B} in
/-- The exact one-form `dc`, as the twisted differential of the degree-zero form `c`. -/
theorem twist_ιMulti_one_D_mem_exactForms (c : B) :
    twist p (exteriorPower.ιMulti B 1 (fun _ ↦ D A B c)) ∈ exactForms p A B 1 :=
  (twist_mem_exactForms_succ _).2 ⟨c • exteriorPower.ιMulti B 0 Fin.elim0,
    deRhamDifferential_zero_smul_ιMulti c _⟩

/-! ### The derivation `b ↦ [b^{p-1} db]` -/

variable {A B} in
/-- **The closed one-form `b^{p-1} db`**, as an element of the closed forms of the twisted
complex. -/
def cartierForm (b : B) : closedForms p A B 1 :=
  ⟨twist p ((b ^ (p - 1)) • exteriorPower.ιMulti B 1 (fun _ ↦ D A B b)),
    (twist_mem_closedForms _).2 (deRhamDifferential_pow_pred_smul_D p b)⟩

variable {A B} in
/-- The underlying twisted form of `cartierForm p b` is `b^{p-1} db`. -/
theorem coe_cartierForm (b : B) :
    (cartierForm p (A := A) b : twistedForms p A B 1) =
      twist p ((b ^ (p - 1)) • exteriorPower.ιMulti B 1 (fun _ ↦ D A B b)) := rfl

variable {A B} in
/-- **Additivity of `b ↦ [b^{p-1} db]`.** -/
theorem cohomologyMk_cartierForm_add (x y : B) :
    cohomologyMk p A B 1 (cartierForm p (x + y)) =
      cohomologyMk p A B 1 (cartierForm p x) + cohomologyMk p A B 1 (cartierForm p y) := by
  rw [← map_add, cohomologyMk_eq_iff, Submodule.coe_add, coe_cartierForm, coe_cartierForm,
    coe_cartierForm, ← map_add, ← map_sub, ← ιMulti_one_smul, ← ιMulti_one_smul,
    ← ιMulti_one_smul, pow_pred_smul_D_add p (A := A) x y, ιMulti_one_add, ιMulti_one_add]
  convert twist_ιMulti_one_D_mem_exactForms p (A := A)
    (MvPolynomial.aeval ![x, y] (addPowQuotient p)) using 2
  abel

variable {A B} in
/-- The Leibniz rule for `cartierForm`, for the twisted action. -/
theorem cartierForm_mul (x y : B) :
    cartierForm p (A := A) (x * y) = x • cartierForm p y + y • cartierForm p x := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_cartierForm, coe_cartierForm,
    coe_cartierForm, smul_twist, smul_twist, ← map_add]
  congr 1
  rw [Derivation.leibniz, ιMulti_one_add, ιMulti_one_smul, ιMulti_one_smul, smul_add]
  simp only [smul_smul]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  congr 2 <;> simp only [Nat.add_sub_cancel, mul_pow, pow_succ] <;> ring

/-- **The derivation `b ↦ [b^{p-1} db]`** of `B` over `A` into `H^1(F_*Ω^•_{B/A})`. -/
def cartierDerivation : Derivation A B (cohomology p A B 1) :=
  Derivation.mk'
    { toFun b := cohomologyMk p A B 1 (cartierForm p b)
      map_add' := cohomologyMk_cartierForm_add p
      map_smul' a b := by
        have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
        change cohomologyMk p A B 1 (cartierForm p (a • b)) =
          algebraMap A B a • cohomologyMk p A B 1 (cartierForm p b)
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        rw [Submodule.coe_smul, coe_cartierForm, coe_cartierForm, smul_twist]
        congr 1
        rw [(D A B).map_smul, ← algebraMap_smul B a (D A B b), ιMulti_one_smul, smul_smul,
          smul_smul, Algebra.smul_def]
        congr 1
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel, mul_pow, pow_succ]
        ring }
    (fun x y ↦ by
      change cohomologyMk p A B 1 (cartierForm p (x * y)) =
        x • cohomologyMk p A B 1 (cartierForm p y) + y • cohomologyMk p A B 1 (cartierForm p x)
      rw [cartierForm_mul, map_add, map_smul, map_smul])

variable {A B} in
/-- `cartierDerivation` sends `b` to the class of `b^{p-1} db`. -/
@[simp]
theorem cartierDerivation_apply (b : B) :
    cartierDerivation p A B b = cohomologyMk p A B 1 (cartierForm p b) := rfl

/-- **The inverse Cartier map in degree one**, `Ω[B⁄A] ⟶ H^1(F_*Ω^•_{B/A})`,
`db ↦ [b^{p-1} db]`. -/
def inverseCartierOne : Ω[B⁄A] →ₗ[B] cohomology p A B 1 :=
  (cartierDerivation p A B).liftKaehlerDifferential

variable {A B} in
/-- `C⁻¹(db) = [b^{p-1} db]` in degree one. -/
@[simp]
theorem inverseCartierOne_D (b : B) :
    inverseCartierOne p A B (D A B b) = cohomologyMk p A B 1 (cartierForm p b) :=
  (cartierDerivation p A B).liftKaehlerDifferential_comp_D b

/-! ### Exactness of wedges with an exact factor -/

variable {A B} in
/-- **A wedge of closed one-forms is exact as soon as its first factor is exact**: for
`ξ` closed, `dc ∧ ξ = d(c ξ)`. -/
theorem twist_ιMulti_cons_D_mem_exactForms {j : ℕ} (c : B) (w : Fin j → Ω[B⁄A])
    (hw : ∀ k, deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ w k)) = 0) :
    twist p (exteriorPower.ιMulti B (j + 1) (Fin.cons (D A B c) w)) ∈ exactForms p A B (j + 1) := by
  refine (twist_mem_exactForms_succ _).2 ⟨c • exteriorPower.ιMulti B j w, ?_⟩
  rw [deRhamDifferential_smul, ιMulti_mem_closedForms w hw, smul_zero, add_zero,
    exteriorPower.wedgeLeft_ιMulti]

variable {A B} in
/-- **A wedge of closed one-forms is exact as soon as one factor is exact.** -/
theorem twist_ιMulti_update_D_mem_exactForms {i : ℕ} (v : Fin i → Ω[B⁄A])
    (hv : ∀ k, deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ v k)) = 0)
    (k : Fin i) (c : B) :
    twist p (exteriorPower.ιMulti B i (Function.update v k (D A B c))) ∈ exactForms p A B i := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := k.2; omega⟩
  have hv' : ∀ l, deRhamDifferential (A := A) 1
      (exteriorPower.ιMulti B 1 (fun _ ↦ Function.update v k (D A B c) l)) = 0 := by
    intro l
    by_cases hl : l = k
    · rw [hl, Function.update_self]; exact deRhamDifferential_ιMulti_one_D c
    · rw [Function.update_of_ne hl]; exact hv l
  let e : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 k
  have hswap := (exteriorPower.ιMulti B (j + 1)).map_perm (Function.update v k (D A B c)) e
  have h0 : (Function.update v k (D A B c) ∘ e) 0 = D A B c := by
    simp [e, Equiv.swap_apply_left]
  have hcomp : Function.update v k (D A B c) ∘ e =
      Fin.cons (D A B c) (Fin.tail (Function.update v k (D A B c) ∘ e)) :=
    (Fin.cons_self_tail _).symm.trans (by rw [h0])
  have hmem := twist_ιMulti_cons_D_mem_exactForms p c
    (Fin.tail (Function.update v k (D A B c) ∘ e)) (fun l ↦ hv' (e l.succ))
  rw [← hcomp, hswap] at hmem
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
  · rwa [h, one_smul] at hmem
  · rw [h, Units.neg_smul, one_smul, map_neg] at hmem
    simpa using (exactForms p A B (j + 1)).neg_mem hmem

/-! ### The wedge of classes -/

variable {A B} in
/-- The underlying differential of a closed one-form, through `⋀^1 Ω ≅ Ω`. -/
abbrev closedOneForm (z : closedForms p A B 1) : Ω[B⁄A] :=
  exteriorPower.oneEquiv B (Ω[B⁄A]) ((twist p).symm (z : twistedForms p A B 1))

variable {A B} in
/-- A closed one-form is the one-form of its underlying differential. -/
theorem ιMulti_one_closedOneForm (z : closedForms p A B 1) :
    exteriorPower.ιMulti B 1 (fun _ ↦ closedOneForm p z) =
      (twist p).symm (z : twistedForms p A B 1) :=
  (exteriorPower.oneEquiv B (Ω[B⁄A])).symm_apply_apply _

variable {A B} in
/-- The underlying differential of a closed one-form is closed. -/
theorem deRhamDifferential_ιMulti_closedOneForm (z : closedForms p A B 1) :
    deRhamDifferential (A := A) 1 (exteriorPower.ιMulti B 1 (fun _ ↦ closedOneForm p z)) = 0 := by
  rw [ιMulti_one_closedOneForm]
  exact (mem_closedForms _).1 z.2

variable {A B} in
/-- `closedOneForm` is additive. -/
theorem closedOneForm_add (z w : closedForms p A B 1) :
    closedOneForm p (z + w) = closedOneForm p z + closedOneForm p w := by
  simp only [closedOneForm, Submodule.coe_add, map_add]

variable {A B} in
/-- `closedOneForm` turns the twisted action of `c` into the action of `c^p`. -/
theorem closedOneForm_smul (c : B) (z : closedForms p A B 1) :
    closedOneForm p (c • z) = c ^ p • closedOneForm p z := by
  simp only [closedOneForm, Submodule.coe_smul, twist_symm_smul, map_smul]

/-- **The wedge of closed one-forms**, as an alternating map for the twisted module structures:
`(z₁, …, z_i) ↦ z₁ ∧ ⋯ ∧ z_i`, which is closed. -/
def wedgeClosed (i : ℕ) :
    closedForms p A B 1 [⋀^Fin i]→ₗ[B] closedForms p A B i where
  toFun z := ⟨twist p (exteriorPower.ιMulti B i (closedOneForm p ∘ z)),
    (twist_mem_closedForms _).2 (ιMulti_mem_closedForms _ fun k ↦
      deRhamDifferential_ιMulti_closedOneForm p (z k))⟩
  map_update_add' := by
    intro _ z k a b
    apply Subtype.ext
    simp only [Submodule.coe_add, Function.comp_update, closedOneForm_add,
      AlternatingMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ z k c a
    apply Subtype.ext
    simp only [Submodule.coe_smul, Function.comp_update, closedOneForm_smul,
      AlternatingMap.map_update_smul, smul_twist]
  map_eq_zero_of_eq' z k l h hkl := by
    apply Subtype.ext
    change twist p (exteriorPower.ιMulti B i (closedOneForm p ∘ z)) = 0
    rw [AlternatingMap.map_eq_zero_of_eq _ (closedOneForm p ∘ z) (i := k) (j := l)
      (by simp [h]) hkl, map_zero]

variable {A B} in
/-- The underlying twisted form of `wedgeClosed p A B i z` is `z₁ ∧ ⋯ ∧ z_i`. -/
theorem coe_wedgeClosed {i : ℕ} (z : Fin i → closedForms p A B 1) :
    (wedgeClosed p A B i z : twistedForms p A B i) =
      twist p (exteriorPower.ιMulti B i (closedOneForm p ∘ z)) := rfl

variable {A B} in
/-- A closed one-form cohomologous to zero is `dc` for some `c`. -/
theorem exists_closedOneForm_eq_D (w : closedForms p A B 1)
    (hw : (w : twistedForms p A B 1) ∈ exactForms p A B 1) :
    ∃ c : B, closedOneForm p w = D A B c := by
  obtain ⟨x, hx⟩ := (twist p).surjective (w : twistedForms p A B 1)
  rw [← hx] at hw
  obtain ⟨y, hy⟩ := (twist_mem_exactForms_succ x).1 hw
  refine ⟨exteriorPower.zeroEquiv B (Ω[B⁄A]) y, ?_⟩
  have hy' : y = exteriorPower.zeroEquiv B (Ω[B⁄A]) y •
      exteriorPower.ιMulti B 0 (Fin.elim0 : Fin 0 → Ω[B⁄A]) := by
    apply (exteriorPower.zeroEquiv B (Ω[B⁄A])).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  rw [closedOneForm, ← hx, AddEquiv.symm_apply_apply, ← hy]
  conv_lhs => rw [hy']
  rw [deRhamDifferential_zero_smul_ιMulti, exteriorPower.oneEquiv_ιMulti]

variable {A B} in
/-- Replacing one closed one-form by a cohomologous one does not change the class of the
wedge. -/
theorem cohomologyMk_wedgeClosed_update {i : ℕ} (z : Fin i → closedForms p A B 1)
    (k : Fin i) (w : closedForms p A B 1)
    (hw : cohomologyMk p A B 1 w = cohomologyMk p A B 1 (z k)) :
    cohomologyMk p A B i (wedgeClosed p A B i (Function.update z k w)) =
      cohomologyMk p A B i (wedgeClosed p A B i z) := by
  classical
  have hsplit : w = z k + (w - z k) := by abel
  rw [hsplit, (wedgeClosed p A B i).map_update_add, Function.update_eq_self, map_add,
    add_eq_left, cohomologyMk_eq_zero_iff]
  obtain ⟨c, hc⟩ := exists_closedOneForm_eq_D p (w - z k) ((cohomologyMk_eq_iff _ _).1 hw)
  rw [coe_wedgeClosed, Function.comp_update, hc]
  exact twist_ιMulti_update_D_mem_exactForms p _
    (fun l ↦ deRhamDifferential_ιMulti_closedOneForm p (z l)) k c

variable {A B} in
/-- **The class of the wedge depends only on the classes of the factors.** -/
theorem cohomologyMk_wedgeClosed_congr {i : ℕ} (z z' : Fin i → closedForms p A B 1)
    (h : ∀ k, cohomologyMk p A B 1 (z k) = cohomologyMk p A B 1 (z' k)) :
    cohomologyMk p A B i (wedgeClosed p A B i z) =
      cohomologyMk p A B i (wedgeClosed p A B i z') := by
  classical
  have key : ∀ S : Finset (Fin i),
      cohomologyMk p A B i (wedgeClosed p A B i fun k ↦ if k ∈ S then z' k else z k) =
        cohomologyMk p A B i (wedgeClosed p A B i z) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
        have hupd : (fun k ↦ if k ∈ insert a S then z' k else z k) =
            Function.update (fun k ↦ if k ∈ S then z' k else z k) a (z' a) := by
          funext k
          by_cases hk : k = a
          · subst hk; simp
          · simp [Finset.mem_insert, hk]
        rw [hupd, cohomologyMk_wedgeClosed_update p _ a (z' a) (by simp [ha, h a]), ih]
  simpa only [Finset.mem_univ, ite_true] using (key Finset.univ).symm

/-- **The wedge of classes** `H^1 × ⋯ × H^1 ⟶ H^i`, read off representatives. -/
def wedgeClass (i : ℕ) : cohomology p A B 1 [⋀^Fin i]→ₗ[B] cohomology p A B i where
  toFun x := cohomologyMk p A B i (wedgeClosed p A B i
    (Function.surjInv (cohomologyMk_surjective p A B 1) ∘ x))
  map_update_add' := by
    intro _ x k a b
    have hs : ∀ y, cohomologyMk p A B 1 (Function.surjInv (cohomologyMk_surjective p A B 1) y) =
        y := Function.surjInv_eq _
    simp only [Function.comp_update]
    rw [← map_add, ← AlternatingMap.map_update_add]
    apply cohomologyMk_wedgeClosed_congr
    intro l
    by_cases hl : l = k
    · rw [hl, Function.update_self, Function.update_self, map_add, hs, hs, hs]
    · rw [Function.update_of_ne hl, Function.update_of_ne hl]
  map_update_smul' := by
    intro _ x k c a
    have hs : ∀ y, cohomologyMk p A B 1 (Function.surjInv (cohomologyMk_surjective p A B 1) y) =
        y := Function.surjInv_eq _
    simp only [Function.comp_update]
    rw [← map_smul, ← AlternatingMap.map_update_smul]
    apply cohomologyMk_wedgeClosed_congr
    intro l
    by_cases hl : l = k
    · rw [hl, Function.update_self, Function.update_self, map_smul, hs, hs]
    · rw [Function.update_of_ne hl, Function.update_of_ne hl]
  map_eq_zero_of_eq' x k l h hkl := by
    change cohomologyMk p A B i (wedgeClosed p A B i _) = 0
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (i := k) (j := l) (by simp [h]) hkl, map_zero]

variable {A B} in
/-- The wedge of the classes of closed one-forms is the class of their wedge. -/
theorem wedgeClass_cohomologyMk {i : ℕ} (z : Fin i → closedForms p A B 1) :
    wedgeClass p A B i (cohomologyMk p A B 1 ∘ z) =
      cohomologyMk p A B i (wedgeClosed p A B i z) :=
  cohomologyMk_wedgeClosed_congr p _ _ fun _ ↦ Function.surjInv_eq _ _

/-! ### The inverse Cartier map -/

/-- **The inverse Cartier map** `C⁻¹ : Ω^i_{B/A} ⟶ H^i(F_*Ω^•_{B/A})`,
`db₁ ∧ ⋯ ∧ db_i ↦ [b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i]`, a `B`-linear map for the action of `B`
on the target through the Frobenius. -/
def inverseCartier (i : ℕ) : ⋀[B]^i (Ω[B⁄A]) →ₗ[B] cohomology p A B i :=
  exteriorPower.alternatingMapLinearEquiv
    ((wedgeClass p A B i).compLinearMap (inverseCartierOne p A B))

variable {A B} in
/-- The closed one-form `b^{p-1} db`, read in `Ω[B⁄A]`. -/
theorem closedOneForm_cartierForm (b : B) :
    closedOneForm p (cartierForm p (A := A) b) = b ^ (p - 1) • D A B b := by
  rw [closedOneForm, coe_cartierForm, AddEquiv.symm_apply_apply, map_smul,
    exteriorPower.oneEquiv_ιMulti]

variable {A B} in
/-- **The value of the inverse Cartier map** on `db₁ ∧ ⋯ ∧ db_i`: the class of
`b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i`. -/
theorem inverseCartier_ιMulti_D {i : ℕ} (b : Fin i → B) :
    inverseCartier p A B i (exteriorPower.ιMulti B i fun k ↦ D A B (b k)) =
      cohomologyMk p A B i (wedgeClosed p A B i (cartierForm p ∘ b)) := by
  rw [inverseCartier, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, ← wedgeClass_cohomologyMk]
  congr 1
  funext k
  exact inverseCartierOne_D p (b k)

variable {A B} in
/-- The form representing `C⁻¹(db₁ ∧ ⋯ ∧ db_i)`. -/
theorem coe_wedgeClosed_cartierForm {i : ℕ} (b : Fin i → B) :
    (wedgeClosed p A B i (cartierForm p ∘ b) : twistedForms p A B i) =
      twist p (exteriorPower.ιMulti B i fun k ↦ b k ^ (p - 1) • D A B (b k)) := by
  rw [coe_wedgeClosed]
  congr 2
  funext k
  exact closedOneForm_cartierForm p (b k)

end Twisted

end KaehlerDifferential.Cartier

end
