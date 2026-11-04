module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import StacksFrontier.RingTheory.DeRham.Complex
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz

/-!
# The Frobenius-twisted de Rham complex and the inverse Cartier map

Let `p` be a prime, `A → B` a ring map with `B` of characteristic `p`, and `Ω^•_{B/A}` the de Rham
complex of `B` over `A`. Since `d(b^p) = p b^{p-1} db = 0`, the Leibniz rule gives
`d(b^p ω) = b^p dω`: the differentials are linear for the action of `B` on every `Ω^i_{B/A}`
through its Frobenius `b ↦ b^p`. Reading each `Ω^i_{B/A}` as a `B`-module in this way gives the
**Frobenius-twisted de Rham complex** `F_*Ω^•_{B/A}`, a complex of `B`-modules with `B`-linear
differentials; it is the affine form of the pushforward of the de Rham complex along the absolute
Frobenius, whose cohomology the Cartier isomorphism computes.

The **inverse Cartier map** is the `B`-linear map

`C⁻¹ : Ω^i_{B/A} ⟶ H^i(F_*Ω^•_{B/A})`,
`b₀ db₁ ∧ ⋯ ∧ db_i ↦ [b₀^p b₁^{p-1} db₁ ∧ ⋯ ∧ b_i^{p-1} db_i]`.

Its degree-one part comes from the `A`-derivation `b ↦ [b^{p-1} db]` of `B` into `H^1`: additivity
holds because `(x + y)^{p-1} d(x + y) - x^{p-1} dx - y^{p-1} dy` is the differential of the
universal polynomial `((x + y)^p - x^p - y^p) / p`, and the Leibniz rule
`(bc)^{p-1} d(bc) = b^p · c^{p-1} dc + c^p · b^{p-1} db` is the twisted module structure. In higher
degrees the wedge of closed one-forms is closed, and it is exact as soon as one factor is exact, so
the wedge of classes is a well-defined alternating map on `H^1`.

No smoothness is assumed here. The inverse Cartier map itself is built in
`StacksFrontier.RingTheory.DeRham.Cartier.InverseCartier`; that it is bijective when `B` has
Frobenius coordinates over `A` (for instance a polynomial algebra over a perfect ring) is
`StacksFrontier.RingTheory.DeRham.Cartier.Coordinates` and
`StacksFrontier.RingTheory.DeRham.Cartier.Polynomial`.

## Main definitions

* `KaehlerDifferential.Cartier.twistedForms`: `Ω^i_{B/A}` as a `B`-module through the Frobenius,
  and `KaehlerDifferential.Cartier.twist` the identification of its elements with forms.
* `KaehlerDifferential.Cartier.twistedD`: the de Rham differential, `B`-linear between these.
* `KaehlerDifferential.Cartier.twistedDeRhamComplex`: the Frobenius-twisted de Rham complex
  `F_*Ω^•_{B/A}`, as a `CochainComplex (ModuleCat B) ℕ`.
* `KaehlerDifferential.Cartier.closedForms`, `KaehlerDifferential.Cartier.exactForms` and
  `KaehlerDifferential.Cartier.cohomology`: the closed and exact forms and the cohomology
  `H^i(F_*Ω^•_{B/A})` as a `B`-module.

## Main results

* `KaehlerDifferential.Cartier.deRhamDifferential_pow_smul`: `d(b^p ω) = b^p dω`.
* `KaehlerDifferential.Cartier.pow_pred_smul_D_add`: `(x + y)^{p-1} d(x + y) - x^{p-1} dx -
  y^{p-1} dy` is the differential of `((x + y)^p - x^p - y^p) / p` evaluated at `(x, y)`.

## References

* P. Cartier, *Une nouvelle opération sur les formes différentielles*, C. R. Acad. Sci. Paris 244
  (1957).
* N. Katz, *Nilpotent connections and the monodromy theorem*, Publ. Math. IHÉS 39 (1970), §7.
* P. Deligne and L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987), §1.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace KaehlerDifferential.Cartier

/-! ### The chain rule for polynomials in several variables -/

section ChainRule

variable {σ : Type*} [Fintype σ] {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
  [Module R M]

/-- **The chain rule** for a polynomial with integer coefficients in several variables:
`D(f(v)) = ∑ᵢ (∂ᵢf)(v) • D(vᵢ)`. -/
theorem derivation_aeval_mvPolynomial (D : Derivation ℤ R M) (v : σ → R)
    (f : MvPolynomial σ ℤ) :
    D (MvPolynomial.aeval v f) =
      ∑ i, MvPolynomial.aeval v (MvPolynomial.pderiv i f) • D (v i) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]
  | mul_X f i hf =>
      have hpd : ∀ x, MvPolynomial.aeval v (MvPolynomial.pderiv x (f * MvPolynomial.X i)) =
          MvPolynomial.aeval v (MvPolynomial.pderiv x f) * v i +
            (if x = i then MvPolynomial.aeval v f else 0) := by
        intro x
        rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add,
          map_mul, map_mul, MvPolynomial.aeval_X]
        by_cases h : x = i
        · subst h; simp [mul_comm, add_comm]
        · simp [Ne.symm h, h, mul_comm]
      rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hf, Finset.smul_sum]
      simp only [hpd, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul, mul_comm (v i)]
      rw [add_comm]

end ChainRule

/-! ### The universal identity behind additivity -/

section Additivity

variable (p : ℕ) [hp : Fact p.Prime]

/-- `((X + Y)^p - X^p - Y^p) / p`, a polynomial with integer coefficients. -/
def addPowQuotient : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 * MvPolynomial.X 1 *
    Classical.choose (exists_add_pow_prime_eq hp.out (MvPolynomial.X (R := ℤ) (0 : Fin 2))
      (MvPolynomial.X 1))

/-- `(X + Y)^p = X^p + Y^p + p · addPowQuotient p` in `ℤ[X, Y]`. -/
theorem add_pow_eq_addPowQuotient :
    (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ p =
      MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ p + (p : MvPolynomial (Fin 2) ℤ) *
        addPowQuotient p := by
  rw [addPowQuotient, ← mul_assoc, ← mul_assoc]
  exact Classical.choose_spec (exists_add_pow_prime_eq hp.out (MvPolynomial.X (R := ℤ) (0 : Fin 2))
      (MvPolynomial.X 1))

/-- In `ℤ[X, Y]`, the partial derivatives of `((X+Y)^p-X^p-Y^p)/p` are `(X+Y)^{p-1} - X^{p-1}`
and `(X+Y)^{p-1} - Y^{p-1}`. -/
theorem pderiv_addPowQuotient (i : Fin 2) :
    MvPolynomial.pderiv i (addPowQuotient p) =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (p - 1) - MvPolynomial.X i ^ (p - 1) := by
  have h := congrArg (MvPolynomial.pderiv i) (add_pow_eq_addPowQuotient p)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
    rw [← map_natCast (MvPolynomial.C (σ := Fin 2) (R := ℤ))]
    exact (map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).2 (by exact_mod_cast hp.out.ne_zero)
  apply mul_left_cancel₀ hp0
  have hX : MvPolynomial.pderiv i (MvPolynomial.X 0 + MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℤ) = 1 := by
    fin_cases i <;> simp [MvPolynomial.pderiv_X]
  simp only [Derivation.leibniz_pow, hX, map_add, Derivation.leibniz, MvPolynomial.pderiv_X,
    smul_eq_mul, mul_one] at h
  fin_cases i <;>
    simp [nsmul_eq_mul] at h <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    linear_combination -h

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [CharP B p]

omit [CharP B p] in
/-- `(x + y)^{p-1} d(x + y) - x^{p-1} dx - y^{p-1} dy` is the differential of
`((x + y)^p - x^p - y^p) / p` evaluated at `(x, y)`. -/
theorem pow_pred_smul_D_add (x y : B) :
    (x + y) ^ (p - 1) • D A B (x + y) =
      x ^ (p - 1) • D A B x + y ^ (p - 1) • D A B y +
        D A B (MvPolynomial.aeval ![x, y] (addPowQuotient p)) := by
  have h := derivation_aeval_mvPolynomial ((D A B).restrictScalars ℤ) ![x, y] (addPowQuotient p)
  simp only [Derivation.coe_restrictScalars, Fin.sum_univ_two, pderiv_addPowQuotient, map_sub,
    map_pow, map_add, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_smul] at h
  rw [h, map_add, smul_add]
  abel

end Additivity

/-! ### Linearity of the differential for the Frobenius action -/

section Twist

variable (p : ℕ) [Fact p.Prime] (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [CharP B p]

variable {B} in
omit [Fact p.Prime] in
/-- `d(b^p) = 0` in characteristic `p`. -/
theorem D_pow_char (b : B) : D A B (b ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, CharP.cast_eq_zero, zero_smul]

variable {B} in
omit [Fact p.Prime] in
/-- **The de Rham differential is linear for the Frobenius**: `d(b^p ω) = b^p dω`. -/
theorem deRhamDifferential_pow_smul (i : ℕ) (b : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i (b ^ p • ξ) = b ^ p • deRhamDifferential (A := A) i ξ := by
  rw [deRhamDifferential_smul, D_pow_char p A b, exteriorPower.wedgeLeft_zero, LinearMap.zero_apply,
    zero_add]

/-- `Ω^i_{B/A}` as a `B`-module through the Frobenius `b ↦ b^p`: the degree-`i` term of the
Frobenius-twisted de Rham complex. -/
def twistedForms (i : ℕ) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (frobenius B p)).obj (ModuleCat.of B (⋀[B]^i (Ω[B⁄A])))

variable {A B} in
/-- A form, read as an element of the twisted forms: the identity of the underlying groups. -/
def twist {i : ℕ} : ⋀[B]^i (Ω[B⁄A]) ≃+ twistedForms p A B i :=
  AddEquiv.refl _

variable {p A B} in
/-- The twisted action of `b` is the action of `b^p`. -/
theorem smul_twist {i : ℕ} (b : B) (x : ⋀[B]^i (Ω[B⁄A])) :
    b • twist p x = twist p (b ^ p • x) :=
  rfl

variable {p A B} in
/-- Reading a twisted form back as a form turns the action of `b` into that of `b^p`. -/
theorem twist_symm_smul {i : ℕ} (b : B) (y : twistedForms p A B i) :
    (twist p).symm (b • y) = b ^ p • (twist p).symm y := by
  obtain ⟨x, rfl⟩ := (twist p).surjective y
  rw [smul_twist, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- The de Rham differential, `B`-linear between the Frobenius-twisted forms. -/
def twistedD (i : ℕ) : twistedForms p A B i →ₗ[B] twistedForms p A B (i + 1) where
  toFun y := twist p (deRhamDifferential (A := A) i ((twist p).symm y))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' b x := by
    rw [RingHom.id_apply, twist_symm_smul, deRhamDifferential_pow_smul, smul_twist]

variable {p A B} in
/-- The twisted differential of a form is its de Rham differential. -/
@[simp]
theorem twistedD_twist (i : ℕ) (x : ⋀[B]^i (Ω[B⁄A])) :
    twistedD p A B i (twist p x) = twist p (deRhamDifferential (A := A) i x) := by
  simp [twistedD]

/-- The twisted differentials square to zero. -/
theorem twistedD_comp_twistedD (i : ℕ) :
    (twistedD p A B (i + 1)).comp (twistedD p A B i) = 0 := by
  ext y
  obtain ⟨x, rfl⟩ := (twist p).surjective y
  simp [deRhamDifferential_comp_self]

/-- **The Frobenius-twisted de Rham complex** `F_*Ω^•_{B/A}`: the de Rham complex of `B` over `A`
with `B` acting on every term through its Frobenius, a complex of `B`-modules. -/
def twistedDeRhamComplex : CochainComplex (ModuleCat.{u} B) ℕ :=
  CochainComplex.of (twistedForms p A B)
    (fun i ↦ ConcreteCategory.ofHom (C := ModuleCat.{u} B) (twistedD p A B i))
    (fun i ↦ ModuleCat.hom_ext (twistedD_comp_twistedD p A B i))

/-- The degree-`i` term of the twisted de Rham complex is `twistedForms p A B i`. -/
@[simp]
theorem twistedDeRhamComplex_X (i : ℕ) :
    (twistedDeRhamComplex p A B).X i = twistedForms p A B i := rfl

/-- The differential of the twisted de Rham complex out of degree `i` is `twistedD p A B i`. -/
@[simp]
theorem twistedDeRhamComplex_d (i : ℕ) :
    (twistedDeRhamComplex p A B).d i (i + 1) =
      ConcreteCategory.ofHom (C := ModuleCat.{u} B) (twistedD p A B i) :=
  CochainComplex.of_d (twistedForms p A B)
    (fun i ↦ ConcreteCategory.ofHom (C := ModuleCat.{u} B) (twistedD p A B i)) i

/-! ### Closed forms, exact forms and cohomology -/

/-- The closed forms of degree `i`, a `B`-submodule of the twisted forms. -/
def closedForms (i : ℕ) : Submodule B (twistedForms p A B i) :=
  LinearMap.ker (twistedD p A B i)

/-- The exact forms of degree `i`: zero in degree `0`, the image of `d` in positive degrees. -/
def exactForms : (i : ℕ) → Submodule B (twistedForms p A B i)
  | 0 => ⊥
  | i + 1 => LinearMap.range (twistedD p A B i)

variable {p A B} in
/-- A form is closed as a twisted form exactly when its de Rham differential vanishes. -/
theorem twist_mem_closedForms {i : ℕ} (x : ⋀[B]^i (Ω[B⁄A])) :
    twist p x ∈ closedForms p A B i ↔ deRhamDifferential (A := A) i x = 0 := by
  rw [closedForms, LinearMap.mem_ker, twistedD_twist, AddEquivClass.map_eq_zero_iff]

variable {p A B} in
/-- A twisted form is closed exactly when the de Rham differential of the underlying form
vanishes. -/
theorem mem_closedForms {i : ℕ} (y : twistedForms p A B i) :
    y ∈ closedForms p A B i ↔ deRhamDifferential (A := A) i ((twist p).symm y) = 0 := by
  rw [← twist_mem_closedForms, AddEquiv.apply_symm_apply]

variable {p A B} in
/-- The only exact form of degree `0` is `0`. -/
theorem twist_mem_exactForms_zero (x : ⋀[B]^0 (Ω[B⁄A])) :
    twist p x ∈ exactForms p A B 0 ↔ x = 0 := by
  show twist p x ∈ (⊥ : Submodule B (twistedForms p A B 0)) ↔ _
  rw [Submodule.mem_bot, AddEquivClass.map_eq_zero_iff]

variable {p A B} in
/-- A form of degree `i + 1` is exact exactly when it is the de Rham differential of a form of
degree `i`. -/
theorem twist_mem_exactForms_succ {i : ℕ} (x : ⋀[B]^(i + 1) (Ω[B⁄A])) :
    twist p x ∈ exactForms p A B (i + 1) ↔ ∃ y, deRhamDifferential (A := A) i y = x := by
  show twist p x ∈ LinearMap.range (twistedD p A B i) ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(twist p).symm y, (twist p).injective ?_⟩
    rw [← hy, ← twistedD_twist, AddEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨twist p y, twistedD_twist i y⟩

/-- Exact forms are closed. -/
theorem exactForms_le_closedForms (i : ℕ) : exactForms p A B i ≤ closedForms p A B i := by
  cases i with
  | zero => exact bot_le
  | succ i =>
      intro y hy
      obtain ⟨x, rfl⟩ := (twist p).surjective y
      obtain ⟨z, rfl⟩ := (twist_mem_exactForms_succ x).1 hy
      exact (twist_mem_closedForms _).2 (deRhamDifferential_comp_self (A := A) (B := B) i z)

/-- The exact forms of degree `i`, as a submodule of the closed forms. -/
abbrev exactInClosed (i : ℕ) : Submodule B (closedForms p A B i) :=
  (exactForms p A B i).comap (closedForms p A B i).subtype

/-- **The cohomology** `H^i(F_*Ω^•_{B/A})` of the Frobenius-twisted de Rham complex, as a
`B`-module: closed forms modulo exact forms. -/
def cohomology (i : ℕ) : Type u :=
  closedForms p A B i ⧸ exactInClosed p A B i

/-- The additive group structure of the cohomology, as a quotient. -/
instance (i : ℕ) : AddCommGroup (cohomology p A B i) :=
  inferInstanceAs (AddCommGroup (closedForms p A B i ⧸ exactInClosed p A B i))

/-- The `B`-module structure of the cohomology, as a quotient. -/
instance (i : ℕ) : Module B (cohomology p A B i) :=
  inferInstanceAs (Module B (closedForms p A B i ⧸ exactInClosed p A B i))

/-- The cohomology is an `A`-module through `A → B`. -/
instance (i : ℕ) : Module A (cohomology p A B i) :=
  Module.compHom _ (algebraMap A B)

/-- The actions of `A` and `B` on the cohomology are compatible. -/
instance (i : ℕ) : IsScalarTower A B (cohomology p A B i) where
  smul_assoc a b x := by
    change (a • b) • x = algebraMap A B a • b • x
    rw [Algebra.smul_def, mul_smul]

/-- The class of a closed form, as a `B`-linear map. -/
def cohomologyMk (i : ℕ) : closedForms p A B i →ₗ[B] cohomology p A B i :=
  (exactInClosed p A B i).mkQ

/-- Every cohomology class is the class of a closed form. -/
theorem cohomologyMk_surjective (i : ℕ) : Function.Surjective (cohomologyMk p A B i) :=
  Submodule.mkQ_surjective _

variable {p A B} in
/-- The class of a closed form vanishes exactly when the form is exact. -/
theorem cohomologyMk_eq_zero_iff {i : ℕ} (x : closedForms p A B i) :
    cohomologyMk p A B i x = 0 ↔ (x : twistedForms p A B i) ∈ exactForms p A B i :=
  Submodule.Quotient.mk_eq_zero _

variable {p A B} in
/-- Two closed forms have the same class exactly when their difference is exact. -/
theorem cohomologyMk_eq_iff {i : ℕ} (x y : closedForms p A B i) :
    cohomologyMk p A B i x = cohomologyMk p A B i y ↔
      ((x : twistedForms p A B i) - y) ∈ exactForms p A B i :=
  Submodule.Quotient.eq _

end Twist

end KaehlerDifferential.Cartier

end
