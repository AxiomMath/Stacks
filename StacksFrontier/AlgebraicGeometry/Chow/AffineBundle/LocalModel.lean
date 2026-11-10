module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The local model of an affine bundle

Over an affine base `Spec B`, an affine bundle degenerating along the vanishing locus of an
element `f : B` is `Spec` of the ring `B[z₁, z₂]/(z₁z₂ - f)`. This ring is **free** as a
`B`-module, on the monomials `z₁^a` for `a ≥ 0` together with `z₂^b` for `b ≥ 1` — equivalently,
on a basis indexed by `ℤ`, with `n ≥ 0` giving `z₁^n` and `n < 0` giving `z₂^{-n}`. In particular
it is flat over `B`, and it is of finite type over `B`.

## Main definitions

* `Stacks.AffineBundle.LocalModel` — the ring `B[z₁, z₂]/(z₁z₂ - f)`.
* `Stacks.AffineBundle.coord` — the images of the two coordinates `z₁, z₂`.
* `Stacks.AffineBundle.basis` — the `ℤ`-indexed `B`-basis of the local model.

## Main results

* `Stacks.AffineBundle.coord_zero_mul_coord_one` — the defining relation `z₁z₂ = f`.
* `Stacks.AffineBundle.coord_pow_mul_coord_pow` — the normal form
  `z₁^a z₂^b = f^{min a b} z₁^{a-b} z₂^{b-a}`.
* `Stacks.AffineBundle.instFreeLocalModel`, `instFlatLocalModel`, `instFiniteTypeLocalModel` —
  the local model is free, hence flat, and of finite type over the base.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.AffineBundle

variable (B : Type u) [CommRing B] (f : B)

/-- The relation `z₁z₂ - f` cutting out the local model of an affine bundle over `B`. -/
def localRelation : MvPolynomial (Fin 2) B := X 0 * X 1 - C f

/-- **The local model `B[z₁, z₂]/(z₁z₂ - f)` of an affine bundle**: the affine bundle over
`Spec B` degenerating along the vanishing locus of `f`. -/
abbrev LocalModel : Type u := MvPolynomial (Fin 2) B ⧸ Ideal.span {localRelation B f}

/-- The quotient map onto the local model, read as a `B`-linear map. -/
abbrev mkL : MvPolynomial (Fin 2) B →ₗ[B] LocalModel B f :=
  (Ideal.Quotient.mkₐ B (Ideal.span {localRelation B f})).toLinearMap

/-- The image in the local model of the `i`-th coordinate of `B[z₁, z₂]`. -/
def coord (i : Fin 2) : LocalModel B f :=
  Ideal.Quotient.mk (Ideal.span {localRelation B f}) (X i)

private theorem mk_localRelation :
    (Ideal.Quotient.mk (Ideal.span {localRelation B f})) (localRelation B f) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- **The defining relation of the local model**: the two coordinates multiply to `f`. -/
theorem coord_zero_mul_coord_one :
    coord B f 0 * coord B f 1 = algebraMap B (LocalModel B f) f := by
  have h : (X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) B) = C f + localRelation B f := by
    rw [localRelation]; ring
  rw [coord, coord, ← map_mul, h, map_add, mk_localRelation, add_zero]
  rfl

private theorem mkL_X_mul_X_mul (p : MvPolynomial (Fin 2) B) :
    mkL B f (X 0 * X 1 * p) = f • mkL B f p := by
  have h : (X (0 : Fin 2) * X 1 * p : MvPolynomial (Fin 2) B)
      = C f * p + localRelation B f * p := by rw [localRelation]; ring
  change (Ideal.Quotient.mk (Ideal.span {localRelation B f})) _ = _
  rw [h, map_add, map_mul, map_mul, mk_localRelation, Algebra.smul_def]
  simp
  rfl

private theorem mkL_X_pow (a b : ℕ) :
    mkL B f (X 0 ^ a * X 1 ^ b)
      = f ^ min a b • mkL B f (X 0 ^ (a - b) * X 1 ^ (b - a)) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    cases b with
    | zero => simp
    | succ b =>
      rw [show (X 0 ^ (a + 1) * X 1 ^ (b + 1) : MvPolynomial (Fin 2) B)
          = X 0 * X 1 * (X 0 ^ a * X 1 ^ b) by ring, mkL_X_mul_X_mul, ih b, smul_smul,
        show min (a + 1) (b + 1) = min a b + 1 by lia, pow_succ,
        show a + 1 - (b + 1) = a - b by lia, show b + 1 - (a + 1) = b - a by lia,
        mul_comm (f ^ min a b) f]

/-- **The monomial normal form in the local model**: `z₁^a z₂^b` is `f^{min a b}` times a power of
a single coordinate. -/
theorem coord_pow_mul_coord_pow (a b : ℕ) :
    coord B f 0 ^ a * coord B f 1 ^ b
      = f ^ min a b • (coord B f 0 ^ (a - b) * coord B f 1 ^ (b - a)) := by
  have h := mkL_X_pow B f a b
  change (Ideal.Quotient.mk (Ideal.span {localRelation B f})) (X 0 ^ a * X 1 ^ b)
      = f ^ min a b • (Ideal.Quotient.mk (Ideal.span {localRelation B f}))
        (X 0 ^ (a - b) * X 1 ^ (b - a)) at h
  rwa [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow] at h

/-- The `B`-linear retraction of `B[z₁, z₂]` onto `ℤ →₀ B` sending the monomial `z₁^{m₀} z₂^{m₁}`
to `f^{min m₀ m₁}` times the basis vector of index `m₀ - m₁`. -/
private def retraction : MvPolynomial (Fin 2) B →ₗ[B] (ℤ →₀ B) :=
  (basisMonomials (Fin 2) B).constr B fun m =>
    f ^ min (m 0) (m 1) • Finsupp.single ((m 0 : ℤ) - (m 1 : ℤ)) (1 : B)

private theorem retraction_monomial (m : Fin 2 →₀ ℕ) (b : B) :
    retraction B f (monomial m b) =
      (b * f ^ min (m 0) (m 1)) • Finsupp.single ((m 0 : ℤ) - (m 1 : ℤ)) (1 : B) := by
  have h : (monomial m b : MvPolynomial (Fin 2) B) = b • (basisMonomials (Fin 2) B) m := by
    change _ = b • (monomial m (1 : B))
    simp [smul_monomial]
  rw [h, map_smul, retraction, Module.Basis.constr_basis, smul_smul]

private theorem retraction_mul_localRelation (p : MvPolynomial (Fin 2) B) :
    retraction B f (p * localRelation B f) = 0 := by
  have h : (retraction B f).comp (LinearMap.mulRight B (localRelation B f)) = 0 := by
    refine (basisMonomials (Fin 2) B).ext fun m => ?_
    change retraction B f (monomial m (1 : B) * localRelation B f) = 0
    rw [localRelation, mul_sub, X, X, monomial_mul_monomial, monomial_mul_monomial,
      show (C f : MvPolynomial (Fin 2) B) = monomial 0 f from rfl, monomial_mul_monomial,
      map_sub, retraction_monomial, retraction_monomial]
    have e1 :
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = 1 := by
      simp
    have e2 :
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = 1 := by
      simp
    simp only [Finsupp.add_apply, e1, e2, one_mul, add_zero]
    rw [show min (m 0 + 1) (m 1 + 1) = min (m 0) (m 1) + 1 by lia, pow_succ,
      show ((m 0 + 1 : ℕ) : ℤ) - ((m 1 + 1 : ℕ) : ℤ) = (m 0 : ℤ) - (m 1 : ℤ) by push_cast; ring,
      mul_comm (f ^ min (m 0) (m 1)) f, sub_self]
  simpa using LinearMap.congr_fun h p

/-- The monomial `z₁^n` for `n ≥ 0` and `z₂^{-n}` for `n < 0`. -/
def monomialOfInt (n : ℤ) : MvPolynomial (Fin 2) B :=
  X 0 ^ n.toNat * X 1 ^ (-n).toNat

private theorem monomial_one_eq (m : Fin 2 →₀ ℕ) :
    (monomial m 1 : MvPolynomial (Fin 2) B) = X 0 ^ m 0 * X 1 ^ m 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

private theorem retraction_X_pow (a b : ℕ) :
    retraction B f (X 0 ^ a * X 1 ^ b) =
      f ^ min a b • Finsupp.single ((a : ℤ) - (b : ℤ)) (1 : B) := by
  rw [show (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) B)
      = monomial (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) 1 by
    rw [monomial_one_eq]; simp, retraction_monomial]
  simp

private theorem retraction_monomialOfInt (n : ℤ) :
    retraction B f (monomialOfInt B n) = Finsupp.single n (1 : B) := by
  rw [monomialOfInt, retraction_X_pow, show min n.toNat (-n).toNat = 0 by lia, pow_zero,
    one_smul, show ((n.toNat : ℤ) - ((-n).toNat : ℤ)) = n by lia]

/-- The `B`-linear map `ℤ →₀ B → B[z₁, z₂]` sending the basis vector of index `n` to `z₁^n` for
`n ≥ 0` and to `z₂^{-n}` for `n < 0`. -/
def fromFinsupp : (ℤ →₀ B) →ₗ[B] MvPolynomial (Fin 2) B :=
  Finsupp.basisSingleOne.constr B (monomialOfInt B)

private theorem fromFinsupp_single (n : ℤ) :
    fromFinsupp B (Finsupp.single n (1 : B)) = monomialOfInt B n := by
  exact Finsupp.basisSingleOne.constr_basis B (monomialOfInt B) n

/-- The `B`-linear map from `ℤ →₀ B` to the local model sending the basis vector of index `n` to
`z₁^n` for `n ≥ 0` and to `z₂^{-n}` for `n < 0`. -/
def toLocalModel : (ℤ →₀ B) →ₗ[B] LocalModel B f :=
  (mkL B f).comp (fromFinsupp B)

private theorem toLocalModel_single (n : ℤ) :
    toLocalModel B f (Finsupp.single n (1 : B)) = mkL B f (monomialOfInt B n) := by
  rw [toLocalModel, LinearMap.comp_apply, fromFinsupp_single]

private theorem retraction_fromFinsupp (c : ℤ →₀ B) :
    retraction B f (fromFinsupp B c) = c := by
  have h : (retraction B f).comp (fromFinsupp B) = LinearMap.id := by
    refine Finsupp.basisSingleOne.ext fun n => ?_
    simp [fromFinsupp_single, retraction_monomialOfInt]
  simpa using LinearMap.congr_fun h c

/-- **The comparison map into the local model is injective**: a `B`-linear combination of the
monomials `z₁^n`, `z₂^{-n}` lying in the ideal `(z₁z₂ - f)` has all coefficients zero. -/
theorem injective_toLocalModel : Function.Injective (toLocalModel B f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  rw [toLocalModel, LinearMap.comp_apply] at hc
  have hmem : fromFinsupp B c ∈ Ideal.span {localRelation B f} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hc
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [← retraction_fromFinsupp B f c, ← hq, retraction_mul_localRelation]

/-- **The comparison map into the local model is surjective.** -/
theorem range_toLocalModel : LinearMap.range (toLocalModel B f) = ⊤ := by
  refine eq_top_iff.mpr fun r _ => ?_
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {localRelation B f}) r
  have hmem : P ∈ Submodule.span B (Set.range (basisMonomials (Fin 2) B)) := by
    rw [(basisMonomials (Fin 2) B).span_eq]
    exact Submodule.mem_top
  have key : ∀ x : MvPolynomial (Fin 2) B,
      x ∈ Submodule.span B (Set.range (basisMonomials (Fin 2) B)) →
      mkL B f x ∈ LinearMap.range (toLocalModel B f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [show (basisMonomials (Fin 2) B) m = monomial m 1 from rfl, monomial_one_eq, mkL_X_pow]
      refine Submodule.smul_mem _ _ ⟨Finsupp.single ((m 0 : ℤ) - (m 1 : ℤ)) 1, ?_⟩
      rw [toLocalModel_single, monomialOfInt,
        show ((m 0 : ℤ) - (m 1 : ℤ)).toNat = m 0 - m 1 by lia,
        show (-((m 0 : ℤ) - (m 1 : ℤ))).toNat = m 1 - m 0 by lia]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  exact hP ▸ key P hmem

/-- **The `ℤ`-indexed basis of the local model over the base**: the basis vector of index `n` is
`z₁^n` for `n ≥ 0` and `z₂^{-n}` for `n < 0`. -/
def basis : Module.Basis ℤ B (LocalModel B f) :=
  Finsupp.basisSingleOne.map
    (LinearEquiv.ofBijective (toLocalModel B f)
      ⟨injective_toLocalModel B f, LinearMap.range_eq_top.mp (range_toLocalModel B f)⟩)

/-- The basis vector of index `n` is `z₁^n` for `n ≥ 0` and `z₂^{-n}` for `n < 0`. -/
theorem basis_apply (n : ℤ) :
    basis B f n = coord B f 0 ^ n.toNat * coord B f 1 ^ (-n).toNat := by
  rw [basis, Module.Basis.map_apply]
  change toLocalModel B f (Finsupp.single n 1) = _
  rw [toLocalModel_single, monomialOfInt]
  change (Ideal.Quotient.mk (Ideal.span {localRelation B f})) _ = _
  rw [map_mul, map_pow, map_pow]
  rfl

/-- **The local model of an affine bundle is free over the base.** -/
instance instFreeLocalModel : Module.Free B (LocalModel B f) :=
  Module.Free.of_basis (basis B f)

/-- **The local model of an affine bundle is flat over the base.** -/
instance instFlatLocalModel : Module.Flat B (LocalModel B f) :=
  Module.Flat.of_free

/-- **The local model of an affine bundle is of finite type over the base.** -/
instance instFiniteTypeLocalModel : Algebra.FiniteType B (LocalModel B f) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ B (Ideal.span {localRelation B f})) Ideal.Quotient.mk_surjective

end Stacks.AffineBundle

end
