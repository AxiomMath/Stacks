module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Domain
public import StacksCore.FieldTheory.ArtinSchreier

/-!
# Artin–Schreier–Witt equations over finite extensions

Let `K` be a field of characteristic `p` and `a` a Witt vector over `K` whose zeroth coefficient
is not of the form `b ^ p - b` with `b ∈ K`. The Artin–Schreier–Witt equation `F θ - θ = a`
then has no solution in the Witt vectors of any finite extension `L` of `K`.

## Main results

* `WittVector.charZero_of_charP`: the Witt vectors over a nontrivial ring of characteristic `p`
  have characteristic zero.
* `WittVector.frobenius_sub_self_ne_map_of_coeff_zero_not_mem`: the equation `F θ - θ = a` has
  no solution over a finite extension when `a₀` is not of the form `b ^ p - b`.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

/-- The ring of Witt vectors over a nontrivial ring of characteristic `p` has characteristic
zero. -/
instance charZero_of_charP {R : Type*} [CommRing R] [CharP R p] [Nontrivial R] :
    CharZero (𝕎 R) where
  cast_injective m n h := by
    have hinj : Function.Injective (map (p := p) (ZMod.castHom (dvd_refl p) R)) :=
      map_injective (p := p) _ (ZMod.castHom (dvd_refl p) R).injective
    have h' : (m : 𝕎 (ZMod p)) = n := hinj (by simpa using h)
    exact Nat.cast_injective (R := ℤ_[p]) (by simpa using congrArg (equiv p) h')

/-- Over a finite extension `L` of a field `K` of characteristic `p`, the Artin–Schreier–Witt
equation `F θ - θ = a` has no solution when the zeroth coefficient of `a` is not of the form
`b ^ p - b` with `b ∈ K`. -/
theorem frobenius_sub_self_ne_map_of_coeff_zero_not_mem {K L : Type*} [Field K] [Field L]
    [CharP K p] [Algebra K L] [FiniteDimensional K L] (a : 𝕎 K)
    (ha : ∀ b : K, b ^ p - b ≠ a.coeff 0) (θ : 𝕎 L) :
    frobenius θ - θ ≠ map (algebraMap K L) a := by
  intro hθ
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let Ω := AlgebraicClosure L
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap L Ω).injective p
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K L Ω
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ι : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  set Θ : 𝕎 Ω := map (ι : L →+* Ω) θ with hΘdef
  set A : 𝕎 Ω := map (algebraMap K Ω) a with hAdef
  have hΘ : frobenius Θ - Θ = A := by
    rw [hΘdef, ← (frobenius_isPoly p).map, ← map_sub, hθ]
    ext n
    simp [map_coeff, ι, hAdef, ← IsScalarTower.algebraMap_apply]
  set b := Θ.coeff 0 with hbdef
  have hb : b ^ p = b + algebraMap K Ω (a.coeff 0) := by
    have := congrArg constantCoeff hΘ
    simp only [map_sub, constantCoeff_apply, coeff_frobenius_charP, hAdef, map_coeff] at this
    linear_combination this
  have ha' : ∀ x : K, x ^ p ≠ x + a.coeff 0 := fun x hx ↦ ha x (by rw [hx]; ring)
  have hmin : minpoly K (b + 1) = minpoly K b := by
    rw [minpoly_eq_X_pow_sub_X_sub_C hb ha',
      minpoly_eq_X_pow_sub_X_sub_C _ ha']
    rw [add_pow_char, one_pow, hb]
    ring
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (E := Ω)).1 hmin
  change g b = b + 1 at hg
  let gR : Ω →+* Ω := g.toAlgHom.toRingHom
  set u : 𝕎 Ω := map gR Θ - Θ with hudef
  have hgA : map gR A = A := by
    ext n
    simp [gR, hAdef, map_coeff]
  have hu : frobenius u = u := by
    have h := congrArg (map gR) hΘ
    rw [map_sub, (frobenius_isPoly p).map, hgA, ← hΘ] at h
    rw [hudef, map_sub]
    linear_combination h
  have hgu : map gR u = u := by
    ext n
    have hn : u.coeff n ^ p - u.coeff n = (0 : Ω) ^ p - 0 := by
      rw [← coeff_frobenius_charP, hu, zero_pow hp.out.ne_zero, sub_self, sub_self]
    obtain ⟨i, -, hi⟩ := exists_eq_add_of_pow_sub_eq_pow_sub hn
    rw [map_coeff, hi, map_add, map_natCast, map_zero]
  have hu0 : u.coeff 0 = 1 := by
    have h : u.coeff 0 = g b - b := by
      rw [hudef, ← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply,
        map_coeff]
      rfl
    rw [h, hg]
    ring
  have hu_ne : u ≠ 0 := fun h ↦ by simp [h] at hu0
  let φ : ℕ → (L →ₐ[K] Ω) := fun k ↦ (g ^ k).toAlgHom.comp ι
  have hφ (k : ℕ) : map (φ k : L →+* Ω) θ = Θ + k * u := by
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, add_zero, hΘdef]
      ext n
      simp [φ, map_coeff]
    | succ k ih =>
      have h : map (φ (k + 1) : L →+* Ω) θ = map gR (map (φ k : L →+* Ω) θ) := by
        ext n
        simp [φ, gR, map_coeff, pow_succ', AlgEquiv.mul_apply]
      rw [h, ih, map_add, map_mul, map_natCast, hgu, show map gR Θ = Θ + u by rw [hudef]; ring,
        Nat.cast_succ]
      ring
  have hinj : Function.Injective φ := by
    intro k k' h
    have h' := hφ k
    rw [h, hφ k'] at h'
    have : (k : 𝕎 Ω) * u = k' * u := by linear_combination h'.symm
    exact Nat.cast_injective (mul_left_injective₀ hu_ne this)
  exact not_injective_infinite_finite φ hinj

end WittVector
