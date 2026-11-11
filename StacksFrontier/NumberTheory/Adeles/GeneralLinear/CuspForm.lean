module

public import StacksFrontier.NumberTheory.Drinfeld.Lattice.Adelic

/-!
# Unramified cusp forms and Hecke operators on `GL_n` of the adeles

Let `K` be a field with adele ring `A = ∏'_v K_v` and integral adeles `O = ∏_v O_v`. This file
defines, for every `n`, the unramified cusp forms on `GL_n(A)` with values in `Λ` and the Hecke
operators `T_{v,i}` acting on them, generalizing the case `n = 2` of
`Stacks.Adeles.IsUnramifiedCuspForm` (Tag 03VS) and of the Hecke operator `T_v`.

An unramified cusp form is a function `f : GL_n(A) → Λ` invariant under right multiplication by
`GL_n(K)` and under left multiplication by `GL_n(O)`, all of whose constant terms along the
unipotent radicals of the standard maximal parabolic subgroups vanish. For `0 < r < n` the
unipotent radical `N_r` consists of the matrices `1 + z` with `z` supported in the rows `< r`
and the columns `≥ r`; `z ↦ 1 + z` is an isomorphism from the additive group of such `z` onto
`N_r`. The constant term along `N_r` is stated without measure theory, as for `GL_2`: the
integrand `z ↦ f (x (1 + z))` is invariant under `N_r(K)` and under an open subgroup `U` of
`N_r(A)`, so it factors through the finite group `N_r(A) / (N_r(K) + U)`, and its vanishing is
the vanishing of the sum over a transversal.

The Hecke operator `T_{v,i}` (`1 ≤ i ≤ n`) is described through adelic lattices: identifying
`GL_n(O) \ GL_n(A)` with the adelic lattices of rank `n` by `x ↦ x⁻¹ (O_w^n)_w`, it sums over the
lattices `L'` that agree with `L = x⁻¹ (O_w^n)_w` away from `v` and satisfy
`m_v L_v ⊆ L'_v ⊆ L_v` with `L_v / L'_v` of order `q_v ^ i`, that is, `L_v / L'_v ≅ κ_v ^ i`.
These are the modifications of type `(1, …, 1, 0, …, 0)` at `v` (the double coset of
`diag(ϖ_v, …, ϖ_v, 1, …, 1)` with `i` entries `ϖ_v`). For `n = 2`, `i = 1` this is the
operator `T_v` of the base (`Stacks.Drinfeld.Lattice.AdelicLattice.heckeOperator_eq_finsum`),
and `T_{v,n}` is translation by the central element `ϖ_v⁻¹`.

## Main definitions

* `Stacks.Adeles.unipotentRadical` — the matrices supported in rows `< r` and columns `≥ r`.
* `Stacks.Adeles.unipotentGL` — `z ↦ 1 + z`, into `GL_n`.
* `Stacks.Adeles.principalUnipotent` — the `z` with principal entries, i.e. `N_r(K)`.
* `Stacks.Adeles.IsUnramifiedCuspFormGL` — unramified cusp forms on `GL_n(A)`.
* `Stacks.Adeles.IsHeckeNeighbourGL` — the lattices summed over by `T_{v,i}`.
* `Stacks.Adeles.heckeOperatorGL` — the Hecke operator `T_{v,i}`.
* `Stacks.Adeles.IsHeckeEigenformGL` — a nonzero common eigenfunction of all `T_{v,i}`.
* `Stacks.Adeles.heckePolynomial` — `∑_i (-1)^i q_v^{i(i-1)/2} t_{v,i} X^{n-i}`, the polynomial
  whose roots are the Satake parameters, normalized as in the `GL_2` correspondence of the base
  (`t_v = Tr ρ(F_v)`, `u_v = q_v⁻¹ det ρ(F_v)`).

## References

* [Stacks Project, Tag 03VS](https://stacks.math.columbia.edu/tag/03VS)
* [dJ-conjecture]
-/

@[expose] public noncomputable section

open Matrix Polynomial

universe u w

namespace Stacks.Adeles

section Unipotent

variable (R : Type*) [Ring R] (n r : ℕ)

/-- The additive group of `n × n` matrices supported in the rows `< r` and the columns `≥ r`;
`z ↦ 1 + z` identifies it with the unipotent radical of the standard parabolic subgroup of type
`(r, n - r)`. -/
public def unipotentRadical : AddSubgroup (Matrix (Fin n) (Fin n) R) where
  carrier := {z | ∀ i j : Fin n, ¬((i : ℕ) < r ∧ r ≤ (j : ℕ)) → z i j = 0}
  zero_mem' _ _ _ := rfl
  add_mem' {a b} ha hb i j h := by simp [ha i j h, hb i j h]
  neg_mem' {a} ha i j h := by simp [ha i j h]

variable {R n r}

/-- A matrix lies in the unipotent radical when its entries outside the rows `< r` and the
columns `≥ r` vanish. -/
public theorem mem_unipotentRadical {z : Matrix (Fin n) (Fin n) R} :
    z ∈ unipotentRadical R n r ↔ ∀ i j : Fin n, ¬((i : ℕ) < r ∧ r ≤ (j : ℕ)) → z i j = 0 :=
  Iff.rfl

/-- The product of two matrices of the unipotent radical vanishes. -/
public theorem mul_eq_zero_of_mem_unipotentRadical {z y : Matrix (Fin n) (Fin n) R}
    (hz : z ∈ unipotentRadical R n r) (hy : y ∈ unipotentRadical R n r) : z * y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : r ≤ (l : ℕ)
  · rw [hy l j (fun h => absurd h.1 (not_lt.2 hl)), mul_zero]
  · rw [hz i l (fun h => hl h.2), zero_mul]

end Unipotent

section UnipotentGL

variable {R : Type*} [CommRing R] {n r : ℕ}

/-- The element `1 + z` of `GL_n(R)` for `z` in the unipotent radical, with inverse `1 - z`. -/
public def unipotentGL (z : unipotentRadical R n r) : GL (Fin n) R where
  val := 1 + z
  inv := 1 - z
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, mul_eq_zero_of_mem_unipotentRadical z.2 z.2]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, mul_eq_zero_of_mem_unipotentRadical z.2 z.2]
    abel

/-- The matrix of `unipotentGL z` is `1 + z`. -/
@[simp]
public theorem coe_unipotentGL (z : unipotentRadical R n r) :
    (unipotentGL z : Matrix (Fin n) (Fin n) R) = 1 + z := rfl

/-- `z ↦ 1 + z` turns addition into multiplication. -/
public theorem unipotentGL_add (z y : unipotentRadical R n r) :
    unipotentGL (z + y) = unipotentGL z * unipotentGL y := by
  ext1
  simp only [coe_unipotentGL, AddSubgroup.coe_add, Matrix.GeneralLinearGroup.coe_mul, add_mul,
    one_mul, mul_add, mul_one, mul_eq_zero_of_mem_unipotentRadical z.2 y.2]
  abel

/-- `unipotentGL 0 = 1`. -/
@[simp]
public theorem unipotentGL_zero : unipotentGL (0 : unipotentRadical R n r) = 1 := by
  ext1
  simp

end UnipotentGL

variable {K : Type u} [Field K]

variable (K) in
/-- `N_r(K)` inside `N_r(A)`: the elements of the unipotent radical over the adeles all of whose
entries are principal adeles. -/
public def principalUnipotent (n r : ℕ) : AddSubgroup (unipotentRadical (AdeleRing K) n r) where
  carrier := {z | ∀ i j, (z : Matrix (Fin n) (Fin n) (AdeleRing K)) i j ∈ principalAdeles K}
  zero_mem' _ _ := (principalAdeles K).zero_mem
  add_mem' ha hb i j := (principalAdeles K).add_mem (ha i j) (hb i j)
  neg_mem' ha i j := (principalAdeles K).neg_mem (ha i j)

/-- An element of `N_r(A)` lies in `N_r(K)` when all its entries are principal. -/
public theorem mem_principalUnipotent {n r : ℕ} {z : unipotentRadical (AdeleRing K) n r} :
    z ∈ principalUnipotent K n r ↔
      ∀ i j, (z : Matrix (Fin n) (Fin n) (AdeleRing K)) i j ∈ principalAdeles K :=
  Iff.rfl

/-- An unramified cusp form on `GL_n(A)` with values in `Λ`: a function on `GL_n(A)` invariant
under right multiplication by `GL_n(K)` and under left multiplication by `GL_n(O)`, whose
constant terms along the unipotent radicals `N_r` of the standard maximal parabolic subgroups
(`0 < r < n`), over `N_r(A)` modulo `N_r(K)`, vanish. For `n = 2` these are the unramified cusp
forms of Tag 03VS (`Stacks.Adeles.IsUnramifiedCuspForm`), and for `n = 1` every function on
`K^× \ A^× / O^×` is one. -/
public structure IsUnramifiedCuspFormGL {Λ : Type w} [AddCommMonoid Λ] (n : ℕ)
    (f : GL (Fin n) (AdeleRing K) → Λ) : Prop where
  /-- Invariance under right multiplication by `GL_n(K)`. -/
  right_invariant (x : GL (Fin n) (AdeleRing K)) (γ : GL (Fin n) (principalAdeles K)) :
    f (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) = f x
  /-- Invariance under left multiplication by `GL_n(O)`. -/
  left_invariant (x : GL (Fin n) (AdeleRing K)) (u : GL (Fin n) (integralAdeles K)) :
    f (GeneralLinearGroup.map (integralAdeles K).subtype u * x) = f x
  /-- For every `0 < r < n` and every `x`, the constant term of `z ↦ f (x (1 + z))` along
  `N_r` vanishes, expressed as the vanishing of the sum over a transversal `s` of
  `N_r(A) / (N_r(K) + U)` for an open subgroup `U` of `N_r(A)` leaving the integrand
  invariant. -/
  vanishing_constant_term (r : ℕ) (hr : 0 < r) (hrn : r < n) (x : GL (Fin n) (AdeleRing K))
      (U : AddSubgroup (unipotentRadical (AdeleRing K) n r))
      (hU : IsOpen (U : Set (unipotentRadical (AdeleRing K) n r)))
      (hinv : ∀ z : unipotentRadical (AdeleRing K) n r, ∀ y ∈ U,
        f (x * unipotentGL (z + y)) = f (x * unipotentGL z))
      (s : Finset (unipotentRadical (AdeleRing K) n r))
      (hs : ∀ a, ∃! z ∈ s, a - z ∈ principalUnipotent K n r ⊔ U) :
    ∑ z ∈ s, f (x * unipotentGL z) = 0

open Stacks.Drinfeld.Lattice

variable {n : ℕ}

/-- `L'` is summed over by the Hecke operator `T_{v,i}` at `L`: `L'_w = L_w` for `w ≠ v`, and
`m_v L_v ⊆ L'_v ⊆ L_v` with `L_v / L'_v` of order `q_v ^ i` (so `L_v / L'_v ≅ κ_v ^ i`). For
`n = 2`, `i = 1` these are the Hecke neighbours of the base
(`Stacks.Drinfeld.Lattice.AdelicLattice.IsHeckeNeighbour`). -/
public def IsHeckeNeighbourGL (v : Place K) (i : ℕ) (L L' : AdelicLattice K n) : Prop :=
  (∀ w, w ≠ v → L'.lattice w = L.lattice w) ∧
    IsLocalRing.maximalIdeal v.integers • L.lattice v ≤ L'.lattice v ∧
    L'.lattice v ≤ L.lattice v ∧
    (L'.lattice v).toAddSubgroup.relIndex (L.lattice v).toAddSubgroup = v.residueCard ^ i

/-- An element `g ∈ GL_n(A)` with `g (O_w^n)_w = L`, when there is one (over a function field
there always is: `Stacks.Drinfeld.Lattice.AdelicLattice.exists_smul_standard`). The value of a
left `GL_n(O)`-invariant function at `g⁻¹` does not depend on the choice. -/
public def latticeRep (L : AdelicLattice K n) : GL (Fin n) (AdeleRing K) :=
  open Classical in
  if h : ∃ g : GL (Fin n) (AdeleRing K), g • AdelicLattice.standard K n = L then h.choose else 1

/-- The Hecke operator `T_{v,i}` on functions on `GL_n(O) \ GL_n(A)`: writing
`f (x) = F (x⁻¹ (O_w^n)_w)`, `T_{v,i} f (x) = ∑_{L'} F (L')`, the sum over the lattices `L'`
with `IsHeckeNeighbourGL v i (x⁻¹ (O_w^n)_w) L'` (finitely many: they correspond to the
subspaces of dimension `n - i` of `κ_v ^ n`). -/
public def heckeOperatorGL {Λ : Type w} [AddCommMonoid Λ] (v : Place K) (i : ℕ)
    (f : GL (Fin n) (AdeleRing K) → Λ) (x : GL (Fin n) (AdeleRing K)) : Λ :=
  ∑ᶠ L' : {L' : AdelicLattice K n //
      IsHeckeNeighbourGL v i (x⁻¹ • AdelicLattice.standard K n) L'},
    f (latticeRep L'.1)⁻¹

/-- `f` is a Hecke eigenform on `GL_n(A)` with eigenvalues `t`: `f ≠ 0` and
`T_{v,i} f = t v i · f` for every place `v` and every `1 ≤ i ≤ n`. -/
public structure IsHeckeEigenformGL {Λ : Type w} [CommRing Λ] (f : GL (Fin n) (AdeleRing K) → Λ)
    (t : Place K → ℕ → Λ) : Prop where
  /-- The eigenform is not zero. -/
  ne_zero : f ≠ 0
  /-- `T_{v,i} f = t v i · f`. -/
  hecke (v : Place K) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (x : GL (Fin n) (AdeleRing K)) :
    heckeOperatorGL v i f x = t v i * f x

/-- The Hecke polynomial `∑_{i=0}^{m} (-1)^i q^{i(i-1)/2} t_i X^{m-i}` of a system `t` of Hecke
eigenvalues on `GL_m` at a place with `q` elements in its residue field (with `t_0 = 1`). For a
representation `ρ` corresponding to the eigenform, it is the characteristic polynomial of
`ρ(F_v)`, `F_v` a geometric Frobenius: `e_i(ρ(F_v)) = q_v^{i(i-1)/2} t_{v,i}`, which for `m = 2`
is the normalization `t_v = Tr ρ(F_v)`, `u_v = q_v⁻¹ det ρ(F_v)` of the base. -/
public def heckePolynomial {Λ : Type w} [CommRing Λ] (m q : ℕ) (t : ℕ → Λ) : Λ[X] :=
  ∑ i ∈ Finset.range (m + 1),
    C ((-1) ^ i * (q : Λ) ^ (i * (i - 1) / 2) * (if i = 0 then 1 else t i)) * X ^ (m - i)

end Stacks.Adeles

end
