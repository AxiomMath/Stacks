module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import StacksFrontier.NumberTheory.Adeles.UnramifiedCuspForm

/-!
# Hecke operators, eigenforms, and cusp forms with prescribed central character

Let `K` be a field and `v` a place of `K`, with completion `K_v`, ring of integers `O_v`,
uniformizer `π_v` and residue field `κ_v = O_v/(π_v)` of cardinality `q_v = #κ_v`. For an
unramified cusp form `f` on `GL₂(A)` with values in `Λ` the Hecke operators are
```
T_v(f)(x) = f (diag (π_v⁻¹, 1) * x) + ∑_{i = 1}^{q_v} f ((1, 0; -π_v⁻¹ λ_i, π_v⁻¹) * x),
U_v(f)(x) = f (diag (π_v⁻¹, π_v⁻¹) * x),
```
where `λ_1, …, λ_{q_v} ∈ O_v` is a system of representatives of `κ_v`. An *eigenform* is an
unramified cusp form some value of which is a unit and which satisfies `T_v f = t_v f` and
`U_v f = u_v f` for (uniquely determined) `t_v, u_v ∈ Λ`. Finally `C(Λ)` is the `Λ`-module
spanned by the unramified cusp forms satisfying `U_v f = q_v⁻¹ f` for every `v`.

## Main definitions

* `Stacks.Adeles.Place.IsUniformizer` and `Stacks.Adeles.Place.IsResidueSystem` — a generator
  of the maximal ideal of `O_v`, and a system of representatives of `κ_v` indexed by `Fin q`.
* `Stacks.Adeles.Place.residueCard` — the cardinality `q_v` of the residue field `κ_v`.
* `Stacks.Adeles.IsLocalMatrixAt` — the adelic matrices which are a prescribed matrix at `v`
  and the identity away from `v`.
* `Stacks.Adeles.heckeOperator` and `Stacks.Adeles.IsHeckeDataAt` — the finite sum defining
  `T_v`, and the conditions on its data making it the Hecke operator at `v`.
* `Stacks.Adeles.centralOperator` and `Stacks.Adeles.IsCentralDataAt` — the same for `U_v`.
* `Stacks.Adeles.IsHeckeEigenvalueAt` and `Stacks.Adeles.IsCentralEigenvalueAt` — the two
  eigenvalue equations.
* `Stacks.Adeles.IsEigenform` — an eigenform.
* `Stacks.Adeles.cuspFormsCentralChar` — the module `C(Λ)`.

## Main results

* `Stacks.Adeles.Place.residueCard_eq_of_isResidueSystem` — a system of representatives of
  `κ_v` indexed by `Fin q` forces `q = q_v`.
* `Stacks.Adeles.IsEigenform.hecke_eigenvalue_unique` and
  `Stacks.Adeles.IsEigenform.central_eigenvalue_unique` — the eigenvalues of an eigenform are
  uniquely determined wherever the operator in question has data.

## Implementation notes

The Stacks source defines `T_v` by an integral over `M_v = {h ∈ Mat(2 × 2, O_v) | det h ∈ π_v
O_v^*}` against the Haar measure normalized by `∫_{GL₂(O_v)} dg = 1`, and then writes out the
resulting finite sum over the `q_v + 1` cosets. It is the finite sum that is formalized here:
it is the source's own explicit formula, and it needs no measure theory.

The adelic matrices `diag (π_v⁻¹, 1)`, `(1, 0; -π_v⁻¹ λ_i, π_v⁻¹)` and `diag (π_v⁻¹, π_v⁻¹)`
are *characterized* rather than constructed: `IsLocalMatrixAt v m x` says that the adele matrix
`x` has `m` as its component at `v` and the identity as its component at every other place, and
the operators take the matrices as data constrained by that predicate. Constructing them
instead would require producing elements of the restricted product, hence a choice of
uniformizer at `v` and of representatives of `κ_v`, none of which is canonical; the predicate
carries exactly the source's conditions on them and nothing else.

A consequence of the predicate style is that `IsHeckeEigenvalueAt v f t` is vacuously true at a
place `v` carrying no Hecke data — for instance at a place whose residue field is infinite,
where no `Fin q`-indexed system of representatives exists. The eigenvalue equations are
therefore quantified over the data, and the uniqueness statements of the source's "(uniquely
determined) `t_v, u_v`" are proved as separate lemmas taking the existence of the data as a
hypothesis, rather than being built into `IsEigenform`.

`C(Λ)` is the source's set
`{unramified cusp forms f with coefficients in Λ such that U_v f = φ_v⁻¹ f for all v}`,
and the symbol `φ_v` is **undefined in the Stacks source**: it occurs exactly once in the whole
chapter, in this definition, and is introduced nowhere. It is read here as `q_v`, the
cardinality of the residue field at `v`, for the following reason — *and this reading is an
inference made here, not a statement of the source*. In Lemma 03VY the representation is into
`SL₂`, so `det ρ(F_v) = 1`; the normalization of Theorem 03VT and Theorem 03VU is
`u_v = q_v⁻¹ det ρ(F_v)`, so the eigenform attached to such a representation has `u_v = q_v⁻¹`,
that is `U_v f = q_v⁻¹ f`. That is the condition that must cut out `C(Λ)` for the proof of
Lemma 03VY to read as the source writes it, and it forces `φ_v = q_v`.

The condition is recorded in the cleared form `q_v · U_v f = f` rather than as
`U_v f = q_v⁻¹ f`. The two are equivalent exactly when `q_v` is invertible in `Λ`, which holds
in every coefficient ring the source uses (`q_v` is a power of the characteristic `p` of the
base field, and `p` is invertible in `Λ` throughout the section), and the cleared form is
`Λ`-linear in `f` and needs no invertibility hypothesis to be stated.

`C(Λ)` is defined as the `Λ`-span of that set of forms, and not as the set itself. The set is a
`Λ`-submodule mathematically, but neither closure under addition nor closure under scalars is
derivable from the stated form of condition (3) of `Stacks.Adeles.IsUnramifiedCuspForm`, which
quantifies over *every* open subgroup `U` leaving the integrand invariant and every transversal
of `A/(K + U)` rather than asserting that one exists: an open subgroup leaving the integrand of
`f + g` invariant need leave neither integrand invariant, so the hypotheses of condition (3)
for `f` and for `g` are unavailable. The span is the smallest submodule containing the set, and
coincides with it as soon as the set is closed under addition and scalars.

## References

* [Stacks Project, Tag 03VS](https://stacks.math.columbia.edu/tag/03VS)
* [Stacks Project, Tag 03VT](https://stacks.math.columbia.edu/tag/03VT)
* [Stacks Project, Tag 03VW](https://stacks.math.columbia.edu/tag/03VW)
-/

@[expose] public noncomputable section

open Matrix
open scoped RestrictedProduct

universe u w

namespace Stacks.Adeles

namespace Place

variable {K : Type u} [Field K]

/-- A uniformizer at a place `v`: an element of `O_v` generating its maximal ideal. -/
public def IsUniformizer (v : Place K) (π : v.integers) : Prop :=
  Ideal.span {π} = IsLocalRing.maximalIdeal v.integers

/-- A system of representatives of the residue field `κ_v = O_v/(π)` indexed by `Fin q`: every
element of `O_v` is congruent modulo `π` to `lam i` for exactly one `i`. -/
public def IsResidueSystem (v : Place K) (π : v.integers) {q : ℕ} (lam : Fin q → v.integers) :
    Prop :=
  ∀ a : v.integers, ∃! i : Fin q, a - lam i ∈ Ideal.span {π}

/-- The cardinality `q_v = #κ_v` of the residue field at a place `v`. -/
public def residueCard (v : Place K) : ℕ := Nat.card (IsLocalRing.ResidueField v.integers)

/-- A system of representatives of `κ_v` indexed by `Fin q` has `q = q_v`: the source's
`λ_i ∈ O_v` a set of representatives of `O_v/(π_v) = κ_v`, `q_v = #κ_v`. -/
public theorem residueCard_eq_of_isResidueSystem {v : Place K} {π : v.integers} {q : ℕ}
    {lam : Fin q → v.integers} (hπ : IsUniformizer v π) (hlam : IsResidueSystem v π lam) :
    residueCard v = q := by
  have hmem : ∀ a b : v.integers,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.integers) a =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.integers) b ↔ a - b ∈ Ideal.span {π} := by
    intro a b
    rw [hπ]
    exact Ideal.Quotient.eq
  have hbij : Function.Bijective
      fun i : Fin q => Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.integers) (lam i) := by
    refine ⟨fun i j hij => ?_, fun y => ?_⟩
    · obtain ⟨i₀, -, huniq⟩ := hlam (lam i)
      rw [huniq i (by simp), huniq j ((hmem _ _).1 hij)]
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨i, hi, -⟩ := hlam a
      exact ⟨i, ((hmem _ _).2 hi).symm⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm.trans (Nat.card_fin q)

end Place

variable {K : Type u} [Field K]

/-- The adelic matrices with prescribed component at one place: `IsLocalMatrixAt v m x` says
that the matrix of adeles `x` has component `m` at `v` and the identity matrix at every other
place. -/
public def IsLocalMatrixAt (v : Place K) (m : Matrix (Fin 2) (Fin 2) v.completion)
    (x : GL (Fin 2) (AdeleRing K)) : Prop :=
  (∀ i j, ((x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) v = m i j) ∧
    ∀ w : Place K, w ≠ v → ∀ i j,
      ((x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) w =
        (1 : Matrix (Fin 2) (Fin 2) w.completion) i j

/-- The sum defining a Hecke operator: `f (g₀ * x) + ∑ i, f (g i * x)`. It is the Hecke
operator `T_v` when the data `g₀`, `g` satisfy `Stacks.Adeles.IsHeckeDataAt`. -/
public def heckeOperator {Λ : Type w} [AddCommMonoid Λ] {q : ℕ}
    (g₀ : GL (Fin 2) (AdeleRing K)) (g : Fin q → GL (Fin 2) (AdeleRing K))
    (f : GL (Fin 2) (AdeleRing K) → Λ) : GL (Fin 2) (AdeleRing K) → Λ :=
  fun x => f (g₀ * x) + ∑ i, f (g i * x)

/-- The data of the source's explicit formula for the Hecke operator at a place `v`: a
uniformizer `π` of `O_v`, a system `lam` of representatives of `κ_v`, the adelic matrix `g₀`
which is `diag (π⁻¹, 1)` at `v` and the identity elsewhere, and the adelic matrices `g i` which
are `(1, 0; -π⁻¹ λ_i, π⁻¹)` at `v` and the identity elsewhere. -/
public structure IsHeckeDataAt (v : Place K) {q : ℕ} (π : v.integers)
    (lam : Fin q → v.integers) (g₀ : GL (Fin 2) (AdeleRing K))
    (g : Fin q → GL (Fin 2) (AdeleRing K)) : Prop where
  /-- `π` generates the maximal ideal of `O_v`. -/
  isUniformizer : Place.IsUniformizer v π
  /-- The `lam i` represent the residue field `κ_v`; in particular `q = q_v`. -/
  isResidueSystem : Place.IsResidueSystem v π lam
  /-- `g₀` is `diag (π⁻¹, 1)` at `v` and the identity away from `v`. -/
  diagonal : IsLocalMatrixAt v (Matrix.diagonal ![(π : v.completion)⁻¹, 1]) g₀
  /-- `g i` is `(1, 0; -π⁻¹ λ_i, π⁻¹)` at `v` and the identity away from `v`. -/
  coset : ∀ i, IsLocalMatrixAt v
    !![1, 0; -((π : v.completion)⁻¹ * (lam i : v.completion)), (π : v.completion)⁻¹] (g i)

/-- `t` is the eigenvalue of `f` for the Hecke operator at `v`: `T_v f = t f`, for every choice
of the data of the source's formula for `T_v`. -/
public def IsHeckeEigenvalueAt {Λ : Type w} [CommRing Λ] (v : Place K)
    (f : GL (Fin 2) (AdeleRing K) → Λ) (t : Λ) : Prop :=
  ∀ {q : ℕ} (π : v.integers) (lam : Fin q → v.integers) (g₀ : GL (Fin 2) (AdeleRing K))
    (g : Fin q → GL (Fin 2) (AdeleRing K)), IsHeckeDataAt v π lam g₀ g →
      ∀ x, heckeOperator g₀ g f x = t * f x

/-- Left multiplication by one adelic matrix: `f ↦ (x ↦ f (a * x))`. It is the operator `U_v`
when `a` satisfies `Stacks.Adeles.IsCentralDataAt`. -/
public def centralOperator {Λ : Type w} (a : GL (Fin 2) (AdeleRing K))
    (f : GL (Fin 2) (AdeleRing K) → Λ) : GL (Fin 2) (AdeleRing K) → Λ := fun x => f (a * x)

/-- The data of the source's formula for `U_v`: an adelic matrix which is the scalar matrix
`diag (π⁻¹, π⁻¹)` at `v`, for some uniformizer `π` of `O_v`, and the identity elsewhere. -/
public def IsCentralDataAt (v : Place K) (a : GL (Fin 2) (AdeleRing K)) : Prop :=
  ∃ π : v.integers, Place.IsUniformizer v π ∧
    IsLocalMatrixAt v (Matrix.diagonal fun _ => (π : v.completion)⁻¹) a

/-- `u` is the eigenvalue of `f` for the operator `U_v`: `U_v f = u f`, for every choice of the
data of the source's formula for `U_v`. -/
public def IsCentralEigenvalueAt {Λ : Type w} [CommRing Λ] (v : Place K)
    (f : GL (Fin 2) (AdeleRing K) → Λ) (u : Λ) : Prop :=
  ∀ a : GL (Fin 2) (AdeleRing K), IsCentralDataAt v a → ∀ x, centralOperator a f x = u * f x

/-- An eigenform with values in `Λ`, with Hecke eigenvalues `t` and central eigenvalues `u`: an
unramified cusp form some value of which is a unit and which satisfies `T_v f = t_v f` and
`U_v f = u_v f` at every place `v`. -/
public structure IsEigenform {Λ : Type w} [CommRing Λ] (f : GL (Fin 2) (AdeleRing K) → Λ)
    (t u : Place K → Λ) : Prop where
  /-- `f` is an unramified cusp form, Tag 03VS. -/
  isUnramifiedCuspForm : IsUnramifiedCuspForm f
  /-- Some value of `f` is a unit. -/
  exists_isUnit : ∃ x, IsUnit (f x)
  /-- `T_v f = t_v f` at every place. -/
  hecke : ∀ v, IsHeckeEigenvalueAt v f (t v)
  /-- `U_v f = u_v f` at every place. -/
  central : ∀ v, IsCentralEigenvalueAt v f (u v)

namespace IsEigenform

variable {Λ : Type w} [CommRing Λ] {f : GL (Fin 2) (AdeleRing K) → Λ} {t u : Place K → Λ}

/-- The Hecke eigenvalue of an eigenform at a place carrying Hecke data is uniquely
determined. -/
public theorem hecke_eigenvalue_unique (hf : IsEigenform f t u) {v : Place K} {t' : Λ}
    (ht' : IsHeckeEigenvalueAt v f t') {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
    {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}
    (hdata : IsHeckeDataAt v π lam g₀ g) : t v = t' := by
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  exact hx.mul_left_inj.1 (((hf.hecke v π lam g₀ g hdata x).symm.trans
    (ht' π lam g₀ g hdata x)))

/-- The central eigenvalue of an eigenform at a place carrying central data is uniquely
determined. -/
public theorem central_eigenvalue_unique (hf : IsEigenform f t u) {v : Place K} {u' : Λ}
    (hu' : IsCentralEigenvalueAt v f u') {a : GL (Fin 2) (AdeleRing K)}
    (hdata : IsCentralDataAt v a) : u v = u' := by
  obtain ⟨x, hx⟩ := hf.exists_isUnit
  exact hx.mul_left_inj.1 ((hf.central v a hdata x).symm.trans (hu' a hdata x))

end IsEigenform

/-- Change of coefficients for functions on `GL₂(A)`: postcomposition with a ring
homomorphism. -/
public def mapCoeffs {Λ : Type*} {Λ' : Type*} [NonAssocSemiring Λ] [NonAssocSemiring Λ']
    (φ : Λ →+* Λ') (f : GL (Fin 2) (AdeleRing K) → Λ) : GL (Fin 2) (AdeleRing K) → Λ' :=
  fun x => φ (f x)

/-- Change of coefficients commutes with the Hecke sum, `T_v (φ ∘ f) = φ ∘ (T_v f)`. This is
the source's "compatibly with `T_v` acting" in Proposition 03VW. -/
public theorem heckeOperator_mapCoeffs {Λ : Type*} {Λ' : Type*} [NonAssocSemiring Λ]
    [NonAssocSemiring Λ'] (φ : Λ →+* Λ') {q : ℕ} (g₀ : GL (Fin 2) (AdeleRing K))
    (g : Fin q → GL (Fin 2) (AdeleRing K)) (f : GL (Fin 2) (AdeleRing K) → Λ)
    (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g (mapCoeffs φ f) x = φ (heckeOperator g₀ g f x) := by
  simp [heckeOperator, mapCoeffs, map_sum]

/-- The zero function is an unramified cusp form. -/
public theorem IsUnramifiedCuspForm.zero {Λ : Type w} [AddCommMonoid Λ] :
    IsUnramifiedCuspForm (0 : GL (Fin 2) (AdeleRing K) → Λ) where
  right_invariant _ _ := rfl
  left_invariant _ _ := rfl
  vanishing_constant_term _ _ _ _ _ _ := Finset.sum_const_zero

/-- The unramified cusp forms with prescribed central character: those satisfying
`q_v · U_v f = f` at every place, the cleared form of the source's `U_v f = φ_v⁻¹ f` under the
reading `φ_v = q_v`. -/
public def IsCuspFormCentralChar (Λ : Type w) [CommRing Λ]
    (f : GL (Fin 2) (AdeleRing K) → Λ) : Prop :=
  IsUnramifiedCuspForm f ∧ ∀ (v : Place K) (a : GL (Fin 2) (AdeleRing K)), IsCentralDataAt v a →
    ∀ x, (Place.residueCard v : Λ) * centralOperator a f x = f x

/-- The module `C(Λ)` of the source: the `Λ`-span of the unramified cusp forms `f` with
coefficients in `Λ` satisfying `U_v f = φ_v⁻¹ f` for every place `v`, read as `q_v · U_v f = f`.
-/
public def cuspFormsCentralChar (K : Type u) [Field K] (Λ : Type w) [CommRing Λ] :
    Submodule Λ (GL (Fin 2) (AdeleRing K) → Λ) :=
  Submodule.span Λ {f | IsCuspFormCentralChar Λ f}

/-- An unramified cusp form with prescribed central character lies in `C(Λ)`. -/
public theorem mem_cuspFormsCentralChar {Λ : Type w} [CommRing Λ]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsCuspFormCentralChar Λ f) :
    f ∈ cuspFormsCentralChar K Λ :=
  Submodule.subset_span hf

end Stacks.Adeles

end
