module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Truncated

/-!
# Witt vectors with coefficients in a subring, and coefficientwise limits

Let `Ω` be a commutative ring and `S` a subring of `Ω`. The Witt vectors over `Ω` all of whose
coefficients lie in `S` are the image of `WittVector.map S.subtype : 𝕎 S →+* 𝕎 Ω`, hence a subring
of `𝕎 Ω`: sums, differences and products of such Witt vectors again have their coefficients in
`S`, because the Witt vector operations are given by integral polynomials. This file records
this subring together with the elementary approximation tools used to solve equations in Witt
vectors one coefficient at a time.

## Main definitions

* `WittVector.coeffSubring S`: the subring of `𝕎 Ω` of Witt vectors with all coefficients in `S`.
* `WittVector.truncLimit x`: for a sequence `x : ℕ → 𝕎 R`, the Witt vector whose `k`-th
  coefficient is the `k`-th coefficient of `x (k + 1)`.

## Main results

* `WittVector.mem_coeffSubring_iff`: `x ∈ coeffSubring S` if and only if `x.coeff n ∈ S` for
  every `n`.
* `WittVector.iterate_verschiebung_mem_coeffSubring`, `WittVector.frobenius_mem_coeffSubring`
  and `WittVector.teichmuller_mem_coeffSubring`: the subring is stable under the Verschiebung and
  the Frobenius, and contains the Teichmüller representatives of elements of `S`.
* `WittVector.truncate_iterate_verschiebung`: `verschiebung^[n] x` has vanishing truncation to
  its first `n` coefficients, and `WittVector.eq_iterate_verschiebung_shift_of_truncate_eq_zero`
  is the converse.
* `WittVector.truncate_truncLimit`: if `x (n + 1)` and `x n` agree in their first `n`
  coefficients for every `n`, then `truncLimit x` agrees with `x n` in its first `n`
  coefficients for every `n`.
* `WittVector.truncate_eq_truncate_iff`: two Witt vectors have the same truncation to `n`
  coefficients if and only if they agree in their coefficients of index `< n`.
* `WittVector.truncate_frobenius_eq_of_truncate_eq`: in characteristic `p`, the truncation of
  `frobenius x` only depends on the truncation of `x`.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section Subring

variable {Ω : Type*} [CommRing Ω]

variable (p) in
/-- The subring of `𝕎 Ω` consisting of the Witt vectors all of whose coefficients lie in the
subring `S` of `Ω`, that is, the image of the Witt vectors of `S`. -/
noncomputable def coeffSubring (S : Subring Ω) : Subring (𝕎 Ω) :=
  (WittVector.map S.subtype).range

/-- A Witt vector lies in `coeffSubring p S` if and only if all its coefficients lie in `S`. -/
theorem mem_coeffSubring_iff {S : Subring Ω} {x : 𝕎 Ω} :
    x ∈ coeffSubring p S ↔ ∀ n, x.coeff n ∈ S := by
  constructor
  · rintro ⟨y, rfl⟩ n
    rw [map_coeff]
    exact (y.coeff n).2
  · intro h
    refine ⟨mk p fun n => ⟨x.coeff n, h n⟩, ?_⟩
    ext n
    rw [map_coeff]
    rfl

/-- `coeffSubring p S` is monotone in the subring `S`. -/
theorem coeffSubring_mono {S S' : Subring Ω} (h : S ≤ S') :
    coeffSubring p S ≤ coeffSubring p S' := fun _ hx =>
  mem_coeffSubring_iff.2 fun n => h (mem_coeffSubring_iff.1 hx n)

/-- If `x` has its coefficients in `S`, then so has `verschiebung^[n] x` for every `n`. -/
theorem iterate_verschiebung_mem_coeffSubring {S : Subring Ω} {x : 𝕎 Ω}
    (hx : x ∈ coeffSubring p S) (n : ℕ) : verschiebung^[n] x ∈ coeffSubring p S := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨verschiebung y, ?_⟩
    rw [Function.iterate_succ_apply', ← hy, map_verschiebung]

/-- The Teichmüller representative of an element of `S` has its coefficients in `S`. -/
theorem teichmuller_mem_coeffSubring {S : Subring Ω} {a : Ω} (ha : a ∈ S) :
    teichmuller p a ∈ coeffSubring p S :=
  ⟨teichmuller p ⟨a, ha⟩, map_teichmuller _ S.subtype _⟩

/-- The Frobenius of a Witt vector with coefficients in `S` has its coefficients in `S`. -/
theorem frobenius_mem_coeffSubring {S : Subring Ω} {x : 𝕎 Ω} (hx : x ∈ coeffSubring p S) :
    frobenius x ∈ coeffSubring p S := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨frobenius y, (frobenius_isPoly p).map S.subtype y⟩

end Subring

variable {R : Type*} [CommRing R]

/-- The truncation of `verschiebung^[n] x` to its first `n` coefficients vanishes. -/
theorem truncate_iterate_verschiebung (n : ℕ) (x : 𝕎 R) :
    truncate n (verschiebung^[n] x) = 0 :=
  (mem_ker_truncate n _).2 fun _ hi => iterate_verschiebung_coeff_eq_zero x hi

/-- A Witt vector whose first `n` coefficients vanish is `verschiebung^[n]` of its shift. -/
theorem eq_iterate_verschiebung_shift_of_truncate_eq_zero {n : ℕ} {x : 𝕎 R}
    (hx : truncate n x = 0) : x = verschiebung^[n] (x.shift n) :=
  eq_iterate_verschiebung fun k hk => (mem_ker_truncate n x).1 hx k hk

variable (p) in
/-- The coefficientwise limit of a sequence of Witt vectors: the Witt vector whose `k`-th
coefficient is the `k`-th coefficient of `x (k + 1)`. When `x (n + 1)` and `x n` agree in their
first `n` coefficients for every `n`, it agrees with each `x n` in its first `n` coefficients
(`WittVector.truncate_truncLimit`). -/
def truncLimit (x : ℕ → 𝕎 R) : 𝕎 R :=
  mk p fun k => (x (k + 1)).coeff k

omit hp [CommRing R] in
/-- The `k`-th coefficient of `truncLimit p x` is the `k`-th coefficient of `x (k + 1)`. -/
@[simp]
theorem coeff_truncLimit (x : ℕ → 𝕎 R) (k : ℕ) : (truncLimit p x).coeff k = (x (k + 1)).coeff k :=
  rfl

/-- Equal truncations to `n` coefficients means equal coefficients of index `< n`, and
conversely. -/
private theorem truncate_eq_truncate_iff_aux {n : ℕ} {x y : 𝕎 R} :
    truncate n x = truncate n y ↔ ∀ i < n, x.coeff i = y.coeff i := by
  simp [TruncatedWittVector.ext_iff, Fin.forall_iff]

/-- If `x (n + 1)` and `x n` agree in their first `n` coefficients for every `n`, then
`truncLimit p x` agrees with `x n` in its first `n` coefficients for every `n`. -/
theorem truncate_truncLimit {x : ℕ → 𝕎 R}
    (hx : ∀ n, truncate n (x (n + 1)) = truncate n (x n)) (n : ℕ) :
    truncate n (truncLimit p x) = truncate n (x n) := by
  have hstab : ∀ k m, k < m → (x m).coeff k = (x (k + 1)).coeff k := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rfl
    | succ m hkm ih => rw [← ih, truncate_eq_truncate_iff_aux.1 (hx m) k hkm]
  refine truncate_eq_truncate_iff_aux.2 fun k hk => ?_
  rw [coeff_truncLimit, hstab k n hk]

/-- Two Witt vectors have the same truncation to `n` coefficients if and only if they agree in
their coefficients of index `< n`. -/
theorem truncate_eq_truncate_iff {n : ℕ} {x y : 𝕎 R} :
    truncate n x = truncate n y ↔ ∀ i < n, x.coeff i = y.coeff i :=
  truncate_eq_truncate_iff_aux

/-- In characteristic `p`, the truncation of `frobenius x` to `n` coefficients only depends on
the truncation of `x`. -/
theorem truncate_frobenius_eq_of_truncate_eq [CharP R p] {n : ℕ} {x y : 𝕎 R}
    (h : truncate n x = truncate n y) : truncate n (frobenius x) = truncate n (frobenius y) := by
  rw [truncate_eq_truncate_iff] at h ⊢
  intro i hi
  rw [coeff_frobenius_charP, coeff_frobenius_charP, h i hi]

end WittVector
