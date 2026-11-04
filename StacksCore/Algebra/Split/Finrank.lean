module

public import StacksCore.Algebra.Split.Basic
public import StacksCore.RingTheory.SimpleRing.Centralizer

/-!
# Splitting fields and dimension counts

An embedding `f : L →ₐ[k] A` of a field into a finite-dimensional algebra makes `A` a right
`L`-module by `a • l = a * f l`. Counting dimensions along the tower `k ⊆ L ⊆ A` through that
module is what relates splitting to the numerical condition `[A : k] = [L : k]²`.

The public results:

* `Algebra.IsCentralSimple.split_of_finrank` — an embedded field of the maximal possible
  degree splits: if `[A : k] = [L : k]²` then `L` splits `A`. This is the direction
  (2) ⇒ (1) of Stacks tag 074Z, and it is where the `L`-module structure does its work —
  `A` becomes an `L`-vector space of dimension `degree k A`, and left multiplication
  identifies `L ⊗[k] A` with `End_L A`, a matrix algebra.
* `DivisionRing.split_iff_finrank` — for a **division** algebra the converse holds too, so
  splitting is *equivalent* to `[D : k] = [L : k]²`, i.e. to `L` being a maximal subfield.
  The division hypothesis is essential; see the docstring there.
* `Algebra.IsSplit.degree_dvd_finrank` (Stacks tag 0751) — for a division algebra `D`, the
  degree `d` divides `[L : k]` for *every* finite splitting field `L`, not just the maximal
  subfields. `Algebra.IsSplit.dvd_finrank_of_sq_eq` is the same statement with `d` supplied
  by a hypothesis `d² = [D : k]`, which is how the tag phrases it.

The divisibility is the primitive here: the dimension count along `k ⊆ D ⊆ (Fin m → L)`
produces the *equation* `d * finrank D (Fin m → L) = [L : k]`, so the bound `d ≤ [L : k]`
used by `split_iff_finrank` is a corollary of it via `Nat.le_of_dvd`, not the reverse.

The `L`-module structure depends on the choice of `f`, so it is introduced locally with `let` at
each use site rather than declared as an instance.
-/

@[expose] public section

variable {k A L : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A]
  [Field L] [Algebra k L] (f : L →ₐ[k] A)

open scoped TensorProduct

private abbrev rightMod : Module L A where
  smul l a := a * f l
  mul_smul l1 l2 a := show a * f (l1 * l2) = a * f l2 * f l1 by
    rw [mul_comm, map_mul, ← mul_assoc]
  one_smul a := show a * f 1 = a by rw [map_one, mul_one]
  smul_zero l := show 0 * f l = 0 by rw [zero_mul]
  smul_add l a1 a2 := show (a1 + a2) * f l = a1 * f l + a2 * f l by rw [add_mul]
  add_smul l1 l2 a := show a * f (l1 + l2) = a * f l1 + a * f l2 by rw [map_add, mul_add]
  zero_smul a := show a * f 0 = 0 by rw [map_zero, mul_zero]

omit [Module.Finite k A] in
private lemma rightMod.smul_def (l : L) (a : A) :
    letI := rightMod f; (l • a : A) = a * f l := rfl

private abbrev scalarTower :
    letI := rightMod f; IsScalarTower k L A :=
  let : Module L A := rightMod f
  { smul_assoc k l a := show a * _ = k • (a * _) by simp}

open Algebra.IsCentralSimple

/-- A natural number whose square is the dimension of `A` is its degree. -/
private lemma eq_degree_of_sq_eq [IsSimpleRing A] [Algebra.IsCentral k A] {d : ℕ}
    (hd : d ^ 2 = Module.finrank k A) : d = degree k A :=
  (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).1
    (hd.trans (degree_sq_eq_finrank k A).symm)

private lemma finrank_eq_deg [IsSimpleRing A] [Algebra.IsCentral k A]
    (hL : Module.finrank k A = Module.finrank k L * Module.finrank k L) :
    letI := rightMod f; Module.finrank L A = degree k A := by
  let := rightMod f
  have := scalarTower f
  have : Module.Finite L A := Module.Finite.right k L A
  have hl := eq_degree_of_sq_eq (k := k) (A := A) (by rw [pow_two, hL])
  have := Module.finrank_mul_finrank k L A
  rw [hL, hl] at this
  exact Nat.eq_of_mul_eq_mul_left (degree_pos k A) this

include f in
public lemma Algebra.IsCentralSimple.split_of_finrank [IsSimpleRing A] [Algebra.IsCentral k A]
    (hL : Module.finrank k A = Module.finrank k L * Module.finrank k L) :
    Algebra.IsSplit k A L := by
  set n := Algebra.IsCentralSimple.degree k A with hn
  let : Module L A := rightMod f
  have := scalarTower f
  have : Module.Finite L A := Module.Finite.right k L A
  refine ⟨n, ne_of_gt (degree_pos k A), ⟨AlgEquiv.trans ?_
    (algEquivMatrix (Module.finBasisOfFinrankEq L A (finrank_eq_deg f hL)))⟩⟩
  let φ1 : A →ₐ[k] Module.End L A := {
    toFun a := {
      toFun := (a * ·)
      map_add' := by simp [mul_add]
      map_smul' := by simp [rightMod.smul_def, mul_assoc]
    }
    map_one' := by ext; simp
    map_mul' _ _ := by ext; simp [mul_assoc]
    map_zero' := by ext; simp
    map_add' _ _ := by ext; simp [add_mul]
    commutes' r := by ext; simp [Algebra.smul_def] }
  let φ : L ⊗[k] A →ₐ[L] Module.End L A := Algebra.TensorProduct.lift (Algebra.ofId L _) φ1 <| by
    simp [commute_iff_eq, LinearMap.ext_iff]
  refine AlgEquiv.ofBijective φ (φ.bijective_of_finrank_eq ?_)
  simp [Module.finrank_linearMap, finrank_eq_deg f hL, ← pow_two, degree_sq_eq_finrank k A]

include f in
/-- A field embedding into a finite-dimensional central simple algebra has degree at most the
degree of the algebra: the range is a commutative simple subalgebra contained in its own
centralizer, whose dimensions are complementary. -/
private lemma finrank_le_degree [IsSimpleRing A] [Algebra.IsCentral k A] :
    Module.finrank k L ≤ degree k A := by
  have finj : Function.Injective f := f.toRingHom.injective
  have : IsSimpleRing ↥f.range :=
    .of_ringEquiv (AlgEquiv.ofInjective f finj).toRingEquiv inferInstance
  have : IsMulCommutative ↥f.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (by simp [← map_mul, mul_comm])⟩⟩
  have hrange : Module.finrank k ↥f.range = Module.finrank k L :=
    ((AlgEquiv.ofInjective f finj).toLinearEquiv.finrank_eq).symm
  have h27 := Subalgebra.finrank_centralizer_mul_finrank (F := k) (A := A) f.range
  rw [hrange] at h27
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  rw [degree_sq_eq_finrank k A, pow_two, ← h27]
  exact Nat.mul_le_mul_right _ (hrange ▸ Submodule.finrank_mono
    (Subalgebra.toSubmodule.le_iff_le.2
      ((Subalgebra.le_centralizer_iff_isMulCommutative f.range).2 inferInstance)))

/-- The size of the matrix algebra in a splitting isomorphism is the degree. -/
private lemma matrix_size_eq_degree [IsSimpleRing A] [Algebra.IsCentral k A] {m : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin m) (Fin m) L) : m = degree k A := by
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h1
  exact eq_degree_of_sq_eq (by simpa [Module.finrank_matrix, pow_two] using h1.symm)

/-- A finite-dimensional central division algebra split by `L` has degree *dividing*
`finrank k L`: the column module `Fin m → L` of the splitting is a nonzero free `D`-module,
and counting its `k`-dimension along `k ⊆ D ⊆ (Fin m → L)` gives
`degree k D * finrank D (Fin m → L) = finrank k L`, exhibiting the cofactor. -/
private lemma degree_dvd_finrank_aux {D : Type*} [DivisionRing D] [Algebra k D]
    [Module.Finite k D] [Algebra.IsCentral k D] [Module.Finite k L] {m : ℕ} (hm : m ≠ 0)
    (e : L ⊗[k] D ≃ₐ[L] Matrix (Fin m) (Fin m) L) :
    degree k D ∣ Module.finrank k L := by
  let Φ : (L ⊗[k] D) →ₐ[L] Module.End L (Fin m → L) :=
    (algEquivMatrix' (R := L)).symm.toAlgHom.comp e.toAlgHom
  let : Module D (Fin m → L) :=
    Module.compHom _ (Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have : IsScalarTower k D (Fin m → L) := ⟨fun c x v ↦ by
    change Φ ((1 : L) ⊗ₜ[k] (c • x)) v = c • Φ ((1 : L) ⊗ₜ[k] x) v
    rw [TensorProduct.tmul_smul, ← algebraMap_smul L c ((1 : L) ⊗ₜ[k] x : L ⊗[k] D),
      map_smul, LinearMap.smul_apply, algebraMap_smul]⟩
  have : Module.Finite D (Fin m → L) := Module.Finite.of_restrictScalars_finite k D _
  have : Module.Free D (Fin m → L) := Module.Free.of_divisionRing D _
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  have hV : Module.finrank k (Fin m → L) = m * Module.finrank k L := by
    simp [Module.finrank_pi_fintype, Finset.sum_const, Fintype.card_fin, smul_eq_mul]
  have hkey : degree k D * (degree k D * Module.finrank D (Fin m → L)) =
      degree k D * Module.finrank k L := by
    rw [← mul_assoc, ← pow_two, degree_sq_eq_finrank k D,
      Module.finrank_mul_finrank k D (Fin m → L), hV, matrix_size_eq_degree e]
  exact ⟨Module.finrank D (Fin m → L),
    (Nat.eq_of_mul_eq_mul_left (degree_pos k D) hkey).symm⟩

/-- The degree bound underlying `DivisionRing.split_iff_finrank`, read off from the
divisibility: the cofactor `finrank D (Fin m → L)` is positive. -/
private lemma degree_le_finrank {D : Type*} [DivisionRing D] [Algebra k D]
    [Module.Finite k D] [Algebra.IsCentral k D] [Module.Finite k L] {m : ℕ} (hm : m ≠ 0)
    (e : L ⊗[k] D ≃ₐ[L] Matrix (Fin m) (Fin m) L) : degree k D ≤ Module.finrank k L :=
  Nat.le_of_dvd Module.finrank_pos (degree_dvd_finrank_aux hm e)

/-- For a finite-dimensional central **division** algebra `D` over `k`, a field `L` admitting
an embedding `g : L →ₐ[k] D` splits `D` if and only if
`finrank k D = finrank k L * finrank k L`, i.e. iff `L` embeds as a maximal subfield.

The division hypothesis is essential: `M₂(k)` is split by `L = k` but has dimension `4`. -/
public lemma DivisionRing.split_iff_finrank {D : Type*} [DivisionRing D]
    [Algebra k D] [Module.Finite k D] [Algebra.IsCentral k D] (g : L →ₐ[k] D) :
    Algebra.IsSplit k D L ↔ Module.finrank k D = Module.finrank k L * Module.finrank k L := by
  refine ⟨fun ⟨m, hm, ⟨e⟩⟩ ↦ ?_, fun h ↦ split_of_finrank g h⟩
  have : Module.Finite k L := Module.Finite.of_injective g.toLinearMap g.toRingHom.injective
  rw [le_antisymm (finrank_le_degree g) (degree_le_finrank hm e), ← pow_two,
    degree_sq_eq_finrank k D]

/-- **Stacks 0751**: for a finite central division algebra `D` over `k` with `d² = [D : k]`,
the degree `d` *divides* `[L : k]` for every finite splitting field `L` of `D`.

Note this is genuinely stronger than `d ≤ [L : k]`. The divisibility is what the dimension
count actually produces — the cofactor is `finrank D (Fin m → L)` for the column module of
the splitting — so the `≤` form is the corollary, not the other way round.

The division hypothesis is essential, as for `DivisionRing.split_iff_finrank`: `M₂(k)` is
split by `L = k` with `degree k M₂(k) = 2` and `finrank k k = 1`, and `2 ∤ 1`. -/
@[stacks 0751]
public theorem Algebra.IsSplit.degree_dvd_finrank {D : Type*} [DivisionRing D] [Algebra k D]
    [Module.Finite k D] [Algebra.IsCentral k D] [Module.Finite k L]
    (h : Algebra.IsSplit k D L) : degree k D ∣ Module.finrank k L := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h
  exact degree_dvd_finrank_aux hm e

/-- **Stacks 0751** in the tag's own phrasing, with `d` given by the hypothesis `d² = [D : k]`
rather than as `Algebra.IsCentralSimple.degree` (which is `Nat.sqrt` of the dimension). -/
public theorem Algebra.IsSplit.dvd_finrank_of_sq_eq {D : Type*} [DivisionRing D] [Algebra k D]
    [Module.Finite k D] [Algebra.IsCentral k D] [Module.Finite k L] {d : ℕ}
    (hd : d ^ 2 = Module.finrank k D) (h : Algebra.IsSplit k D L) :
    d ∣ Module.finrank k L := by
  exact eq_degree_of_sq_eq hd ▸ h.degree_dvd_finrank
