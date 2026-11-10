module

public import StacksFrontier.Algebra.Polynomial.PadicResultant
public import StacksFrontier.Algebra.Polynomial.MultiplicativeNorm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Kernel counts of integer matrices modulo `ℓ^N`, and `det R(M) = Res(χ_M, R)`

For an integer matrix `B` of size `r` and `N ≥ 0`, the kernel of `B` on `(ℤ/ℓ^N)^r` has the
cardinality of the `ℓ^N`-torsion of `ℤ^r / B ℤ^r`, a group of order `|det B|` when
`det B ≠ 0` (`Stacks.TorsionCount.index_range_mulVecLin`). Consequently, if the kernel has fewer
than `ℓ^N` elements, then `det B ≠ 0` and the kernel has exactly `ℓ^{v_ℓ(det B)}` elements
(`Stacks.TorsionCount.natCard_ker_mulVecMod_of_lt`). The inputs are the counts of primary
torsion in a finite abelian group (`Stacks.TorsionCount.natCard_tors_pow_eq`,
`Stacks.TorsionCount.factorization_le_of_natCard_tors_lt`).

It also proves `det R(M) = Res(χ_M, R)` for a square matrix `M` and a polynomial `R`
(`Stacks.Polynomial.det_aeval_eq_resultant_charpoly`, over fields and over `ℤ`), the identity
`N_{(ℚ[X]/χ)/ℚ}(R) = Res(χ, R)` for the norm form of `Stacks.Polynomial.normForm`
(`Stacks.Polynomial.normForm_eq_resultant`), and the existence of limits in `ℤ_ℓ` of compatible
sequences in `ℤ/ℓ^N` (`Stacks.TorsionCount.exists_toZModPow_eq`,
`Stacks.TorsionCount.exists_map_toZModPow_eq`).

## Main results

* `Stacks.TorsionCount.natCard_ker_mulVecMod_of_lt`, `natCard_ker_mulVecMod_of_le`.
* `Stacks.Polynomial.det_aeval_eq_resultant_charpoly_int`.
* `Stacks.Polynomial.normForm_eq_resultant`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.TorsionCount

variable {H : Type*} [AddCommGroup H] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The `n`-torsion `H[n]` as an additive subgroup. -/
abbrev tors (H : Type*) [AddCommGroup H] (n : ℕ) : AddSubgroup H :=
  (Submodule.torsionBy ℤ H (n : ℤ)).toAddSubgroup

/-- An element `x` lies in `H[n]` if and only if `n • x = 0`. -/
theorem mem_tors {n : ℕ} {x : H} : x ∈ tors H n ↔ n • x = 0 := by
  rw [AddSubgroup.mem_mk, Submodule.mem_toAddSubmonoid, Submodule.mem_torsionBy_iff, natCast_zsmul]

/-- The `ℓ^k`-torsion of a finite group has order a power of `ℓ`. -/
theorem exists_natCard_tors_eq_pow [Finite H] (k : ℕ) :
    ∃ a : ℕ, Nat.card (tors H (ℓ ^ k)) = ℓ ^ a := by
  have hpos : Nat.card (tors H (ℓ ^ k)) ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdvd => ?_⟩
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
  have h1 : (ℓ ^ k) • x = 0 := Subtype.ext (mem_tors.1 x.2)
  have h2 : d ∣ ℓ ^ k := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero h1
  exact (Nat.prime_dvd_prime_iff_eq hd hℓ.out).1 (hd.dvd_of_dvd_pow h2)

omit hℓ in
/-- For `a ≤ b`, the `ℓ^a`-torsion is contained in the `ℓ^b`-torsion. -/
theorem tors_pow_mono {a b : ℕ} (hab : a ≤ b) : tors H (ℓ ^ a) ≤ tors H (ℓ ^ b) := fun x hx => by
  rw [mem_tors] at hx ⊢
  rw [← Nat.pow_sub_mul_pow ℓ hab, mul_comm, mul_nsmul, hx, nsmul_zero]

/-- If `a * b = |H|` with `a`, `b` coprime, then `|H[a]| * |H[b]| = |H|`. -/
theorem natCard_tors_mul_natCard_tors_of_coprime [Finite H] {a b : ℕ} (hab : a.Coprime b)
    (h : a * b = Nat.card H) : Nat.card (tors H a) * Nat.card (tors H b) = Nat.card H := by
  rw [← Nat.card_prod]
  refine Nat.card_eq_of_bijective (fun y => (y.1 : H) + y.2) ⟨fun y z hyz => ?_, fun x => ?_⟩
  · have hd : (y.1 : H) - z.1 = z.2 - y.2 := by
      simp only at hyz
      rw [sub_eq_sub_iff_add_eq_add, hyz, add_comm]
    have h1 : a • ((y.1 : H) - z.1) = 0 := by
      rw [nsmul_sub, mem_tors.1 y.1.2, mem_tors.1 z.1.2, sub_zero]
    have h2 : b • ((y.1 : H) - z.1) = 0 := by
      rw [hd, nsmul_sub, mem_tors.1 y.2.2, mem_tors.1 z.2.2, sub_zero]
    have h0 : (y.1 : H) - z.1 = 0 := AddMonoid.addOrderOf_eq_one_iff.1 <|
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.of_dvd (addOrderOf_dvd_of_nsmul_eq_zero h1)
        (addOrderOf_dvd_of_nsmul_eq_zero h2) hab) dvd_rfl
    have h0' : (z.2 : H) - y.2 = 0 := hd ▸ h0
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 h0)) (Subtype.ext (sub_eq_zero.1 h0').symm)
  · obtain ⟨α, β, hαβ⟩ : ∃ α β : ℤ, α * a + β * b = 1 := by
      refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
      have := Nat.gcd_eq_gcd_ab a b
      rw [hab.gcd_eq_one, Nat.cast_one] at this
      linarith
    have hnx : Nat.card H • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.1 (addOrderOf_dvd_natCard x)
    refine ⟨(⟨(β * b) • x, mem_tors.2 ?_⟩, ⟨(α * a) • x, mem_tors.2 ?_⟩), ?_⟩
    · rw [← natCast_zsmul, smul_smul, show (a : ℤ) * (β * b) = β * Nat.card H by
        rw [← h]; push_cast; ring, mul_zsmul, natCast_zsmul, hnx, zsmul_zero]
    · rw [← natCast_zsmul, smul_smul, show (b : ℤ) * (α * a) = α * Nat.card H by
        rw [← h]; push_cast; ring, mul_zsmul, natCast_zsmul, hnx, zsmul_zero]
    · simp only
      rw [← add_zsmul, add_comm, hαβ, one_zsmul]

/-- In a finite group of order `ℓ^v m`, `ℓ ∤ m`, the `ℓ^N`-torsion for `N ≥ v` has `ℓ^v`
elements. -/
theorem natCard_tors_pow_eq [Finite H] (N : ℕ) (hN : (Nat.card H).factorization ℓ ≤ N) :
    Nat.card (tors H (ℓ ^ N)) = ℓ ^ (Nat.card H).factorization ℓ := by
  set n := Nat.card H
  set v := n.factorization ℓ
  set m := n / ℓ ^ v
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have hnm : ℓ ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hm : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ.out hn0
  have hcop : Nat.Coprime (ℓ ^ v) m := Nat.Coprime.pow_left _ ((hℓ.out.coprime_iff_not_dvd).2 hm)
  -- `H[ℓ^N] = H[ℓ^v]`
  have hTN : tors H (ℓ ^ N) = tors H (ℓ ^ v) := by
    refine le_antisymm (fun x hx => ?_) (tors_pow_mono hN)
    rw [mem_tors] at hx ⊢
    have h2 : addOrderOf x ∣ ℓ ^ v * m := hnm ▸ addOrderOf_dvd_natCard x
    exact addOrderOf_dvd_iff_nsmul_eq_zero.1 ((Nat.Coprime.coprime_dvd_left
      (addOrderOf_dvd_of_nsmul_eq_zero hx) (Nat.Coprime.pow_left _
        ((hℓ.out.coprime_iff_not_dvd).2 hm))).dvd_of_dvd_mul_right h2)
  rw [hTN]
  -- `H = H[ℓ^v] ⊕ H[m]`
  obtain ⟨a, ha⟩ := exists_natCard_tors_eq_pow (H := H) (ℓ := ℓ) v
  have hsum : Nat.card (tors H (ℓ ^ v)) * Nat.card (tors H m) = n :=
    natCard_tors_mul_natCard_tors_of_coprime hcop hnm
  have hTm : ¬ ℓ ∣ Nat.card (tors H m) := fun hd => by
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' ℓ hd
    have : m • (y : H) = 0 := mem_tors.1 y.2
    have hy' : addOrderOf (y : H) = ℓ := by rw [AddSubgroup.addOrderOf_coe, hy]
    exact hm (hy' ▸ addOrderOf_dvd_of_nsmul_eq_zero this)
  rw [ha] at hsum ⊢
  have hv : (ℓ ^ a * Nat.card (tors H m)).factorization ℓ = a := by
    rw [Nat.factorization_mul (pow_ne_zero _ hℓ.out.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, hℓ.out.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hTm, add_zero]
  rw [← hv, hsum]

/-- If the `ℓ^N`-torsion of a finite group has fewer than `ℓ^N` elements, then it is the whole
`ℓ`-primary part, of order `ℓ^v`, `v = v_ℓ(#H) ≤ N`. -/
theorem factorization_le_of_natCard_tors_lt [Finite H] (N : ℕ)
    (h : Nat.card (tors H (ℓ ^ N)) < ℓ ^ N) : (Nat.card H).factorization ℓ ≤ N := by
  by_contra hvN
  push Not at hvN
  set v := (Nat.card H).factorization ℓ
  have hstab : ∀ k j, tors H (ℓ ^ (k + 1)) = tors H (ℓ ^ k) →
      tors H (ℓ ^ (k + j)) = tors H (ℓ ^ k) := by
    intro k j hk
    induction j with
    | zero => rfl
    | succ j ih =>
      refine le_antisymm (fun x hx => ?_) (ih ▸ tors_pow_mono (by omega))
      rw [← ih, mem_tors]
      have : (ℓ ^ j) • x ∈ tors H (ℓ ^ (k + 1)) := by
        rw [mem_tors, smul_smul, ← pow_add, show k + 1 + j = k + (j + 1) by ring]
        exact mem_tors.1 hx
      rw [hk, mem_tors, smul_smul, ← pow_add] at this
      exact this
  have hv := natCard_tors_pow_eq (H := H) (ℓ := ℓ) v le_rfl
  have main : ∀ k, k ≤ N → ℓ ^ k ≤ Nat.card (tors H (ℓ ^ k)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      by_cases heq : tors H (ℓ ^ (k + 1)) = tors H (ℓ ^ k)
      · exfalso
        have h1 := hstab k (v - k) heq
        have h2 := hstab k (N - k) heq
        rw [show k + (v - k) = v by omega] at h1
        rw [show k + (N - k) = N by omega] at h2
        rw [h2, ← h1, hv] at h
        exact absurd h (not_lt.2 (Nat.pow_le_pow_right hℓ.out.pos hvN.le))
      · obtain ⟨a, ha⟩ := exists_natCard_tors_eq_pow (H := H) (ℓ := ℓ) k
        obtain ⟨b, hb⟩ := exists_natCard_tors_eq_pow (H := H) (ℓ := ℓ) (k + 1)
        have hdvd := AddSubgroup.card_dvd_of_le (tors_pow_mono (H := H) (ℓ := ℓ) (Nat.le_succ k))
        rw [ha, hb] at hdvd
        have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right hℓ.out.one_lt).1 hdvd
        have hne : a ≠ b := fun e => heq (AddSubgroup.eq_of_le_of_card_ge
          (tors_pow_mono (Nat.le_succ k)) (by rw [ha, hb, e])).symm
        rw [hb, pow_succ]
        calc ℓ ^ k * ℓ ≤ ℓ ^ a * ℓ := Nat.mul_le_mul_right _ (ha ▸ ih)
          _ = ℓ ^ (a + 1) := (pow_succ _ _).symm
          _ ≤ ℓ ^ b := Nat.pow_le_pow_right hℓ.out.pos (by omega)
  exact absurd (main N le_rfl) (not_le.2 h)

/-- The lattice `B ℤ^r` has index `|det B|` in `ℤ^r`. -/
theorem index_range_mulVecLin {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det ≠ 0) :
    (LinearMap.range B.mulVecLin).toAddSubgroup.index = B.det.natAbs := by
  classical
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have hspan : Submodule.span ℤ (Set.range B.col) = LinearMap.range B.mulVecLin :=
    (Matrix.range_mulVecLin B).symm
  let bN : Module.Basis (Fin r) ℤ (LinearMap.range B.mulVecLin) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin r)) _ bN, Module.Basis.det_apply]
  congr 2
  ext i j
  simp only [bN, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.map_apply,
    LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  rfl

/-- The lattice `B ℤ^r` has finite index in `ℤ^r` when `det B ≠ 0`. -/
private theorem finiteIndex_range_mulVecLin {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : B.det ≠ 0) : (LinearMap.range B.mulVecLin).toAddSubgroup.FiniteIndex :=
  ⟨by rw [index_range_mulVecLin B hB]; exact Int.natAbs_ne_zero.2 hB⟩

/-- The quotient `ℤ^r / B ℤ^r` has `|det B|` elements when `det B ≠ 0`. -/
private theorem natCard_quotient_range_mulVecLin {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : B.det ≠ 0) :
    Nat.card ((Fin r → ℤ) ⧸ (LinearMap.range B.mulVecLin).toAddSubgroup) = B.det.natAbs := by
  have := finiteIndex_range_mulVecLin B hB
  rw [← AddSubgroup.index_eq_card, index_range_mulVecLin B hB]

/-- Multiplication by an integer matrix `B` on `(ℤ/ℓ^N)^r`. -/
def mulVecMod {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (N : ℕ) :
    (Fin r → ZMod (ℓ ^ N)) →+ (Fin r → ZMod (ℓ ^ N)) :=
  (B.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVecLin.toAddMonoidHom

/-- Multiplication by `n` on an additive commutative group. -/
def nsmulHom (G : Type*) [AddCommGroup G] (n : ℕ) : G →+ G where
  toFun x := n • x
  map_zero' := nsmul_zero n
  map_add' x y := nsmul_add x y n

omit hℓ in
/-- The preimage of `B (ℤ/ℓ^N)^r` under reduction is the preimage of `ℓ^N (ℤ^r / B ℤ^r)`. -/
private theorem comap_range_mulVecMod_eq {r N : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (π : (Fin r → ℤ) →+ (Fin r → ZMod (ℓ ^ N))) (hπapp : ∀ x i, π x i = (x i : ZMod (ℓ ^ N)))
    (hπ : Function.Surjective π) (hπB : ∀ x, π (B.mulVec x) = mulVecMod (ℓ := ℓ) B N (π x)) :
    AddSubgroup.comap π (mulVecMod (ℓ := ℓ) B N).range =
      AddSubgroup.comap (QuotientAddGroup.mk' (LinearMap.range B.mulVecLin).toAddSubgroup)
        (nsmulHom ((Fin r → ℤ) ⧸ (LinearMap.range B.mulVecLin).toAddSubgroup) (ℓ ^ N)).range := by
  set L := (LinearMap.range B.mulVecLin).toAddSubgroup
  set q : (Fin r → ℤ) →+ (Fin r → ℤ) ⧸ L := QuotientAddGroup.mk' L
  ext x
  simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := hπ y
    rw [← hπB] at hy
    have h0 : π (x - B.mulVec y') = 0 := by rw [map_sub, hy, sub_self]
    have hdiv : ∀ i, ((ℓ ^ N : ℕ) : ℤ) ∣ (x - B.mulVec y') i := fun i => by
      have := congrFun h0 i
      rw [hπapp, Pi.zero_apply] at this
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    choose z hz using hdiv
    refine ⟨q z, ?_⟩
    have : x = B.mulVec y' + (ℓ ^ N : ℕ) • z := by
      funext i
      rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
      have := hz i
      simp only [Pi.sub_apply] at this
      push_cast at this ⊢
      linarith
    rw [this, map_add]
    have hBq : q (B.mulVec y') = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨y', rfl⟩
    rw [hBq, zero_add, map_nsmul]
    rfl
  · rintro ⟨g, hg⟩
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L g
    have : q (x - (ℓ ^ N : ℕ) • z) = 0 := by
      rw [map_sub, map_nsmul, ← hg]
      exact sub_self _
    obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff _).1 this
    refine ⟨π y, ?_⟩
    rw [← hπB]
    change π (B.mulVecLin y) = π x
    rw [hy, map_sub, map_nsmul]
    have hz0 : (ℓ ^ N : ℕ) • π z = 0 := by
      funext i
      rw [Pi.smul_apply, hπapp, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hz0, sub_zero]

/-- **The kernel of `B` on `(ℤ/ℓ^N)^r` is the `ℓ^N`-torsion of `ℤ^r / B ℤ^r`.** Both have the
cardinality of the cokernel of `B` on `(ℤ/ℓ^N)^r`, which is `ℤ^r / (B ℤ^r + ℓ^N ℤ^r)`. -/
theorem natCard_ker_mulVecMod {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det ≠ 0) (N : ℕ) :
    Nat.card (mulVecMod (ℓ := ℓ) B N).ker = Nat.card (tors ((Fin r → ℤ) ⧸
      (LinearMap.range B.mulVecLin).toAddSubgroup) (ℓ ^ N)) := by
  classical
  have : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  set L := (LinearMap.range B.mulVecLin).toAddSubgroup
  have := finiteIndex_range_mulVecLin B hB
  set G := (Fin r → ℤ) ⧸ L
  set q : (Fin r → ℤ) →+ G := QuotientAddGroup.mk' L
  let π : (Fin r → ℤ) →+ (Fin r → ZMod (ℓ ^ N)) :=
    { toFun := fun x i => (x i : ZMod (ℓ ^ N))
      map_zero' := by funext; simp
      map_add' := fun _ _ => by funext; simp }
  have hπapp : ∀ x i, π x i = (x i : ZMod (ℓ ^ N)) := fun _ _ => rfl
  have hπ : Function.Surjective π := fun y => ⟨fun i => ((y i).val : ℤ), funext fun i => by
    rw [hπapp]
    simp⟩
  have hπB : ∀ x, π (B.mulVec x) = mulVecMod (ℓ := ℓ) B N (π x) := fun x => by
    funext i
    simp only [hπapp, mulVecMod, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Matrix.map_apply,
      Int.coe_castRingHom]
  have hker_tors : (nsmulHom G (ℓ ^ N)).ker = tors G (ℓ ^ N) := by
    ext x
    rw [AddMonoidHom.mem_ker, mem_tors]
    rfl
  have hcomap : AddSubgroup.comap π (mulVecMod (ℓ := ℓ) B N).range =
      AddSubgroup.comap q (nsmulHom G (ℓ ^ N)).range :=
    comap_range_mulVecMod_eq B π hπapp hπ hπB
  have : Finite G := AddSubgroup.finite_quotient_of_finiteIndex
  rw [← AddSubgroup.index_range, ← AddSubgroup.index_comap_of_surjective _ hπ, hcomap,
    AddSubgroup.index_comap_of_surjective _ (QuotientAddGroup.mk'_surjective L),
    AddSubgroup.index_range, hker_tors]

/-- A singular integer matrix kills a vector with a coordinate prime to `ℓ`. -/
theorem exists_mulVec_eq_zero_not_dvd {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det = 0) :
    ∃ w : Fin r → ℤ, B.mulVec w = 0 ∧ ∃ i, ¬ (ℓ : ℤ) ∣ w i := by
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hB
  have hex : ∃ n, ∃ v : Fin r → ℤ, v ≠ 0 ∧ B.mulVec v = 0 ∧ ∑ i, (v i).natAbs = n :=
    ⟨_, v, hv0, hv, rfl⟩
  obtain ⟨w, hw0, hw, hwn⟩ := Nat.find_spec hex
  refine ⟨w, hw, ?_⟩
  by_contra hall
  push Not at hall
  choose u hu using hall
  have hu0 : u ≠ 0 := fun h => hw0 (funext fun i => by rw [hu i, h, Pi.zero_apply, mul_zero])
  have hwu : w = (ℓ : ℤ) • u := funext hu
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hBu : B.mulVec u = 0 := by
    rw [hwu, Matrix.mulVec_smul] at hw
    exact (smul_eq_zero.1 hw).resolve_left hℓ0
  have hlt : ∑ i, (u i).natAbs < Nat.find hex := by
    rw [← hwn]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hu0
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · rw [hu i, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.2 hℓ0)
    · rw [hu j, Int.natAbs_mul]
      exact lt_mul_left (Int.natAbs_pos.2 hj) (by simpa using hℓ.out.one_lt)
  exact Nat.find_min hex hlt ⟨u, hu0, hBu, rfl⟩

/-- **Kernel counts and the `ℓ`-adic valuation of a determinant.** For an integer matrix `B`
and `N`: if `B` has fewer than `ℓ^N` kernel vectors on `(ℤ/ℓ^N)^r`, then `det B ≠ 0`,
`v_ℓ(det B) ≤ N`, and the kernel has exactly `ℓ^{v_ℓ(det B)}` elements. -/
theorem natCard_ker_mulVecMod_of_lt {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (N : ℕ)
    (h : Nat.card (mulVecMod (ℓ := ℓ) B N).ker < ℓ ^ N) :
    B.det ≠ 0 ∧ B.det.natAbs.factorization ℓ ≤ N ∧
      Nat.card (mulVecMod (ℓ := ℓ) B N).ker = ℓ ^ B.det.natAbs.factorization ℓ := by
  classical
  have : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  have hdet : B.det ≠ 0 := by
    intro hB
    obtain ⟨w, hw, i, hi⟩ := exists_mulVec_eq_zero_not_dvd (ℓ := ℓ) B hB
    let w' : Fin r → ZMod (ℓ ^ N) := fun i => (w i : ZMod (ℓ ^ N))
    have hw' : w' ∈ (mulVecMod (ℓ := ℓ) B N).ker := by
      rw [AddMonoidHom.mem_ker]
      funext j
      have := congrArg (fun v : Fin r → ℤ => (v j : ZMod (ℓ ^ N))) hw
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Pi.zero_apply,
        Int.cast_zero] at this
      simpa [mulVecMod, Matrix.mulVec, dotProduct, w'] using this
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have h1 : (1 : ℕ) ≤ Nat.card (mulVecMod (ℓ := ℓ) B 0).ker := Nat.card_pos
      have h2 : ℓ ^ 0 = 1 := pow_zero ℓ
      omega
    have hord : addOrderOf w' = ℓ ^ N := by
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine addOrderOf_eq_prime_pow (fun h0 => hi ?_) (funext fun j => ?_)
      · have := congrFun h0 i
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, w'] at this
        have h2 : ((ℓ ^ (N' + 1) : ℕ) : ℤ) ∣ (ℓ ^ N' : ℕ) * w i := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast at this ⊢
          exact this
        push_cast at h2
        rw [pow_succ] at h2
        exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero))).1 h2
      · simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, w']
        rw [show ((ℓ ^ (N' + 1) : ℕ) : ZMod (ℓ ^ (N' + 1))) = 0 from ZMod.natCast_self _, zero_mul]
    have := addOrderOf_dvd_natCard (⟨w', hw'⟩ : (mulVecMod (ℓ := ℓ) B N).ker)
    rw [AddSubgroup.addOrderOf_mk, hord] at this
    exact absurd (Nat.le_of_dvd Nat.card_pos this) (not_le.2 h)
  have := finiteIndex_range_mulVecLin B hdet
  have : Finite ((Fin r → ℤ) ⧸ (LinearMap.range B.mulVecLin).toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hcard := natCard_quotient_range_mulVecLin B hdet
  rw [natCard_ker_mulVecMod B hdet] at h ⊢
  have hv := factorization_le_of_natCard_tors_lt N h
  rw [hcard] at hv
  refine ⟨hdet, hv, ?_⟩
  rw [natCard_tors_pow_eq N (by rwa [hcard]), hcard]

/-- If `v_ℓ(det B) ≤ N` (and `det B ≠ 0`), then `B` has exactly `ℓ^{v_ℓ(det B)}` kernel vectors on
`(ℤ/ℓ^N)^r`. -/
theorem natCard_ker_mulVecMod_of_le {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (hdet : B.det ≠ 0)
    (N : ℕ) (hN : B.det.natAbs.factorization ℓ ≤ N) :
    Nat.card (mulVecMod (ℓ := ℓ) B N).ker = ℓ ^ B.det.natAbs.factorization ℓ := by
  have := finiteIndex_range_mulVecLin B hdet
  have : Finite ((Fin r → ℤ) ⧸ (LinearMap.range B.mulVecLin).toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hcard := natCard_quotient_range_mulVecLin B hdet
  rw [natCard_ker_mulVecMod B hdet, natCard_tors_pow_eq N (by rwa [hcard]), hcard]

end Stacks.TorsionCount

namespace Stacks.Polynomial

/-- **`det R(M) = Res(χ_M, R)`** over an algebraically closed field: with
`R = a ∏ (X - μ_j)`, `det R(M) = a^r ∏ det(M - μ_j) = (-1)^{r d} a^r ∏ χ_M(μ_j)`. -/
theorem det_aeval_eq_resultant_charpoly_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    {r : ℕ} (M : Matrix (Fin r) (Fin r) K) (R : K[X]) :
    (aeval M R).det = M.charpoly.resultant R r R.natDegree := by
  classical
  have hroots : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hR := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hc : M.charpoly.natDegree = r := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [resultant_comm, resultant_eq_prod_eval R M.charpoly r hc.le (IsAlgClosed.splits R)]
  have hdet : ∀ μ : K, (aeval M (X - C μ)).det = (-1) ^ r * M.charpoly.eval μ := fun μ => by
    rw [Matrix.eval_charpoly, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      show M - μ • (1 : Matrix (Fin r) (Fin r) K) = -(Matrix.scalar (Fin r) μ - M) by
        rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal],
      Matrix.det_neg, Fintype.card_fin]
  let Φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval M).toRingHom.toMonoidHom
  have hΦ : ∀ S, Φ S = (aeval M S).det := fun _ => rfl
  rw [← hΦ]
  conv_lhs => rw [← hR]
  rw [map_mul, map_multiset_prod, Multiset.map_map, hΦ, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  simp only [Function.comp_def, hΦ, hdet, Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, hroots]
  ring

/-- `R(M)` commutes with ring homomorphisms applied entrywise. -/
theorem mapMatrix_aeval {A B : Type*} [CommRing A] [CommRing B] {r : ℕ} (f : A →+* B)
    (M : Matrix (Fin r) (Fin r) A) (R : A[X]) :
    f.mapMatrix (aeval M R) = aeval (f.mapMatrix M) (R.map f) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
  congr 1
  ext a i j
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- `det R(M) = Res(χ_M, R)` over a commutative ring, from an injection into an algebraically
closed field. -/
private theorem det_aeval_eq_resultant_charpoly_of_injective {A K : Type*} [CommRing A] [Field K]
    [IsAlgClosed K] (ι : A →+* K) (hι : Function.Injective ι) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (R : A[X]) :
    (aeval M R).det = M.charpoly.resultant R r R.natDegree := by
  apply hι
  rw [RingHom.map_det, mapMatrix_aeval, ← resultant_map_map, RingHom.mapMatrix_apply,
    ← Matrix.charpoly_map, det_aeval_eq_resultant_charpoly_of_isAlgClosed,
    natDegree_map_eq_of_injective hι]

/-- **`det R(B) = Res(χ_B, R)` for integer matrices**, from the algebraically closed case through
`ℤ ⊆ ℚ̄`. -/
theorem det_aeval_eq_resultant_charpoly_int {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (R : ℤ[X]) :
    (aeval B R).det = B.charpoly.resultant R r R.natDegree :=
  det_aeval_eq_resultant_charpoly_of_injective (Int.castRingHom (AlgebraicClosure ℚ))
    (RingHom.injective_int _) B R

/-- `det R(B) = Res(χ_B, R)` over a field, through its algebraic closure. -/
theorem det_aeval_eq_resultant_charpoly {K : Type*} [Field K] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (R : K[X]) :
    (aeval M R).det = M.charpoly.resultant R r R.natDegree :=
  det_aeval_eq_resultant_charpoly_of_injective (algebraMap K (AlgebraicClosure K))
    (algebraMap K (AlgebraicClosure K)).injective M R

/-- **The norm form is the resultant**: `N_{(ℚ[X]/χ)/ℚ}(R) = Res(χ, R)` for `χ` monic. -/
theorem normForm_eq_resultant {χ : ℚ[X]} (hχ : χ.Monic) (R : ℤ[X]) :
    normForm χ R = χ.resultant (R.map (Int.castRingHom ℚ)) := by
  classical
  set pb := AdjoinRoot.powerBasis' hχ
  have hchar : (Algebra.leftMulMatrix pb.basis (AdjoinRoot.root χ)).charpoly = χ := by
    have h := charpoly_leftMulMatrix pb
    rwa [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root hχ.ne_zero, hχ.leadingCoeff, inv_one,
      C_1, mul_one] at h
  have hdim : pb.dim = χ.natDegree := AdjoinRoot.powerBasis'_dim hχ
  rw [normForm, Algebra.norm_eq_matrix_det pb.basis, ← AdjoinRoot.aeval_eq, ← aeval_algHom_apply,
    det_aeval_eq_resultant_charpoly, hchar, hdim]

end Stacks.Polynomial

namespace Stacks.TorsionCount

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Multiplication by `ℓ^{N-n}`, `ℤ/ℓ^n → ℤ/ℓ^N`, for `n ≤ N`. -/
def scaleEmb {n N : ℕ} (h : n ≤ N) : ZMod (ℓ ^ n) →+ ZMod (ℓ ^ N) :=
  ZMod.lift (ℓ ^ n) ⟨(AddMonoidHom.mulLeft ((ℓ : ZMod (ℓ ^ N)) ^ (N - n))).comp
    (Int.castAddHom (ZMod (ℓ ^ N))), by
      change (ℓ : ZMod (ℓ ^ N)) ^ (N - n) * (((ℓ ^ n : ℕ) : ℤ) : ZMod (ℓ ^ N)) = 0
      rw [Int.cast_natCast, Nat.cast_pow, ← pow_add, Nat.sub_add_cancel h]
      exact_mod_cast ZMod.natCast_self (ℓ ^ N)⟩

omit hℓ in
/-- `scaleEmb` sends the class of an integer `k` to `ℓ^{N-n} k`. -/
theorem scaleEmb_intCast {n N : ℕ} (h : n ≤ N) (k : ℤ) :
    scaleEmb (ℓ := ℓ) h (k : ZMod (ℓ ^ n)) = (ℓ : ZMod (ℓ ^ N)) ^ (N - n) * k := by
  rw [scaleEmb, ZMod.lift_coe]
  rfl

omit hℓ in
/-- `scaleEmb` is `ℤ/ℓ^N`-linear: for `c` in `ℤ/ℓ^N`, it sends `(c mod ℓ^n) * a` to
`c * scaleEmb a`. -/
theorem scaleEmb_mul {n N : ℕ} (h : n ≤ N) (c : ZMod (ℓ ^ N)) (a : ZMod (ℓ ^ n)) :
    scaleEmb (ℓ := ℓ) h (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n)) c * a) =
      c * scaleEmb h a := by
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective c
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast, ← Int.cast_mul, scaleEmb_intCast, scaleEmb_intCast]
  push_cast
  ring

/-- Multiplication by `ℓ^{N-n}` from `ℤ/ℓ^n` to `ℤ/ℓ^N` is injective. -/
theorem scaleEmb_injective {n N : ℕ} (h : n ≤ N) : Function.Injective (scaleEmb (ℓ := ℓ) h) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [scaleEmb_intCast] at ha
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : ((ℓ ^ N : ℕ) : ℤ) ∣ (ℓ : ℤ) ^ (N - n) * a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact ha
  rw [show ((ℓ ^ N : ℕ) : ℤ) = (ℓ : ℤ) ^ (N - n) * (ℓ : ℤ) ^ n by
    push_cast; rw [← pow_add, Nat.sub_add_cancel h]] at this
  push_cast
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero))).1 this

/-- Every element of `ℤ/ℓ^N` killed by `ℓ^n` lies in the image of `scaleEmb`. -/
theorem mem_range_scaleEmb {n N : ℕ} (h : n ≤ N) (b : ZMod (ℓ ^ N)) (hb : (ℓ ^ n) • b = 0) :
    ∃ a, scaleEmb (ℓ := ℓ) h a = b := by
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  have hdvd : ((ℓ ^ N : ℕ) : ℤ) ∣ (ℓ : ℤ) ^ n * b := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [nsmul_eq_mul] at hb
    push_cast at hb ⊢
    exact hb
  rw [show ((ℓ ^ N : ℕ) : ℤ) = (ℓ : ℤ) ^ n * (ℓ : ℤ) ^ (N - n) by
    push_cast; rw [← pow_add, Nat.add_sub_cancel' h]] at hdvd
  obtain ⟨t, ht⟩ := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero))).1
    hdvd
  exact ⟨(t : ZMod (ℓ ^ n)), by rw [scaleEmb_intCast, ht]; push_cast; ring⟩


/-- The compatible sequences in `∏_N ℤ/ℓ^N`. -/
def compatibleSubring (ℓ : ℕ) : Subring (∀ N : ℕ, ZMod (ℓ ^ N)) where
  carrier := {x | ∀ n N (h : n ≤ N), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n)) (x N) = x n}
  mul_mem' {x y} hx hy n N h := by simp only [Pi.mul_apply, map_mul, hx n N h, hy n N h]
  one_mem' n N h := by simp only [Pi.one_apply, map_one]
  add_mem' {x y} hx hy n N h := by simp only [Pi.add_apply, map_add, hx n N h, hy n N h]
  zero_mem' n N h := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {x} hx n N h := by simp only [Pi.neg_apply, map_neg, hx n N h]

/-- **A compatible sequence in `ℤ/ℓ^N` has a limit in `ℤ_ℓ`.** -/
theorem exists_toZModPow_eq (x : ∀ N : ℕ, ZMod (ℓ ^ N))
    (hx : ∀ n N (h : n ≤ N), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n)) (x N) = x n) :
    ∃ y : ℤ_[ℓ], ∀ N, PadicInt.toZModPow N y = x N := by
  let f : ∀ k, compatibleSubring ℓ →+* ZMod (ℓ ^ k) := fun k =>
    (Pi.evalRingHom (fun N => ZMod (ℓ ^ N)) k).comp (compatibleSubring ℓ).subtype
  have hf : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))).comp (f k2) = f k1 :=
    fun k1 k2 hk => RingHom.ext fun z => z.2 k1 k2 hk
  refine ⟨PadicInt.lift hf ⟨x, hx⟩, fun N => ?_⟩
  exact congrArg (fun φ => φ ⟨x, hx⟩) (PadicInt.lift_spec hf N)

/-- **A compatible sequence of polynomials of bounded degree over `ℤ/ℓ^N` has a limit in
`ℤ_ℓ[X]`.** -/
theorem exists_map_toZModPow_eq (c : ∀ N : ℕ, (ZMod (ℓ ^ N))[X]) (d : ℕ)
    (hd : ∀ N, (c N).natDegree ≤ d)
    (hc : ∀ n N (h : n ≤ N), (c N).map (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n))) = c n) :
    ∃ F : ℤ_[ℓ][X], F.natDegree ≤ d ∧ ∀ N, F.map (PadicInt.toZModPow N) = c N := by
  choose y hy using fun k => exists_toZModPow_eq (ℓ := ℓ) (fun N => (c N).coeff k)
    (fun n N h => by rw [← hc n N h, coeff_map])
  refine ⟨∑ k ∈ Finset.range (d + 1), C (y k) * X ^ k, ?_, fun N => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  · ext k
    rw [coeff_map, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
    split_ifs with hk
    · exact hy k N
    · rw [map_zero, coeff_eq_zero_of_natDegree_lt ((hd N).trans_lt (by omega))]

end Stacks.TorsionCount
