module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.LinearCombination

/-!
# Torsion of a divisible abelian group

Let `G` be an abelian group which is divisible, and let `n` be a positive integer such that for
every prime `ℓ ∣ n` the `ℓ`-torsion `G[ℓ]` is a direct sum of `r` copies of `ℤ/ℓℤ`.  Then the
`n`-torsion `G[n]` is a direct sum of `r` copies of `ℤ/nℤ`.  This is the group theory used in the
proof of parts (7) and (8) of Stacks Tag 03RP.

## Main definitions

* `AddCommGroup.IsTorsionBasis`: a family `y : ι → G` of `n`-torsion elements such that every
  element of `G[n]` is an integer combination of the `y i`, and such a combination vanishes
  exactly when every coefficient is divisible by `n`.

## Main results

* `AddCommGroup.IsTorsionBasis.addEquiv`: a torsion basis of `G[n]` identifies `G[n]` with
  `ι → ZMod n`.
* `AddCommGroup.isTorsionBasis_of_addEquiv`: conversely an identification of `G[n]` with
  `ι → ZMod n` gives a torsion basis.
* `AddCommGroup.IsTorsionBasis.mul_of_dvd` and `AddCommGroup.IsTorsionBasis.mul_of_coprime`:
  the two induction steps, a divided basis for `a * n'` when `a ∣ n'`, and the sum of two bases
  for coprime `a` and `b`.
* `AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible`: the main statement.
* `AddCommGroup.exists_torsionBy_prime_addEquiv`: a finite group of exponent dividing a prime
  `ℓ` is a direct sum of copies of `ℤ/ℓℤ`.

## Implementation notes

The `n`-torsion is Mathlib's `AddSubgroup.torsionBy G n`.  The proof works with integer
coefficients throughout and only passes to `ZMod n` at the end, through the two surjections
`(ι → ℤ) → G[n]` and `(ι → ℤ) → (ι → ZMod n)`, which have the same kernel.  The induction on
`n` peels off the smallest prime factor `ℓ` of `n = ℓ * n'`: if `ℓ ∣ n'` a basis of `G[n']` is
divided by `ℓ` (this is where divisibility is used), and otherwise a basis of `G[ℓ]` is added to
it, which is the Chinese remainder theorem with integer coefficients.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open scoped BigOperators

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]

/-- Scalar multiplication by a product of natural numbers, as two successive multiplications. -/
private theorem natCast_mul_zsmul (a b : ℕ) (x : G) :
    ((a * b : ℕ) : ℤ) • x = (b : ℤ) • (a : ℤ) • x := by
  rw [Nat.cast_mul, mul_comm, mul_zsmul]

/-- A **torsion basis** of the `n`-torsion `G[n]`: a family of `n`-torsion elements whose integer
combinations exhaust `G[n]`, and whose combination with coefficients `c` vanishes exactly when
`n` divides every `c i`. -/
structure IsTorsionBasis (n : ℕ) (y : ι → G) : Prop where
  nsmul_eq_zero : ∀ i, (n : ℤ) • y i = 0
  dvd_of_sum_eq_zero : ∀ c : ι → ℤ, ∑ i, c i • y i = 0 → ∀ i, (n : ℤ) ∣ c i
  exists_sum_eq : ∀ h : G, (n : ℤ) • h = 0 → ∃ c : ι → ℤ, ∑ i, c i • y i = h

namespace IsTorsionBasis

variable {n : ℕ} {y : ι → G}

/-- An integer combination of a torsion basis of `G[n]` vanishes exactly when `n` divides every
coefficient. -/
theorem sum_eq_zero_iff (hy : IsTorsionBasis n y) (c : ι → ℤ) :
    ∑ i, c i • y i = 0 ↔ ∀ i, (n : ℤ) ∣ c i := by
  refine ⟨hy.dvd_of_sum_eq_zero c, fun h => Finset.sum_eq_zero fun i _ => ?_⟩
  obtain ⟨d, hd⟩ := h i
  rw [hd, mul_comm, mul_zsmul, hy.nsmul_eq_zero, zsmul_zero]

/-- Every integer combination of a torsion basis of `G[n]` is killed by `n`. -/
theorem nsmul_sum_eq_zero (hy : IsTorsionBasis n y) (c : ι → ℤ) :
    (n : ℤ) • ∑ i, c i • y i = 0 := by
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, hy.nsmul_eq_zero, zsmul_zero]

/-- Integer combinations of a torsion basis, as a homomorphism onto `G[n]`. -/
def sumHom (hy : IsTorsionBasis n y) : (ι → ℤ) →+ AddSubgroup.torsionBy G n where
  toFun c := ⟨∑ i, c i • y i, (Submodule.mem_torsionBy_iff _ _).mpr (hy.nsmul_sum_eq_zero c)⟩
  map_zero' := by ext; simp
  map_add' c d := by ext; simp [add_zsmul, Finset.sum_add_distrib]

/-- Integer combinations of a torsion basis exhaust `G[n]`. -/
theorem sumHom_surjective (hy : IsTorsionBasis n y) : Function.Surjective hy.sumHom := by
  rintro ⟨h, hh⟩
  obtain ⟨c, hc⟩ := hy.exists_sum_eq h ((Submodule.mem_torsionBy_iff _ _).mp hh)
  exact ⟨c, Subtype.ext hc⟩

/-- Reduction modulo `n` of integer coefficients. -/
def castHom (n : ℕ) : (ι → ℤ) →+ (ι → ZMod n) :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod n)) ι

omit [Fintype ι] in
/-- Reduction modulo `n` of integer coefficients is surjective. -/
theorem castHom_surjective : Function.Surjective (castHom (ι := ι) n) := fun a =>
  ⟨fun i => (a i).cast, funext fun i => ZMod.intCast_zmod_cast (a i)⟩

/-- The integer coefficient vectors whose combination of a torsion basis of `G[n]` vanishes are
exactly those that vanish modulo `n`. -/
theorem ker_sumHom (hy : IsTorsionBasis n y) : hy.sumHom.ker = (castHom (ι := ι) n).ker := by
  ext c
  simp only [AddMonoidHom.mem_ker]
  rw [show hy.sumHom c = 0 ↔ ∑ i, c i • y i = 0 from Subtype.ext_iff, hy.sum_eq_zero_iff,
    funext_iff]
  simp [castHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A torsion basis of `G[n]` identifies `G[n]` with `ι → ZMod n`. -/
noncomputable def addEquiv (hy : IsTorsionBasis n y) :
    AddSubgroup.torsionBy G n ≃+ (ι → ZMod n) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ hy.sumHom_surjective).symm.trans <|
    (QuotientAddGroup.quotientAddEquivOfEq hy.ker_sumHom).trans <|
      QuotientAddGroup.quotientKerEquivOfSurjective _ castHom_surjective

/-- **Division step.** If `y'` is a torsion basis of `G[n']` with `n' = a * b ≠ 0`, and
`a • y i = y' i`, then `y` is a torsion basis of `G[a * n']`. -/
theorem mul_of_dvd {n' a b : ℕ} (hab : n' = a * b) (ha : a ≠ 0) (hb : b ≠ 0) {y' : ι → G}
    (hy' : IsTorsionBasis n' y') (hy : ∀ i, (a : ℤ) • y i = y' i) :
    IsTorsionBasis (a * n') y := by
  have hy'' : ∀ i, ((a * n' : ℕ) : ℤ) • y i = 0 := fun i => by
    rw [natCast_mul_zsmul, hy, hy'.nsmul_eq_zero]
  have hsum : ∀ c : ι → ℤ, (a : ℤ) • ∑ i, c i • y i = ∑ i, c i • y' i := fun c => by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, hy]
  have hny : ∀ i, (n' : ℤ) • y i = (b : ℤ) • y' i := fun i => by
    rw [hab, natCast_mul_zsmul, hy]
  refine ⟨hy'', fun c hc i => ?_, fun h hh => ?_⟩
  · have hc' : ∀ i, (n' : ℤ) ∣ c i := hy'.dvd_of_sum_eq_zero c (by rw [← hsum, hc, zsmul_zero])
    choose d hd using hc'
    have h0 : ∑ i, (d i * b) • y' i = 0 := by
      rw [← hc]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hd, mul_comm (n' : ℤ), mul_smul (d i) (n' : ℤ), hny, mul_smul]
    obtain ⟨e, he⟩ := hy'.dvd_of_sum_eq_zero _ h0 i
    have hbz : (b : ℤ) ≠ 0 := by exact_mod_cast hb
    have : d i = a * e := by
      rw [hab, Nat.cast_mul] at he
      exact mul_right_cancel₀ hbz (by linarith)
    exact ⟨e, by rw [hd, this, Nat.cast_mul]; ring⟩
  · have h1 : (n' : ℤ) • ((a : ℤ) • h) = 0 := by
      rwa [← natCast_mul_zsmul]
    obtain ⟨c, hc⟩ := hy'.exists_sum_eq _ h1
    set g := h - ∑ i, c i • y i with hg
    have hga : (a : ℤ) • g = 0 := by rw [hg, zsmul_sub, hsum, hc, sub_self]
    have hgn : (n' : ℤ) • g = 0 := by
      rw [hab, natCast_mul_zsmul, hga, zsmul_zero]
    obtain ⟨d, hd⟩ := hy'.exists_sum_eq g hgn
    have hsumd : ∑ i, ((a : ℤ) * d i) • y' i = (a : ℤ) • g := by
      rw [← hd, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_zsmul _ _ _
    have hdiv : ∀ i, (n' : ℤ) ∣ a * d i :=
      hy'.dvd_of_sum_eq_zero _ (by rw [hsumd, hga])
    have hdb : ∀ i, (b : ℤ) ∣ d i := fun i => by
      obtain ⟨e, he⟩ := hdiv i
      have haz : (a : ℤ) ≠ 0 := by exact_mod_cast ha
      rw [hab, Nat.cast_mul, mul_assoc] at he
      exact ⟨e, mul_left_cancel₀ haz he⟩
    choose e he using hdb
    refine ⟨fun i => c i + e i * n', ?_⟩
    have hgy : g = ∑ i, (e i * n') • y i := by
      rw [← hd]
      exact Finset.sum_congr rfl fun i _ => by rw [he, mul_smul, mul_smul, hny,
        smul_comm]
    calc ∑ i, (c i + e i * n') • y i = ∑ i, c i • y i + ∑ i, (e i * n') • y i := by
          simp only [add_zsmul, Finset.sum_add_distrib]
      _ = h := by rw [← hgy, hg]; abel

/-- **Coprime step.** Torsion bases of `G[a]` and of `G[b]`, for coprime `a` and `b`, add up to
a torsion basis of `G[a * b]`. -/
theorem mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) {ya yb : ι → G}
    (ha : IsTorsionBasis a ya) (hb : IsTorsionBasis b yb) :
    IsTorsionBasis (a * b) (ya + yb) := by
  have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have hsplit : ∀ c : ι → ℤ, ∑ i, c i • (ya + yb) i = ∑ i, c i • ya i + ∑ i, c i • yb i :=
    fun c => by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  have hcongr : ∀ {m : ℕ} {z : ι → G}, IsTorsionBasis m z → ∀ c d : ι → ℤ,
      (∀ i, (m : ℤ) ∣ c i - d i) → ∑ i, c i • z i = ∑ i, d i • z i := by
    intro m z hz c d hcd
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp_rw [← sub_smul]
    exact (hz.sum_eq_zero_iff (fun i => c i - d i)).mpr hcd
  refine ⟨fun i => ?_, fun c hc i => ?_, fun h hh => ?_⟩
  · rw [Pi.add_apply, zsmul_add, Nat.cast_mul, mul_smul, mul_smul,
      smul_comm (a : ℤ) (b : ℤ) (ya i), ha.nsmul_eq_zero, hb.nsmul_eq_zero, smul_zero, smul_zero,
      add_zero]
  · rw [hsplit] at hc
    have hka : ∑ i, ((b : ℤ) * c i) • ya i = 0 := by
      simpa only [zsmul_add, hb.nsmul_sum_eq_zero, add_zero, zsmul_zero, Finset.smul_sum,
        smul_smul] using congrArg ((b : ℤ) • ·) hc
    have hkb : ∑ i, ((a : ℤ) * c i) • yb i = 0 := by
      simpa only [zsmul_add, ha.nsmul_sum_eq_zero, zero_add, zsmul_zero, Finset.smul_sum,
        smul_smul] using congrArg ((a : ℤ) • ·) hc
    rw [Nat.cast_mul]
    exact hco.mul_dvd (hco.dvd_of_dvd_mul_left (ha.dvd_of_sum_eq_zero _ hka i))
      (hco.symm.dvd_of_dvd_mul_left (hb.dvd_of_sum_eq_zero _ hkb i))
  · obtain ⟨u, v, huv⟩ := hco
    have hbh : (a : ℤ) • ((b : ℤ) • h) = 0 := by
      rwa [← natCast_mul_zsmul, mul_comm]
    have hah : (b : ℤ) • ((a : ℤ) • h) = 0 := by
      rwa [← natCast_mul_zsmul]
    obtain ⟨c, hc⟩ := ha.exists_sum_eq _ hbh
    obtain ⟨d, hd⟩ := hb.exists_sum_eq _ hah
    refine ⟨fun i => v * b * (v * c i) + u * a * (u * d i), ?_⟩
    rw [hsplit, hcongr ha _ (fun i => v * c i) (fun i => ⟨u * (u * d i) - u * v * c i, by
        linear_combination (v * c i) * huv⟩),
      hcongr hb _ (fun i => u * d i) (fun i => ⟨v * (v * c i) - u * v * d i, by
        linear_combination (u * d i) * huv⟩)]
    simp_rw [mul_zsmul]
    rw [← Finset.smul_sum, ← Finset.smul_sum, hc, hd, smul_smul, smul_smul, ← add_zsmul,
      show v * b + u * a = 1 by linarith, one_zsmul]

end IsTorsionBasis

/-- An identification of `G[n]` with `ι → ZMod n` gives a torsion basis of `G[n]`, namely the
preimages of the standard basis vectors. -/
theorem isTorsionBasis_of_addEquiv {n : ℕ} [DecidableEq ι]
    (e : AddSubgroup.torsionBy G n ≃+ (ι → ZMod n)) :
    IsTorsionBasis n (fun i => (e.symm (Pi.single i 1) : G)) := by
  have hsum : ∀ c : ι → ℤ, ∑ i, c i • (e.symm (Pi.single i 1) : G) =
      (e.symm (fun i => (c i : ZMod n)) : G) := fun c => by
    have : ∑ i, c i • Pi.single i (1 : ZMod n) = fun i => (c i : ZMod n) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [← this, map_sum, AddSubgroup.val_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, AddSubgroup.coe_zsmul]
  refine ⟨fun i => (Submodule.mem_torsionBy_iff _ _).mp (e.symm (Pi.single i 1)).2,
    fun c hc i => ?_, fun h hh => ?_⟩
  · rw [hsum] at hc
    have h0 : e.symm (fun i => (c i : ZMod n)) = 0 := Subtype.ext hc
    rw [AddEquiv.symm_apply_eq, map_zero] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun h0 i)
  · refine ⟨fun i => (e ⟨h, (Submodule.mem_torsionBy_iff _ _).mpr hh⟩ i).cast, ?_⟩
    rw [hsum]
    simp_rw [ZMod.intCast_zmod_cast]
    simp

/-- The `1`-torsion has the empty torsion basis, in the form of the zero family. -/
theorem isTorsionBasis_one : IsTorsionBasis 1 (0 : ι → G) :=
  ⟨fun _ => by simp, fun _ _ _ => by simp, fun h hh => ⟨0, by simpa using hh.symm⟩⟩

/-- **Torsion of a divisible group.** Let `G` be divisible by every prime factor of `n ≠ 0`, and
suppose that for every prime `ℓ ∣ n` the `ℓ`-torsion `G[ℓ]` is isomorphic to `ι → ZMod ℓ`.
Then `G[n]` has a torsion basis indexed by `ι`. -/
theorem exists_isTorsionBasis_of_divisible {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ x : G, ∃ y : G, (ℓ : ℤ) • y = x)
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n →
      Nonempty (AddSubgroup.torsionBy G ℓ ≃+ (ι → ZMod ℓ))) :
    ∃ y : ι → G, IsTorsionBasis n y := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨0, isTorsionBasis_one⟩
    set ℓ := n.minFac with hℓdef
    have hℓ : ℓ.Prime := Nat.minFac_prime hn1
    obtain ⟨n', hn'⟩ := Nat.minFac_dvd n
    have hn'0 : n' ≠ 0 := by rintro rfl; rw [mul_zero] at hn'; exact hn hn'
    have hlt : n' < n := by
      rw [hn']
      exact lt_mul_left (Nat.pos_of_ne_zero hn'0) hℓ.one_lt
    have hdvd' : ∀ ℓ', ℓ' ∣ n' → ℓ' ∣ n := fun ℓ' h => h.trans ⟨ℓ, by rw [hn', mul_comm]⟩
    obtain ⟨y', hy'⟩ := ih n' hlt hn'0 (fun ℓ' hp hd => hdiv ℓ' hp (hdvd' ℓ' hd))
      (fun ℓ' hp hd => hprime ℓ' hp (hdvd' ℓ' hd))
    by_cases hℓn' : ℓ ∣ n'
    · obtain ⟨b, hb⟩ := hℓn'
      choose y hy using fun i => hdiv ℓ hℓ (Nat.minFac_dvd n) (y' i)
      refine ⟨y, ?_⟩
      have := IsTorsionBasis.mul_of_dvd hb hℓ.ne_zero
        (by rintro rfl; rw [mul_zero] at hb; exact hn'0 hb) hy' hy
      rwa [← hn'] at this
    · obtain ⟨e⟩ := hprime ℓ hℓ (Nat.minFac_dvd n)
      refine ⟨(fun i => (e.symm (Pi.single i 1) : G)) + y', ?_⟩
      have := IsTorsionBasis.mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓn')
        (isTorsionBasis_of_addEquiv e) hy'
      rwa [← hn'] at this

omit [Fintype ι] in
/-- **Torsion of a divisible group, as a direct sum.** Under the hypotheses of
`AddCommGroup.exists_isTorsionBasis_of_divisible`, the `n`-torsion `G[n]` is isomorphic to
`ι → ZMod n`. -/
theorem nonempty_torsionBy_addEquiv_of_divisible [Finite ι] {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ x : G, ∃ y : G, (ℓ : ℤ) • y = x)
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n →
      Nonempty (AddSubgroup.torsionBy G ℓ ≃+ (ι → ZMod ℓ))) :
    Nonempty (AddSubgroup.torsionBy G n ≃+ (ι → ZMod n)) :=
  have := Fintype.ofFinite ι
  let ⟨_, hy⟩ := exists_isTorsionBasis_of_divisible hn hdiv hprime
  ⟨hy.addEquiv⟩

/-- **Elementary abelian groups.** If the `ℓ`-torsion of `G` is finite, for a prime `ℓ`, then it
is a direct sum of `f` copies of `ZMod ℓ`, where `ℓ ^ f` is its order. -/
theorem exists_torsionBy_prime_addEquiv {ℓ : ℕ} (hℓ : ℓ.Prime)
    [Finite (AddSubgroup.torsionBy G ℓ)] :
    ∃ f : ℕ, ℓ ^ f = Nat.card (AddSubgroup.torsionBy G ℓ) ∧
      Nonempty (AddSubgroup.torsionBy G ℓ ≃+ (Fin f → ZMod ℓ)) := by
  have := Fact.mk hℓ
  let _ : Module (ZMod ℓ) (AddSubgroup.torsionBy G ℓ) := AddSubgroup.torsionBy.zmodModule
  have : Module.Finite (ZMod ℓ) (AddSubgroup.torsionBy G ℓ) := Module.Finite.of_finite
  refine ⟨Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy G ℓ), ?_,
    ⟨(Module.finBasis (ZMod ℓ) _).equivFun.toAddEquiv⟩⟩
  have := Fintype.ofFinite (AddSubgroup.torsionBy G ℓ)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod ℓ), ZMod.card]

end AddCommGroup

end
