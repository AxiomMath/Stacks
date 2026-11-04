module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Torsion subgroups with the cardinalities of a free `ℤ/n`-module

Let `G` be an abelian group, `n ≥ 1` and `r ≥ 0`. If for every divisor `d` of `n` the
`d`-torsion subgroup `G[d]` is finite with `d ^ r` elements, then `G[n] ≅ (ℤ/nℤ)^r`.

This is the group-theoretic last step of [Stacks, Tag 03RP], part (7): there `G` is the group
of rational points of an abelian variety of dimension `g` over an algebraically closed field,
`r = 2g`, and the cardinalities come from the degree of the finite étale group scheme `A[d]`.

## Main results

* `AddCommGroup.nonempty_addEquiv_pi_zmod_prime_pow`: a finite abelian group killed by `p ^ k`
  with `p ^ (k r)` elements whose `p`-torsion has `p ^ r` elements is `(ℤ/p^k)^r`.
* `AddSubgroup.nonempty_torsionBy_addEquiv_pi_zmod`: the statement above.

## Implementation notes

The prime-power case is Nakayama's lemma over `ℤ/p^k`: since `x ↦ p x` has kernel `M[p]`, the
quotient `M / pM` has as many elements as `M[p]`, so it is an `r`-dimensional `𝔽_p`-vector
space; lifts of a basis generate `M` because `p` is nilpotent on `M`, and the resulting
surjection `(ℤ/p^k)^r → M` is a bijection by counting. The general case follows by the Chinese
remainder theorem, splitting `G[ab] = G[a] × G[b]` for coprime `a` and `b`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open scoped AddSubgroup

namespace AddCommGroup

variable {M : Type*} [AddCommGroup M]

/-- The image of multiplication by `p` has index `#M[p]`: `#(M / pM) = #M[p]`. -/
theorem natCard_quotient_range_nsmul_eq [Finite M] (p : ℕ) :
    Nat.card (M ⧸ (nsmulAddMonoidHom (α := M) p).range) =
      Nat.card (AddSubgroup.torsionBy M p) := by
  have hker : (nsmulAddMonoidHom (α := M) p).ker = AddSubgroup.torsionBy M p := by
    ext x
    simp
  have h1 := (nsmulAddMonoidHom (α := M) p).range.index_mul_card
  have h2 := (nsmulAddMonoidHom (α := M) p).ker.index_mul_card
  rw [AddSubgroup.index_ker, hker] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (by rw [← h2, mul_comm]))

/-- An `𝔽_p`-vector space with `p ^ r` elements is spanned by `r` vectors, with natural-number
coefficients. -/
theorem exists_spanning_fin_of_natCard_eq {p : ℕ} [hp : Fact p.Prime] (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] {r : ℕ} (hV : Nat.card V = p ^ r) :
    ∃ m : Fin r → V, ∀ x : V, ∃ c : Fin r → ℕ, x = ∑ i, c i • m i := by
  have : Fintype V := Fintype.ofFinite V
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) V = r := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hV] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let b := (Module.finBasis (ZMod p) V).reindex (finCongr hrank)
  refine ⟨b, fun x => ⟨fun i => (b.repr x i).val, ?_⟩⟩
  conv_lhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

/-- If `p ^ k` kills `M` and every element of `M` lies in `H` modulo `p • M`, then `H = M`. -/
theorem mem_of_forall_exists_sub_eq_nsmul {H : AddSubgroup M} {p k : ℕ}
    (hexp : ∀ x : M, (p ^ k) • x = 0)
    (hstep : ∀ x : M, ∃ n ∈ H, ∃ y : M, x - n = p • y) (x : M) : x ∈ H := by
  have hpow : ∀ j : ℕ, ∀ x : M, ∃ n ∈ H, ∃ y : M, x - n = (p ^ j) • y := by
    intro j
    induction j with
    | zero => exact fun x => ⟨0, zero_mem _, x, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨n, hn, y, hy⟩ := ih x
      obtain ⟨n', hn', y', hy'⟩ := hstep y
      refine ⟨n + (p ^ j) • n', add_mem hn (AddSubgroup.nsmul_mem _ hn' _), y', ?_⟩
      rw [pow_succ, mul_comm, mul_nsmul, ← hy', nsmul_sub, ← hy]
      abel
  obtain ⟨n, hn, y, hy⟩ := hpow k x
  rw [hexp, sub_eq_zero] at hy
  rwa [hy]

/-- **Prime-power case.** A finite abelian group `M` killed by `p ^ k`, with `p ^ (k r)`
elements and with `p ^ r` elements of order dividing `p`, is isomorphic to `(ℤ/p^k)^r`. -/
theorem nonempty_addEquiv_pi_zmod_prime_pow [Finite M] {p : ℕ} [hp : Fact p.Prime] {k r : ℕ}
    (hexp : ∀ x : M, (p ^ k) • x = 0) (hcard : Nat.card M = p ^ (k * r))
    (htors : Nat.card (AddSubgroup.torsionBy M p) = p ^ r) :
    Nonempty (M ≃+ (Fin r → ZMod (p ^ k))) := by
  classical
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let : Module (ZMod (p ^ k)) M := AddCommGroup.zmodModule hexp
  set pM := (nsmulAddMonoidHom (α := M) p).range with hpM
  have hQexp : ∀ q : M ⧸ pM, p • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨x, rfl⟩
  let : Module (ZMod p) (M ⧸ pM) := AddCommGroup.zmodModule hQexp
  have hQcard : Nat.card (M ⧸ pM) = p ^ r := by
    rw [natCard_quotient_range_nsmul_eq, htors]
  obtain ⟨b, hb⟩ := exists_spanning_fin_of_natCard_eq (M ⧸ pM) hQcard
  let m : Fin r → M := fun i => (QuotientAddGroup.mk_surjective (b i)).choose
  have hm : ∀ i, (m i : M ⧸ pM) = b i := fun i =>
    (QuotientAddGroup.mk_surjective (b i)).choose_spec
  let φ : (Fin r → ZMod (p ^ k)) →+ M :=
    (Fintype.linearCombination (ZMod (p ^ k)) m).toAddMonoidHom
  have hmφ : ∀ i, m i ∈ φ.range := fun i =>
    ⟨Pi.single i 1, by simp [φ, Fintype.linearCombination_apply_single]⟩
  have hstep : ∀ x : M, ∃ n ∈ φ.range, ∃ y : M, x - n = p • y := by
    intro x
    obtain ⟨c, hc⟩ := hb (x : M ⧸ pM)
    refine ⟨∑ i, c i • m i,
      AddSubgroup.sum_mem _ fun i _ => AddSubgroup.nsmul_mem _ (hmφ i) _, ?_⟩
    have hx : ((x - ∑ i, c i • m i : M) : M ⧸ pM) = 0 := by
      rw [QuotientAddGroup.mk_sub, sub_eq_zero, QuotientAddGroup.mk_sum, hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [QuotientAddGroup.mk_nsmul, hm]
    rw [QuotientAddGroup.eq_zero_iff] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hsurj : Function.Surjective φ := fun x =>
    AddMonoidHom.mem_range.1 (mem_of_forall_exists_sub_eq_nsmul hexp hstep x)
  have hbij : Function.Bijective φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin,
      ← pow_mul]
  exact ⟨(AddEquiv.ofBijective φ hbij).symm⟩

end AddCommGroup

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- An element `x` lies in the `n`-torsion subgroup of `G` if and only if `n • x = 0`. -/
theorem mem_torsionBy_iff_zsmul {n : ℤ} {x : G} : x ∈ torsionBy G n ↔ n • x = 0 :=
  Submodule.mem_torsionBy_iff ..

/-- For coprime `a` and `b`, the `ab`-torsion of `G` is the product of its `a`- and
`b`-torsion. -/
noncomputable def torsionByMulAddEquivProd {a b : ℕ} (hab : a.Coprime b) :
    torsionBy G (a * b : ℕ) ≃+ torsionBy G a × torsionBy G b :=
  let huv : IsCoprime (a : ℤ) b := Nat.isCoprime_iff_coprime.2 hab
  let u := huv.choose
  let v := huv.choose_spec.choose
  have huv' : u * a + v * b = 1 := huv.choose_spec.choose_spec
  have hab' : ∀ x : torsionBy G (a * b : ℕ), ((a : ℤ) * b) • (x : G) = 0 := fun x => by
    simp
  { toFun := fun x => (⟨(v * b) • (x : G), mem_torsionBy_iff_zsmul.2 (by
        rw [smul_smul, show (a : ℤ) * (v * b) = v * (a * b) by ring, mul_smul, hab' x,
          smul_zero])⟩,
      ⟨(u * a) • (x : G), mem_torsionBy_iff_zsmul.2 (by
        rw [smul_smul, show (b : ℤ) * (u * a) = u * (a * b) by ring, mul_smul, hab' x,
          smul_zero])⟩)
    invFun := fun y => ⟨(y.1 : G) + y.2, mem_torsionBy_iff_zsmul.2 (by
        have h1 := mem_torsionBy_iff_zsmul.1 y.1.2
        have h2 := mem_torsionBy_iff_zsmul.1 y.2.2
        push_cast
        rw [smul_add, mul_smul, smul_comm (a : ℤ) (b : ℤ) (y.1 : G), h1, smul_zero, zero_add,
          mul_smul, h2, smul_zero])⟩
    left_inv := fun x => by
      ext
      simp only
      rw [← add_smul, add_comm, huv', one_smul]
    right_inv := fun y => by
      have h1 := mem_torsionBy_iff_zsmul.1 y.1.2
      have h2 := mem_torsionBy_iff_zsmul.1 y.2.2
      have e1 : (v * b) • ((y.1 : G) + y.2) = y.1 := by
        rw [smul_add, mul_smul (v : ℤ) (b : ℤ) (y.2 : G), h2, smul_zero, add_zero,
          show v * (b : ℤ) = 1 - u * a by rw [← huv']; ring, sub_smul, one_smul,
          mul_smul, h1, smul_zero, sub_zero]
      have e2 : (u * a) • ((y.1 : G) + y.2) = y.2 := by
        rw [smul_add, mul_smul (u : ℤ) (a : ℤ) (y.1 : G), h1, smul_zero, zero_add,
          show u * (a : ℤ) = 1 - v * b by rw [← huv']; ring, sub_smul, one_smul,
          mul_smul, h2, smul_zero, sub_zero]
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    map_add' := fun x y => by
      ext <;> simp [smul_add] }

/-- For `d ∣ n`, the `d`-torsion of `G[n]` has as many elements as `G[d]`. -/
theorem natCard_torsionBy_torsionBy_of_dvd {d n : ℕ} (hdn : d ∣ n) :
    Nat.card (torsionBy (torsionBy G n) d) = Nat.card (torsionBy G d) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((x : torsionBy G n) : G), ?_⟩
      invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · exact mem_torsionBy_iff_zsmul.2 (congrArg Subtype.val (mem_torsionBy_iff_zsmul.1 x.2))
  · obtain ⟨e, rfl⟩ := hdn
    have := mem_torsionBy_iff_zsmul.1 y.2
    exact mem_torsionBy_iff_zsmul.2 (by push_cast; rw [mul_comm, mul_smul, this, smul_zero])
  · exact mem_torsionBy_iff_zsmul.2 (Subtype.ext (mem_torsionBy_iff_zsmul.1 y.2))

/-- **Stacks Tag 03RP (7), the group-theoretic step.** If `n ≥ 1` and for every divisor `d` of
`n` the subgroup `G[d]` has `d ^ r` elements, then `G[n] ≅ (ℤ/nℤ)^r`. -/
theorem nonempty_torsionBy_addEquiv_pi_zmod {r n : ℕ} (hn : 0 < n)
    (hcard : ∀ d, d ∣ n → Nat.card (torsionBy G d) = d ^ r) :
    Nonempty (torsionBy G n ≃+ (Fin r → ZMod n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one =>
    have : Subsingleton (torsionBy G (1 : ℕ)) := by
      refine ⟨fun x y => ?_⟩
      ext
      have hx := mem_torsionBy_iff_zsmul.1 x.2
      have hy := mem_torsionBy_iff_zsmul.1 y.2
      simp only [Nat.cast_one, one_smul] at hx hy
      rw [hx, hy]
    have : Unique (torsionBy G (1 : ℕ)) := uniqueOfSubsingleton 0
    exact ⟨AddEquiv.ofUnique⟩
  | prime_pow p k hp hk =>
    have : Fact p.Prime := ⟨hp⟩
    have hfin : Finite (torsionBy G (p ^ k : ℕ)) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hcard _ dvd_rfl]
      exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)
    refine AddCommGroup.nonempty_addEquiv_pi_zmod_prime_pow (p := p) (k := k) (r := r)
      (fun x => torsionBy.nsmul x) ?_ ?_
    · rw [hcard _ dvd_rfl, ← pow_mul]
    · rw [natCard_torsionBy_torsionBy_of_dvd (dvd_pow_self p hk.ne'),
        hcard _ (dvd_pow_self p hk.ne')]
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨ea⟩ := iha (by omega) fun d hd => hcard d (hd.mul_right b)
    obtain ⟨eb⟩ := ihb (by omega) fun d hd => hcard d (hd.mul_left a)
    exact ⟨(torsionByMulAddEquivProd hab).trans ((ea.prodCongr eb).trans
      (({ toEquiv := Equiv.arrowProdEquivProdArrow _ _ _, map_add' := fun _ _ => rfl } :
          (Fin r → ZMod a × ZMod b) ≃+ (Fin r → ZMod a) × (Fin r → ZMod b)).symm.trans
        (AddEquiv.piCongrRight fun _ => (ZMod.chineseRemainder hab).toAddEquiv.symm)))⟩

end AddSubgroup
