module

public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Torsion of an abelian group with the torsion counts of `(ℤ/n)^r`

Let `G` be an abelian group and `n ≥ 1`. If for every divisor `m` of `n` the `m`-torsion
subgroup `G[m]` has `m ^ r` elements, then `G[n] ≅ (ℤ/n)^r`. This is the group-theoretic step of
the proof of clause (7) of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP), there
applied to the rational points of an abelian variety with `r = 2 dim A`.

## Main results

* `Stacks.torsionBy_prime_pow_addEquiv_pi_zmod_of_card`: the prime-power case.
* `Stacks.nonempty_torsionBy_addEquiv_pi_zmod_of_card`: the general case.

## Implementation notes

`G[n]` is `Submodule.torsionBy ℤ G n`. For a prime power `ℓ ^ m`, the finite group `G[ℓ ^ m]` is
a product of cyclic groups `ℤ/ℓ ^ kᵢ` with `1 ≤ kᵢ ≤ m`; its `ℓ`-torsion has `ℓ` to the number of
factors elements, which forces `r` factors, and its order `ℓ ^ (∑ kᵢ) = ℓ ^ (r m)` forces every
`kᵢ = m`. The general case is the Chinese remainder theorem. The source argues instead by
induction on `m` with the short exact sequences `0 → G[ℓ] → G[ℓ^(m+1)] → G[ℓ^m] → 0`; the counts
of the hypothesis are what those sequences give.

The prime-power argument follows an auxiliary lemma for Stacks 0385, with the
divisibility hypothesis there replaced by the count of `G[ℓ ^ m]`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open scoped DirectSum Function

namespace Stacks

/-- The `p`-torsion of `ZMod (p ^ k)`, for `p` prime and `k ≥ 1`, has `p` elements. -/
private lemma nat_card_torsionBy_prime_pow_zmod (p k : ℕ) (hp : Nat.Prime p)
    (hk : 1 ≤ k) :
    Nat.card (Submodule.torsionBy ℤ (ZMod (p ^ k)) (p : ℤ)) = p := by
  classical
  let T := Submodule.torsionBy ℤ (ZMod (p ^ k)) (p : ℤ)
  have : IsAddCyclic T := AddSubgroup.isAddCyclic (Submodule.toAddSubgroup T)
  have hn : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ k) := ⟨hn⟩
  have : Finite T := Finite.of_injective (fun x : T => (x : ZMod (p ^ k)))
    Subtype.val_injective
  let : Fintype T := Fintype.ofFinite T
  have he : AddMonoid.exponent T = p := by
    apply Nat.dvd_antisymm
    · refine AddMonoid.exponent_dvd.mpr fun x => addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
      rw [← Nat.cast_smul_eq_nsmul ℤ p x]
      exact Submodule.smul_torsionBy (R := ℤ) (M := ZMod (p ^ k)) (a := (p : ℤ)) x
    · have horder : addOrderOf ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) = p := by
        rw [ZMod.addOrderOf_coe _ hn, Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le k 1))]
        apply Nat.div_eq_of_eq_mul_left (Nat.pow_pos hp.pos)
        rw [← pow_succ', Nat.sub_add_cancel hk]
      have hmem : ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) ∈ T := by
        rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul ℤ p]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mp horder.dvd
      let yT : T := ⟨_, hmem⟩
      exact horder.symm.dvd.trans ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (congrArg Subtype.val (addOrderOf_nsmul_eq_zero yT))).trans
        (AddMonoid.addOrder_dvd_exponent yT))
  change Nat.card T = p
  rw [← IsAddCyclic.exponent_eq_card, he]

/-- An additive isomorphism restricts to an isomorphism of `a`-torsion subgroups. -/
private def addEquiv_torsionBy {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (a : ℤ) :
    Submodule.torsionBy ℤ A a ≃+ Submodule.torsionBy ℤ B a where
  toFun x := ⟨e x, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul]
    simp⟩
  invFun x := ⟨e.symm x, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul]
    simp⟩
  left_inv x := Subtype.ext (e.left_inv x)
  right_inv x := Subtype.ext (e.right_inv x)
  map_add' x y := Subtype.ext (e.map_add x y)

/-- The `a`-torsion of a product is the product of the `a`-torsion subgroups. -/
private def torsionBy_pi_equiv {ι : Type*} (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] (a : ℤ) :
    Submodule.torsionBy ℤ (∀ i, A i) a ≃+
      (∀ i, Submodule.torsionBy ℤ (A i) a) where
  toFun x i := ⟨x.val i, (Submodule.mem_torsionBy_iff _ _).mpr
    (congrFun ((Submodule.mem_torsionBy_iff _ _).mp x.2) i)⟩
  invFun x := ⟨fun i => (x i).val, by
    rw [Submodule.mem_torsionBy_iff]
    funext i
    simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- For `a ∣ b`, the `a`-torsion of the `b`-torsion of `G` is the `a`-torsion of `G`. -/
private def torsionBy_torsionBy_equiv (G : Type*) [AddCommGroup G] (a b : ℤ) (hab : a ∣ b) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ G b) a ≃+ Submodule.torsionBy ℤ G a where
  toFun x := ⟨x.1.1, (Submodule.mem_torsionBy_iff _ _).mpr
    (congrArg Subtype.val (Submodule.smul_coe_torsionBy (R := ℤ) a x))⟩
  invFun x := ⟨⟨x.1, Submodule.torsionBy_le_torsionBy_of_dvd a b hab x.2⟩,
    Subtype.ext ((Submodule.mem_torsionBy_iff _ _).mp x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- If `a` kills `M ≃+ ∀ i, ZMod (n i)`, then every `n i` divides `a`. -/
lemma intCast_dvd_of_addEquiv_pi_zmod {ι M : Type*} [AddCommGroup M]
    {n : ι → ℕ} (e : M ≃+ ∀ i, ZMod (n i)) {a : ℤ} (hM : ∀ x : M, a • x = 0) (i : ι) :
    (n i : ℤ) ∣ a := by
  classical
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
  simpa using congrFun (congrArg e (hM (e.symm (Pi.single i 1)))) i

/-- For `ℓ` prime and `n i = ℓ ^ kᵢ` with every `kᵢ ≥ 1`, the product over `i` of the `ℓ`-torsion
subgroups of `ZMod (n i)` has `ℓ ^ card ι` elements. -/
lemma nat_card_pi_torsionBy_zmod_prime_pow {ι : Type*} [Fintype ι] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {n k : ι → ℕ} (hk : ∀ i, 1 ≤ k i) (hn : ∀ i, n i = ℓ ^ k i) :
    Nat.card (∀ i, Submodule.torsionBy ℤ (ZMod (n i)) (ℓ : ℤ)) = ℓ ^ Fintype.card ι := by
  rw [Nat.card_pi]
  calc
    ∏ i, Nat.card (Submodule.torsionBy ℤ (ZMod (n i)) (ℓ : ℤ)) = ∏ _i : ι, ℓ :=
      Finset.prod_congr rfl fun i _ => by
        rw [hn i]
        exact nat_card_torsionBy_prime_pow_zmod ℓ (k i) hℓ (hk i)
    _ = ℓ ^ Fintype.card ι := by simp

/-- **The `ℓ ^ m`-torsion of an abelian group is free over `ZMod (ℓ ^ m)` of rank `r` as soon as
the `ℓ`-torsion has `ℓ ^ r` elements and the `ℓ ^ m`-torsion has `ℓ ^ (r * m)` elements**, for
`ℓ` prime and `m ≥ 1`. -/
theorem torsionBy_prime_pow_addEquiv_pi_zmod_of_card
    (G : Type*) [AddCommGroup G]
    {ℓ r : ℕ} (hℓ : Nat.Prime ℓ) (m : ℕ) (hm : 1 ≤ m)
    (h₁ : Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) = ℓ ^ r)
    (hₘ : Nat.card (Submodule.torsionBy ℤ G ((ℓ : ℤ) ^ m)) = ℓ ^ (r * m)) :
    Nonempty (Submodule.torsionBy ℤ G ((ℓ : ℤ) ^ m) ≃+ (Fin r → ZMod (ℓ ^ m))) := by
  classical
  let Tₘ := Submodule.torsionBy ℤ G ((ℓ : ℤ) ^ m)
  have : Finite Tₘ := Nat.finite_of_card_ne_zero (hₘ.trans_ne (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨ι, _, n, hn, ⟨eD⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' Tₘ
  let eP : Tₘ ≃+ (∀ i : ι, ZMod (n i)) :=
    eD.trans (DirectSum.addEquivProd fun i => ZMod (n i))
  have : ∀ i : ι, NeZero (n i) := fun i => ⟨(zero_lt_one.trans (hn i)).ne'⟩
  choose k hkBound hnPow using fun i => (Nat.dvd_prime_pow hℓ).mp (by
    exact_mod_cast intCast_dvd_of_addEquiv_pi_zmod eP
      (fun x => Submodule.smul_torsionBy (a := (ℓ : ℤ) ^ m) x) i : n i ∣ ℓ ^ m)
  have hkPos (i : ι) : 1 ≤ k i :=
    Nat.one_le_iff_ne_zero.mpr fun h => by simpa [h, hnPow i] using hn i
  have hT₁idx : Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) = ℓ ^ Fintype.card ι :=
    calc
      Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) =
          Nat.card (Submodule.torsionBy ℤ Tₘ (ℓ : ℤ)) :=
        Nat.card_congr (torsionBy_torsionBy_equiv G ℓ _ (dvd_pow_self _ (by omega))).symm.toEquiv
      _ = Nat.card (Submodule.torsionBy ℤ (∀ i : ι, ZMod (n i)) (ℓ : ℤ)) :=
        Nat.card_congr (addEquiv_torsionBy eP (ℓ : ℤ)).toEquiv
      _ = Nat.card (∀ i : ι, Submodule.torsionBy ℤ (ZMod (n i)) (ℓ : ℤ)) :=
        Nat.card_congr (torsionBy_pi_equiv (fun i : ι => ZMod (n i)) (ℓ : ℤ)).toEquiv
      _ = ℓ ^ Fintype.card ι := nat_card_pi_torsionBy_zmod_prime_pow hℓ hkPos hnPow
  have hcardι : Fintype.card ι = r := Nat.pow_right_injective hℓ.two_le (hT₁idx.symm.trans h₁)
  have hTₘpowCard : Nat.card Tₘ = ℓ ^ (∑ i : ι, k i) :=
    calc
      Nat.card Tₘ = ∏ i : ι, n i := by
        rw [Nat.card_congr eP.toEquiv]
        simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
      _ = ∏ i : ι, ℓ ^ (k i) := Fintype.prod_congr _ _ hnPow
      _ = ℓ ^ (∑ i : ι, k i) := Finset.prod_pow_eq_pow_sum _ _ _
  have hsumEq : ∑ i : ι, k i = ∑ _i : ι, m := by
    simpa [hcardι, Nat.mul_comm] using (show ∑ i : ι, k i = r * m from
      Nat.pow_right_injective hℓ.two_le (hTₘpowCard.symm.trans hₘ))
  have hnFinal (i : ι) : n i = ℓ ^ m := by
    rw [hnPow i, (Finset.sum_eq_sum_iff_of_le fun j _ => hkBound j).mp hsumEq i
      (Finset.mem_univ i)]
  let eFactors : (∀ i : ι, ZMod (n i)) ≃+ (∀ i : ι, ZMod (ℓ ^ m)) :=
    AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (hnFinal i)).toAddEquiv
  exact ⟨eP.trans (eFactors.trans (RingEquiv.piCongrLeft (fun _ : Fin r => ZMod (ℓ ^ m))
    ((Fintype.equivFin ι).trans (finCongr hcardι))).toAddEquiv)⟩

/-- For pairwise coprime `q i`, the torsion by their product is the product of the torsion
subgroups. -/
private noncomputable def torsionBy_finset_prod_equiv_pi
    (G : Type*) [AddCommGroup G] {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → ℤ)
    (hq : (S : Set I).Pairwise (IsCoprime on q)) :
    Submodule.torsionBy ℤ G (∏ i ∈ S, q i) ≃+
      (∀ i : S, Submodule.torsionBy ℤ G (q i)) := by
  classical
  let T := Submodule.torsionBy ℤ G (∏ i ∈ S, q i)
  let A : S → Submodule ℤ T := fun i => Submodule.torsionBy ℤ T (q i.1)
  let e : (⨁ i, A i) ≃ₗ[ℤ] T := LinearEquiv.ofBijective (DirectSum.coeLinearMap A)
    (Submodule.torsionBy_isInternal (R := ℤ) (M := T) (S := S) (q := q) hq
      (Submodule.torsionBy_isTorsionBy (R := ℤ) (M := G) (∏ i ∈ S, q i)))
  exact (e.symm.toAddEquiv.trans (DirectSum.addEquivProd fun i : S => A i)).trans
    (AddEquiv.piCongrRight fun i : S => torsionBy_torsionBy_equiv G (q i.1) _
      (Finset.dvd_prod_of_mem q i.2))

/-- Under the counts of `nonempty_torsionBy_addEquiv_pi_zmod_of_card`, for a prime factor `p` of
`n` the torsion by `p ^ n.factorization p` is `(ℤ/p ^ n.factorization p)^r`. -/
theorem nonempty_torsionBy_ordProj_addEquiv_pi_zmod_of_card (G : Type*) [AddCommGroup G]
    {n : ℕ} (hn : n ≠ 0) (r : ℕ)
    (h : ∀ m : ℕ, m ∣ n → Nat.card (Submodule.torsionBy ℤ G (m : ℤ)) = m ^ r)
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    Nonempty (Submodule.torsionBy ℤ G ((p : ℤ) ^ n.factorization p) ≃+
      (Fin r → ZMod (p ^ n.factorization p))) := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  refine torsionBy_prime_pow_addEquiv_pi_zmod_of_card G hp' _
    (hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp))
    (h p (Nat.dvd_of_mem_primeFactors hp)) ?_
  have hd := h (p ^ n.factorization p) (Nat.ordProj_dvd n p)
  rw [← pow_mul, mul_comm] at hd
  simpa only [Nat.cast_pow] using hd

/-- The Chinese remainder theorem in each of `r` coordinates: the product over the prime factors
`p` of `n` of `(ℤ/p ^ n.factorization p)^r` is `(ℤ/n)^r`. -/
private noncomputable def piZModEquivPi (n : ℕ) (hn : n ≠ 0) (r : ℕ) :
    (∀ p : n.primeFactors, Fin r → ZMod (p.1 ^ n.factorization p.1)) ≃+ (Fin r → ZMod n) where
  toFun x j := (ZMod.equivPi n hn).symm fun p => x p j
  invFun x p j := ZMod.equivPi n hn (x j) p
  left_inv x := by
    funext p j
    simp
  right_inv x := by
    funext j
    simp
  map_add' x y := funext fun j =>
    map_add (ZMod.equivPi n hn).symm (fun p => x p j) fun p => y p j

/-- **An abelian group whose `m`-torsion has `m ^ r` elements for every divisor `m` of `n ≠ 0`
has `n`-torsion isomorphic to `(ℤ/n)^r`.** -/
theorem nonempty_torsionBy_addEquiv_pi_zmod_of_card (G : Type*) [AddCommGroup G] {n : ℕ}
    (hn : n ≠ 0) (r : ℕ)
    (h : ∀ m : ℕ, m ∣ n → Nat.card (Submodule.torsionBy ℤ G (m : ℤ)) = m ^ r) :
    Nonempty (Submodule.torsionBy ℤ G (n : ℤ) ≃+ (Fin r → ZMod n)) := by
  classical
  let q : ℕ → ℤ := fun p => (p : ℤ) ^ n.factorization p
  have hcop : (n.primeFactors : Set ℕ).Pairwise (IsCoprime on q) := by
    intro a ha b hb hab
    have hab' : (⟨a, ha⟩ : n.primeFactors) ≠ ⟨b, hb⟩ := fun hh => hab (congrArg Subtype.val hh)
    simpa [q] using
      (Nat.Coprime.cast ((Nat.pairwise_coprime_pow_primeFactors_factorization (n := n)) hab'))
  have hprod : (∏ p ∈ n.primeFactors, q p) = (n : ℤ) := by
    calc
      ∏ p ∈ n.primeFactors, q p = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℤ) := by
        simp only [q, ← Nat.cast_pow]
        rw [← Nat.cast_prod]
      _ = (n : ℤ) := congrArg (fun x : ℕ => (x : ℤ))
        (Nat.prod_primeFactors_pow_factorization hn).symm
  have eTorsionProd :
      Submodule.torsionBy ℤ G (n : ℤ) ≃+
        (∀ p : n.primeFactors, Submodule.torsionBy ℤ G (q p.1)) := by
    rw [← hprod]
    exact torsionBy_finset_prod_equiv_pi G n.primeFactors q hcop
  let eComponents :
      (∀ p : n.primeFactors, Submodule.torsionBy ℤ G (q p.1)) ≃+
        (∀ p : n.primeFactors, Fin r → ZMod (p.1 ^ n.factorization p.1)) :=
    AddEquiv.piCongrRight fun p =>
      Classical.choice (nonempty_torsionBy_ordProj_addEquiv_pi_zmod_of_card G hn r h p.2)
  exact ⟨eTorsionProd.trans (eComponents.trans (piZModEquivPi n hn r))⟩

end Stacks

end
