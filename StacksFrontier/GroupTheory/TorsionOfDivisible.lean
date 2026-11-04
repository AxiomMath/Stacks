module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# The `n`-torsion of an `n`-divisible abelian group

Let `G` be an abelian group which is `n`-divisible, and suppose that for every prime `p ∣ n` the
`p`-torsion `G[p]` has `p ^ N` elements. Then `G[n] ≅ (𝐙/n𝐙)^N`.

This is the group-theoretic last step of clause (7) of [Stacks, Tag 03RP]: there `G = A(k)` for an
abelian variety `A` of dimension `g` over an algebraically closed field `k`, `n` is invertible in
`k`, `A(k)` is divisible by clause (4), and `#A(k)[p] = p ^ {2g}` for the primes `p ∣ n` by
clause (5).

The proof builds a basis of `G[m]` over `𝐙/m𝐙` for every `m ∣ n`, by induction on `m`: write
`m = p m'` with `p` prime; if `p ∣ m'`, divide a basis of `G[m']` by `p`; if `p ∤ m'`, add a basis
of `G[p]` to a basis of `G[m']`. A basis is phrased over `𝐙` (`AddCommGroup.IsFinTorsionBasis`), so
that no module structure over `𝐙/m𝐙` has to be carried along the induction.

## Main results

* `AddCommGroup.IsFinTorsionBasis.addEquiv`: a basis of `G[m]` gives `(𝐙/m𝐙)^N ≃+ G[m]`.
* `AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible_of_card`: `G[n] ≃+ (𝐙/n𝐙)^N`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public noncomputable section

open Finset AddSubgroup

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {N : ℕ}

/-- `a` is a basis of the `m`-torsion `G[m]` over `𝐙/m𝐙`, phrased over `𝐙`: an integer
combination of the `a i` vanishes exactly when every coefficient is divisible by `m`, and every
element killed by `m` is an integer combination of the `a i`. -/
structure IsFinTorsionBasis (m : ℕ) (a : Fin N → G) : Prop where
  sum_eq_zero_iff : ∀ c : Fin N → ℤ, ∑ i, c i • a i = 0 ↔ ∀ i, (m : ℤ) ∣ c i
  exists_sum_eq : ∀ x : G, m • x = 0 → ∃ c : Fin N → ℤ, ∑ i, c i • a i = x

namespace IsFinTorsionBasis

variable {m : ℕ} {a : Fin N → G}

/-- Each basis element `a i` of `G[m]` is killed by every integer divisible by `m`. -/
theorem zsmul_eq_zero (h : IsFinTorsionBasis m a) (i : Fin N) {d : ℤ} (hd : (m : ℤ) ∣ d) :
    d • a i = 0 := by
  have := (h.sum_eq_zero_iff (Pi.single i d)).2 fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hd
    · simp [hj]
  simpa [Pi.single_apply, ite_smul] using this

/-- Each basis element `a i` of `G[m]` is killed by `m`. -/
theorem nsmul_eq_zero (h : IsFinTorsionBasis m a) (i : Fin N) : m • a i = 0 := by
  simpa [natCast_zsmul] using h.zsmul_eq_zero i (dvd_refl (m : ℤ))

/-- Every integer combination `∑ cᵢ aᵢ` of a basis of `G[m]` is killed by `m`. -/
theorem nsmul_sum (h : IsFinTorsionBasis m a) (c : Fin N → ℤ) : m • ∑ i, c i • a i = 0 := by
  rw [smul_sum]
  exact sum_eq_zero fun i _ => by rw [smul_comm, h.nsmul_eq_zero i, smul_zero]

/-- The basis `0` of `G[1] = 0`. -/
theorem one : IsFinTorsionBasis 1 (0 : Fin N → G) where
  sum_eq_zero_iff c := by simp
  exists_sum_eq x hx := ⟨0, by simpa using hx.symm⟩

/-- **Dividing a basis.** If `a` is a basis of `G[m]`, `p ∣ m`, and `p • a' i = a i`, then `a'`
is a basis of `G[p m]`. -/
theorem of_nsmul_eq {p : ℕ} {a' : Fin N → G} (h : IsFinTorsionBasis m a) (hm : m ≠ 0) (hpm : p ∣ m)
    (ha' : ∀ i, p • a' i = a i) : IsFinTorsionBasis (p * m) a' := by
  obtain ⟨m'', rfl⟩ := hpm
  have hm'' : (m'' : ℤ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hm
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hm
  have hz : ∀ i, (p : ℤ) • a' i = a i := fun i => by rw [natCast_zsmul, ha']
  refine ⟨fun c => ⟨fun hc => ?_, fun hc => ?_⟩, fun x hx => ?_⟩
  · have h1 : ∑ i, c i • a i = 0 := by
      simp_rw [← hz, smul_comm (c _) (p : ℤ), ← smul_sum, hc, smul_zero]
    choose d hd using fun i => (h.sum_eq_zero_iff c).1 h1 i
    have h2 : ∑ i, ((m'' : ℤ) * d i) • a i = 0 := by
      rw [← hc]
      refine sum_congr rfl fun i _ => ?_
      rw [hd i, ← hz, smul_smul]
      congr 1
      push_cast
      ring
    intro i
    obtain ⟨e, he⟩ := (h.sum_eq_zero_iff _).1 h2 i
    have hpd : (p : ℤ) ∣ d i := ⟨e, by
      apply mul_left_cancel₀ hm''
      push_cast at he
      linear_combination he⟩
    obtain ⟨f, hf⟩ := hpd
    exact ⟨f, by rw [hd i, hf]; push_cast; ring⟩
  · refine sum_eq_zero fun i _ => ?_
    obtain ⟨e, he⟩ := hc i
    rw [he, show ((p * (p * m'') : ℕ) : ℤ) * e = ((p * m'' : ℕ) : ℤ) * e * p by push_cast; ring,
      mul_smul, hz]
    exact h.zsmul_eq_zero i (dvd_mul_right _ _)
  · have hpx : (p * m'') • (p • x) = 0 := by
      rw [smul_smul, mul_comm, hx]
    obtain ⟨c, hc⟩ := h.exists_sum_eq _ hpx
    set y := x - ∑ i, c i • a' i with hy
    have hpy : p • y = 0 := by
      rw [hy, smul_sub, ← hc, smul_sum]
      simp_rw [← ha', smul_comm p (c _), sub_self]
    have hmy : (p * m'') • y = 0 := by
      rw [mul_comm, mul_smul, hpy, smul_zero]
    obtain ⟨e, he⟩ := h.exists_sum_eq y hmy
    refine ⟨fun i => c i + p * e i, ?_⟩
    have : ∀ i, (c i + p * e i) • a' i = c i • a' i + e i • a i := fun i => by
      rw [add_smul, mul_comm, mul_smul, hz]
    rw [sum_congr rfl fun i _ => this i, sum_add_distrib, he, hy, add_sub_cancel]

/-- **Adding a coprime basis.** If `a` is a basis of `G[m]`, `b` a basis of `G[p]`, and `p`, `m`
are coprime, then `a + b` is a basis of `G[p m]`. -/
theorem add_of_coprime {p : ℕ} {b : Fin N → G} (ha : IsFinTorsionBasis m a)
    (hb : IsFinTorsionBasis p b) (hpm : p.Coprime m) : IsFinTorsionBasis (p * m) (a + b) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hpm
  have key : ∀ s : G, p • s = 0 → m • s = 0 → s = 0 := fun s hp hm => by
    rw [← one_zsmul s, ← huv, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hp, hm,
      smul_zero, smul_zero, add_zero]
  refine ⟨fun c => ⟨fun hc => ?_, fun hc => ?_⟩, fun x hx => ?_⟩
  · simp only [Pi.add_apply, smul_add, sum_add_distrib] at hc
    have hs : ∑ i, c i • a i = 0 := key _
      (by rw [eq_neg_of_add_eq_zero_left hc, smul_neg, hb.nsmul_sum, neg_zero]) (ha.nsmul_sum c)
    rw [hs, zero_add] at hc
    intro i
    push_cast
    exact (Nat.isCoprime_iff_coprime.2 hpm).mul_dvd ((hb.sum_eq_zero_iff c).1 hc i)
      ((ha.sum_eq_zero_iff c).1 hs i)
  · refine sum_eq_zero fun i _ => ?_
    have hci : ((p : ℤ) * m) ∣ c i := by exact_mod_cast hc i
    rw [Pi.add_apply, smul_add, ha.zsmul_eq_zero i (dvd_trans (dvd_mul_left _ _) hci),
      hb.zsmul_eq_zero i (dvd_trans (dvd_mul_right _ _) hci), add_zero]
  · have hkill : ∀ (q : ℕ) (r : ℤ), (p : ℤ) * m ∣ q * r → q • (r • x) = 0 := by
      intro q r ⟨k, hk⟩
      rw [← natCast_zsmul, smul_smul, hk, mul_comm, mul_smul, ← Nat.cast_mul, natCast_zsmul, hx,
        smul_zero]
    have hy := hkill m (u * p) ⟨u, by ring⟩
    have hz := hkill p (v * m) ⟨v, by ring⟩
    obtain ⟨e, he⟩ := ha.exists_sum_eq _ hy
    obtain ⟨f, hf⟩ := hb.exists_sum_eq _ hz
    refine ⟨fun i => e i + (f i - e i) * v * m, ?_⟩
    have h1 : ∀ i, (e i + (f i - e i) * v * m) • a i = e i • a i := fun i => by
      rw [add_smul, ha.zsmul_eq_zero i (dvd_mul_left _ _), add_zero]
    have h2 : ∀ i, (e i + (f i - e i) * v * m) • b i = f i • b i := fun i => by
      rw [show e i + (f i - e i) * v * m = f i + (e i - f i) * u * p by
        linear_combination (f i - e i) * huv, add_smul, hb.zsmul_eq_zero i (dvd_mul_left _ _),
        add_zero]
    simp only [Pi.add_apply, smul_add, sum_add_distrib, h1, h2, he, hf]
    rw [← add_smul, huv, one_smul]

/-- The map `(𝐙/m𝐙)^N → G[m]`, `c ↦ ∑ cᵢ aᵢ`, attached to a basis. -/
def toTorsionBy (h : IsFinTorsionBasis m a) : (Fin N → ZMod m) →+ G[m] where
  toFun c := ⟨∑ i, ZMod.lift m ⟨zmultiplesHom G (a i), by
      simpa using h.zsmul_eq_zero i (dvd_refl (m : ℤ))⟩ (c i), by
    obtain ⟨d, rfl⟩ : ∃ d : Fin N → ℤ, (fun i => (d i : ZMod m)) = c :=
      ⟨fun i => (ZMod.intCast_surjective (c i)).choose,
        funext fun i => (ZMod.intCast_surjective (c i)).choose_spec⟩
    rw [torsionBy.nsmul_iff]
    simpa using h.nsmul_sum d⟩
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp [sum_add_distrib]

/-- On the reductions mod `m` of integers `dᵢ`, `toTorsionBy` is `∑ dᵢ aᵢ`. -/
theorem coe_toTorsionBy_intCast (h : IsFinTorsionBasis m a) (d : Fin N → ℤ) :
    (h.toTorsionBy (fun i => (d i : ZMod m)) : G) = ∑ i, d i • a i := by
  simp [toTorsionBy]

/-- **A basis of `G[m]` gives `(𝐙/m𝐙)^N ≃+ G[m]`.** -/
def addEquiv (h : IsFinTorsionBasis m a) : (Fin N → ZMod m) ≃+ G[m] :=
  AddEquiv.ofBijective h.toTorsionBy <| by
    have lift : ∀ c : Fin N → ZMod m, ∃ d : Fin N → ℤ, (fun i => (d i : ZMod m)) = c := fun c =>
      ⟨fun i => (ZMod.intCast_surjective (c i)).choose,
        funext fun i => (ZMod.intCast_surjective (c i)).choose_spec⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun x => ?_⟩
    · obtain ⟨d, rfl⟩ := lift c
      have := congrArg Subtype.val hc
      rw [coe_toTorsionBy_intCast, ZeroMemClass.coe_zero] at this
      funext i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ((h.sum_eq_zero_iff d).1 this i)
    · obtain ⟨d, hd⟩ := h.exists_sum_eq x (torsionBy.nsmul_iff.1 x.2)
      exact ⟨fun i => (d i : ZMod m), Subtype.ext (by rw [coe_toTorsionBy_intCast, hd])⟩

end IsFinTorsionBasis

/-- **A basis of `G[p]`**, for `p` prime and `#G[p] = p ^ N`. -/
theorem exists_isTorsionBasis_prime {p : ℕ} (hp : p.Prime) (hcard : Nat.card G[p] = p ^ N) :
    ∃ b : Fin N → G, IsFinTorsionBasis p b := by
  have := Fact.mk hp
  let : Module (ZMod p) G[p] := torsionBy.zmodModule
  have : Finite G[p] := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have : Fintype G[p] := Fintype.ofFinite _
  have : Module.Finite (ZMod p) G[p] := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) G[p] = N := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := G[p])
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let B := Module.finBasisOfFinrankEq (ZMod p) G[p] hrank
  have hsum : ∀ c : Fin N → ℤ, ∑ i, c i • (B i : G) = ((∑ i, (c i : ZMod p) • B i : G[p]) : G) :=
    fun c => by simp [Int.cast_smul_eq_zsmul]
  refine ⟨fun i => B i, fun c => ?_, fun x hx => ?_⟩
  · rw [hsum, ZeroMemClass.coe_eq_zero]
    refine ⟨fun hc i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      (Fintype.linearIndependent_iff.1 B.linearIndependent _ hc i), fun hc => ?_⟩
    simp [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hc _)]
  · let y : G[p] := ⟨x, torsionBy.nsmul_iff.2 hx⟩
    refine ⟨fun i => ((B.repr y i).val : ℤ), ?_⟩
    rw [hsum]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, B.sum_repr, y]

/-- **A basis of `G[m]` for every `m ∣ n`**, if `G` is `n`-divisible and `#G[p] = p ^ N` for the
primes `p ∣ n`. -/
theorem exists_isTorsionBasis_of_dvd {n : ℕ} (hdiv : ∀ x : G, ∃ y, n • y = x)
    (hcard : ∀ p, p.Prime → p ∣ n → Nat.card G[p] = p ^ N) :
    ∀ m, m ∣ n → m ≠ 0 → ∃ a : Fin N → G, IsFinTorsionBasis m a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hmn hm0
  rcases eq_or_ne m 1 with rfl | hm1
  · exact ⟨0, IsFinTorsionBasis.one⟩
  have hp := Nat.minFac_prime hm1
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  have hm'0 : m' ≠ 0 := by rintro rfl; simp only [mul_zero] at hm'; exact hm0 hm'
  have hlt : m' < m := by
    rw [hm']
    exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hp.one_lt
  obtain ⟨a, ha⟩ := ih m' hlt (dvd_trans (Dvd.intro_left _ hm'.symm) hmn) hm'0
  rw [hm']
  have hpn : m.minFac ∣ n := dvd_trans (Nat.minFac_dvd m) hmn
  by_cases hpm : m.minFac ∣ m'
  · have hdivp : ∀ x : G, ∃ y, m.minFac • y = x := fun x => by
      obtain ⟨k, hk⟩ := hpn
      obtain ⟨y, rfl⟩ := hdiv x
      exact ⟨k • y, by rw [smul_smul, ← hk]⟩
    choose a' ha' using fun i => hdivp (a i)
    exact ⟨a', ha.of_nsmul_eq hm'0 hpm ha'⟩
  · obtain ⟨b, hb⟩ := exists_isTorsionBasis_prime hp (hcard _ hp hpn)
    exact ⟨a + b, ha.add_of_coprime hb ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)⟩

/-- **The `n`-torsion of an `n`-divisible group.** If `G` is `n`-divisible and the `p`-torsion has
`p ^ N` elements for every prime `p ∣ n`, then `G[n] ≅ (𝐙/n𝐙)^N`.

This is the group theory in the last step of clause (7) of [Stacks, Tag 03RP]. -/
theorem nonempty_torsionBy_addEquiv_of_divisible_of_card {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ x : G, ∃ y, n • y = x)
    (hcard : ∀ p, p.Prime → p ∣ n → Nat.card G[p] = p ^ N) :
    Nonempty (G[n] ≃+ (Fin N → ZMod n)) :=
  let ⟨_, ha⟩ := exists_isTorsionBasis_of_dvd hdiv hcard n dvd_rfl hn
  ⟨ha.addEquiv.symm⟩

end AddCommGroup
