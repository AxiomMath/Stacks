module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.RingTheory.Polynomial.MonicLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `R⟨X⟩` is a Jacobson ring for Noetherian `R`

For a commutative Noetherian ring `R`, the localization `R⟨X⟩` of `R[X]` at the monic
polynomials is a Jacobson ring (Brewer–Heinzer, *R Noetherian implies R⟨X⟩ is a Hilbert ring*,
J. Algebra 67 (1980)).

## Main results

* `Ideal.exists_isPrime_lt_le_notMem_of_lt_lt`: in a Noetherian ring, given primes `q < m < M`
  and `z ∉ q`, some prime `Q` with `q < Q ≤ M` avoids `z`.
* `isJacobsonRing_of_isLocalization_of_forall_eq_pow_mul_one_add`: a localization `U⁻¹C` of a
  Noetherian ring `C` is Jacobson when, for some `y`, the submonoid `U` consists of the elements
  `yᵏ (1 + y c)`.
* `Polynomial.isJacobsonRing_of_isLocalization_monicSubmonoid`: `R⟨X⟩` is Jacobson for `R`
  Noetherian.

## Proof

Write `t = X⁻¹ ∈ R⟨X⟩`. Evaluating polynomials in a new variable `Y` at `t` identifies `R⟨X⟩`
with the localization of `R[Y]` at `U = {Yᵏ (1 + Y c)}`: the reversal `reflect N s` of a
polynomial `s` with constant term `1` is monic, and `s(t) = (reflect N s)(X) · tᴺ`.

For the localization `A = U⁻¹C`, let `P` be a prime of `A` and `f ∉ P`. Choose a prime `Q ⊇ P`
maximal with `f ∉ Q`. If `Q` were not maximal, its contraction `q` would lie strictly below the
contraction `m` of a maximal ideal of `A`. Then `m + (y)` is proper, since `1 + y c ∉ m`, so it
lies in a maximal ideal `M` of `C`, and `q < m < M`. Writing `f = a / u`, Krull's principal
ideal theorem gives a prime `q < Q' ≤ M` with `y a ∉ Q'`. Such a `Q'` misses `U`, because
`y ∉ Q'` and `1 + y c ∉ M`, so it gives a prime of `A` strictly above `Q` avoiding `f`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Ideal

variable {C : Type*} [CommRing C] [IsNoetherianRing C]

/-- In a Noetherian ring there is no chain of primes `q < J < P` with `P` minimal over
`q + (x)`: the image of `P` in `C ⧸ q` is minimal over a principal ideal, so has height at most
one by Krull's principal ideal theorem. -/
@[ega "0 16.3.2" "special case"]
theorem not_lt_lt_of_mem_minimalPrimes_sup_span_singleton {q J P : Ideal C} [q.IsPrime]
    [J.IsPrime] {x : C} (hP : P ∈ (q ⊔ span {x}).minimalPrimes) (hqJ : q < J) (hJP : J < P) :
    False := by
  have : P.IsPrime := hP.1.1
  let π := Quotient.mk q
  have hker : RingHom.ker π = q := mk_ker
  have hprime : ∀ I : Ideal C, I.IsPrime → q ≤ I → (I.map π).IsPrime := fun I hI hqI =>
    map_isPrime_of_surjective Quotient.mk_surjective (hker.le.trans hqI)
  have hstrict : ∀ I I' : Ideal C, q ≤ I → I < I' → I.map π < I'.map π := fun I I' hqI hII' =>
    (map_mono hII'.le).lt_of_ne fun h => hII'.ne <| by
      rw [← comap_map_mk hqI, h, comap_map_mk (hqI.trans hII'.le)]
  have := hprime q inferInstance le_rfl
  have := hprime J inferInstance hqJ.le
  have := hprime P inferInstance (hqJ.le.trans hJP.le)
  have h1 := height_add_one_le_of_lt_of_isPrime (hstrict q J le_rfl hqJ)
  have h2 := height_add_one_le_of_lt_of_isPrime (hstrict J P hqJ.le hJP)
  have h4 : (2 : ℕ∞) ≤ (P.map π).height := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (q.map π).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (J.map π).height + 1 := by gcongr
      _ ≤ _ := h2
  exact absurd (h4.trans (map_height_le_one_of_mem_minimalPrimes hP)) (by norm_num)

/-- In a Noetherian ring, given primes `q < m < M` and `z ∉ q`, there is a prime `Q` with
`q < Q ≤ M` and `z ∉ Q`. If not, every minimal prime of `q + (z)` would lie in no chain of
length two above `q`, prime avoidance would give `w ∈ M` outside all of them, and a minimal
prime of `q + (w)` below `M` would be one of them. -/
theorem exists_isPrime_lt_le_notMem_of_lt_lt {q m M : Ideal C} [q.IsPrime] [m.IsPrime]
    [M.IsPrime] (hqm : q < m) (hmM : m < M) {z : C} (hz : z ∉ q) :
    ∃ Q : Ideal C, Q.IsPrime ∧ q < Q ∧ Q ≤ M ∧ z ∉ Q := by
  by_contra! H
  have hzm : z ∈ m := H m inferInstance hqm hmM.le
  set F := (q ⊔ span {z}).minimalPrimes
  have hFfin : F.Finite := finite_minimalPrimes_of_isNoetherianRing C _
  have hsup : ∀ {J : Ideal C} {x : C}, q ≤ J → x ∈ J → q ⊔ span {x} ≤ J := fun hq hx =>
    sup_le hq (span_le.mpr (by simpa using hx))
  -- a minimal prime of `q + (x)` contains `x`, and lies strictly above `q` if `x ∉ q`
  have hmin : ∀ {x : C} {P : Ideal C}, x ∉ q → P ∈ (q ⊔ span {x}).minimalPrimes →
      x ∈ P ∧ q < P := fun hx hP => by
    have hxP := hP.1.2 (mem_sup_right (mem_span_singleton_self _))
    exact ⟨hxP, (le_sup_left.trans hP.1.2).lt_of_ne fun h => hx (h ▸ hxP)⟩
  -- `M` is not contained in any minimal prime of `q + (z)`.
  have hMF : ¬ ∃ P ∈ hFfin.toFinset, M ≤ P := by
    rintro ⟨P, hPF, hMP⟩
    rw [Set.Finite.mem_toFinset] at hPF
    have : P.IsPrime := hPF.1.1
    exact not_lt_lt_of_mem_minimalPrimes_sup_span_singleton hPF hqm (hmM.trans_le hMP)
  obtain ⟨w, hwM, hwF⟩ : ∃ w ∈ M, ∀ P ∈ F, w ∉ P := by
    have key : ((M : Set C) ⊆ ⋃ i ∈ (↑hFfin.toFinset : Set (Ideal C)), id i) ↔
        ∃ i ∈ hFfin.toFinset, M ≤ id i :=
      subset_union_prime ⊤ ⊤ fun P hP _ _ => by
        rw [Set.Finite.mem_toFinset] at hP
        exact hP.1.1
    obtain ⟨w, hwM, hw⟩ := Set.not_subset.mp (mt key.mp hMF)
    exact ⟨w, hwM, fun P hP hwP => hw (Set.mem_biUnion (x := P) (by simpa using hP) hwP)⟩
  obtain ⟨P₀, hP₀, -⟩ := exists_minimalPrimes_le (hsup hqm.le hzm)
  have hwq : w ∉ q := fun h => hwF P₀ hP₀ (hP₀.1.2 (le_sup_left (b := span {z}) h))
  obtain ⟨Q, hQ, hQM⟩ := exists_minimalPrimes_le (hsup (hqm.le.trans hmM.le) hwM)
  obtain ⟨hwQ, hqQ⟩ := hmin hwq hQ
  have : Q.IsPrime := hQ.1.1
  obtain ⟨P, hPF, hPQ⟩ := exists_minimalPrimes_le (J := Q) (hsup hqQ.le (H Q inferInstance hqQ hQM))
  have : P.IsPrime := hPF.1.1
  rcases hPQ.lt_or_eq with hlt | heq
  · exact not_lt_lt_of_mem_minimalPrimes_sup_span_singleton hQ (hmin hz hPF).2 hlt
  · exact hwF P hPF (heq ▸ hwQ)

end Ideal

section Localization

open Ideal

variable {C : Type*} [CommRing C] [IsNoetherianRing C] {A : Type*} [CommRing A] [Algebra C A]

/-- Let `U` be a submonoid of a Noetherian ring `C` all of whose elements have the form
`yᵏ (1 + y c)`. Given primes `q < m < M` with `M` maximal, `y ∈ M`, and `y, a ∉ q`, there is a
prime `Q'` with `q < Q' ≤ M` and `y a ∉ Q'`, disjoint from `U`. -/
theorem exists_isPrime_lt_le_disjoint_of_forall_eq_pow_mul_one_add (U : Submonoid C) {y : C}
    (hU : ∀ u ∈ U, ∃ (k : ℕ) (c : C), u = y ^ k * (1 + y * c)) {q m M : Ideal C} [q.IsPrime]
    [m.IsPrime] (hM : M.IsMaximal) (hqm : q < m) (hmM : m < M) (hyM : y ∈ M) (hyq : y ∉ q)
    {a : C} (haq : a ∉ q) :
    ∃ Q' : Ideal C, Q'.IsPrime ∧ q < Q' ∧ Q' ≤ M ∧ y * a ∉ Q' ∧ Disjoint (U : Set C) Q' := by
  obtain ⟨Q', hQ', hqQ', hQ'M, hyaQ'⟩ := exists_isPrime_lt_le_notMem_of_lt_lt hqm hmM
    (z := y * a) fun h => ((‹q.IsPrime›).mem_or_mem h).elim hyq haq
  refine ⟨Q', hQ', hqQ', hQ'M, hyaQ', Set.disjoint_left.mpr fun u hu huQ' => ?_⟩
  obtain ⟨k, c, rfl⟩ := hU u hu
  rcases hQ'.mem_or_mem huQ' with h | h
  · exact hyaQ' (Q'.mul_mem_right a (hQ'.mem_of_pow_mem k h))
  · exact hM.ne_top ((eq_top_iff_one _).mpr (by
      simpa using M.sub_mem (hQ'M h) (M.mul_mem_right c hyM)))

/-- Let `C` be Noetherian, `y ∈ C`, and `U` a submonoid of `C` containing `y` and every `1 + y c`,
all of whose elements have the form `yᵏ (1 + y c)`. Then the localization `U⁻¹C` is a Jacobson
ring. -/
theorem isJacobsonRing_of_isLocalization_of_forall_eq_pow_mul_one_add (U : Submonoid C)
    [IsLocalization U A] (y : C) (hy : y ∈ U) (h1 : ∀ c : C, 1 + y * c ∈ U)
    (hU : ∀ u ∈ U, ∃ (k : ℕ) (c : C), u = y ^ k * (1 + y * c)) : IsJacobsonRing A := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm (fun f hf => ?_) le_jacobson
  by_contra hfP
  -- a prime `Q ⊇ P` maximal with `f ∉ Q`
  obtain ⟨(Q : Ideal A), ⟨hQ, hPQ, hfQ⟩, hQmax⟩ := set_has_maximal_iff_noetherian.mpr
    (IsLocalization.isNoetherianRing U A inferInstance)
    {Q : Ideal A | Q.IsPrime ∧ P ≤ Q ∧ f ∉ Q} ⟨P, hP, le_rfl, hfP⟩
  have hQM : Q.IsMaximal := by
    by_contra hQM
    obtain ⟨MA, hMA, hQMA⟩ := exists_le_maximal Q hQ.ne_top
    have hQlt : Q < MA := hQMA.lt_of_ne fun h => hQM (h ▸ hMA)
    set q := Q.comap (algebraMap C A)
    set m := MA.comap (algebraMap C A)
    have hqm : q < m :=
      (comap_mono hQlt.le).lt_of_ne fun h => hQlt.ne <| by
        rw [← IsLocalization.map_under U A Q, ← IsLocalization.map_under U A MA]
        exact congrArg _ h
    have hmU : Disjoint (U : Set C) m := (IsLocalization.disjoint_under_iff U A MA).mpr hMA.ne_top
    have hmy : m ⊔ Ideal.span {y} ≠ ⊤ := by
      intro htop
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := 1))
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have : 1 + y * (-c) ∈ m := (show a = 1 + y * (-c) by linear_combination hab) ▸ ha
      exact Set.disjoint_left.mp hmU (h1 (-c)) this
    obtain ⟨M, hM, hmyM⟩ := exists_le_maximal _ hmy
    have hyM : y ∈ M := hmyM (mem_sup_right (mem_span_singleton_self y))
    have hym : y ∉ m := Set.disjoint_left.mp hmU hy
    have hmM : m < M := (le_sup_left.trans hmyM).lt_of_ne fun h => hym (h ▸ hyM)
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective U f
    have haq : a ∉ q := fun h => hfQ (IsLocalization.mk'_mem_iff.mpr h)
    have hqU : Disjoint (U : Set C) q := (IsLocalization.disjoint_under_iff U A Q).mpr hQ.ne_top
    have hyq : y ∉ q := Set.disjoint_left.mp hqU hy
    have : q.IsPrime := comap_isPrime _ _
    have : m.IsPrime := comap_isPrime _ _
    obtain ⟨Q', hQ', hqQ', hQ'M, hyaQ', hQ'U⟩ :=
      exists_isPrime_lt_le_disjoint_of_forall_eq_pow_mul_one_add U hU hM hqm hmM hyM hyq haq
    have hQA := IsLocalization.isPrime_of_isPrime_disjoint U A Q' hQ' hQ'U
    have hcomap := IsLocalization.under_map_of_isPrime_disjoint U A hQ' hQ'U
    have hQQA : Q ≤ Q'.map (algebraMap C A) := by
      rw [← IsLocalization.map_under U A Q]
      exact map_mono hqQ'.le
    have hfQA : IsLocalization.mk' A a u ∉ Q'.map (algebraMap C A) := fun h =>
      hyaQ' (Q'.mul_mem_left y (hcomap.le (IsLocalization.mk'_mem_iff.mp h)))
    exact hQmax _ ⟨hQA, hPQ.trans hQQA, hfQA⟩ (hQQA.lt_of_ne fun h =>
      hqQ'.ne ((congrArg (comap (algebraMap C A)) h).trans hcomap))
  exact hfQ (mem_sInf.mp hf ⟨hPQ, hQM⟩)

end Localization

namespace Polynomial

/-- If `ι X * t = 1`, evaluating the reversal `reflect N p` at `t` gives `ι p * t ^ N`. -/
theorem eval₂_reflect_of_mul_eq_one {R S : Type*} [CommRing R] [CommRing S] (ι : R[X] →+* S)
    {t : S} (ht : ι X * t = 1) {N : ℕ} {p : R[X]} (hp : p.natDegree ≤ N) :
    eval₂ (ι.comp C) t (reflect N p) = ι p * t ^ N := by
  let _ : Invertible t := ⟨ι X, ht, (mul_comm _ _).trans ht⟩
  have := eval₂_reflect_mul_pow (ι.comp C) t N (reflect N p)
    (natDegree_reflect_le.trans (max_le le_rfl hp))
  rw [reflect_reflect] at this
  conv_rhs => rw [← eval₂_C_X (p := p), hom_eval₂]
  exact this.symm

/-- If `ι X * t = 1`, evaluating `p` at `t` gives `ι (reflect p.natDegree p) * t ^ p.natDegree`. -/
theorem eval₂_eq_reflect_mul_pow_of_mul_eq_one {R S : Type*} [CommRing R] [CommRing S]
    (ι : R[X] →+* S) {t : S} (ht : ι X * t = 1) (p : R[X]) :
    eval₂ (ι.comp C) t p = ι (reflect p.natDegree p) * t ^ p.natDegree := by
  have h := eval₂_reflect_of_mul_eq_one ι ht (p := reflect p.natDegree p)
    (natDegree_reflect_le.trans (max_le le_rfl le_rfl))
  rwa [reflect_reflect] at h

/-- The reversal of a polynomial with constant coefficient `1` is monic. -/
theorem monic_reflect_natDegree_of_coeff_zero_eq_one {R : Type*} [Semiring R] {s : R[X]}
    (hs : s.coeff 0 = 1) : (reflect s.natDegree s).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one s.natDegree
    (natDegree_reflect_le.trans (max_le le_rfl le_rfl))
    (by rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, hs])

/-- The submonoid of `R[X]` of the polynomials `Xᵏ (1 + X c)`. -/
def powMulOneAddSubmonoid (R : Type*) [CommRing R] : Submonoid R[X] where
  carrier := {u | ∃ (k : ℕ) (c : R[X]), u = X ^ k * (1 + X * c)}
  mul_mem' := by
    rintro _ _ ⟨k, c, rfl⟩ ⟨l, d, rfl⟩
    exact ⟨k + l, c + d + X * c * d, by ring⟩
  one_mem' := ⟨0, 0, by simp⟩

/-- Membership in `powMulOneAddSubmonoid`. -/
theorem mem_powMulOneAddSubmonoid {R : Type*} [CommRing R] {u : R[X]} :
    u ∈ powMulOneAddSubmonoid R ↔ ∃ (k : ℕ) (c : R[X]), u = X ^ k * (1 + X * c) :=
  Iff.rfl

/-- For a commutative Noetherian ring `R`, the localization `R⟨X⟩` of `R[X]` at the monic
polynomials is a Jacobson ring (Brewer–Heinzer). -/
theorem isJacobsonRing_of_isLocalization_monicSubmonoid (R : Type*) [CommRing R]
    [IsNoetherianRing R] (D : Type*) [CommRing D] [Algebra R[X] D]
    [IsLocalization (monicSubmonoid R) D] : IsJacobsonRing D := by
  classical
  let ι : R[X] →+* D := algebraMap R[X] D
  have hx : IsUnit (ι X) := IsLocalization.map_units D (⟨X, monic_X⟩ : monicSubmonoid R)
  let t : D := ↑(hx.unit⁻¹)
  have ht : IsUnit t := Units.isUnit _
  have htX : ι X * t = 1 := by simp [t]
  let φ : R[X] →+* D := eval₂RingHom (ι.comp C) t
  have hφX : φ X = t := eval₂_X _ _
  have hrefl : ∀ (N : ℕ) (p : R[X]), p.natDegree ≤ N → φ (reflect N p) = ι p * t ^ N :=
    fun _ _ hp => eval₂_reflect_of_mul_eq_one ι htX hp
  have hrefl' : ∀ p : R[X], φ p = ι (reflect p.natDegree p) * t ^ p.natDegree :=
    eval₂_eq_reflect_mul_pow_of_mul_eq_one ι htX
  have hunit : ∀ s : R[X], s.coeff 0 = 1 → IsUnit (φ s) := fun s hs => by
    rw [hrefl' s]
    exact (IsLocalization.map_units D
      (⟨_, monic_reflect_natDegree_of_coeff_zero_eq_one hs⟩ : monicSubmonoid R)).mul (ht.pow _)
  have hinj : Function.Injective ι := IsLocalization.injective D (M := monicSubmonoid R)
    fun _ hp => (mem_monicSubmonoid.mp hp).mem_nonZeroDivisors
  let U := powMulOneAddSubmonoid R
  have hloc : @IsLocalization R[X] _ U D _ φ.toAlgebra := by
    refine (@isLocalization_iff R[X] _ U D _ φ.toAlgebra).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, hu⟩
      obtain ⟨k, c, rfl⟩ := mem_powMulOneAddSubmonoid.mp hu
      change IsUnit (φ (X ^ k * (1 + X * c)))
      rw [map_mul, map_pow, hφX]
      exact (ht.pow k).mul (hunit _ (by simp))
    · intro z
      obtain ⟨⟨g, ⟨h, hh⟩⟩, hz⟩ := IsLocalization.surj (monicSubmonoid R) z
      change z * ι h = ι g at hz
      obtain ⟨c, hc⟩ : X ∣ reflect h.natDegree h - 1 := by
        rw [X_dvd_iff, coeff_sub, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero,
          coeff_one_zero]
        exact sub_eq_zero.mpr (mem_monicSubmonoid.mp hh)
      refine ⟨⟨X ^ h.natDegree * reflect g.natDegree g,
        ⟨X ^ g.natDegree * reflect h.natDegree h, g.natDegree, c, by rw [← hc]; ring⟩⟩, ?_⟩
      change z * φ (X ^ g.natDegree * reflect h.natDegree h) =
        φ (X ^ h.natDegree * reflect g.natDegree g)
      rw [map_mul, map_mul, map_pow, map_pow, hφX, hrefl _ _ le_rfl, hrefl _ _ le_rfl]
      linear_combination (t ^ g.natDegree * t ^ h.natDegree) * hz
    · intro a b hab
      refine ⟨1, ?_⟩
      change φ a = φ b at hab
      have h := hrefl' (a - b)
      rw [map_sub, hab, sub_self, eq_comm, (ht.pow _).mul_left_eq_zero, ← map_zero ι] at h
      rw [sub_eq_zero.mp (reflect_eq_zero_iff.mp (hinj h))]
  exact @isJacobsonRing_of_isLocalization_of_forall_eq_pow_mul_one_add R[X] _ _ D _ φ.toAlgebra
    U hloc X (mem_powMulOneAddSubmonoid.mpr ⟨1, 0, by simp⟩)
    (fun c => mem_powMulOneAddSubmonoid.mpr ⟨0, c, by simp⟩) fun _ => mem_powMulOneAddSubmonoid.mp

/-- `R⟨X⟩` is a Jacobson ring when `R` is Noetherian. -/
instance isJacobsonRing_monicLocalization (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsJacobsonRing (MonicLocalization R) :=
  isJacobsonRing_of_isLocalization_monicSubmonoid R _

end Polynomial
