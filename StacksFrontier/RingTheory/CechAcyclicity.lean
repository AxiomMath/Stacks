module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Basic

/-!
# Acyclicity of the Čech complex of localizations

Let `A` be a commutative ring, `M` an `A`-module and `g : Fin n → A` a family generating the
unit ideal. The (unordered) Čech complex of the standard covering of `Spec A` determined by
`g`, with coefficients in `M`, has `p`-th term the product of the localizations
`M_{g (x 0) ⋯ g (x p)}` over all tuples `x : Fin (p + 1) → Fin n`, with the usual alternating
sum of restriction maps as differential. This file proves that this complex is exact in every
positive degree, which is the purely algebraic core of the vanishing of higher Čech cohomology
of a quasi-coherent module on an affine scheme.

## Main definitions

* `AwayLoc M a` is `M` localized at the powers of `a`.
* `resAway M h` is the restriction map `AwayLoc M a →ₗ[A] AwayLoc M b` attached to `h : a ∣ b`.
* `tupleProd g x` is the product `∏ k, g (x k)` of the entries of a tuple.
* `CechTerm M g f p` is the `p`-th term of the Čech complex twisted by `f`, namely the product
  of `AwayLoc M (f * tupleProd g x)` over all `x : Fin (p + 1) → Fin n`.
* `cechD M g f p` is the alternating sum differential.
* `localPrimitive M g f i p s` is the primitive of `s` obtained, after inverting `g i`, by
  prepending the index `i` to a tuple.

## Main results

* `cechD_comp_cechD`: the differentials compose to zero, so `CechTerm` really is a complex.
* `cech_exact`: if `g` generates the unit ideal then every cocycle in positive degree is a
  coboundary, i.e. the complex is exact (its cohomology vanishes) in all positive degrees.
  Taking the twist `f = 1` gives the Čech complex of `M` itself.

## Implementation notes

The complex is indexed by *all* tuples `Fin (p + 1) → Fin n`, not only the strictly increasing
ones, so it is the unordered Čech complex of the covering and is nonzero in arbitrarily large
degrees. The repository already contains the extended *alternating* Čech complex, indexed by
subsets, together with its null homotopy when one of the elements is invertible
(`Cech.cechComplex_nullHomotopic`) and the cohomology computation of Tag 0G6K; the present
file is independent of that development and no comparison between the two complexes is
made here.

Everything is stated for the complex twisted by an auxiliary element `f`, whose `p`-th term
localizes `M` at `f * g (x 0) ⋯ g (x p)`. This costs nothing — it is the Čech complex of the
localization `M_f` over `A_f` with respect to the images of the `g i`, and the untwisted
complex is the case `f = 1` — and it is what makes the induction step expressible without
transporting along equalities of rings: the local primitive of a cocycle for the twist `f`
lives in the complex twisted by `f * g i`.

The proof is the standard local-global argument in explicit form. If `s` is a cocycle in degree
`p + 1`, then for each index `i` the tuple-prepending map produces a primitive of `s` in the
complex twisted by `f * g i`; this is nothing but the cocycle identity for `s` evaluated at
tuples beginning with `i`. Clearing denominators (`exists_resAway_eq_smul` and
`exists_pow_smul_eq_zero`, which say that the `f * g i`-twisted term is the localization of the
`f`-twisted term at `g i`) turns that into a primitive of `g i ^ k • s` inside the `f`-twisted
complex, and a partition of unity `1 = ∑ c i * g i ^ k` assembles these into a primitive of `s`.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public section

universe u v

namespace Stacks.RingTheory.CechAcyclicity

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] {n : ℕ}

/-! ### Localization away from an element -/

/-- `AwayLoc M a` is the module `M` localized at the powers of `a`. -/
abbrev AwayLoc (M : Type v) [AddCommGroup M] [Module A M] (a : A) : Type (max u v) :=
  LocalizedModule (Submonoid.powers a) M

/-- A divisor of an element acting invertibly on a module acts invertibly itself. -/
theorem isUnit_algebraMap_of_dvd {N : Type*} [AddCommGroup N] [Module A N] {a b : A}
    (hab : a ∣ b) (hb : IsUnit (algebraMap A (Module.End A N) b)) :
    IsUnit (algebraMap A (Module.End A N) a) := by
  obtain ⟨c, rfl⟩ := hab
  obtain ⟨w, hw⟩ := hb
  refine ⟨⟨algebraMap A (Module.End A N) a,
    algebraMap A (Module.End A N) c * (↑w⁻¹ : Module.End A N), ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, ← map_mul, ← hw]
    exact w.mul_inv
  · rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm c a, ← hw]
    exact w.mul_inv

/-- Powers of a divisor of `b` act invertibly on `M` localized at the powers of `b`. -/
theorem isUnit_pow_awayLoc {a b : A} (h : a ∣ b) (k : ℕ) :
    IsUnit (algebraMap A (Module.End A (AwayLoc M b)) (a ^ k)) :=
  isUnit_algebraMap_of_dvd (pow_dvd_pow_of_dvd h k)
    (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers b) M)
      (⟨b ^ k, k, rfl⟩ : Submonoid.powers b))

/-- Every power of a divisor of `b` acts invertibly on `M` localized at the powers of `b`. -/
theorem isUnit_powers_awayLoc {a b : A} (h : a ∣ b) (s : Submonoid.powers a) :
    IsUnit (algebraMap A (Module.End A (AwayLoc M b)) (s : A)) := by
  obtain ⟨k, hk⟩ := s.2
  rw [← hk]
  exact isUnit_pow_awayLoc h k

/-- Multiplication by a power of a divisor of `b` is injective on `M` localized at `b`. -/
theorem smul_pow_injective_of_dvd {a b : A} (h : a ∣ b) (k : ℕ) {x y : AwayLoc M b}
    (hxy : a ^ k • x = a ^ k • y) : x = y :=
  ((Module.End.isUnit_iff _).1 (isUnit_pow_awayLoc (M := M) h k)).1 hxy

/-- The restriction map between localizations of `M` attached to a divisibility `a ∣ b`. -/
noncomputable def resAway (M : Type v) [AddCommGroup M] [Module A M] {a b : A} (h : a ∣ b) :
    AwayLoc M a →ₗ[A] AwayLoc M b :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M) (isUnit_powers_awayLoc h)

/-- The restriction map sends the class of `m / 1` to the class of `m / 1`. -/
@[simp]
theorem resAway_mk_one {a b : A} (h : a ∣ b) (m : M) :
    resAway M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  simp [resAway]

/-- Restriction along `a ∣ b` followed by restriction along `b ∣ c` is restriction along
`a ∣ c`. -/
theorem resAway_comp {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) :
    (resAway M h₂).comp (resAway M h₁) = resAway M (h₁.trans h₂) := by
  refine (LocalizedModule.lift_unique _ _ (isUnit_powers_awayLoc (h₁.trans h₂)) _ ?_).symm
  ext m
  simp

/-- Elementwise form of `resAway_comp`: restricting twice is restricting once. -/
@[simp]
theorem resAway_resAway {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) (z : AwayLoc M a) :
    resAway M h₂ (resAway M h₁ z) = resAway M (h₁.trans h₂) z :=
  DFunLike.congr_fun (resAway_comp (M := M) h₁ h₂) z

/-- If `b = a * c`, the restriction map sends `m / a ^ k` to `c ^ k • m / b ^ k`. -/
theorem resAway_mk {a b c : A} (hb : b = a * c) (h : a ∣ b) (m : M) (k : ℕ) :
    resAway M h (LocalizedModule.mk m ⟨a ^ k, k, rfl⟩) =
      LocalizedModule.mk (c ^ k • m) (⟨b ^ k, k, rfl⟩ : Submonoid.powers b) := by
  refine smul_pow_injective_of_dvd h k ?_
  rw [← map_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
  rw [show (a ^ k • m : M) = (⟨a ^ k, k, rfl⟩ : Submonoid.powers a) • m from rfl,
    LocalizedModule.mk_cancel, resAway_mk_one]
  rw [show (a ^ k • c ^ k • m : M) = (⟨b ^ k, k, rfl⟩ : Submonoid.powers b) • m by
    simp [Submonoid.smul_def, hb, mul_pow, smul_smul], LocalizedModule.mk_cancel]

/-- A fraction `m / s` in `M` localized at the powers of `a` vanishes if and only if some power
of `a` kills `m`. -/
theorem mk_eq_zero_iff {a : A} (m : M) (s : Submonoid.powers a) :
    LocalizedModule.mk m s = 0 ↔ ∃ t : Submonoid.powers a, (t : A) • m = 0 := by
  rw [show (0 : AwayLoc M a) = LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk 1).symm,
    LocalizedModule.mk_eq]
  simp [Submonoid.smul_def]

/-- Localizing `M` at `a * c` is localizing `M_a` at `c`: every element of `M_{a c}` becomes a
restriction after multiplying by a power of `c`. -/
theorem exists_resAway_eq_smul {a b c : A} (hb : b = a * c) (h : a ∣ b) (z : AwayLoc M b) :
    ∃ (k : ℕ) (u : AwayLoc M a), resAway M h u = c ^ k • z := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨j, hj⟩ := s.2
    refine ⟨j, LocalizedModule.mk m ⟨a ^ j, j, rfl⟩, ?_⟩
    rw [resAway_mk hb h, LocalizedModule.smul'_mk]
    congr 1
    exact Subtype.ext hj

/-- Localizing `M` at `a * c` is localizing `M_a` at `c`: the kernel of the restriction map
consists of elements killed by a power of `c`. -/
theorem exists_pow_smul_eq_zero {a b c : A} (hb : b = a * c) (h : a ∣ b) (u : AwayLoc M a)
    (hu : resAway M h u = 0) : ∃ l : ℕ, c ^ l • u = 0 := by
  induction u using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨j, hj⟩ := s.2
    subst hb
    rw [show s = (⟨a ^ j, j, rfl⟩ : Submonoid.powers a) from Subtype.ext hj.symm] at hu ⊢
    rw [resAway_mk rfl h, mk_eq_zero_iff] at hu
    obtain ⟨t, ht⟩ := hu
    obtain ⟨r, hr⟩ := t.2
    refine ⟨r + j, ?_⟩
    rw [LocalizedModule.smul'_mk, mk_eq_zero_iff]
    refine ⟨⟨a ^ r, r, rfl⟩, ?_⟩
    have hz : ((a * c) ^ r : A) • c ^ j • m = 0 := by rw [← hr] at ht; exact ht
    simp only [mul_pow, pow_add, smul_smul] at hz ⊢
    rw [← hz]
    ring_nf

/-! ### Simplicial identities and the cancelling involution -/

/-- The first simplicial identity, at the level of `Fin.succAbove`: omitting `i` and then
`j + 1` is the same as omitting `j` and then `i`, for `i ≤ j`. -/
theorem succAbove_succ_succAbove {m : ℕ} {i j : Fin (m + 2)} (h : i ≤ j) (l : Fin (m + 1)) :
    j.succ.succAbove (i.succAbove l) = i.castSucc.succAbove (j.succAbove l) := by
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases l with ⟨l, _⟩
  simp only [Fin.succAbove, Fin.lt_def, Fin.le_def] at *
  split_ifs <;> simp_all <;> omega

/-- The first simplicial identity in the form used for the Čech differential: the pair
`(J, K)` and the pair `(J.succAbove K, K.predAbove J)` describe the same pair of omitted
indices. -/
theorem succAbove_swap {m : ℕ} (J : Fin (m + 2)) (K : Fin (m + 1)) (l : Fin m) :
    J.succAbove (K.succAbove l) = (J.succAbove K).succAbove ((K.predAbove J).succAbove l) := by
  cases m with
  | zero => exact l.elim0
  | succ N =>
    rcases Nat.lt_or_ge (K : ℕ) (J : ℕ) with h | h
    · have hcs : K.castSucc < J := h
      have hne : J ≠ 0 := Fin.ne_zero_of_lt hcs
      rw [Fin.succAbove_of_castSucc_lt _ _ hcs, Fin.predAbove_of_castSucc_lt _ _ hcs]
      have hle : K ≤ J.pred hne := by
        rw [Fin.le_def, Fin.val_pred]
        omega
      have key := succAbove_succ_succAbove hle l
      rwa [Fin.succ_pred] at key
    · have hK := K.isLt
      have hcs : J ≤ K.castSucc := h
      have hne : J ≠ Fin.last (N + 2) :=
        Fin.ne_of_val_ne (by rw [Fin.val_last]; omega)
      rw [Fin.succAbove_of_le_castSucc _ _ hcs, Fin.predAbove_of_le_castSucc _ _ hcs]
      have hle : J.castPred hne ≤ K := by
        rw [Fin.le_def, Fin.coe_castPred]
        omega
      have key := succAbove_succ_succAbove hle l
      rw [Fin.castSucc_castPred] at key
      exact key.symm

/-- The map `(J, K) ↦ (J.succAbove K, K.predAbove J)` is an involution: first component. -/
theorem succAbove_predAbove_self {m : ℕ} (J : Fin (m + 2)) (K : Fin (m + 1)) :
    (J.succAbove K).succAbove (K.predAbove J) = J := by
  rcases Nat.lt_or_ge (K : ℕ) (J : ℕ) with h | h
  · have hcs : K.castSucc < J := h
    have hne : J ≠ 0 := Fin.ne_zero_of_lt hcs
    rw [Fin.succAbove_of_castSucc_lt _ _ hcs, Fin.predAbove_of_castSucc_lt _ _ hcs,
      Fin.succAbove_of_le_castSucc, Fin.succ_pred]
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc, Fin.val_pred]
    omega
  · have hK := K.isLt
    have hcs : J ≤ K.castSucc := h
    have hne : J ≠ Fin.last (m + 1) := Fin.ne_of_val_ne (by rw [Fin.val_last]; omega)
    rw [Fin.succAbove_of_le_castSucc _ _ hcs, Fin.predAbove_of_le_castSucc _ _ hcs,
      Fin.succAbove_of_castSucc_lt, Fin.castSucc_castPred]
    rw [Fin.lt_def, Fin.val_succ, Fin.castSucc_castPred]
    omega

/-- The map `(J, K) ↦ (J.succAbove K, K.predAbove J)` is an involution: second component. -/
theorem predAbove_succAbove_self {m : ℕ} (J : Fin (m + 2)) (K : Fin (m + 1)) :
    (K.predAbove J).predAbove (J.succAbove K) = K := by
  rcases Nat.lt_or_ge (K : ℕ) (J : ℕ) with h | h
  · have hcs : K.castSucc < J := h
    have hne : J ≠ 0 := Fin.ne_zero_of_lt hcs
    rw [Fin.succAbove_of_castSucc_lt _ _ hcs, Fin.predAbove_of_castSucc_lt _ _ hcs,
      Fin.predAbove_of_le_castSucc, Fin.castPred_castSucc]
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc, Fin.val_pred]
    omega
  · have hK := K.isLt
    have hcs : J ≤ K.castSucc := h
    have hne : J ≠ Fin.last (m + 1) := Fin.ne_of_val_ne (by rw [Fin.val_last]; omega)
    rw [Fin.succAbove_of_le_castSucc _ _ hcs, Fin.predAbove_of_le_castSucc _ _ hcs,
      Fin.predAbove_of_castSucc_lt, Fin.pred_succ]
    rw [Fin.lt_def, Fin.val_succ, Fin.castSucc_castPred]
    omega

/-- The involution `(J, K) ↦ (J.succAbove K, K.predAbove J)` reverses the Čech sign. -/
theorem sign_swap {m : ℕ} (J : Fin (m + 2)) (K : Fin (m + 1)) :
    (-1 : A) ^ (((J.succAbove K : Fin (m + 2)) : ℕ) + ((K.predAbove J : Fin (m + 1)) : ℕ)) =
      -(-1 : A) ^ ((J : ℕ) + (K : ℕ)) := by
  rcases Nat.lt_or_ge (K : ℕ) (J : ℕ) with h | h
  · have hcs : K.castSucc < J := h
    rw [Fin.succAbove_of_castSucc_lt _ _ hcs, Fin.predAbove_of_castSucc_lt _ _ hcs,
      Fin.val_castSucc, Fin.val_pred,
      show (J : ℕ) + (K : ℕ) = ((K : ℕ) + ((J : ℕ) - 1)) + 1 by omega, pow_succ]
    ring
  · have hcs : J ≤ K.castSucc := h
    rw [Fin.succAbove_of_le_castSucc _ _ hcs, Fin.predAbove_of_le_castSucc _ _ hcs,
      Fin.val_succ, Fin.coe_castPred,
      show (K : ℕ) + 1 + (J : ℕ) = ((J : ℕ) + (K : ℕ)) + 1 by omega, pow_succ]
    ring

/-- A double sum over `Fin (m + 2) × Fin (m + 1)` whose terms cancel in pairs under
`(J, K) ↦ (J.succAbove K, K.predAbove J)` vanishes. -/
theorem sum_sum_eq_zero_of_swap {m : ℕ} {N : Type*} [AddCommGroup N]
    (F : Fin (m + 2) → Fin (m + 1) → N)
    (h : ∀ (J : Fin (m + 2)) (K : Fin (m + 1)), F J K + F (J.succAbove K) (K.predAbove J) = 0) :
    ∑ J, ∑ K, F J K = 0 := by
  classical
  rw [← Finset.sum_product']
  exact Finset.sum_ninvolution (fun q => (q.1.succAbove q.2, q.2.predAbove q.1))
    (fun q => h q.1 q.2)
    (fun q _ hc => Fin.succAbove_ne q.1 q.2 (congrArg Prod.fst hc))
    (fun _ => Finset.mem_univ _)
    (fun q => Prod.ext (succAbove_predAbove_self q.1 q.2) (predAbove_succAbove_self q.1 q.2))

/-! ### The Čech complex of a family of elements -/

/-- The product of the entries of a tuple of indices under `g`. -/
def tupleProd (g : Fin n → A) {m : ℕ} (x : Fin m → Fin n) : A := ∏ k, g (x k)

/-- The product over a tuple splits off the entry at any position `j`. -/
theorem tupleProd_succAbove (g : Fin n → A) {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin (m + 1)) :
    tupleProd g x = g (x j) * tupleProd g fun i => x (j.succAbove i) :=
  Fin.prod_univ_succAbove _ j

/-- The product over a tuple with `i` prepended is `g i` times the product over the rest. -/
theorem tupleProd_cons (g : Fin n → A) {m : ℕ} (i : Fin n) (y : Fin m → Fin n) :
    tupleProd g (Fin.cons i y) = g i * tupleProd g y := by
  simp [tupleProd, Fin.prod_univ_succ]

/-- The divisibility underlying the `j`-th face map of the Čech complex. -/
theorem dvd_face (g : Fin n → A) (f : A) {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin (m + 1)) :
    f * tupleProd g (fun i => x (j.succAbove i)) ∣ f * tupleProd g x := by
  rw [tupleProd_succAbove g x j]
  exact ⟨g (x j), by ring⟩

/-- The divisibility underlying the comparison of the complexes twisted by `f` and by `f * c`. -/
theorem dvd_twist (g : Fin n → A) (f c : A) {m : ℕ} (x : Fin m → Fin n) :
    f * tupleProd g x ∣ f * c * tupleProd g x :=
  ⟨c, by ring⟩

/-- The divisibility (in fact an equality) underlying the tuple-prepending map. -/
theorem dvd_cons (g : Fin n → A) (f : A) {m : ℕ} (i : Fin n) (y : Fin m → Fin n) :
    f * tupleProd g (Fin.cons i y) ∣ f * g i * tupleProd g y :=
  dvd_of_eq (by rw [tupleProd_cons, mul_assoc])

/-- The `p`-th term of the Čech complex of `g` with coefficients in `M`, twisted by `f`: the
product over all tuples `x : Fin (p + 1) → Fin n` of `M` localized at `f * g (x 0) ⋯ g (x p)`.
The untwisted Čech complex is the case `f = 1`. -/
abbrev CechTerm (M : Type v) [AddCommGroup M] [Module A M] (g : Fin n → A) (f : A) (p : ℕ) :
    Type (max u v) :=
  ∀ x : Fin (p + 1) → Fin n, AwayLoc M (f * tupleProd g x)

/-- The Čech differential: the alternating sum of the restrictions along the face maps. -/
noncomputable def cechD (M : Type v) [AddCommGroup M] [Module A M] (g : Fin n → A) (f : A)
    (p : ℕ) : CechTerm M g f p →ₗ[A] CechTerm M g f (p + 1) :=
  LinearMap.pi fun x => ∑ j : Fin (p + 2), (-1 : A) ^ (j : ℕ) •
    (resAway M (dvd_face g f x j)).comp (LinearMap.proj fun i => x (j.succAbove i))

/-- The value of the Čech differential at a tuple `x` is the alternating sum of the restrictions
of `s` along the faces of `x`. -/
theorem cechD_apply (g : Fin n → A) (f : A) (p : ℕ) (s : CechTerm M g f p)
    (x : Fin (p + 2) → Fin n) :
    cechD M g f p s x = ∑ j : Fin (p + 2), (-1 : A) ^ (j : ℕ) •
      resAway M (dvd_face g f x j) (s fun i => x (j.succAbove i)) := by
  simp [cechD, LinearMap.sum_apply]

/-- The comparison map from the complex twisted by `f` to the complex twisted by `f * c`. -/
noncomputable def cechRes (M : Type v) [AddCommGroup M] [Module A M] (g : Fin n → A) (f c : A)
    (p : ℕ) : CechTerm M g f p →ₗ[A] CechTerm M g (f * c) p :=
  LinearMap.pi fun x => (resAway M (dvd_twist g f c x)).comp (LinearMap.proj x)

/-- The comparison map restricts each component along `dvd_twist`. -/
@[simp]
theorem cechRes_apply (g : Fin n → A) (f c : A) (p : ℕ) (s : CechTerm M g f p)
    (x : Fin (p + 1) → Fin n) :
    cechRes M g f c p s x = resAway M (dvd_twist g f c x) (s x) := by
  simp [cechRes]

/-- Restrictions of a Čech cochain along equal tuples agree. -/
theorem resAway_apply_congr {g : Fin n → A} {f : A} {q : ℕ} (s : CechTerm M g f q)
    {x y : Fin (q + 1) → Fin n} (hxy : x = y) {c : A} (hx : f * tupleProd g x ∣ c)
    (hy : f * tupleProd g y ∣ c) : resAway M hx (s x) = resAway M hy (s y) := by
  subst hxy
  rfl

/-- The comparison maps commute with the Čech differentials, so they form a map of
complexes. -/
theorem cechD_comp_cechRes (g : Fin n → A) (f c : A) (p : ℕ) (s : CechTerm M g f p) :
    cechD M g (f * c) p (cechRes M g f c p s) = cechRes M g f c (p + 1) (cechD M g f p s) := by
  funext x
  rw [cechD_apply, cechRes_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, cechRes_apply, resAway_resAway, resAway_resAway]

/-- The Čech differential squares to zero. -/
theorem cechD_cechD (g : Fin n → A) (f : A) (p : ℕ) (s : CechTerm M g f p) :
    cechD M g f (p + 1) (cechD M g f p s) = 0 := by
  funext x
  set F : Fin (p + 3) → Fin (p + 2) → AwayLoc M (f * tupleProd g x) := fun J K =>
    (-1 : A) ^ ((J : ℕ) + (K : ℕ)) •
      resAway M ((dvd_face g f (fun i => x (J.succAbove i)) K).trans (dvd_face g f x J))
        (s fun i => x (J.succAbove (K.succAbove i))) with hF
  have hsum : cechD M g f (p + 1) (cechD M g f p s) x =
      ∑ J : Fin (p + 3), ∑ K : Fin (p + 2), F J K := by
    rw [cechD_apply]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [cechD_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [map_smul, resAway_resAway, smul_smul, ← pow_add, hF]
  rw [Pi.zero_apply, hsum]
  refine sum_sum_eq_zero_of_swap F fun J K => ?_
  have hneg : F (J.succAbove K) (K.predAbove J) = -F J K := by
    simp only [hF]
    rw [sign_swap, neg_smul]
    refine congrArg Neg.neg (congrArg (fun z => (-1 : A) ^ ((J : ℕ) + (K : ℕ)) • z) ?_)
    exact resAway_apply_congr s (funext fun i => congrArg x (succAbove_swap J K i).symm) _ _
  rw [hneg, add_neg_cancel]

/-- The differentials of the Čech complex compose to zero, so the terms `CechTerm M g f p`
together with `cechD M g f p` form a cochain complex. -/
theorem cechD_comp_cechD (g : Fin n → A) (f : A) (p : ℕ) :
    (cechD M g f (p + 1)).comp (cechD M g f p) = 0 :=
  LinearMap.ext fun s => cechD_cechD g f p s

/-! ### The local primitive -/

/-- The primitive of a Čech cochain `s` of degree `p + 1` obtained by prepending the index `i`
to a tuple. It is a cochain of degree `p` for the complex twisted by `f * g i`, and
`cechD_localPrimitive` shows that it is a primitive of `s` there whenever `s` is a cocycle. -/
noncomputable def localPrimitive (M : Type v) [AddCommGroup M] [Module A M] (g : Fin n → A)
    (f : A) (i : Fin n) (p : ℕ) (s : CechTerm M g f (p + 1)) : CechTerm M g (f * g i) p :=
  fun y => resAway M (dvd_cons g f i y) (s (Fin.cons i y))

/-- Evaluating the differential of `s` at a tuple beginning with `i` expresses the restriction
of `s` to the complex twisted by `f * g i` in terms of the differential of the local
primitive. -/
theorem resAway_cechD_cons (g : Fin n → A) (f : A) (i : Fin n) (p : ℕ)
    (s : CechTerm M g f (p + 1)) (x : Fin (p + 2) → Fin n) :
    resAway M (dvd_cons g f i x) (cechD M g f (p + 1) s (Fin.cons i x)) =
      cechRes M g f (g i) (p + 1) s x - cechD M g (f * g i) p (localPrimitive M g f i p s) x := by
  rw [cechD_apply, map_sum, Fin.sum_univ_succ]
  have h0 : resAway M (dvd_cons g f i x) ((-1 : A) ^ ((0 : Fin (p + 3)) : ℕ) •
      resAway M (dvd_face g f (Fin.cons i x) 0)
        (s fun l => (Fin.cons i x : Fin (p + 3) → Fin n) ((0 : Fin (p + 3)).succAbove l))) =
      cechRes M g f (g i) (p + 1) s x := by
    rw [map_smul, resAway_resAway, cechRes_apply]
    simp only [Fin.val_zero, pow_zero, one_smul]
    exact resAway_apply_congr s (by simp) _ _
  have htail : ∀ j : Fin (p + 2), resAway M (dvd_cons g f i x)
      ((-1 : A) ^ ((j.succ : Fin (p + 3)) : ℕ) • resAway M (dvd_face g f (Fin.cons i x) j.succ)
        (s fun l => (Fin.cons i x : Fin (p + 3) → Fin n) (j.succ.succAbove l))) =
      -((-1 : A) ^ (j : ℕ) • resAway M (dvd_face g (f * g i) x j)
        (localPrimitive M g f i p s fun l => x (j.succAbove l))) := by
    intro j
    have hx : (fun l => (Fin.cons i x : Fin (p + 3) → Fin n) (j.succ.succAbove l)) =
        Fin.cons i fun l => x (j.succAbove l) := by
      funext l
      induction l using Fin.cases with
      | zero => simp
      | succ l => simp
    have hsign : ((-1 : A) ^ ((j.succ : Fin (p + 3)) : ℕ)) = -(-1 : A) ^ (j : ℕ) := by
      rw [Fin.val_succ, pow_succ]
      ring
    rw [map_smul, resAway_resAway, hsign, neg_smul, localPrimitive, resAway_resAway]
    exact congrArg (fun z => -((-1 : A) ^ (j : ℕ) • z)) (resAway_apply_congr s hx _ _)
  rw [h0, Finset.sum_congr rfl fun j _ => htail j, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    cechD_apply]

/-- If `s` is a cocycle then its local primitive is a primitive after inverting `g i`. -/
theorem cechD_localPrimitive (g : Fin n → A) (f : A) (i : Fin n) (p : ℕ)
    (s : CechTerm M g f (p + 1)) (hs : cechD M g f (p + 1) s = 0) :
    cechD M g (f * g i) p (localPrimitive M g f i p s) = cechRes M g f (g i) (p + 1) s := by
  funext x
  have h := resAway_cechD_cons g f i p s x
  rw [hs] at h
  simp only [Pi.zero_apply, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-! ### Descent and exactness -/

/-- A function from a finite type to `ℕ` is bounded. -/
private theorem exists_forall_le_nat {ι : Type*} [Finite ι] (k : ι → ℕ) : ∃ K, ∀ i, k i ≤ K :=
  have := Fintype.ofFinite ι
  ⟨Finset.univ.sup k, fun i => Finset.le_sup (Finset.mem_univ i)⟩

/-- Raising the exponent of `c ^ k • x` from `k` to `K ≥ k`. -/
private theorem pow_sub_smul_pow_smul {N : Type*} [AddCommGroup N] [Module A N] (c : A) {k K : ℕ}
    (hk : k ≤ K) (x : N) : c ^ (K - k) • c ^ k • x = c ^ K • x := by
  rw [smul_smul, ← pow_add, Nat.sub_add_cancel hk]

/-- Clearing denominators: a primitive of `s` in the complex twisted by `f * c` yields a
primitive of a `c`-power multiple of `s` in the complex twisted by `f`. -/
theorem exists_cechD_eq_pow_smul (g : Fin n → A) (f c : A) (p : ℕ) (s : CechTerm M g f (p + 1))
    (t : CechTerm M g (f * c) p) (ht : cechD M g (f * c) p t = cechRes M g f c (p + 1) s) :
    ∃ (k : ℕ) (u : CechTerm M g f p), cechD M g f p u = c ^ k • s := by
  classical
  choose k u hu using fun y : Fin (p + 1) → Fin n =>
    exists_resAway_eq_smul (M := M) (by ring : f * c * tupleProd g y = f * tupleProd g y * c)
      (dvd_twist g f c y) (t y)
  obtain ⟨K, hKle⟩ := exists_forall_le_nat k
  set U : CechTerm M g f p := fun y => c ^ (K - k y) • u y with hUdef
  have hUt : cechRes M g f c p U = c ^ K • t := by
    funext y
    rw [cechRes_apply, hUdef, Pi.smul_apply, map_smul, hu y, pow_sub_smul_pow_smul _ (hKle y)]
  have hD : cechRes M g f c (p + 1) (cechD M g f p U) =
      cechRes M g f c (p + 1) (c ^ K • s) := by
    rw [← cechD_comp_cechRes, hUt, map_smul, ht, map_smul]
  have hker : ∀ x : Fin (p + 2) → Fin n,
      ∃ l : ℕ, c ^ l • (cechD M g f p U x - (c ^ K • s) x) = 0 := by
    intro x
    refine exists_pow_smul_eq_zero (M := M)
      (by ring : f * c * tupleProd g x = f * tupleProd g x * c) (dvd_twist g f c x) _ ?_
    have hx := congrFun hD x
    rw [cechRes_apply, cechRes_apply] at hx
    rw [map_sub, hx, sub_self]
  choose l hl using hker
  obtain ⟨L, hLle⟩ := exists_forall_le_nat l
  refine ⟨L + K, c ^ L • U, ?_⟩
  funext x
  have h1 : c ^ L • (cechD M g f p U x - (c ^ K • s) x) = 0 := by
    rw [← pow_sub_smul_pow_smul c (hLle x) (cechD M g f p U x - (c ^ K • s) x), hl x,
      smul_zero]
  rw [smul_sub, sub_eq_zero] at h1
  rw [map_smul, Pi.smul_apply, Pi.smul_apply, h1, Pi.smul_apply, smul_smul, ← pow_add]

/-- **Exactness of the Čech complex in positive degrees.** If the family `g` generates the unit
ideal of `A`, then every cocycle of positive degree in the Čech complex of `g` with
coefficients in `M` (twisted by any element `f`) is a coboundary. Together with
`cechD_comp_cechD` this says that the cohomology of the complex vanishes in all positive
degrees; the untwisted Čech complex of `M` is the case `f = 1`. -/
theorem cech_exact (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) (f : A) (p : ℕ)
    (s : CechTerm M g f (p + 1)) (hs : cechD M g f (p + 1) s = 0) :
    ∃ u : CechTerm M g f p, cechD M g f p u = s := by
  classical
  choose k u hu using fun i : Fin n =>
    exists_cechD_eq_pow_smul g f (g i) p s (localPrimitive M g f i p s)
      (cechD_localPrimitive g f i p s hs)
  obtain ⟨K, hKle⟩ := exists_forall_le_nat k
  have hu' : ∀ i : Fin n, ∃ v : CechTerm M g f p, cechD M g f p v = g i ^ K • s := by
    intro i
    refine ⟨g i ^ (K - k i) • u i, ?_⟩
    rw [map_smul, hu i, pow_sub_smul_pow_smul _ (hKle i)]
  choose v hv using hu'
  have himg : (Set.range fun i => g i ^ K) = (fun x : A => x ^ K) '' Set.range g :=
    Set.range_comp _ _
  have h1 : (1 : A) ∈ Ideal.span (Set.range fun i => g i ^ K) := by
    rw [himg, Ideal.span_pow_eq_top (Set.range g) hg K]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp h1
  simp only [smul_eq_mul] at hc
  refine ⟨∑ i, c i • v i, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun i _ => by rw [map_smul, hv i, smul_smul],
    ← Finset.sum_smul, hc, one_smul]

end Stacks.RingTheory.CechAcyclicity

end
